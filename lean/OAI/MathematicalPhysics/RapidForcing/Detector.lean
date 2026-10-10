import OAI.MathematicalPhysics.RapidForcing.ParticlePaths
import OAI.MathematicalPhysics.RapidForcing.MachineRun
import OAI.MathematicalPhysics.RapidForcing.Flow

namespace OAI

open scoped BigOperators ENNReal Topology NNReal
open Set MeasureTheory
namespace RapidForcing

lemma addressPath_smooth (M : Machine) (d : ScaleData) (n m : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (addressPath M d n m) :=
  contDiff_const.add (theta_smooth.smul contDiff_const)

lemma materialFlow_loading (M : Machine) (w : M.Input)
    {X : ℝ → Space → Space} (hX : MaterialFlow (addressedVelocity M w) X)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    X t 0 = θ t • vec (-1) ((M.scaleData w).δ 0 * (M.initialDigit w : ℝ)) 0 := by
  let c : ℝ → Space := fun s => θ s • vec (-1) ((M.scaleData w).δ 0 * (M.initialDigit w : ℝ)) 0
  have hc : ContDiff ℝ (⊤ : ℕ∞) c := theta_smooth.smul contDiff_const
  have htr : TrajectoryOn (addressedVelocity M w) 0 1 c := by
    refine ⟨?_, ?_⟩
    · simp [c, theta_zero (by norm_num : (0 : ℝ) ≤ 1 / 4)]
    · intro s hs
      have h := addressedVelocity_at_loadingPath M w hs.2
      change addressedVelocity M w s (c s) = deriv c s at h
      rw [h]
      exact (hc.differentiable (by simp) s).hasDerivAt.hasDerivWithinAt
  exact (hX.2.2 1 zero_lt_one 0 c htr t ht).symm

lemma materialFlow_addressPath (M : Machine) (w : M.Input)
    {X : ℝ → Space → Space} (hX : MaterialFlow (addressedVelocity M w) X)
    (n m : ℕ) (hm : m ≤ (M.scaleData w).D n)
    (hstart : X (1 + (n : ℝ)) 0 = addressCenter (M.scaleData w) n m)
    {σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) 1) :
    X (1 + (n : ℝ) + σ) 0 = addressPath M (M.scaleData w) n m σ := by
  let c := addressPath M (M.scaleData w) n m
  let η : ℝ → Space := fun t => c (t - 1 - (n : ℝ))
  have hc := addressPath_smooth M (M.scaleData w) n m
  have he : EqOn (fun t => X t 0) η (Icc (1 + (n : ℝ)) (2 + (n : ℝ))) := by
    apply solution_unique_Icc (addressedVelocity_joint_smooth M w)
      (addressedVelocity_supported M w) (by positivity)
    · intro t ht
      apply (hX.2.1 0 t (by have := Nat.cast_nonneg (α := ℝ) n; linarith [ht.1])).mono
      intro s hs
      have := Nat.cast_nonneg (α := ℝ) n
      exact le_trans (by positivity) hs.1
    · intro t ht
      have ht' : t - 1 - (n : ℝ) ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [ht.1, ht.2]
      have hh := addressedVelocity_at_addressPath M w n m hm ht'
      rw [show 1 + (n : ℝ) + (t - 1 - (n : ℝ)) = t by ring] at hh
      change addressedVelocity M w t (η t) = deriv c (t - 1 - (n : ℝ)) at hh
      rw [hh]
      have hshift : HasDerivAt (fun s : ℝ => s - 1 - (n : ℝ)) 1 t :=
        ((hasDerivAt_id t).sub_const 1).sub_const (n : ℝ)
      have hd := (hc.differentiable (by simp) (t - 1 - (n : ℝ))).hasDerivAt.scomp t hshift
      simpa only [one_smul, Function.comp_def] using hd.hasDerivWithinAt
    · rw [hstart]
      dsimp [η, c]
      rw [show 1 + (n : ℝ) - 1 - (n : ℝ) = 0 by ring]
      simp [addressPath, theta_zero (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  have h := he (show 1 + (n : ℝ) + σ ∈ Icc (1 + (n : ℝ)) (2 + (n : ℝ)) from
    ⟨by linarith [hσ.1], by linarith [hσ.2]⟩)
  change X (1 + (n : ℝ) + σ) 0 = c (1 + (n : ℝ) + σ - 1 - (n : ℝ)) at h
  rwa [show 1 + (n : ℝ) + σ - 1 - (n : ℝ) = σ by ring] at h

namespace ScaleData
lemma history_zero (d : ScaleData) (k : ℕ → ℕ) : d.history k 0 = d.δ 0 * (k 0 : ℝ) := by
  simp [history]

lemma history_succ (d : ScaleData) (k : ℕ → ℕ) (n : ℕ) :
    d.history k (n + 1) = d.history k n + d.δ (n + 1) * (k (n + 1) : ℝ) :=
  Finset.sum_range_succ _ _
end ScaleData

lemma runAddress_center (M : Machine) (w : M.Input) (n : ℕ) :
    addressCenter (M.scaleData w) n ((M.scaleData w).addressIndex (M.runCode w) n) =
      vec (-1) ((M.scaleData w).history (M.runCode w) n) 0 := by
  unfold addressCenter
  rw [← (M.scaleData w).history_eq_address]

lemma runAddress_mod (M : Machine) (w : M.Input) (n : ℕ) :
    ((M.scaleData w).addressIndex (M.runCode w) n) % (M.scaleData w).capacity n = M.runCode w n :=
  (M.scaleData w).address_mod_capacity (M.runCode w) n (M.runCode_lt w n)

lemma runAddress_le_D (M : Machine) (w : M.Input) (n : ℕ) :
    (M.scaleData w).addressIndex (M.runCode w) n ≤ (M.scaleData w).D n :=
  ((M.scaleData w).address_lt_D (M.runCode w) n (fun j _ => M.runCode_lt w j)).le

lemma runAddress_nonterminal_end (M : Machine) (w : M.Input) {n : ℕ}
    (hn : (M.run w n).state.val ≠ M.states) :
    addressPath M (M.scaleData w) n ((M.scaleData w).addressIndex (M.runCode w) n) 1 =
      vec (-1) ((M.scaleData w).history (M.runCode w) (n + 1)) 0 := by
  unfold addressPath
  rw [runAddress_center, theta_one (by norm_num : (3 / 4 : ℝ) ≤ 1), one_smul]
  unfold addressDisplacement
  rw [runAddress_mod]
  dsimp only
  rw [M.runCode_terminal, ite_eq_right hn, ← M.runCode_succ w hn, (M.scaleData w).history_succ]
  ext i
  fin_cases i <;> simp [vec]

lemma runAddress_nonterminal_first (M : Machine) (w : M.Input) {n : ℕ}
    (hn : (M.run w n).state.val ≠ M.states) (σ : ℝ) :
    (addressPath M (M.scaleData w) n ((M.scaleData w).addressIndex (M.runCode w) n) σ) 0 = -1 := by
  unfold addressPath addressDisplacement
  rw [runAddress_mod]
  dsimp only
  rw [M.runCode_terminal, ite_eq_right hn]
  simp [addressCenter, vec]

lemma runAddress_terminal_first (M : Machine) (w : M.Input) {n : ℕ}
    (hn : (M.run w n).state.val = M.states) :
    (addressPath M (M.scaleData w) n ((M.scaleData w).addressIndex (M.runCode w) n) 1) 0 =
      -1 - (M.scaleData w).b n := by
  unfold addressPath addressDisplacement
  rw [runAddress_mod]
  dsimp only
  rw [M.runCode_terminal, ite_eq_left hn, theta_one (by norm_num : (3 / 4 : ℝ) ≤ 1)]
  simp [addressCenter, vec, sub_eq_add_neg]

theorem materialFlow_at_codeTime (M : Machine) (w : M.Input)
    {X : ℝ → Space → Space} (hX : MaterialFlow (addressedVelocity M w) X)
    (n : ℕ) (hn : ∀ j < n, (M.run w j).state.val ≠ M.states) :
    X (1 + (n : ℝ)) 0 = vec (-1) ((M.scaleData w).history (M.runCode w) n) 0 := by
  induction n with
  | zero =>
    simpa only [Nat.cast_zero, add_zero, (M.scaleData w).history_zero, M.runCode_zero,
      theta_one (by norm_num : (3 / 4 : ℝ) ≤ 1), one_smul] using
      materialFlow_loading M w hX (t := 1) (by constructor <;> norm_num)
  | succ n ih =>
    have hstart : X (1 + (n : ℝ)) 0 =
        addressCenter (M.scaleData w) n ((M.scaleData w).addressIndex (M.runCode w) n) := by
      rw [ih (fun j hj => hn j (by omega)), runAddress_center]
    have h := materialFlow_addressPath M w hX n _ (runAddress_le_D M w n) hstart
      (σ := 1) (by constructor <;> norm_num)
    rw [runAddress_nonterminal_end M w (hn n (by omega))] at h
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using h

lemma materialFlow_run_slot (M : Machine) (w : M.Input)
    {X : ℝ → Space → Space} (hX : MaterialFlow (addressedVelocity M w) X)
    (n : ℕ) (hn : ∀ j < n, (M.run w j).state.val ≠ M.states)
    {σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) 1) :
    X (1 + (n : ℝ) + σ) 0 =
      addressPath M (M.scaleData w) n ((M.scaleData w).addressIndex (M.runCode w) n) σ := by
  apply materialFlow_addressPath M w hX n _ (runAddress_le_D M w n) _ hσ
  rw [materialFlow_at_codeTime M w hX n hn, runAddress_center]

lemma materialFlow_nonhalting_first (M : Machine) (w : M.Input)
    {X : ℝ → Space → Space} (hX : MaterialFlow (addressedVelocity M w) X)
    (hnh : ¬ M.Halts w) {t : ℝ} (ht : 0 ≤ t) : -1 ≤ (X t 0) 0 := by
  have hn (n : ℕ) : (M.run w n).state.val ≠ M.states := fun h => hnh ⟨n, h⟩
  by_cases ht1 : t ≤ 1
  · rw [materialFlow_loading M w hX ⟨ht, ht1⟩]
    simp only [PiLp.smul_apply, vec_zero_coord, smul_eq_mul, mul_neg_one]
    exact neg_le_neg (theta_le_one t)
  · let n := Nat.floor (t - 1)
    have hn1 : (n : ℝ) ≤ t - 1 := Nat.floor_le (by linarith)
    have hn2 : t - 1 < (n : ℝ) + 1 := Nat.lt_floor_add_one _
    have hσ : t - 1 - (n : ℝ) ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith
    have he := materialFlow_run_slot M w hX n (fun j _ => hn j) hσ
    rw [show 1 + (n : ℝ) + (t - 1 - (n : ℝ)) = t by ring] at he
    rw [he, runAddress_nonterminal_first M w (hn n)]

theorem materialFlow_halting_iff (M : Machine) (w : M.Input)
    {X : ℝ → Space → Space} (hX : MaterialFlow (addressedVelocity M w) X) :
    M.Halts w ↔ ∃ t : ℝ, 0 ≤ t ∧ (X t 0) 0 < -1 := by
  constructor
  · intro hhalt
    let n := Nat.find hhalt
    have hn : (M.run w n).state.val = M.states := Nat.find_spec hhalt
    have hprev : ∀ j < n, (M.run w j).state.val ≠ M.states := by
      intro j hj he
      have hlu := Nat.find_min' hhalt he
      omega
    refine ⟨1 + (n : ℝ) + 1, by positivity, ?_⟩
    rw [materialFlow_run_slot M w hX n hprev (show (1 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num),
      runAddress_terminal_first M w hn]
    have := (M.scaleData w).b_pos n
    linarith
  · rintro ⟨t, ht, he⟩
    by_contra hnh
    have := materialFlow_nonhalting_first M w hX hnh ht
    linarith

theorem addressed_particle_detection (M : Machine) (w : M.Input) :
    ∃ X : ℝ → Space → Space, MaterialFlow (addressedVelocity M w) X ∧
      (M.Halts w ↔ ∃ t : ℝ, 0 ≤ t ∧ (X t 0) 0 < -1) := by
  obtain ⟨X, hX⟩ := addressed_materialFlow M w
  exact ⟨X, hX, materialFlow_halting_iff M w hX⟩

end RapidForcing

end OAI
