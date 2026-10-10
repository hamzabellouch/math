import Mathlib
import OAI.Probability.GaussianRegression.Main
import OAI.Probability.MemoryPrecision.CoefficientStep

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression

def BlockCount (T p : ℕ) : ℕ := ⌈(T:ℝ)/(p:ℝ)⌉₊
lemma blockCount_mul_ge (T : ℕ) {p : ℕ} (hp : 0 < p) : T ≤ BlockCount T p * p := by
  have hp' : (0:ℝ) < p := by exact_mod_cast hp
  have h := (div_le_iff₀ hp').mp (Nat.le_ceil ((T:ℝ)/(p:ℝ)))
  exact_mod_cast h
lemma blockCount_mono {T S p : ℕ} (h : T ≤ S) : BlockCount T p ≤ BlockCount S p :=
  Nat.ceil_mono (div_le_div_of_nonneg_right (by exact_mod_cast h) (by positivity))
@[simp] lemma blockCount_zero (p : ℕ) : BlockCount 0 p = 0 := by simp [BlockCount]
lemma blockCount_pos {T p : ℕ} (hT : 0 < T) (hp : 0 < p) : 0 < BlockCount T p := by
  apply Nat.ceil_pos.mpr
  exact div_pos (by exact_mod_cast hT) (by exact_mod_cast hp)

def StepConstant : ℝ := Classical.choose coefficient_step
lemma stepConstant_one : 1 ≤ StepConstant := (Classical.choose_spec coefficient_step).1
lemma stepConstant_pos : 0 < StepConstant := lt_of_lt_of_le zero_lt_one stepConstant_one

def RealStep (d N : ℕ) : ℝ := StepConstant^d * (N:ℝ)^(1/((d/8:ℕ):ℝ))
lemma realStep_one (d : ℕ) {N : ℕ} (hN : 1 ≤ N) : 1 ≤ RealStep d N := by
  apply one_le_mul_of_one_le_of_one_le
  · exact one_le_pow₀ stepConstant_one
  · exact Real.one_le_rpow (by exact_mod_cast hN) (by positivity)
lemma realStep_pos (d : ℕ) {N : ℕ} (hN : 1 ≤ N) : 0 < RealStep d N :=
  lt_of_lt_of_le zero_lt_one (realStep_one d hN)

lemma sphere_deterministic_step {d m N : ℕ} (hd : 16 ≤ d) (hm : 1 ≤ m)
    (hmp : m ≤ d/8) (hN : 1 ≤ N) {α H : ℝ}
    (hαlo : ((d:ℝ)-1)/2 ≤ α) (hαhi : α ≤ (d:ℝ)/2) (hH : 0 < H)
    (h : Fin N → Space d → ℝ≥0∞) (hh : ∀ w, Measurable (h w))
    (hh1 : ∀ w s, h w s ≤ 1)
    (hb : ∀ w, SphereBallBound (fun s => h w s.val) H α)
    (φ : ((Fin m → Space d) × (Fin m → ℝ)) → Fin N) (hφ : Measurable φ) :
    SphereBallBound (fun s => blockValue h φ s.val) (RealStep d N * H) α := by
  classical
  let g (w : Fin N) (x : (Fin m → Space d) × (Fin m → ℝ)) : ℝ≥0∞ :=
    if φ x = w then 1 else 0
  have hg (w) : Measurable (g w) := by
    exact Measurable.ite (measurableSet_eq_fun hφ measurable_const) measurable_const measurable_const
  have hg1 (x) : ∑ w, g w x ≤ 1 := by simp [g]
  have hb' := (Classical.choose_spec coefficient_step).2 d m N hd hm hmp hN α H
    hαlo hαhi hH (fun w s => h w s.val) (fun w => (hh w).comp measurable_subtype_coe)
    (fun w s => hh1 w s.val) hb g hg hg1
  convert hb' using 1
  · funext s
    unfold blockValue SphereBlock
    congr 1
    funext A
    simp [g]
  · rfl

lemma SphereBallBound.mono {d : ℕ} {h : Sphere d → ℝ≥0∞} {H K α : ℝ}
    (hh : SphereBallBound h H α) (hHK : H ≤ K) : SphereBallBound h K α := by
  intro z r hr
  exact (hh z r hr).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hHK (by positivity)))

lemma real_continuation_mass {d N : ℕ} (hd : 16 ≤ d) (hN : 1 ≤ N)
    {δ : ℕ → Fin N → (Space d × ℝ) → Fin N}
    {w : ℕ → Fin N → Space d → ℝ≥0∞}
    (hδ : ∀ n j, Measurable (δ n j)) (hw : ∀ n j, Measurable (w n j))
    (hw1 : ∀ n j s, w n j s ≤ 1) {H α : ℝ} (hH : 0 < H)
    (hαlo : ((d:ℝ)-1)/2 ≤ α) (hαhi : α ≤ (d:ℝ)/2)
    (hlocal : ∀ n j, SphereBallBound (fun s => w n j s.val) H α)
    (b k : ℕ) (hk : k ≤ b*(d/8)) (n : ℕ) (j : Fin N) :
    SphereBallBound (fun s => continuation δ w n k j s.val)
      (H * RealStep d N ^ b) α := by
  have hp : 0 < d/8 := by omega
  have hK := realStep_one d hN
  have hK0 := realStep_pos d hN
  induction b generalizing k n j with
  | zero =>
    have : k = 0 := by omega
    subst k
    simpa [continuation] using hlocal n j
  | succ b ih =>
    by_cases hk0 : k = 0
    · subst k
      apply (hlocal n j).mono
      simpa [continuation] using le_mul_of_one_le_right hH.le (one_le_pow₀ hK)
    · let m := min k (d/8)
      have hm : 1 ≤ m := by dsimp [m]; omega
      have hmp : m ≤ d/8 := min_le_right _ _
      have hmk : m ≤ k := min_le_left _ _
      have hk' : k-m ≤ b*(d/8) := by
        dsimp [m]
        rw [Nat.succ_mul] at hk
        omega
      have hb := sphere_deterministic_step hd hm hmp hN hαlo hαhi
        (mul_pos hH (pow_pos hK0 b))
        (fun a => continuation δ w (n+m) (k-m) a)
        (fun a => measurable_continuation hδ hw _ _ a)
        (fun a s => continuation_le_one hw1 _ _ a s)
        (fun a => ih (k-m) hk' (n+m) a) (streamRoute δ n m j)
        (measurable_streamRoute hδ n m j)
      have he : (fun s : Sphere d => continuation δ w n k j s.val) =
          (fun s : Sphere d => blockValue (fun a => continuation δ w (n+m) (k-m) a)
            (streamRoute δ n m j) s.val) := by
        funext s
        simpa [Nat.add_sub_of_le hmk] using continuation_unroll hδ n m (k-m) j s.val
      rw [he]
      convert hb using 1
      rw [pow_succ]; ring

end MemoryPrecision


end

end OAI
