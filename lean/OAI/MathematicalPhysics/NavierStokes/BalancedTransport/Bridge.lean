import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.MachineHalting
import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.Periodic

namespace OAI

noncomputable section
namespace BalancedTransport.Recorder.Exec
variable {Q Γ : Type*} {M : Machine Q Γ}

theorem split {n m : ℕ} {c d : Configuration Q Γ} (h : Exec M (n + m) c d) :
    ∃ e, Exec M n c e ∧ Exec M m e d := by
  induction n generalizing c with
  | zero => exact ⟨c, .refl _, by simpa using h⟩
  | succ n ih =>
    have hh : Exec M ((n + m) + 1) c d := by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    cases hh with
    | @cons _ _ b _ hcb hbd =>
      obtain ⟨e, hce, hed⟩ := ih hbd
      exact ⟨e, .cons hcb hce, hed⟩

lemma take {m n : ℕ} {c d : Configuration Q Γ} (h : Exec M n c d) (hm : m ≤ n) :
    ∃ e, Exec M m c e := by
  have hh : Exec M (m + (n - m)) c d := by rwa [Nat.add_sub_of_le hm]
  obtain ⟨e, he, _⟩ := hh.split
  exact ⟨e, he⟩

lemma one_iff {c d : Configuration Q Γ} : Exec M 1 c d ↔ Step M c d := by
  constructor
  · intro h
    cases h with
    | cons h h' => cases h'; exact h
  · exact single

lemma snoc {n : ℕ} {c d : Configuration Q Γ} (h : Exec M (n + 1) c d) :
    ∃ e, Exec M n c e ∧ Step M e d := by
  obtain ⟨e, he, hed⟩ := h.split
  exact ⟨e, he, one_iff.mp hed⟩

end BalancedTransport.Recorder.Exec
end

noncomputable section
namespace BalancedTransport.Recorder.Checkpoint
variable {Q Γ : Type*} {M : Machine Q Γ}

theorem arbitrarily_long_execution (M : Machine Q Γ) (c : Checkpoint Q Γ)
    (hh : ¬∃ d, Relation.ReflTransGen (WorkStep M) c d ∧ d.state = M.halt)
    (n : ℕ) : ∃ d, Exec M n (c.expand M) d := by
  induction n using Nat.strong_induction_on generalizing c with
  | h n ih =>
    have hc : c.state ≠ M.halt := fun he => hh ⟨c, .refl, he⟩
    let m := 2 * (c.right.length + 1) + 2
    have hm : 0 < m := by dsimp [m]; omega
    have he : Exec M m (c.expand M) ((c.next M).expand M) := next_exec M c hc
    by_cases hnm : n ≤ m
    · exact he.take hnm
    · have hh' : ¬∃ d, Relation.ReflTransGen (WorkStep M) (c.next M) d ∧ d.state = M.halt := by
        rintro ⟨d, hd, hs⟩
        exact hh ⟨d, (Relation.ReflTransGen.single (show WorkStep M c (c.next M) from
          ⟨hc, rfl⟩)).trans hd, hs⟩
      obtain ⟨d, hd⟩ := ih (n - m) (by omega) (c.next M) hh'
      exact ⟨d, by simpa [Nat.add_sub_of_le (le_of_not_ge hnm)] using he.trans hd⟩

end BalancedTransport.Recorder.Checkpoint
end

noncomputable section
namespace BalancedTransport.Recorder
variable {Q Γ : Type*} {M : Machine Q Γ}
variable [Fintype Q] [Fintype Γ] [DecidableEq Q]

lemma Configuration.code_guard {M : Machine Q Γ} {c : Configuration Q Γ}
    (hc : c.control ≠ .ready M.halt) : 4 ≤ c.code M 0 := by
  have hp : (1 : ℝ) ≤ placement M c.control := by
    exact_mod_cast placement_positive M c.control hc
  have hb := (Coding.stream_mem_interior base_pos digit digit_pos digit_upper (c.stacks 0)).1
  change 4 ≤ 4 * (placement M c.control : ℝ) + Coding.stream digit (c.stacks 0)
  linarith

def GuardedTemplate (M : Machine Q Γ) (v : Velocity) : Prop :=
  ∀ r : Row Q Γ, r.valid M → ∀ x,
    x ∈ (r.instruction M).sourceBox (base Q Γ : ℝ)⁻¹
      (fun a => (digit a : ℝ)) (placement M) →
    ∃ γ : ℝ → Space,
      γ 0 = x ∧ γ 1 = (r.instruction M).fullMap M x ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt γ (v t (γ t)) (Set.Icc 0 1) t) ∧
      ((r.instruction M).targetControl ≠ .ready M.halt →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∉ observer)

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Geometry
open Set
open scoped NNReal

lemma IsMaterialFlow.shift_unit {U : Velocity} {X : MaterialFlow}
    (hX : IsMaterialFlow U X) (a : Space) {b : ℝ} (hb : 0 ≤ b)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (fun s => X (s + b) a) (U (t + b) (X (t + b) a)) (Icc 0 1) t := by
  have hd := (hX.2 a (t + b) (add_nonneg ht.1 hb)).scomp t
    ((hasDerivAt_id t).add_const b).hasDerivWithinAt
    (show MapsTo (fun s : ℝ => s + b) (Icc 0 1) (Ici 0) from
      fun s hs => add_nonneg hs.1 hb)
  simpa only [Function.comp_def, one_smul, id_eq] using hd

lemma loadedRepeat_on_later_unit {load v : Velocity}
    (hl : TimeCollars load) (hv : TimeCollars v) (n : ℕ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    loadedRepeat load v (t + ((n : ℝ) + 1)) = v t := by
  rw [loadedRepeat_after hl (by linarith [ht.1, Nat.cast_nonneg (α := ℝ) n])]
  have hp := (repeatTemplate_zero_period v).nat_mul (n + 1) t
  simp only [Nat.cast_add, Nat.cast_one, mul_one] at hp
  rw [hp, repeatTemplate_on_unit hv ht]

lemma materialFlow_loading {z : Space} {η : ℝ} (hη : 0 < η)
    {v : Velocity} (hv : TimeCollars v) {X : MaterialFlow}
    (hX : IsMaterialFlow (loadedRepeat (loadingVelocity z η) v) X)
    {L : ℝ≥0}
    (hL : ∀ t, 0 ≤ t → LipschitzWith L (loadingVelocity z η t))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    X t fixedLabel = loadingPath z t := by
  have hd : ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun s => X s fixedLabel)
        (loadingVelocity z η s (X s fixedLabel)) (Icc 0 1) s := by
    intro s hs
    have hh := (hX.2 fixedLabel s hs.1).mono (show Icc (0 : ℝ) 1 ⊆ Ici 0 from Icc_subset_Ici_self)
    rwa [loadedRepeat_before hv hs.1 hs.2] at hh
  exact curves_agree_on_overlap hL (HasDerivWithinAt.continuousOn hd)
    (HasDerivWithinAt.continuousOn (fun s _ => (loadingPath_hasDerivAt z hη s).hasDerivWithinAt))
    hd (fun s _ => (loadingPath_hasDerivAt z hη s).hasDerivWithinAt)
    ((hX.1 fixedLabel).trans (loadingPath_start z).symm) ht.1 ht.2 ht.2

end BalancedTransport.Geometry
end

noncomputable section
namespace BalancedTransport.Recorder
open Set BalancedTransport.Geometry
open scoped NNReal
variable {Q Γ : Type*} [Fintype Q] [Fintype Γ] [DecidableEq Q]
variable {M : Machine Q Γ} {v load : Velocity} {X : MaterialFlow} {L : ℝ≥0}

lemma guarded_period_step (hg : GuardedTemplate M v) (hv : TimeCollars v)
    (hl : TimeCollars load)
    (hLip : ∀ t, 0 ≤ t → LipschitzWith L (v t))
    (hX : IsMaterialFlow (loadedRepeat load v) X)
    {c d : Configuration Q Γ} (hcd : Step M c d) (n : ℕ) (a : Space)
    (hstart : X ((n : ℝ) + 1) a = c.code M) :
    X ((n : ℝ) + 2) a = d.code M ∧
      (d.control ≠ .ready M.halt → ∀ t ∈ Icc (0 : ℝ) 1,
        X (t + ((n : ℝ) + 1)) a ∉ observer) := by
  obtain ⟨r, hr, tails, rfl, rfl⟩ := hcd
  obtain ⟨γ, hγ₀, hγ₁, hdγ, hguard⟩ := hg r hr _
    ((r.instruction M).source_code_mem M tails)
  have hdX : ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun s => X (s + ((n : ℝ) + 1)) a)
        (v s (X (s + ((n : ℝ) + 1)) a)) (Icc 0 1) s := by
    intro s hs
    have hh := Geometry.IsMaterialFlow.shift_unit hX a
      (show (0 : ℝ) ≤ (n : ℝ) + 1 by positivity) hs
    rwa [loadedRepeat_on_later_unit hl hv n hs] at hh
  have heq : ∀ t ∈ Icc (0 : ℝ) 1, X (t + ((n : ℝ) + 1)) a = γ t := by
    intro t ht
    exact curves_agree_on_overlap hLip (HasDerivWithinAt.continuousOn hdX)
      (HasDerivWithinAt.continuousOn hdγ) hdX hdγ
      (by simpa only [zero_add] using hstart.trans hγ₀.symm) ht.1 ht.2 ht.2
  constructor
  · have he := (heq 1 ⟨by norm_num, le_rfl⟩).trans
      (hγ₁.trans ((r.instruction M).fullMap_code M tails))
    simpa only [show (1 : ℝ) + ((n : ℝ) + 1) = (n : ℝ) + 2 by ring] using he
  · intro hnh t ht
    rw [heq t ht]
    exact hguard hnh t ht

lemma guarded_execution_endpoint (hg : GuardedTemplate M v) (hv : TimeCollars v)
    (hl : TimeCollars load)
    (hLip : ∀ t, 0 ≤ t → LipschitzWith L (v t))
    (hX : IsMaterialFlow (loadedRepeat load v) X)
    {c d : Configuration Q Γ} {n : ℕ} (h : Exec M n c d) (a : Space)
    (hinit : X 1 a = c.code M) : X ((n : ℝ) + 1) a = d.code M := by
  induction n generalizing d with
  | zero => cases h; simpa using hinit
  | succ n ih =>
      obtain ⟨e, he, hed⟩ := h.snoc
      have hn := guarded_period_step hg hv hl hLip hX hed n a (ih he)
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hn.1

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Geometry
open Set

lemma TimeCollars.repeats {v : Velocity} (hv : TimeCollars v) : RepeatsAfter 1 v := by
  intro t ht
  rw [hv t (Or.inr (by linarith)), hv (t + 1) (Or.inr (by linarith))]

end BalancedTransport.Geometry
end

noncomputable section
namespace BalancedTransport.Recorder
open Set BalancedTransport.Geometry
open scoped NNReal
variable {Q Γ : Type*} [Fintype Q] [Fintype Γ] [DecidableEq Q] [DecidableEq Γ]

theorem loaded_template_halting_iff (M : Machine Q Γ) (c : Checkpoint Q Γ)
    {η : ℝ} (hη : 0 < η) {K : Set Space} (hK : IsCompact K) {v : Velocity}
    (hv : JointSmooth v) (hc : TimeCollars v) (hs : SpatiallySupported K v)
    (hg : GuardedTemplate M v) {X : MaterialFlow}
    (hX : IsMaterialFlow (loadedRepeat (loadingVelocity ((c.expand M).code M) η) v) X) :
    (∃ t : ℝ, 0 ≤ t ∧ X t fixedLabel ∈ observer) ↔
      ∃ d, Relation.ReflTransGen (Checkpoint.WorkStep M) c d ∧ d.state = M.halt := by
  let z := (c.expand M).code M
  have hlc : TimeCollars (loadingVelocity z η) := fun _ ht => loadingVelocity_zero ht
  obtain ⟨L, hLip⟩ := spatial_lipschitz_of_boundedMixed hv
    (boundedMixed_of_compact_repeating hK hv hs hc.repeats)
  obtain ⟨L₀, hLip₀⟩ := spatial_lipschitz_of_boundedMixed (loadingVelocity_jointSmooth z η)
    (loadingVelocity_boundedMixed z hη)
  have hload : ∀ t ∈ Icc (0 : ℝ) 1, X t fixedLabel = loadingPath z t :=
    fun _ ht => materialFlow_loading hη hc hX hLip₀ ht
  have hinit : X 1 fixedLabel = z :=
    (hload 1 ⟨by norm_num, le_rfl⟩).trans (loadingPath_end z)
  have hend {n : ℕ} {d : Configuration Q Γ} (hd : Exec M n (c.expand M) d) :
      X ((n : ℝ) + 1) fixedLabel = d.code M :=
    guarded_execution_endpoint hg hc hlc hLip hX hd fixedLabel hinit
  constructor
  · rintro ⟨t, ht, hobs⟩
    by_contra hn
    have hstate : c.state ≠ M.halt := fun he => hn ⟨c, .refl, he⟩
    by_cases ht₁ : t ≤ 1
    · rw [hload t ⟨ht, ht₁⟩] at hobs
      exact loadingPath_avoids_observer
        (Configuration.code_guard (show (c.expand M).control ≠ .ready M.halt by
          exact fun he => hstate (Control.ready.inj he))) t hobs
    · let n : ℕ := ⌊t - 1⌋₊
      have hnf : (n : ℝ) ≤ t - 1 := Nat.floor_le (by linarith)
      have hnt : t - 1 < (n : ℝ) + 1 := Nat.lt_floor_add_one (t - 1)
      let s := t - ((n : ℝ) + 1)
      have hs' : s ∈ Icc (0 : ℝ) 1 := by dsimp [s]; constructor <;> linarith
      obtain ⟨e, he⟩ := c.arbitrarily_long_execution M hn (n + 1)
      obtain ⟨d, hd, hde⟩ := he.snoc
      have hne : e.control ≠ .ready M.halt := fun hh =>
        hn (Checkpoint.halt_reflection M he hh)
      have hguard := (guarded_period_step hg hc hlc hLip hX hde n fixedLabel (hend hd)).2
        hne s hs'
      have heq : s + ((n : ℝ) + 1) = t := sub_add_cancel _ _
      exact hguard (by rwa [heq])
  · intro hhalt
    obtain ⟨n, d, hd, hh⟩ := (Checkpoint.halting_iff M c).mpr hhalt
    exact ⟨(n : ℝ) + 1, by positivity, by rw [hend hd]; exact (code_mem_observer_iff M d).mpr hh⟩

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.FiniteMachine
open BalancedTransport.Geometry

theorem compiled_continuous_halting_iff (M : FiniteMachine) (w : Input M)
    {η : ℝ} (hη : 0 < η) {K : Set Space} (hK : IsCompact K) {v : Velocity}
    (hv : JointSmooth v) (hc : TimeCollars v) (hs : SpatiallySupported K v)
    (hg : Recorder.GuardedTemplate M.normalized v) {X : MaterialFlow}
    (hX : IsMaterialFlow
      (loadedRepeat (loadingVelocity (((M.initialWork w).expand M.normalized).code M.normalized) η) v) X) :
    (∃ t : ℝ, 0 ≤ t ∧ X t fixedLabel ∈ observer) ↔ Halts M w :=
  (Recorder.loaded_template_halting_iff M.normalized (M.initialWork w) hη hK hv hc hs hg hX).trans
    (normalized_halting_iff M w)

end BalancedTransport.FiniteMachine
end

end OAI
