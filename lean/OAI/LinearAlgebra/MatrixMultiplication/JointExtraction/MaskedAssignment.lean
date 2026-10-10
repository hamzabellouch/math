import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.MaskedSelection

namespace OAI

/-! Joint tensor extraction, compatibility and entropy estimates. -/

noncomputable section

namespace MatrixMultiplication.JointMaskedSelection.OrbitData

open JointCoarseHashing

attribute [local instance] Classical.propDecidable

variable {P E O V : Type*} [Fintype P] [Fintype E]

def actualTargets (d : OrbitData P E O V) : Finset (Triple P) :=
  Finset.univ.image d.coarse

theorem coarse_mem_actualTargets (d : OrbitData P E O V) (e : E) :
    d.coarse e ∈ d.actualTargets :=
  Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩

def xFlag (k : ℕ) (U : Finset (ZMod (37 ^ k))) (s : Sample P k) (I : Word P) : Prop :=
  JointHashing.xHash s (castWord k I) ∈ U

def yFlag (k : ℕ) (U : Finset (ZMod (37 ^ k))) (s : Sample P k) (J : Word P) : Prop :=
  JointHashing.yHash s (castWord k J) ∈ U

def zFlag (d : OrbitData P E O V) (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (s : Sample P k) (K : Word P) : Prop :=
  JointHashing.zHash (twoUnit k) s (fun p => (d.support p : ZMod (37 ^ k))) (castWord k K) ∈ U

omit [Fintype E] in
theorem actual_survival_iff (d : OrbitData P E O V) (k : ℕ)
    (U : Finset (ZMod (37 ^ k)))
    (hAP : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, x + y = 2 * z → x = z ∧ y = z)
    (s : Sample P k) (f : Triple P) (hf : f ∈ d.ambient) :
    JointCoarseAssignment.survives (xFlag k U s) (yFlag k U s) (d.zFlag k U s) f ↔
      Survives k U f s :=
  full_survival_iff k U hAP d.support f (d.support_ambient f hf) s

def actualEligible (d : OrbitData P E O V) (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (s : Sample P k) : Finset (Triple P) :=
  JointCoarseAssignment.eligible d.ambient d.actualTargets
    (xFlag k U s) (yFlag k U s) (d.zFlag k U s)

theorem good_mem_actualEligible (d : OrbitData P E O V) (k : ℕ)
    (U : Finset (ZMod (37 ^ k)))
    (hAP : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, x + y = 2 * z → x = z ∧ y = z)
    (N : ℝ) (e : E) (s : Sample P k) (hg : d.Good k U N e s) :
    d.coarse e ∈ d.actualEligible k U s := by
  apply JointAssignmentLoss.eligible_of_no_ambientXCollision d.ambient d.actualTargets
    (xFlag k U s) (yFlag k U s) (d.zFlag k U s) (d.coarse e)
    (d.target_mem e) (d.coarse_mem_actualTargets e)
    ((d.actual_survival_iff k U hAP s _ (d.target_mem e)).2 hg.1)
  rintro ⟨f, hf, hne, hs, hx⟩
  exact d.good_eligibility k U N e s hg
    ⟨f, (d.mem_eligibilityCompetitors e f).2 ⟨hf, hne, hx⟩,
      (d.actual_survival_iff k U hAP s f hf).1 hs⟩

def actualAssignment (d : OrbitData P E O V) (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (compatible useful : Triple P → V → Prop) (keep : V → Prop)
    (s : Sample P k) (v : V) : Option (Triple P) :=
  JointExtraction.retainAssignment
    (JointCoarseAssignment.assignUseful (d.actualEligible k U s) compatible useful) keep v

theorem model_retained_assigned (d : OrbitData P E O V) (k : ℕ)
    (U : Finset (ZMod (37 ^ k)))
    (hAP : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, x + y = 2 * z → x = z ∧ y = z)
    (N : ℝ) (e : E) (o : O) (ho : o ∈ d.orbits e) (s : Sample P k)
    (hg : d.Good k U N e s)
    (compatible useful : Triple P → V → Prop) (keep : V → Prop)
    (v : V) (hv : v ∈ JointLossCounts.retained (d.passing e o) (d.variableBad k U e o) s)
    (hc : compatible (d.coarse e) v) (hu : useful (d.coarse e) v) (hk : keep v)
    (hcover : ∀ f ∈ d.actualTargets, f ≠ d.coarse e → compatible f v →
      f ∈ d.competitors e o v) :
    d.actualAssignment k U compatible useful keep s v = some (d.coarse e) := by
  obtain ⟨hpass, hnotbad⟩ := Finset.mem_filter.1 hv
  have hassign := JointAssignmentLoss.assignUseful_of_no_targetCollision
    d.ambient d.actualTargets (xFlag k U s) (yFlag k U s) (d.zFlag k U s)
    compatible useful (d.coarse e) v (d.good_mem_actualEligible k U hAP N e s hg) hc hu
    (by
      rintro ⟨f, hf, hne, hsurv, hcomp⟩
      have hfc := hcover f hf hne hcomp
      have hfa := d.competitor_mem e o ho v hpass f hfc
      exact hnotbad ⟨f, hfc, (d.actual_survival_iff k U hAP s f hfa).1 hsurv⟩)
  simpa only [actualAssignment, actualEligible, JointExtraction.retainAssignment, ite_eq_left hk] using hassign

theorem actual_failure_subset_model_missing (d : OrbitData P E O V) (k : ℕ)
    (U : Finset (ZMod (37 ^ k)))
    (hAP : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, x + y = 2 * z → x = z ∧ y = z)
    (N : ℝ) (e : E) (o : O) (ho : o ∈ d.orbits e) (s : Sample P k)
    (hg : d.Good k U N e s)
    (compatible useful : Triple P → V → Prop) (keep : V → Prop)
    (hc : ∀ v ∈ d.passing e o, compatible (d.coarse e) v)
    (hu : ∀ v ∈ d.passing e o, useful (d.coarse e) v)
    (hk : ∀ v ∈ d.passing e o, keep v)
    (hcover : ∀ v ∈ d.passing e o, ∀ f ∈ d.actualTargets,
      f ≠ d.coarse e → compatible f v → f ∈ d.competitors e o v) :
    (d.full e o).filter (fun v => d.actualAssignment k U compatible useful keep s v ≠
      some (d.coarse e)) ⊆
    d.full e o \ JointLossCounts.retained (d.passing e o) (d.variableBad k U e o) s := by
  intro v hv
  obtain ⟨hvfull, hvfail⟩ := Finset.mem_filter.1 hv
  apply Finset.mem_sdiff.2
  refine ⟨hvfull, ?_⟩
  intro hvmodel
  have hpass := (Finset.mem_filter.1 hvmodel).1
  exact hvfail (d.model_retained_assigned k U hAP N e o ho s hg compatible useful keep v
    hvmodel (hc v hpass) (hu v hpass) (hk v hpass) (hcover v hpass))

theorem good_actual_missingFraction_le (d : OrbitData P E O V) (k : ℕ)
    (U : Finset (ZMod (37 ^ k)))
    (hAP : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, x + y = 2 * z → x = z ∧ y = z)
    (C₀ N : ℝ) (e : E) (o : O) (ho : o ∈ d.orbits e) (s : Sample P k)
    (hg : d.Good k U N e s)
    (compatible useful : Triple P → V → Prop) (keep : V → Prop)
    (hc : ∀ v ∈ d.passing e o, compatible (d.coarse e) v)
    (hu : ∀ v ∈ d.passing e o, useful (d.coarse e) v)
    (hk : ∀ v ∈ d.passing e o, keep v)
    (hcover : ∀ v ∈ d.passing e o, ∀ f ∈ d.actualTargets,
      f ≠ d.coarse e → compatible f v → f ∈ d.competitors e o v)
    (hdet : ∀ o ∈ d.orbits e,
      JointLossCounts.deterministicLossFraction (d.full e o) (d.passing e o) ≤ C₀ / N) :
    (((d.full e o).filter (fun v => d.actualAssignment k U compatible useful keep s v ≠
      some (d.coarse e))).card : ℝ) / ((d.full e o).card : ℝ) ≤ (C₀ + 1) / N := by
  have hcard := Finset.card_le_card
    (d.actual_failure_subset_model_missing k U hAP N e o ho s hg compatible useful keep hc hu hk hcover)
  have hR : (((d.full e o).filter (fun v => d.actualAssignment k U compatible useful keep s v ≠
      some (d.coarse e))).card : ℝ) ≤
      ((d.full e o \ JointLossCounts.retained (d.passing e o) (d.variableBad k U e o) s).card : ℝ) := by
    exact_mod_cast hcard
  exact (div_le_div_of_nonneg_right hR (Nat.cast_nonneg _)).trans
    (d.good_missingFraction_le k U C₀ N e s hg hdet o ho)

end MatrixMultiplication.JointMaskedSelection.OrbitData

end

end OAI
