import OAI.Analysis.KadisonKastler.Normalizer
import OAI.Analysis.KadisonKastler.Algebra
import OAI.Analysis.KadisonKastler.CocycleMetric

namespace OAI

/-! # The closed group of unitary normalizers

Uniform limits of normalizing unitary families remain normalizing. This
provides the complete space in which the normalizer correction is iterated.
-/

namespace KadisonKastler

open scoped BoundedContinuousFunction

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The normalizers of a concrete von Neumann algebra as an actual subgroup. -/
def normalizerGroup (P : VonNeumannAlgebra H) : Subgroup (unitary (H →L[ℂ] H)) where
  carrier := {v | Conjugates v P P}
  one_mem' := conjugates_one P
  mul_mem' hv hw := hw.trans hv
  inv_mem' hv := by
    change Conjugates _ P P
    simpa only [← Unitary.star_eq_inv] using hv.symm

theorem mem_normalizerGroup_iff (P : VonNeumannAlgebra H)
    (v : unitary (H →L[ℂ] H)) : v ∈ normalizerGroup P ↔
      ∀ x ∈ P, unitaryConj v x ∈ P ∧ unitaryConj (star v) x ∈ P := by
  constructor
  · intro hv x hx
    have hf : unitaryConj v x ∈ (P : Set (H →L[ℂ] H)) := by
      rw [← hv]
      exact ⟨x, hx, rfl⟩
    have hb : unitaryConj (star v) x ∈ (P : Set (H →L[ℂ] H)) := by
      rw [← hv.symm]
      exact ⟨x, hx, rfl⟩
    exact ⟨hf, hb⟩
  · intro hv
    apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (hv x hx).1
    · intro x hx
      exact ⟨unitaryConj (star v) x, (hv x hx).2, by
        simpa only [star_star] using unitaryConj_star_unitaryConj (star v) x⟩

theorem isClosed_normalizerGroup (P : VonNeumannAlgebra H) :
    IsClosed (normalizerGroup P : Set (unitary (H →L[ℂ] H))) := by
  have hc (x : H →L[ℂ] H) : Continuous (fun v : unitary (H →L[ℂ] H) =>
      unitaryConj v x) := by
    unfold unitaryConj
    fun_prop
  have hs (x : H →L[ℂ] H) : Continuous (fun v : unitary (H →L[ℂ] H) =>
      unitaryConj (star v) x) := (hc x).comp continuous_star
  have he : (normalizerGroup P : Set (unitary (H →L[ℂ] H))) =
      {v | ∀ x ∈ P, unitaryConj v x ∈ P ∧ unitaryConj (star v) x ∈ P} := by
    ext v
    exact mem_normalizerGroup_iff P v
  rw [he]
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun x => isClosed_iInter fun _ =>
    ((isClosed_algebra P).preimage (hc x)).inter ((isClosed_algebra P).preimage (hs x))

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

local instance normalizerFamilyCStar : CStarAlgebra (G →ᵇ (H →L[ℂ] H)) where

/-- Uniformly bounded families all of whose values normalize the algebra. -/
def NormalizingFamily (P : VonNeumannAlgebra H) :=
  {V : unitary (G →ᵇ (H →L[ℂ] H)) // ∀ g, unitaryFamilyEval V g ∈ normalizerGroup P}

omit [Group G] [DiscreteTopology G] in
theorem continuous_unitaryFamilyEval (g : G) :
    Continuous (fun V : unitary (G →ᵇ (H →L[ℂ] H)) => unitaryFamilyEval V g) := by
  apply Continuous.subtype_mk
  exact (BoundedContinuousFunction.lipschitz_eval_const g).continuous.comp
    continuous_subtype_val

omit [Group G] [DiscreteTopology G] in
theorem isClosed_normalizingFamilies (P : VonNeumannAlgebra H) :
    IsClosed {V : unitary (G →ᵇ (H →L[ℂ] H)) |
      ∀ g, unitaryFamilyEval V g ∈ normalizerGroup P} := by
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun g => (isClosed_normalizerGroup P).preimage
    (continuous_unitaryFamilyEval g)

instance normalizingFamilyMetricSpace (P : VonNeumannAlgebra H) :
    MetricSpace (NormalizingFamily (G := G) P) := inferInstanceAs (MetricSpace (Subtype _))

instance normalizingFamilyCompleteSpace (P : VonNeumannAlgebra H) :
    CompleteSpace (NormalizingFamily (G := G) P) := by
  let : CompleteSpace (unitary (G →ᵇ (H →L[ℂ] H))) := isClosed_unitary.completeSpace_coe
  exact (isClosed_normalizingFamilies P).completeSpace_coe

end

end KadisonKastler

end OAI
