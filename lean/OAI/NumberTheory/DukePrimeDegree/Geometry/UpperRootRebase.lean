import OAI.NumberTheory.DukePrimeDegree.Geometry.UpperRootRegularKernel
import OAI.NumberTheory.DukePrimeDegree.Geometry.UpperRootGlobalCoordinates

namespace OAI

/-! # Rebasing full upper-root coordinates at their current group point -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

def upperRootRebase (n : ℕ) (t : UpperRootTime n) : UpperRootTime n ≃ₜ UpperRootTime n :=
  (upperRootWordHomeomorph n).trans
    ((Homeomorph.mulLeft (upperRootWordHomeomorph n t)⁻¹).trans
      (upperRootWordHomeomorph n).symm)

lemma upperRootRebase_apply (n : ℕ) (t u : UpperRootTime n) :
    upperRootRebase n t u = (upperRootWordHomeomorph n).symm
      ((upperRootWordHomeomorph n t)⁻¹ * upperRootWordHomeomorph n u) := rfl

lemma continuous_upperRootRebase (n : ℕ) :
    Continuous (fun z : UpperRootTime n × UpperRootTime n => upperRootRebase n z.1 z.2) :=
  (upperRootWordHomeomorph n).symm.continuous.comp
    (((upperRootWordHomeomorph n).continuous.comp continuous_fst).inv.mul
      ((upperRootWordHomeomorph n).continuous.comp continuous_snd))

lemma upperRootWord_zero (n : ℕ) :
    upperRootWordHomeomorph n (completeRootChain n).zeroTime = 1 := by
  apply Subtype.ext
  exact (completeRootChain n).word_zeroTime

lemma upperRootRebase_self (n : ℕ) (t : UpperRootTime n) :
    upperRootRebase n t t = (completeRootChain n).zeroTime := by
  apply (upperRootWordHomeomorph n).injective
  rw [upperRootRebase_apply, Homeomorph.apply_symm_apply, inv_mul_cancel, upperRootWord_zero]

def centerUpperRootMeasure (n : ℕ) (ν : Measure (UpperRootTime n)) (t : UpperRootTime n) :
    Measure (UpperRootTime n) := ν.map (upperRootRebase n t)

lemma centerUpperRootMeasure_locallyFinite (n : ℕ) (ν : Measure (UpperRootTime n))
    [IsLocallyFiniteMeasure ν] (t : UpperRootTime n) :
    IsLocallyFiniteMeasure (centerUpperRootMeasure n ν t) := by
  let E := upperRootRebase n t
  constructor
  intro u
  obtain ⟨V,hu,hV,hfin⟩ := Measure.exists_isOpen_measure_lt_top ν (E.symm u)
  refine ⟨E '' V, (E.isOpenMap _ hV).mem_nhds ⟨E.symm u,hu,E.apply_symm_apply u⟩, ?_⟩
  change ν.map E (E '' V) < ⊤
  rw [Measure.map_apply E.measurable (E.isOpenMap _ hV).measurableSet,
    E.injective.preimage_image]
  exact hfin

end DukePrimeDegree

end

end OAI
