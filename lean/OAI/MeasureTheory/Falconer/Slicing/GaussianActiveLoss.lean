import OAI.MeasureTheory.Falconer.Slicing.GaussianActiveFamily
import OAI.MeasureTheory.Falconer.Slicing.GaussianPrunedMass
import OAI.MeasureTheory.Falconer.Slicing.SliceDirectionDeletion

namespace OAI

/-! # Cost of deleting excessive active original tube lists -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d h : ℕ} {ι κ : Type*} [Fintype κ] [DecidableEq κ]

theorem gaussian_active_loss_in_row
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (δ : ℝ) (r : ι → ℝ) (TP TD : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (A : Fin h → Space d) (E : Set (Space d × Sphere d))
    (J : Sphere d → Finset κ) (hJ : ∀ i, MeasurableSet {w | i ∈ J w}) (a : κ → Space d)
    {R : ℝ} (hR : 0 ≤ R) {N T P : ℝ≥0∞} (hN : ∀ w, ((J w).card : ℝ≥0∞) ≤ N)
    (hT : T ≠ 0) (hTfin : T ≠ ∞)
    (hP : ∀ z, ((gaussianPointSliceMeasure μ A z δ).restrict
      (gaussianPointGood μ δ r TP (A,z))) univ ≤ P) :
    (∫⁻ z : Space h, gaussianPrunedIncidence μ ν δ r TP TD M
      (E ∩ (univ ×ˢ {w | T < (gaussianActiveAnchorCount A (J w) a R z : ℝ≥0∞)})) (A,z)) ≤
      P*(N*ENNReal.ofReal ((2*R)^h)/T)*M := by
  let β := (gaussianDirectionSliceMeasure ν A δ).restrict (gaussianDirectionGood ν δ r TD M A)
  let α := fun z : Space h => (gaussianPointSliceMeasure μ A z δ).restrict
    (gaussianPointGood μ δ r TP (A,z))
  have : IsFiniteMeasure β := by change IsFiniteMeasure (Measure.restrict _ _); infer_instance
  have : ∀ z, SFinite (α z) := fun z => by change SFinite (Measure.restrict _ _); infer_instance
  let D : Set (Space h × Sphere d) :=
    {p | T < (gaussianActiveAnchorCount A (J p.2) a R p.1 : ℝ≥0∞)}
  have hD : MeasurableSet D := gaussianActiveFamily_slice_measurable A J hJ a R T
  have hc : ∀ w, (volume : Measure (Space h)) {z | (z,w) ∈ D} ≤
      N*ENNReal.ofReal ((2*R)^h)/T :=
    gaussianActiveFamily_exceptional_bound A J a hR hN hT hTfin
  change (∫⁻ z : Space h, ((α z).prod β) (E ∩ (univ ×ˢ {w | (z,w) ∈ D}))) ≤ _
  have hl := slice_direction_deletion_cost (Z := Space h) (X := Space d) (W := Sphere d)
    (volume : Measure (Space h)) α β D hD E hP hc
  exact hl.trans (mul_le_mul_right (gaussianDirectionGood_mass ν δ r TD M A) _)

end Falconer

end OAI
