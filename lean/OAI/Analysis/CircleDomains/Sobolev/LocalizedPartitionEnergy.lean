import OAI.Analysis.CircleDomains.Sobolev.PartitionGradientEnergy

namespace OAI

/-! Localizing the global smoothing error keeps the original density on
the complement of a penalty region. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

theorem partition_smooth_gradient_energy_on
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*} [Countable ι]
    (ρ : OpenPlanePartition Ω ι) (W : ι → Set EuclideanPlane)
    (hW : ∀j, MeasurableSet (W j)) (hsub : ∀j, tsupport (ρ.weight j) ⊆ W j)
    (G : ι → EuclideanPlane → ℝ)
    (hGm : ∀j, AEStronglyMeasurable (G j) (volume.restrict (W j)))
    (g : EuclideanPlane → ℝ)
    (hG : ∀j, ∀ᵐx ∂volume.restrict (W j), |G j x| ≤ g x)
    {w : EuclideanPlane → ℝ} (i : Fin 2) {ε : ℝ≥0∞}
    (herr : eLpNorm (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1) -
      ∑ᶠj, ρ.weight j x * G j x) 2 (volume.restrict Ω) < ε)
    (S : Set EuclideanPlane) (hS : S ⊆ Ω) :
    eLpNorm (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1)) 2 (volume.restrict S) ≤
      ε + eLpNorm g 2 (volume.restrict S) := by
  let P : EuclideanPlane → ℝ := fun x => ∑ᶠj, ρ.weight j x * G j x
  let D : EuclideanPlane → ℝ := fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1)
  have hμ : volume.restrict S ≤ volume.restrict (Ω : Set EuclideanPlane) :=
    Measure.restrict_mono_set volume hS
  have hP : AEStronglyMeasurable P (volume.restrict S) :=
    (partition_component_aestronglyMeasurable ρ W hW hsub G hGm).mono_measure
      Measure.restrict_le_self
  have hnormP : eLpNorm P 2 (volume.restrict S) ≤ eLpNorm g 2 (volume.restrict S) := by
    apply eLpNorm_mono_ae_real hP
    exact (ae_mono hμ) (partition_component_bound ρ W hW hsub G g hG)
  calc
    _ = eLpNorm (fun x => (D x - P x) + P x) 2 (volume.restrict S) := by
      congr 1
      funext x
      exact (sub_add_cancel _ _).symm
    _ ≤ eLpNorm (fun x => D x - P x) 2 (volume.restrict S) +
        eLpNorm P 2 (volume.restrict S) := eLpNorm_add_le (by norm_num)
    _ ≤ ε + eLpNorm g 2 (volume.restrict S) := add_le_add
      ((eLpNorm_mono_measure _ hμ).trans herr.le) hnormP

end CircleDomainRigidity

end

end OAI
