import OAI.Analysis.CircleDomains.Sobolev.PartitionGradientBound

namespace OAI

/-! Turn the constructed gradient error and a common local density bound
into a global finite-energy estimate for the actual smooth function. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace CircleDomainRigidity

theorem partition_smooth_gradient_energy
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*} [Countable ι]
    (ρ : OpenPlanePartition Ω ι) (W : ι → Set EuclideanPlane)
    (hW : ∀j, MeasurableSet (W j)) (hsub : ∀j, tsupport (ρ.weight j) ⊆ W j)
    (G : ι → EuclideanPlane → ℝ)
    (hGm : ∀j, AEStronglyMeasurable (G j) (volume.restrict (W j)))
    {g : EuclideanPlane → ℝ} (hg : MemLp g 2 (volume.restrict Ω))
    (hG : ∀j, ∀ᵐ x ∂volume.restrict (W j), |G j x| ≤ g x)
    {w : EuclideanPlane → ℝ}
    (i : Fin 2) {ε : ℝ≥0∞}
    (herr : eLpNorm (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1) -
      ∑ᶠj, ρ.weight j x * G j x) 2 (volume.restrict Ω) < ε) :
    MemLp (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1)) 2 (volume.restrict Ω) ∧
    eLpNorm (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1)) 2 (volume.restrict Ω) ≤
      ε + eLpNorm g 2 (volume.restrict Ω) := by
  let P : EuclideanPlane → ℝ := fun x => ∑ᶠj, ρ.weight j x * G j x
  let D : EuclideanPlane → ℝ := fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1)
  have hP : MemLp P 2 (volume.restrict Ω) :=
    partition_component_memLp ρ W hW hsub G hGm hg hG
  have hE : MemLp (fun x => D x - P x) 2 (volume.restrict Ω) :=
    herr.trans_le le_top
  have hsum : (fun x => (D x - P x) + P x) = D := by
    funext x
    exact sub_add_cancel _ _
  have hnormP : eLpNorm P 2 (volume.restrict Ω) ≤ eLpNorm g 2 (volume.restrict Ω) := by
    apply eLpNorm_mono_ae_real hP.aestronglyMeasurable
    simpa only [Real.norm_eq_abs] using partition_component_bound ρ W hW hsub G g hG
  constructor
  · have hh := hE.add hP
    change MemLp D 2 (volume.restrict Ω)
    convert hh using 1
    funext x
    exact (sub_add_cancel (D x) (P x)).symm
  · change eLpNorm D 2 (volume.restrict Ω) ≤ _
    calc
      _ = eLpNorm (fun x => (D x - P x) + P x) 2 (volume.restrict Ω) := by rw [hsum]
      _ ≤ eLpNorm (fun x => D x - P x) 2 (volume.restrict Ω) +
          eLpNorm P 2 (volume.restrict Ω) := eLpNorm_add_le (by norm_num)
      _ ≤ _ := add_le_add herr.le hnormP

end CircleDomainRigidity

end

end OAI
