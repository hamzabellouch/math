import OAI.Analysis.CircleDomains.Sobolev.CirclePartitionGradient
import OAI.Analysis.CircleDomains.Sobolev.PartitionLiftErrorSum

namespace OAI

/-! The intrinsic differential of the glued circle coordinate differs
from the partition of local weak derivatives by exactly the selected
summable approximation errors. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity
namespace OpenPlanePartition

variable {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*} (ρ : OpenPlanePartition Ω ι)

theorem circleMix_gradient_error_identity
    (W : ι → Set EuclideanPlane) (hW : ∀ k, IsOpen (W k))
    (hsub : ∀ k, tsupport (ρ.weight k) ⊆ W k)
    (f : EuclideanPlane → UnitAddCircle) (u v : ι → EuclideanPlane → ℝ)
    (hu : ∀ k, ContinuousOn (u k) (W k))
    (hlift : ∀ k y, y ∈ W k → (u k y : UnitAddCircle) = f y)
    (hv : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (v k))
    (G : ι → EuclideanPlane → EuclideanPlane)
    {x : EuclideanPlane} (hx : x ∈ Ω) (i : Fin 2) :
    FiniteTransfer.circleFDeriv (ρ.circleMix f u v) x (EuclideanSpace.single i 1) -
      (∑ᶠ k, ρ.weight k x * G k x i) =
      ∑ᶠ k, partitionLiftDerivativeError ρ u G v i k x := by
  classical
  obtain ⟨s, hs, _, _, _⟩ := ρ.finite_weights_and_derivatives hx
  have hleft : (∑ᶠ k, (ρ.weight k x * (fderiv ℝ (v k) x) (EuclideanSpace.single i 1) +
      (fderiv ℝ (ρ.weight k) x) (EuclideanSpace.single i 1) * (v k x - u k x))) =
      ∑ k ∈ s, (ρ.weight k x * (fderiv ℝ (v k) x) (EuclideanSpace.single i 1) +
        (fderiv ℝ (ρ.weight k) x) (EuclideanSpace.single i 1) * (v k x - u k x)) := by
    apply finsum_eq_sum_of_support_subset
    intro k hk
    by_contra hks
    apply hk
    simp only [(hs k hks).1, (hs k hks).2, zero_apply, zero_mul, zero_add]
  have hG : (∑ᶠ k, ρ.weight k x * G k x i) = ∑ k ∈ s, ρ.weight k x * G k x i := by
    apply finsum_eq_sum_of_support_subset
    intro k hk
    by_contra hks
    apply hk
    change ρ.weight k x * G k x i = 0
    rw [(hs k hks).1, zero_mul]
  have herr : (∑ᶠ k, partitionLiftDerivativeError ρ u G v i k x) =
      ∑ k ∈ s, partitionLiftDerivativeError ρ u G v i k x := by
    apply finsum_eq_sum_of_support_subset
    intro k hk
    by_contra hks
    apply hk
    change partitionLiftDerivativeError ρ u G v i k x = 0
    simp only [partitionLiftDerivativeError, (hs k hks).1, (hs k hks).2,
      zero_apply, zero_mul, zero_add]
  rw [ρ.circleMix_derivative W hW hsub f u v hu hlift hv hx i, hleft, hG, herr,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  dsimp only [partitionLiftDerivativeError]
  ring

end OpenPlanePartition

 theorem exists_positive_circle_smoothing
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*} [Countable ι]
    (ρ : OpenPlanePartition Ω ι) (W : ι → Set EuclideanPlane)
    (hW : ∀ k, IsOpen (W k)) (hsub : ∀ k, tsupport (ρ.weight k) ⊆ W k)
    (f : EuclideanPlane → UnitAddCircle) (u : ι → EuclideanPlane → ℝ)
    (hc : ∀ k, ContinuousOn (u k) (W k))
    (hlift : ∀ k x, x ∈ W k → (u k x : UnitAddCircle) = f x)
    (hu : ∀ k, DeGiorgi.MemW1pWitness 2 (u k) (W k))
    (ε : ι → ℝ≥0∞) (hε : ∀ k, 0 < ε k) :
    ∃ v : ι → EuclideanPlane → ℝ,
      (∀ k, (ContDiff ℝ (⊤ : ℕ∞) (v k) ∧ HasCompactSupport (v k)) ∧
        ∀ a b : ℝ, (∀ x ∈ W k, u k x ∈ Icc a b) →
          ∀ x ∈ tsupport (ρ.weight k), v k x ∈ Icc a b) ∧
      FiniteTransfer.SmoothCircleOn (ρ.circleMix f u v) Ω ∧
      ∀ i : Fin 2, eLpNorm (fun x =>
        FiniteTransfer.circleFDeriv (ρ.circleMix f u v) x (EuclideanSpace.single i 1) -
          ∑ᶠ k, ρ.weight k x * (hu k).weakGrad x i) 2 (volume.restrict Ω) ≤ ∑' k, ε k := by
  obtain ⟨v, hv, he⟩ := exists_partition_lift_approximation_with_summed_error ρ W hW hsub u hu ε hε
  have hs (k : ι) := (hv k).1.1
  refine ⟨v, hv, ρ.circleMix_smooth W hW hsub f u v hc hlift hs, ?_⟩
  intro i
  calc
    _ = eLpNorm (fun x => ∑ᶠ k,
        partitionLiftDerivativeError ρ u (fun k => (hu k).weakGrad) v i k x)
        2 (volume.restrict Ω) := by
      apply eLpNorm_congr_ae
      filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
      exact ρ.circleMix_gradient_error_identity W hW hsub f u v hc hlift hs _ hx i
    _ ≤ eLpNorm (fun x => ∑ᶠ k,
        partitionLiftDerivativeError ρ u (fun k => (hu k).weakGrad) v i k x) 2 volume :=
      eLpNorm_mono_measure _ Measure.restrict_le_self
    _ ≤ _ := he i

end CircleDomainRigidity

end

end OAI
