import OAI.Analysis.CircleDomains.Sobolev.CirclePartitionEnergy
import OAI.Analysis.CircleDomains.Selection.LocalLiftBands

namespace OAI

/-! Circle smoothing with a prescribed continuous positive pointwise
error. The same choice controls all local derivative errors and preserves
interval bounds on each sampling patch. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

 theorem exists_circle_smoothing_with_tolerance
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*} [Countable ι]
    (ρ : OpenPlanePartition Ω ι) (W : ι → Set EuclideanPlane)
    (hW : ∀ k, IsOpen (W k)) (hsub : ∀ k, tsupport (ρ.weight k) ⊆ W k)
    (f : EuclideanPlane → UnitAddCircle) (u : ι → EuclideanPlane → ℝ)
    (hc : ∀ k, ContinuousOn (u k) (W k))
    (hlift : ∀ k x, x ∈ W k → (u k x : UnitAddCircle) = f x)
    (hu : ∀ k, DeGiorgi.MemW1pWitness 2 (u k) (W k))
    (e : EuclideanPlane → ℝ) (he : ContinuousOn e Ω) (hepos : ∀ x ∈ Ω, 0 < e x)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ v : ι → EuclideanPlane → ℝ,
      (∀ k, (ContDiff ℝ (⊤ : ℕ∞) (v k) ∧ HasCompactSupport (v k)) ∧
        ∀ a b : ℝ, (∀ x ∈ W k, u k x ∈ Icc a b) →
          ∀ x ∈ tsupport (ρ.weight k), v k x ∈ Icc a b) ∧
      FiniteTransfer.SmoothCircleOn (ρ.circleMix f u v) Ω ∧
      (∀ x ∈ Ω, |ρ.mix (fun k y => v k y - u k y) x| ≤ e x) ∧
      ∀ i : Fin 2, eLpNorm (fun x =>
        FiniteTransfer.circleFDeriv (ρ.circleMix f u v) x (EuclideanSpace.single i 1) -
          ∑ᶠ k, ρ.weight k x * (hu k).weakGrad x i) 2 (volume.restrict Ω) < ε := by
  have hd (k : ι) : ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ tsupport (ρ.weight k), δ ≤ e x :=
    (ρ.compact k).isCompact.exists_forall_le' (he.mono (ρ.inside k))
      (fun x hx => hepos x (ρ.inside k hx))
  choose δ hδ hδe using hd
  obtain ⟨ξ, hξ, hsum⟩ := ENNReal.exists_pos_sum_of_countable' hε.ne' ι
  obtain ⟨v, hv⟩ := exists_partition_lift_approximants_with_accuracy ρ W hW hsub u hu hc δ hδ ξ hξ
  have hs (k : ι) := (hv k).1.1
  refine ⟨v, (fun k => ⟨(hv k).1, (hv k).2.1⟩),
    ρ.circleMix_smooth W hW hsub f u v hc hlift hs, ?_, ?_⟩
  · intro x hx
    apply abs_le.mpr
    apply ρ.mix_mem_Icc _ hx
    intro k hk
    have hxk := subset_tsupport (ρ.weight k) hk
    have hb := abs_lt.mp ((hv k).2.2.1 x hxk)
    have he' := hδe k x hxk
    constructor <;> linarith [hb.1, hb.2]
  · intro i
    have hsumerr : eLpNorm (fun x => ∑ᶠ k,
        partitionLiftDerivativeError ρ u (fun k => (hu k).weakGrad) v i k x)
        2 volume ≤ ∑' k, ξ k := by
      apply (eLpNorm_finsum_le_tsum_of_pointFinite volume _ ?_
        (partitionLiftDerivativeError_pointFinite ρ u _ v i)).trans
      · exact ENNReal.tsum_le_tsum (fun k => ((hv k).2.2.2 i).le)
      · intro k
        exact aestronglyMeasurable_partition_derivative_error (hW k) (hu k)
          (hv k).1.1 (ρ.smooth k) (hsub k) i
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
      _ < ε := hsumerr.trans_lt hsum

end CircleDomainRigidity

end

end OAI
