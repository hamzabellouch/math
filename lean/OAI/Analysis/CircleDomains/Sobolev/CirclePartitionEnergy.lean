import OAI.Analysis.CircleDomains.Topology.CirclePartitionError
import OAI.Analysis.CircleDomains.Sobolev.PartitionGradientBound

namespace OAI

/-! Quantitative energy control for the actual smooth circle map. Local
weak-gradient bounds survive positive mixing, while the selected smoothing
errors contribute an arbitrarily small additive L² term. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

theorem partition_field_energy
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*} [Countable ι]
    (ρ : OpenPlanePartition Ω ι) (W : ι → Set EuclideanPlane)
    (hW : ∀ k, MeasurableSet (W k)) (hsub : ∀ k, tsupport (ρ.weight k) ⊆ W k)
    (G : ι → EuclideanPlane → ℝ)
    (hGm : ∀ k, AEStronglyMeasurable (G k) (volume.restrict (W k)))
    {g D : EuclideanPlane → ℝ} (hg : MemLp g 2 (volume.restrict Ω))
    (hG : ∀ k, ∀ᵐ x ∂volume.restrict (W k), |G k x| ≤ g x)
    {ε : ℝ≥0∞}
    (herr : eLpNorm (fun x => D x - ∑ᶠ k, ρ.weight k x * G k x)
      2 (volume.restrict Ω) < ε) :
    MemLp D 2 (volume.restrict Ω) ∧
      eLpNorm D 2 (volume.restrict Ω) ≤ ε + eLpNorm g 2 (volume.restrict Ω) := by
  let P : EuclideanPlane → ℝ := fun x => ∑ᶠ k, ρ.weight k x * G k x
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
    change MemLp (fun x => (D x - P x) + P x) 2 (volume.restrict Ω) at hh
    rwa [hsum] at hh
  · calc
      _ = eLpNorm (fun x => (D x - P x) + P x) 2 (volume.restrict Ω) := by rw [hsum]
      _ ≤ eLpNorm (fun x => D x - P x) 2 (volume.restrict Ω) +
          eLpNorm P 2 (volume.restrict Ω) := eLpNorm_add_le (by norm_num)
      _ ≤ _ := add_le_add herr.le hnormP

 theorem exists_positive_circle_smoothing_with_energy
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*} [Countable ι]
    (ρ : OpenPlanePartition Ω ι) (W : ι → Set EuclideanPlane)
    (hW : ∀ k, IsOpen (W k)) (hsub : ∀ k, tsupport (ρ.weight k) ⊆ W k)
    (f : EuclideanPlane → UnitAddCircle) (u : ι → EuclideanPlane → ℝ)
    (hc : ∀ k, ContinuousOn (u k) (W k))
    (hlift : ∀ k x, x ∈ W k → (u k x : UnitAddCircle) = f x)
    (hu : ∀ k, DeGiorgi.MemW1pWitness 2 (u k) (W k))
    {g : EuclideanPlane → ℝ} (hg : MemLp g 2 (volume.restrict Ω))
    (hG : ∀ k (i : Fin 2), ∀ᵐ x ∂volume.restrict (W k), |(hu k).weakGrad x i| ≤ g x)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ v : ι → EuclideanPlane → ℝ,
      (∀ k, (ContDiff ℝ (⊤ : ℕ∞) (v k) ∧ HasCompactSupport (v k)) ∧
        ∀ a b : ℝ, (∀ x ∈ W k, u k x ∈ Icc a b) →
          ∀ x ∈ tsupport (ρ.weight k), v k x ∈ Icc a b) ∧
      FiniteTransfer.SmoothCircleOn (ρ.circleMix f u v) Ω ∧
      ∀ i : Fin 2,
        MemLp (fun x => FiniteTransfer.circleFDeriv (ρ.circleMix f u v) x
          (EuclideanSpace.single i 1)) 2 (volume.restrict Ω) ∧
        eLpNorm (fun x => FiniteTransfer.circleFDeriv (ρ.circleMix f u v) x
          (EuclideanSpace.single i 1)) 2 (volume.restrict Ω) ≤
            ε + eLpNorm g 2 (volume.restrict Ω) := by
  obtain ⟨δ, hδ, hsum⟩ := ENNReal.exists_pos_sum_of_countable' hε.ne' ι
  obtain ⟨v, hv, hs, he⟩ := exists_positive_circle_smoothing ρ W hW hsub f u hc hlift hu δ hδ
  refine ⟨v, hv, hs, ?_⟩
  intro i
  exact partition_field_energy ρ W (fun k => (hW k).measurableSet) hsub
    (fun k x => (hu k).weakGrad x i)
    (fun k => ((hu k).weakGrad_component_memLp i).aestronglyMeasurable) hg
    (fun k => hG k i) ((he i).trans_lt hsum)

end CircleDomainRigidity

end

end OAI
