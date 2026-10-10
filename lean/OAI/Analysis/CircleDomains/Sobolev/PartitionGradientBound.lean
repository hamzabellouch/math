import OAI.Analysis.CircleDomains.Sobolev.PositivePartitionSmoothing

namespace OAI

/-! A positive partition preserves a common pointwise bound on local
weak-gradient components, and hence their common L² bound. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

theorem partition_component_pointFinite
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*}
    (ρ : OpenPlanePartition Ω ι) (G : ι → EuclideanPlane → ℝ) (x : EuclideanPlane) :
    HasFiniteSupport (fun j => ρ.weight j x * G j x) := by
  apply (ρ.point_finite x).subset
  intro j hj
  by_contra hn
  apply hj
  change ρ.weight j x * G j x = 0
  rw [show ρ.weight j x = 0 from not_not.mp hn, zero_mul]

theorem partition_component_aestronglyMeasurable
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*} [Countable ι]
    (ρ : OpenPlanePartition Ω ι) (W : ι → Set EuclideanPlane)
    (hW : ∀j, MeasurableSet (W j)) (hsub : ∀j, tsupport (ρ.weight j) ⊆ W j)
    (G : ι → EuclideanPlane → ℝ)
    (hG : ∀j, AEStronglyMeasurable (G j) (volume.restrict (W j))) :
    AEStronglyMeasurable (fun x => ∑ᶠ j, ρ.weight j x * G j x) volume := by
  exact aestronglyMeasurable_finsum_of_pointFinite volume _
    (fun j => aestronglyMeasurable_mul_of_support (hW j) (hG j) (ρ.smooth j).continuous
      ((subset_tsupport (ρ.weight j)).trans (hsub j)))
    (partition_component_pointFinite ρ G)

theorem partition_component_bound
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*} [Countable ι]
    (ρ : OpenPlanePartition Ω ι) (W : ι → Set EuclideanPlane)
    (hW : ∀j, MeasurableSet (W j)) (hsub : ∀j, tsupport (ρ.weight j) ⊆ W j)
    (G : ι → EuclideanPlane → ℝ) (g : EuclideanPlane → ℝ)
    (hG : ∀j, ∀ᵐ x ∂volume.restrict (W j), |G j x| ≤ g x) :
    ∀ᵐ x ∂volume.restrict Ω, |∑ᶠ j, ρ.weight j x * G j x| ≤ g x := by
  have hglobal : ∀ᵐ x ∂(volume : Measure EuclideanPlane), ∀j, x ∈ W j → |G j x| ≤ g x :=
    ae_all_iff.mpr (fun j => (ae_restrict_iff' (hW j)).1 (hG j))
  filter_upwards [ae_restrict_of_ae hglobal, ae_restrict_mem Ω.isOpen.measurableSet] with x hx hxΩ
  have hb : (∑ᶠ j, ρ.weight j x * G j x) ∈ Icc (-g x) (g x) := by
    simpa only [smul_eq_mul] using (convex_Icc (-g x) (g x)).finsum_mem
      (fun j => ρ.nonneg j x) (ρ.sum_one ⟨x, hxΩ⟩)
      (fun j hj => abs_le.mp (hx j (hsub j (subset_tsupport (ρ.weight j) hj))))
  exact abs_le.mpr hb

theorem partition_component_memLp
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*} [Countable ι]
    (ρ : OpenPlanePartition Ω ι) (W : ι → Set EuclideanPlane)
    (hW : ∀j, MeasurableSet (W j)) (hsub : ∀j, tsupport (ρ.weight j) ⊆ W j)
    (G : ι → EuclideanPlane → ℝ)
    (hGm : ∀j, AEStronglyMeasurable (G j) (volume.restrict (W j)))
    {g : EuclideanPlane → ℝ} (hg : MemLp g 2 (volume.restrict Ω))
    (hG : ∀j, ∀ᵐ x ∂volume.restrict (W j), |G j x| ≤ g x) :
    MemLp (fun x => ∑ᶠ j, ρ.weight j x * G j x) 2 (volume.restrict Ω) := by
  apply hg.of_le (partition_component_aestronglyMeasurable ρ W hW hsub G hGm).restrict
  filter_upwards [partition_component_bound ρ W hW hsub G g hG] with x hx
  simpa only [Real.norm_eq_abs] using hx.trans (le_abs_self (g x))

end CircleDomainRigidity

end

end OAI
