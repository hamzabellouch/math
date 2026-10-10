import OAI.Analysis.CircleDomains.Sobolev.WeakPartialLocality
import OAI.Analysis.CircleDomains.Sobolev.PartitionGradientBound
import OAI.Analysis.CircleDomains.Sobolev.LocalWeakGradientEnergy
import OAI.Analysis.CircleDomains.Sobolev.SobolevRepresentative

namespace OAI

/-! Actual global weak gradients from local Sobolev witnesses. Uniqueness
on overlaps identifies the partition sum with each local gradient, and
finite test decomposition proves the global weak identity. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem partition_gradient_eq_local
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*} [Countable ι]
    (ρ : OpenPlanePartition Ω ι) (V : ι → Set EuclideanPlane)
    (hV : ∀ j, IsOpen (V j)) (hVΩ : ∀ j, V j ⊆ Ω)
    (hsub : ∀ j, tsupport (ρ.weight j) ⊆ V j)
    {u : EuclideanPlane → ℝ} (W : ∀ j, DeGiorgi.MemW1pWitness 2 u (V j))
    (j : ι) (k : Fin 2) :
    (fun x => ∑ᶠ l, ρ.weight l x*(W l).weakGrad x k) =ᵐ[volume.restrict (V j)]
      (fun x => (W j).weakGrad x k) := by
  have hpair (l : ι) : ∀ᵐ x ∂volume, x ∈ V j ∩ V l →
      (W j).weakGrad x = (W l).weakGrad x := by
    apply (ae_restrict_iff' ((hV j).inter (hV l)).measurableSet).mp
    exact weakGradient_eq_on_subset ((hV j).inter (hV l)) inter_subset_left (W j)
      ((W l).restrict ((hV j).inter (hV l)) inter_subset_right) (fun _ _ => rfl)
  have hall := ae_all_iff.mpr hpair
  filter_upwards [ae_restrict_of_ae hall,ae_restrict_mem (hV j).measurableSet] with x hx hxV
  calc
    _ = ∑ᶠ l, ρ.weight l x*(W j).weakGrad x k := by
      apply finsum_congr
      intro l
      by_cases hl : ρ.weight l x = 0
      · simp only [hl,zero_mul]
      · rw [hx l ⟨hxV,hsub l (subset_tsupport (ρ.weight l) hl)⟩]
    _ = (∑ᶠ l, ρ.weight l x)*(W j).weakGrad x k := (finsum_mul _ _).symm
    _ = (W j).weakGrad x k := by rw [ρ.sum_one ⟨x,hVΩ j hxV⟩,one_mul]

 theorem exists_partition_weak_gradient
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*} [Countable ι]
    (ρ : OpenPlanePartition Ω ι) (V : ι → Set EuclideanPlane)
    (hV : ∀ j, IsOpen (V j)) (hVΩ : ∀ j, V j ⊆ Ω)
    (hsub : ∀ j, tsupport (ρ.weight j) ⊆ V j)
    {u : EuclideanPlane → ℝ} (hu : MemLp u 2 (volume.restrict Ω))
    (W : ∀ j, DeGiorgi.MemW1pWitness 2 u (V j))
    {P : EuclideanPlane → ℝ} (hP : MemLp P 2 (volume.restrict Ω))
    (hbound : ∀ j k, ∀ᵐ x ∂volume.restrict (V j), |(W j).weakGrad x k| ≤ P x) :
    ∃ H : DeGiorgi.MemW1pWitness 2 u Ω,
      ∀ k : Fin 2, ∀ᵐ x ∂volume.restrict Ω, |H.weakGrad x k| ≤ P x := by
  let G : Fin 2 → EuclideanPlane → ℝ := fun k x => ∑ᶠ j, ρ.weight j x*(W j).weakGrad x k
  have hG (k : Fin 2) : MemLp (G k) 2 (volume.restrict Ω) :=
    partition_component_memLp ρ V (fun j => (hV j).measurableSet) hsub
      (fun j x => (W j).weakGrad x k) (fun j => (W j).weakGrad_component_memLp k |>.aestronglyMeasurable)
      hP (fun j => hbound j k)
  have hGbound (k : Fin 2) : ∀ᵐ x ∂volume.restrict Ω, |G k x| ≤ P x :=
    partition_component_bound ρ V (fun j => (hV j).measurableSet) hsub
      (fun j x => (W j).weakGrad x k) P (fun j => hbound j k)
  have hweak (k : Fin 2) : DeGiorgi.HasWeakPartialDeriv k (G k) u Ω := by
    apply weakPartial_of_local Ω.isOpen (hu.locallyIntegrable (by norm_num))
      ((hG k).locallyIntegrable (by norm_num))
    intro x hx
    have hex : ∃ j, ρ.weight j x ≠ 0 := by
      by_contra! hz
      have hone := ρ.sum_one ⟨x,hx⟩
      simp only [hz,finsum_zero] at hone
      exact zero_ne_one hone
    obtain ⟨j,hj⟩ := hex
    refine ⟨V j,hV j,hsub j (subset_tsupport (ρ.weight j) hj),hVΩ j,?_⟩
    exact ((W j).isWeakGrad k).congr_ae Filter.EventuallyEq.rfl
      (partition_gradient_eq_local ρ V hV hVΩ hsub W j k).symm
  let H : DeGiorgi.MemW1pWitness 2 u Ω := {
    memLp := hu
    weakGrad := fun x => WithLp.toLp 2 (fun k => G k x)
    weakGrad_component_memLp := hG
    isWeakGrad := hweak }
  exact ⟨H,hGbound⟩

end CircleDomainRigidity

end

end OAI
