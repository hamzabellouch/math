import OAI.Analysis.CircleDomains.Sobolev.PartitionApproximation
import OAI.Analysis.CircleDomains.Sobolev.PartitionMixing
import OAI.Analysis.CircleDomains.Sobolev.LocallyFiniteL2Sum

namespace OAI

/-! The selected local smoothing errors have a globally controlled L²
sum. Finiteness at each point follows from local finiteness of the weights. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

def partitionDerivativeError
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*}
    (ρ : OpenPlanePartition Ω ι) (u : EuclideanPlane → ℝ)
    (G : ι → EuclideanPlane → EuclideanPlane) (v : ι → EuclideanPlane → ℝ)
    (i : Fin 2) (j : ι) (x : EuclideanPlane) : ℝ :=
  ρ.weight j x * ((fderiv ℝ (v j) x) (EuclideanSpace.single i 1) - G j x i) +
    (fderiv ℝ (ρ.weight j) x) (EuclideanSpace.single i 1) * (v j x - u x)

theorem partitionDerivativeError_pointFinite
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*}
    (ρ : OpenPlanePartition Ω ι) (u : EuclideanPlane → ℝ)
    (G : ι → EuclideanPlane → EuclideanPlane) (v : ι → EuclideanPlane → ℝ)
    (i : Fin 2) (x : EuclideanPlane) :
    HasFiniteSupport (fun j => partitionDerivativeError ρ u G v i j x) := by
  classical
  by_cases hx : x ∈ Ω
  · obtain ⟨s, hs⟩ := ρ.eventually_finite_weights hx
    apply s.finite_toSet.subset
    intro j hj
    by_contra hjs
    apply hj
    change partitionDerivativeError ρ u G v i j x = 0
    have hz : ρ.weight j =ᶠ[𝓝 x] (fun _ => 0) := hs.mono fun _ hy => hy j hjs
    have hd : fderiv ℝ (ρ.weight j) x = 0 := by
      rw [hz.fderiv_eq]
      exact fderiv_const_apply 0
    simp only [partitionDerivativeError, hz.eq_of_nhds, hd,
      zero_apply, zero_mul, zero_add]
  · apply finite_empty.subset
    intro j hj
    apply False.elim
    apply hj
    change partitionDerivativeError ρ u G v i j x = 0
    have hnot : x ∉ tsupport (ρ.weight j) := fun h => hx (ρ.inside j h)
    simp only [partitionDerivativeError, image_eq_zero_of_notMem_tsupport hnot,
      fderiv_of_notMem_tsupport ℝ hnot, zero_apply, zero_mul, zero_add]

theorem exists_partition_approximation_with_summed_error
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*} [Countable ι]
    (ρ : OpenPlanePartition Ω ι) (W : ι → Set EuclideanPlane)
    (hW : ∀j, IsOpen (W j)) (hsub : ∀j, tsupport (ρ.weight j) ⊆ W j)
    (u : EuclideanPlane → ℝ) (hu : ∀j, DeGiorgi.MemW1pWitness 2 u (W j))
    (hunit : ∀j x, x ∈ W j → u x ∈ Icc 0 1)
    (ε : ι → ℝ≥0∞) (hε : ∀j, 0 < ε j) :
    ∃v : ι → EuclideanPlane → ℝ,
      (∀j, (ContDiff ℝ (⊤ : ℕ∞) (v j) ∧ HasCompactSupport (v j) ∧
          ∀x, v j x ∈ Icc 0 1) ∧
        ∀a b : ℝ, (∀x ∈ W j, u x ∈ Icc a b) →
          ∀x ∈ tsupport (ρ.weight j), v j x ∈ Icc a b) ∧
      ∀i : Fin 2, eLpNorm (fun x => ∑ᶠ j,
        partitionDerivativeError ρ u (fun j => (hu j).weakGrad) v i j x)
        2 volume ≤ ∑' j, ε j := by
  obtain ⟨v, hv⟩ := exists_partition_smooth_approximants ρ W hW hsub u hu hunit ε hε
  refine ⟨v, fun j => ⟨(hv j).1, (hv j).2.1⟩, ?_⟩
  intro i
  apply (eLpNorm_finsum_le_tsum_of_pointFinite volume _ ?_
    (partitionDerivativeError_pointFinite ρ u _ v i)).trans
  · exact ENNReal.tsum_le_tsum (fun j => ((hv j).2.2 i).le)
  · intro j
    exact aestronglyMeasurable_partition_derivative_error (hW j) (hu j)
      (hv j).1.1 (ρ.smooth j) (hsub j) i

end CircleDomainRigidity

end

end OAI
