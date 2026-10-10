import OAI.Analysis.CircleDomains.Sobolev.PartitionGradientIdentity

namespace OAI

/-! Derivatives of a partition sum require smoothness only of its
weighted local terms, as needed for different real circle branches. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
namespace OpenPlanePartition

variable {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*} (ρ : OpenPlanePartition Ω ι)

 theorem mix_fderiv_of_products (v : ι → EuclideanPlane → ℝ)
    {x : EuclideanPlane} (hx : x ∈ Ω)
    (hv : ∀ i, DifferentiableAt ℝ (fun y => ρ.weight i y * v i y) x) :
    fderiv ℝ (ρ.mix v) x = ∑ᶠ i, fderiv ℝ (fun y => ρ.weight i y * v i y) x := by
  classical
  obtain ⟨s, hs⟩ := ρ.eventually_finite_weights hx
  have he : ρ.mix v =ᶠ[𝓝 x] fun y => ∑ i ∈ s, ρ.weight i y * v i y := by
    filter_upwards [hs] with y hy
    apply finsum_eq_sum_of_support_subset
    intro i hi
    by_contra his
    apply hi
    change ρ.weight i y * v i y = 0
    rw [hy i his, zero_mul]
  rw [he.fderiv_eq, fderiv_fun_sum (fun i _ => hv i)]
  symm
  apply finsum_eq_sum_of_support_subset
  intro i hi
  by_contra his
  apply hi
  change fderiv ℝ (fun y => ρ.weight i y * v i y) x = 0
  have hz : (fun y => ρ.weight i y * v i y) =ᶠ[𝓝 x] (fun _ => 0) :=
    hs.mono fun y hy => by
      change ρ.weight i y * v i y = 0
      rw [hy i his, zero_mul]
  rw [hz.fderiv_eq]
  exact fderiv_const_apply 0

end OpenPlanePartition
end CircleDomainRigidity

end

end OAI
