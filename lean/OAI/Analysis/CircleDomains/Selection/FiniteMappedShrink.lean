import OAI.Analysis.CircleDomains.Topology.FiniteJordanShrink
import Mathlib.Topology.UniformSpace.HeineCantor

namespace OAI

/-! The finite shrinking step controls diameter under any fixed
continuous metric-valued observation, by uniform continuity on the
compact union of the selected closed disks. -/
open Set Metric Function
noncomputable section
namespace CircleDomainRigidity

lemma exists_finite_jordan_mapped_shrink
    {I Y : Type*} [Finite I] [PseudoMetricSpace Y]
    (H : I → ℂ ≃ₜ ℂ) {K : Set ℂ} (hK : IsCompact K)
    (hd : Pairwise (fun i j => Disjoint (closure (jordanInterior (H i)))
      (closure (jordanInterior (H j)))))
    (hcover : K ⊆ ⋃ i, jordanInterior (H i))
    (havoid : ∀ i, Disjoint K (frontier (jordanInterior (H i))))
    (p : ℂ → Y) (hp : Continuous p) {ε : ℝ} (hε : 0<ε) :
    ∃ F : ℂ ≃ₜ ℂ,
      (∀ z ∉ ⋃ i, jordanInterior (H i), F z=z) ∧
      (∀ i, MapsTo F (jordanInterior (H i)) (jordanInterior (H i))) ∧
      ∀ x ∈ K, ∀ y ∈ connectedComponentIn K x,
        ∀ z ∈ connectedComponentIn K x, dist (p (F y)) (p (F z))<ε := by
  let B := ⋃ i, closure (jordanInterior (H i))
  have hB : IsCompact B := isCompact_iUnion (fun i => isCompact_closure_jordanInterior (H i))
  obtain ⟨δ,hδ,hpδ⟩ := Metric.uniformContinuousOn_iff.mp
    (hB.uniformContinuousOn_of_continuous hp.continuousOn) ε hε
  obtain ⟨F,hfix,hmaps,hsmall⟩ := exists_finite_jordan_shrink H hK hd hcover havoid hδ
  have hFB : ∀ z ∈ K, F z ∈ B := by
    intro z hz
    obtain ⟨i,hi⟩ := mem_iUnion.mp (hcover hz)
    exact mem_iUnion.mpr ⟨i,subset_closure (hmaps i hi)⟩
  refine ⟨F,hfix,hmaps,?_⟩
  intro x hx y hy z hz
  exact hpδ (F y) (hFB y (connectedComponentIn_subset _ _ hy))
    (F z) (hFB z (connectedComponentIn_subset _ _ hz)) (hsmall x hx y hy z hz)

end CircleDomainRigidity

end

end OAI
