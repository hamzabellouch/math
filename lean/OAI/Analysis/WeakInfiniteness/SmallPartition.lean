import Mathlib

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped BigOperators Topology

lemma exists_small_partition (K : Set ℝ) (hK : IsCompact K) {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ, ∃ c : Fin n → ℝ, ∃ f : Fin n → C(ℝ,ℝ),
      (∀ i, tsupport (f i) ⊆ Metric.ball (c i) δ) ∧
      (∀ x ∈ K, ∑ i,f i x=1) ∧ (∀ i x,0 ≤ f i x ∧ f i x ≤ 1) := by
  classical
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover (fun c : ℝ => Metric.ball c δ)
    (fun _ => Metric.isOpen_ball) (by
      intro x _
      exact Set.mem_iUnion.mpr ⟨x,by simpa using hδ⟩)
  let e : Fin s.card ≃ s := by simpa using (Fintype.equivFin s).symm
  let c : Fin s.card → ℝ := fun i => (e i).val
  have hcover : K ⊆ ⋃ i, Metric.ball (c i) δ := by
    intro x hx
    obtain ⟨y,hxy⟩ := Set.mem_iUnion.mp (hs hx)
    obtain ⟨hy',hxy'⟩ := Set.mem_iUnion.mp hxy
    exact Set.mem_iUnion.mpr ⟨e.symm ⟨y,hy'⟩,by simpa [c] using hxy'⟩
  obtain ⟨f,hf,hfs,hn,_⟩ := exists_continuous_sum_one_of_isOpen_isCompact
    (s := fun i : Fin s.card => Metric.ball (c i) δ)
    (fun _ => Metric.isOpen_ball) hK hcover
  refine ⟨s.card,c,f,hf,?_,hn⟩
  intro x hx
  simpa using hfs hx

end

end WeakPureInfiniteness
end

end OAI
