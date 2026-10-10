import Mathlib
import OAI.Analysis.SymmetricDomains.DivisibleHermitianModel
import OAI.Analysis.SymmetricDomains.HermitianModelSymmetric

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open Filter Topology
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
namespace Release061
open Set

theorem main {n : ℕ} (V U : Set (Affine n))
    (hV : IsAffineAlgebraic V) (hUV : U ⊆ V)
    (hopen : IsOpen ((Subtype.val : V → Affine n) ⁻¹' U))
    (hconn : IsConnected U) (hsa : IsSemialgebraic U)
    (hbounded : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) :
    IsSmooth U ∧ ∃ (m : ℕ) (D : Set (Affine m)),
      IsBoundedSymmetricDomain D ∧ Nonempty (Biholomorph U D) := by
  classical
  by_cases hpoint : U.Subsingleton
  · exact main_point U hconn.nonempty hpoint
  obtain ⟨r,k,B,C,l,c,_hCo,_hCc,_hC0,_hcone,_hcpos,_hpositive,_hherm,
      hDo,_hDc,_ha,htr,hr,hd,⟨A,hAo,hAc,hAb,⟨e⟩⟩,g,_hg⟩ :=
    original_divisible_hermitian_model V U hV hUV hopen hconn hpoint hbounded hsa Γ hhol
  let S := (affineProductCoordinates r (k+1)) '' quadraticDomain (Hermitian.hermQuadratic B) C
  let : LocallyCompactSpace S :=
    ((affineProductCoordinates r (k+1)).isOpenMap _ hDo).locallyCompactSpace
  let : LocallyCompactSpace A := hAo.locallyCompactSpace
  let f : Biholomorph U A := g.trans e
  let : MulAction Γ A := conjugateMulAction f.toHomeomorph.toEquiv
  let : ProperSMul Γ A := conjugateMulAction_proper f.toHomeomorph
  let : CompactSpace (Quotient (MulAction.orbitRel Γ A)) :=
    conjugateMulAction_compact_quotient f.toHomeomorph
  have hholA : ∀ γ : Γ, HolomorphicOnSubset A (fun p => (γ • p : A).val) :=
    f.conjugate_action_holomorphic hhol
  have hsymm := Biholomorph.hermitian_model_bounded_symmetric hAo hAc hAb Γ hholA B C hDo htr hd hr e
  refine ⟨?_,r+(k+1),A,hsymm,⟨f⟩⟩
  intro p
  exact ⟨r+(k+1),U,Subset.rfl,by simp,p.property,A,hAo,⟨f⟩⟩

end Release061

end

end OAI
