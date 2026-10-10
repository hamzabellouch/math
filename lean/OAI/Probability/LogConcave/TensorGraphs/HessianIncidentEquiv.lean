import Mathlib
import OAI.Probability.LogConcave.TensorGraphs.RankEquiv

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling.AdjointRemoval
open GraphSchedule
open scoped Classical

variable {n : ℕ} {S : State (Fin (n+1))}

noncomputable def hessianIncidentEquiv
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (q : ℕ) (h : S.hessians) :
    {t : Edge (U:=InternalEdge β) q //
      IncidentAt (edgeSource (S:=S) β) (edgeTarget hS β)
        (Sum.inl 0) (Sum.inl (Fin.last n)) (Sum.inr h) q t} ≃
      {i : Fin (n+1) // destination hS i=Sum.inr h} where
  toFun t := by
    rcases t with ⟨(⟨k,j⟩|i)|(a|a),ht⟩
    · simp only [IncidentAt,edgeSource,edgeTarget,Sum.inl_ne_inr,or_self] at ht
    · exact ⟨i,ht.resolve_left (Sum.inl_ne_inr)⟩
    · exact False.elim (Sum.inl_ne_inr ht)
    · exact False.elim (Sum.inl_ne_inr ht)
  invFun i := ⟨Sum.inl (Sum.inr i.val),Or.inr i.property⟩
  left_inv t := by
    rcases t with ⟨(⟨k,j⟩|i)|(a|a),ht⟩
    · simp only [IncidentAt,edgeSource,edgeTarget,Sum.inl_ne_inr,or_self] at ht
    · rfl
    · exact False.elim (Sum.inl_ne_inr ht)
    · exact False.elim (Sum.inl_ne_inr ht)
  right_inv i := rfl

noncomputable def hessianSlotEquiv
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (q : ℕ) (h : S.hessians) :
    Fin ((h : Hessian (Fin (n+1))).first::(h : Hessian (Fin (n+1))).second::
      (h : Hessian (Fin (n+1))).extra).length ≃
      {t : Edge (U:=InternalEdge β) q //
        IncidentAt (edgeSource (S:=S) β) (edgeTarget hS β)
          (Sum.inl 0) (Sum.inl (Fin.last n)) (Sum.inr h) q t} :=
  (hessianEdgeEquiv hS h).trans (hessianIncidentEquiv hS β q h).symm

lemma hessianSlotEquiv_val
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (q : ℕ) (h : S.hessians)
    (k : Fin ((h : Hessian (Fin (n+1))).first::(h : Hessian (Fin (n+1))).second::
      (h : Hessian (Fin (n+1))).extra).length) :
    (hessianSlotEquiv hS β q h k).val=Sum.inl (Sum.inr
      (((h : Hessian (Fin (n+1))).first::(h : Hessian (Fin (n+1))).second::
        (h : Hessian (Fin (n+1))).extra).get k)) := rfl
end LogConcaveSampling.AdjointRemoval

end UpperProof
end
end
end

end OAI
