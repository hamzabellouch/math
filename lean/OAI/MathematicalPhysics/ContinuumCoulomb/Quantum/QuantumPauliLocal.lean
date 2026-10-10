import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPauliAlgebra

namespace OAI

/-! Exact supports and tensor joins of the Pauli words used in the reduction. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def qmaPauliSupport (w : ι → Fin 4) : Finset ι := Finset.univ.filter (fun i => w i ≠ 0)

theorem qmaPauliWord_local (S : Finset ι) (w : ι → Fin 4)
    (hw : ∀ i, i ∉ S → w i = 0) : QMALocalOn S (qmaPauliWord w) := by
  refine ⟨qmaPauliWord (fun i : {i // i ∈ S} => w i.val),?_⟩
  ext s t
  rw [qmaLocalLift_apply]
  change (∏ i, qmaPauli (w i) (s i) (t i)) =
    (∏ i : {i // i ∈ S}, qmaPauli (w i.val) (s i.val) (t i.val))*
      (if (fun i : {i // i ∉ S} => s i.val) = (fun i : {i // i ∉ S} => t i.val) then 1 else 0)
  by_cases hr : (fun i : {i // i ∉ S} => s i.val) = (fun i : {i // i ∉ S} => t i.val)
  · rw [ite_eq_left hr,mul_one]
    have he (i : ι) (_hi : i ∈ Finset.univ) (hi : i ∉ S) : qmaPauli (w i) (s i) (t i) = 1 := by
      rw [hw i hi,qmaPauli_zero,Matrix.one_apply]
      exact ite_eq_left (congrFun hr ⟨i,hi⟩)
    have hp := Finset.prod_subset (Finset.subset_univ S) he
    have hs := Finset.prod_subtype (F := inferInstance) S
      (by simp : ∀ i, i ∈ S ↔ i ∈ S) (fun i => qmaPauli (w i) (s i) (t i))
    exact hp.symm.trans hs
  · rw [ite_eq_right hr,mul_zero]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp hr
    apply Finset.prod_eq_zero (Finset.mem_univ i.val)
    rw [hw i.val i.property,qmaPauli_zero,Matrix.one_apply]
    exact ite_eq_right hi

theorem qmaPauliWord_support (w : ι → Fin 4) : QMALocalOn (qmaPauliSupport w) (qmaPauliWord w) := by
  apply qmaPauliWord_local
  intro i hi
  simpa [qmaPauliSupport] using hi

omit [DecidableEq ι] in
theorem qmaPauliWord_join (w : ι → Fin 4) (v : κ → Fin 4) :
    qmaJoinMatrix (qmaPauliWord w) (qmaPauliWord v) = qmaPauliWord (Sum.elim w v) := by
  ext s t
  change (∏ i, qmaPauli (w i) (s (Sum.inl i)) (t (Sum.inl i)))*
    (∏ k, qmaPauli (v k) (s (Sum.inr k)) (t (Sum.inr k))) =
      ∏ a : ι ⊕ κ, qmaPauli (Sum.elim w v a) (s a) (t a)
  rw [Fintype.prod_sum_type]
  rfl

theorem qmaPauliSupport_join (w : ι → Fin 4) (v : κ → Fin 4) :
    qmaPauliSupport (Sum.elim w v) =
      (qmaPauliSupport w).map Function.Embedding.inl ∪
      (qmaPauliSupport v).map Function.Embedding.inr := by
  ext a
  cases a <;> simp [qmaPauliSupport]

theorem qmaPauliSupport_join_card (w : ι → Fin 4) (v : κ → Fin 4) :
    (qmaPauliSupport (Sum.elim w v)).card = (qmaPauliSupport w).card+(qmaPauliSupport v).card := by
  rw [qmaPauliSupport_join,Finset.card_union_of_disjoint,Finset.card_map,Finset.card_map]
  apply Finset.disjoint_left.mpr
  intro a ha hb
  obtain ⟨i,_,hi⟩ := Finset.mem_map.mp ha
  obtain ⟨k,_,hk⟩ := Finset.mem_map.mp hb
  exact Sum.inl_ne_inr (hi.trans hk.symm)

end ContinuumCoulomb

end

end OAI
