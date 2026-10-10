import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRowOrder

namespace OAI

/-! A logical gate is inserted immediately after its last operand arrives. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Classical

theorem qmaMapGate_sites (sourceWork targetWork : ℕ)
    (f : Fin (sourceWork+1) → Fin (targetWork+1)) (g : QMAGate) :
    qmaGateSites targetWork (qmaMapGate sourceWork targetWork f g) =
      (qmaGateSites sourceWork g).image f := by
  cases g <;> simp [qmaMapGate,qmaGateSites,qmaQubit_fin]

def qmaGateCut (work : ℕ) (e : Equiv.Perm (Fin (work+1))) (g : QMAGate) : ℕ :=
  (qmaGateSites work g).sup (fun i => (e.symm i).val)+1

theorem qmaGateCut_le (work : ℕ) (e : Equiv.Perm (Fin (work+1))) (g : QMAGate) :
    qmaGateCut work e g ≤ work+1 := by
  apply Nat.succ_le_of_lt
  apply (Finset.sup_lt_iff (by omega : 0 < work+1)).mpr
  intro i _
  exact (e.symm i).isLt

theorem qmaGateCut_site (work : ℕ) (e : Equiv.Perm (Fin (work+1)))
    (g : QMAGate) (i : Fin (work+1)) (hi : i ∈ qmaGateSites work g) :
    (e.symm i).val < qmaGateCut work e g := by
  exact Nat.lt_succ_of_le (Finset.le_sup (f := fun j => (e.symm j).val) hi)

def qmaRowStage (width work : ℕ)
    (l r : Fin (width+1) → Fin (work+1)) (e : Equiv.Perm (Fin (width+1)))
    (g : QMAGate) : List QMAGate :=
  let ps := qmaRowPairs (l ∘ e) (r ∘ e)
  qmaTransferGates (ps.take (qmaGateCut width e g)) ++
    [qmaMapGate width work r g] ++
      qmaTransferGates (ps.drop (qmaGateCut width e g))

theorem qmaRowStage_tail_avoids (width work : ℕ)
    (l r : Fin (width+1) → Fin (work+1)) (hr : Function.Injective r)
    (hlr : ∀ i j, l i ≠ r j) (e : Equiv.Perm (Fin (width+1))) (g : QMAGate) :
    ∀ k ∈ qmaGateSites work (qmaMapGate width work r g),
      ∀ p ∈ (qmaRowPairs (l ∘ e) (r ∘ e)).drop (qmaGateCut width e g),
        k ≠ p.1 ∧ k ≠ p.2 := by
  intro k hk p hp
  rw [qmaMapGate_sites] at hk
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hk
  obtain ⟨j,hj,hp⟩ := List.mem_drop_iff_getElem.mp hp
  have hj' : qmaGateCut width e g+j < width+1 := by
    simpa only [qmaRowPairs,List.length_ofFn,Nat.add_comm] using hj
  have he : (l (e ⟨qmaGateCut width e g+j,hj'⟩),
      r (e ⟨qmaGateCut width e g+j,hj'⟩)) = p := by
    simpa only [qmaRowPairs,List.getElem_ofFn,Function.comp_apply] using hp
  rw [←he]
  refine ⟨(hlr _ i).symm,?_⟩
  intro heq
  have hh := hr heq
  have hcut := qmaGateCut_site width e g i hi
  rw [hh,e.symm_apply_apply] at hcut
  change qmaGateCut width e g+j < qmaGateCut width e g at hcut
  omega

theorem qmaRowStage_matrix (width work : ℕ)
    (l r : Fin (width+1) → Fin (work+1)) (hl : Function.Injective l)
    (hr : Function.Injective r) (hlr : ∀ i j, l i ≠ r j)
    (e : Equiv.Perm (Fin (width+1))) (g : QMAGate) (hg : g.WellFormed (width+1)) :
    qmaGateProduct work (qmaRowStage width work l r e g) =
      qmaGateMatrix work (qmaMapGate width work r g)*
        qmaGateProduct work (qmaTransferGates (qmaRowPairs l r)) := by
  unfold qmaRowStage
  rw [qmaTransfer_insert_gate _ _
    (fun p hp => qmaRowPairs_distinct (l ∘ e) (r ∘ e)
      (fun i j => hlr (e i) (e j)) p (List.mem_of_mem_drop hp))
    _ (qmaMapGate_wellFormed width work r hr g hg)
    (qmaRowStage_tail_avoids width work l r hr hlr e g),
    List.take_append_drop,qmaRowTransfer_matrix_reindex l r hl hr hlr e]

end ContinuumCoulomb

end

end OAI
