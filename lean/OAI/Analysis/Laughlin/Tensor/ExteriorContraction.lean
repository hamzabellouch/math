import OAI.Analysis.Laughlin.FourBody.CARReadout
import OAI.Analysis.Laughlin.Tensor.Antisymmetry
import OAI.Analysis.Laughlin.Tensor.ExteriorRotation

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

noncomputable def orderedWedge {n Q : ℕ} (a : Configuration n Q) : Space Q :=
  ExteriorAlgebra.ιMulti ℂ n (fun k => mode (a k))

theorem orderedWedge_cons {n Q : ℕ} (i : Fin (Q+1)) (a : Configuration n Q) :
    orderedWedge (Fin.cons i a) = create i (orderedWedge a) := by
  simp only [orderedWedge, ExteriorAlgebra.ιMulti_succ_apply, Fin.cons_zero]
  rfl

theorem orderedWedge_head {n Q : ℕ} (a : Configuration (n+1) Q) :
    orderedWedge a = create (a 0) (orderedWedge (fun j => a j.succ)) := by
  rw [← orderedWedge_cons]
  congr 1
  exact (Fin.cons_self_tail a).symm

theorem annihilate_orderedWedge (n Q : ℕ) (i : Fin (Q+1))
    (a : Configuration (n+1) Q) :
    annihilate i (orderedWedge a) =
      ∑ k : Fin (n+1), ((-1 : ℂ)^k.val * delta i (a k)) •
        orderedWedge (k.removeNth a) := by
  induction n with
  | zero =>
    rw [orderedWedge_head, annihilate_create_apply]
    simp [orderedWedge, ExteriorAlgebra.ιMulti_zero_apply, annihilate_vacuum]
  | succ n ih =>
    rw [orderedWedge_head, annihilate_create_apply, ih, map_sum]
    conv_rhs => rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ, pow_succ,
      map_smul]
    have h0 : (0 : Fin (n+2)).removeNth a = fun j => a j.succ := by rfl
    rw [h0]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    have hw : orderedWedge (k.succ.removeNth a) =
        create (a 0) (orderedWedge (k.removeNth (fun j => a j.succ))) := by
      rw [← orderedWedge_cons]
      congr 1
      have h := Fin.cons_comp_succ_succAbove (a 0) (fun j => a j.succ) k
      have ha : Fin.cons (a 0) (fun j => a j.succ) = a := Fin.cons_self_tail a
      rw [ha] at h
      exact h
    rw [hw]
    simp only [mul_neg_one, neg_mul, neg_smul]

theorem tensorExterior_cons (n Q : ℕ) (ψ : State (n+1) Q) :
    tensorExterior (n+1) Q ψ =
      ∑ i : Fin (Q+1), create i (tensorExterior n Q (fun a => ψ (Fin.cons i a))) := by
  change (∑ a, ψ a • orderedWedge a) = _
  rw [sum_config_cons]
  change (∑ i, ∑ b, ψ (Fin.cons i b) • orderedWedge (Fin.cons i b)) = _
  simp only [orderedWedge_cons,tensorExterior,map_sum,map_smul]
  rfl

theorem annihilate_tensorExterior (n Q : ℕ) (ψ : State (n+1) Q)
    (hψ : Antisymmetric ψ) (i : Fin (Q+1)) :
    annihilate i (tensorExterior (n+1) Q ψ) =
      (n+1 : ℂ) • tensorExterior n Q (fun a => ψ (Fin.cons i a)) := by
  change annihilate i (∑ a, ψ a • orderedWedge a) = _
  simp only [map_sum,map_smul,annihilate_orderedWedge,Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  have hs (k : Fin (n+1)) :
      (∑ a : Configuration (n+1) Q,
        (ψ a * ((-1 : ℂ)^k.val * delta i (a k))) • orderedWedge (k.removeNth a)) =
        tensorExterior n Q (fun a => ψ (Fin.cons i a)) := by
    rw [sum_config_insert k]
    simp only [Fin.insertNth_apply_same, Fin.removeNth_insertNth,
      antisymmetric_insertNth hψ]
    have he (x : Fin (Q+1)) (b : Configuration n Q) :
        ((-1 : ℂ)^k.val * ψ (Fin.cons x b) * ((-1 : ℂ)^k.val * delta i x)) =
          delta i x * ψ (Fin.cons x b) := by
      have hpow : ((-1 : ℂ)^k.val)^2 = 1 := by
        rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
      calc
        _ = ((-1 : ℂ)^k.val)^2 * (delta i x * ψ (Fin.cons x b)) := by ring
        _ = _ := by rw [hpow,one_mul]
    simp only [he]
    simp [delta,tensorExterior,orderedWedge]
  simp only [hs,Finset.sum_const,Finset.card_univ,Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℂ]
  simp

end Laughlin.Fock

end OAI
