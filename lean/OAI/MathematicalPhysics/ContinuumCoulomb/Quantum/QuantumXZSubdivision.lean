import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPauliSingle
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitSubdivisionLocalFamily

namespace OAI

/-! Explicit X/Z Pauli output for subdivision, including its occupation term. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def qmaXZSubdivisionWord (a b : ι → Fin 4) (e : κ) : Fin 4 → (ι ⊕ κ → Fin 4) :=
  ![fun _ => 0, Sum.elim (fun _ => 0) (qmaSinglePauliWord e 3),
    Sum.elim a (qmaSinglePauliWord e 1), Sum.elim b (qmaSinglePauliWord e 1)]

def qmaXZSubdivisionWeight (R j : ℝ) : Fin 4 → ℝ :=
  ![R^2/2+1+(j/2)^2, -R^2/2, R, -R*j/2]

omit [DecidableEq ι] in
theorem qmaJoinOccupation_pauli (e : κ) :
    qmaJoinMatrix (1 : Matrix (ι → Fin 2) (ι → Fin 2) ℂ) (qmaAncillaOccupation e) =
      (1/2:ℂ) • (1-qmaPauliWord (Sum.elim (fun _ : ι => 0) (qmaSinglePauliWord e 3))) := by
  rw [← qmaPauliWord_join,qmaPauliWord_zero,qmaAncillaOccupation_pauli]
  ext s t
  simp only [qmaJoinMatrix,Matrix.submatrix_apply,Matrix.kroneckerMap_apply,
    Matrix.smul_apply,Matrix.sub_apply,Matrix.one_apply]
  have he : (s = t) ↔
      ((Equiv.sumArrowEquivProdArrow ι κ (Fin 2)) s).1 =
        ((Equiv.sumArrowEquivProdArrow ι κ (Fin 2)) t).1 ∧
      ((Equiv.sumArrowEquivProdArrow ι κ (Fin 2)) s).2 =
        ((Equiv.sumArrowEquivProdArrow ι κ (Fin 2)) t).2 := by
    constructor
    · rintro rfl
      exact ⟨rfl,rfl⟩
    · intro h
      apply (Equiv.sumArrowEquivProdArrow ι κ (Fin 2)).injective
      exact Prod.ext h.1 h.2
  simp only [smul_eq_mul,he,ite_and]
  split_ifs <;> ring

omit [DecidableEq ι] in
theorem qmaXZSubdivision_sum (a b : ι → Fin 4) (e : κ) (R j : ℝ) :
    (∑ k, (qmaXZSubdivisionWeight R j k : ℂ) • qmaPauliWord (qmaXZSubdivisionWord a b e k)) =
      ∑ k, qmaSubdivisionLocalPiece (qmaPauliWord a) (qmaPauliWord b) e R j (fun _ => false) k := by
  have hflip : qmaPolarizedFlip (fun _ : κ => false) e = qmaBitFlipMatrix e := by
    simp [qmaPolarizedFlip_eq]
  simp only [qmaXZSubdivisionWord,qmaXZSubdivisionWeight,qmaSubdivisionLocalPiece,
    Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,Matrix.cons_val_succ,add_zero,
    qmaPauliWord_zero,← qmaPauliWord_join,qmaSinglePauliWord_X,hflip,
    qmaJoinOccupation_pauli]
  have hr (r : ℝ) (M : Matrix (ι ⊕ κ → Fin 2) (ι ⊕ κ → Fin 2) ℂ) :
      r • M = (r:ℂ) • M := rfl
  simp only [hr]
  push_cast
  module

omit [Fintype ι] [DecidableEq ι] [Fintype κ] in
theorem qmaXZSubdivision_noY (a b : ι → Fin 4) (e : κ)
    (ha : ∀ i, a i ≠ 2) (hb : ∀ i, b i ≠ 2) (k : Fin 4) (x : ι ⊕ κ) :
    qmaXZSubdivisionWord a b e k x ≠ 2 := by
  fin_cases k <;> cases x <;> simp [qmaXZSubdivisionWord,qmaSinglePauliWord,ha,hb] <;> split_ifs <;> decide

theorem qmaXZSubdivision_support (a b : ι → Fin 4) (e : κ) {d : ℕ}
    (ha : (qmaPauliSupport a).card ≤ d) (hb : (qmaPauliSupport b).card ≤ d) (k : Fin 4) :
    (qmaPauliSupport (qmaXZSubdivisionWord a b e k)).card ≤ d+1 := by
  have hs (i : Fin 4) : (qmaPauliSupport (qmaSinglePauliWord e i)).card ≤ 1 :=
    (Finset.card_le_card (qmaSinglePauliWord_support e i)).trans (by simp)
  fin_cases k
  · change (qmaPauliSupport (fun _ : ι ⊕ κ => 0)).card ≤ d+1
    simp [qmaPauliSupport]
  · change (qmaPauliSupport (Sum.elim (fun _ : ι => 0) (qmaSinglePauliWord e 3))).card ≤ d+1
    rw [qmaPauliSupport_join_card]
    have hz : (qmaPauliSupport (fun _ : ι => 0)).card = 0 := by simp [qmaPauliSupport]
    rw [hz]
    have := hs 3
    omega
  · change (qmaPauliSupport (Sum.elim a (qmaSinglePauliWord e 1))).card ≤ d+1
    rw [qmaPauliSupport_join_card]
    have := hs 1
    omega
  · change (qmaPauliSupport (Sum.elim b (qmaSinglePauliWord e 1))).card ≤ d+1
    rw [qmaPauliSupport_join_card]
    have := hs 1
    omega

end ContinuumCoulomb

end

end OAI
