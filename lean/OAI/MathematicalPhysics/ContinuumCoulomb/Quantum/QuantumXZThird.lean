import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumXZSubdivision
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumXZTriple

namespace OAI

/-! Seven explicit X/Z words for the third-order three-to-two-local gadget. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def qmaXZThirdWord (a b c v : ι → Fin 4) (e : κ) : Fin 7 → (ι ⊕ κ → Fin 4) :=
  ![fun _ => 0, Sum.elim (fun _ => 0) (qmaSinglePauliWord e 3),
    Sum.elim v (fun _ => 0), Sum.elim c (fun _ => 0),
    Sum.elim c (qmaSinglePauliWord e 3),
    Sum.elim a (qmaSinglePauliWord e 1), Sum.elim b (qmaSinglePauliWord e 1)]

def qmaXZThirdWeight (R j : ℝ) : Fin 7 → ℝ :=
  ![R^3/2+R*(1+(j/2)^2), -R^3/2, R*j, R^2/2-(1+(j/2)^2),
    -R^2/2, R^2, R^2*j/2]

omit [Fintype ι] [DecidableEq ι] in
theorem qmaJoinOccupation_expand (M : Matrix (ι → Fin 2) (ι → Fin 2) ℂ) (e : κ) :
    qmaJoinMatrix M (qmaAncillaOccupation e) = (1/2:ℂ) •
      (qmaJoinMatrix M 1-qmaJoinMatrix M (qmaPauliWord (qmaSinglePauliWord e 3))) := by
  rw [qmaAncillaOccupation_pauli]
  ext s t
  simp only [qmaJoinMatrix,Matrix.submatrix_apply,Matrix.kroneckerMap_apply,
    Matrix.smul_apply,Matrix.sub_apply,smul_eq_mul]
  ring

theorem qmaXZThird_sum (a b c v : ι → Fin 4) (e : κ) (R j : ℝ)
    (hab : qmaPauliWord a*qmaPauliWord b = qmaPauliWord v) :
    (∑ k, (qmaXZThirdWeight R j k : ℂ) • qmaPauliWord (qmaXZThirdWord a b c v e k)) =
      ∑ k, qmaThirdLocalPiece (qmaPauliWord a) (qmaPauliWord b) (qmaPauliWord c) e R j k := by
  have hI : qmaJoinMatrix (1 : Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
      (1 : Matrix (κ → Fin 2) (κ → Fin 2) ℂ) = 1 := by
    simp [qmaJoinMatrix,Matrix.submatrix_one_equiv]
  simp only [qmaXZThirdWord,qmaXZThirdWeight,qmaThirdLocalPiece,
    Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,Matrix.cons_val_succ,add_zero,
    qmaPauliWord_zero,← qmaPauliWord_join,qmaSinglePauliWord_X,
    qmaJoinOccupation_expand,hI,hab]
  have hr (r : ℝ) (M : Matrix (ι ⊕ κ → Fin 2) (ι ⊕ κ → Fin 2) ℂ) :
      r • M = (r:ℂ) • M := rfl
  simp only [hr]
  push_cast
  module

omit [Fintype ι] [DecidableEq ι] [Fintype κ] in
theorem qmaXZThird_noY (a b c v : ι → Fin 4) (e : κ)
    (ha : ∀ i, a i ≠ 2) (hb : ∀ i, b i ≠ 2) (hc : ∀ i, c i ≠ 2) (hv : ∀ i, v i ≠ 2)
    (k : Fin 7) (x : ι ⊕ κ) : qmaXZThirdWord a b c v e k x ≠ 2 := by
  fin_cases k <;> cases x <;>
    simp [qmaXZThirdWord,qmaSinglePauliWord,ha,hb,hc,hv] <;> split_ifs <;> decide

theorem qmaXZThird_support (a b c v : ι → Fin 4) (e : κ)
    (ha : (qmaPauliSupport a).card ≤ 1) (hb : (qmaPauliSupport b).card ≤ 1)
    (hc : (qmaPauliSupport c).card ≤ 1) (hv : (qmaPauliSupport v).card ≤ 2) (k : Fin 7) :
    (qmaPauliSupport (qmaXZThirdWord a b c v e k)).card ≤ 2 := by
  have hzι : (qmaPauliSupport (fun _ : ι => 0)).card = 0 := by simp [qmaPauliSupport]
  have hzκ : (qmaPauliSupport (fun _ : κ => 0)).card = 0 := by simp [qmaPauliSupport]
  have hs (i : Fin 4) : (qmaPauliSupport (qmaSinglePauliWord e i)).card ≤ 1 :=
    (Finset.card_le_card (qmaSinglePauliWord_support e i)).trans (by simp)
  fin_cases k
  · change (qmaPauliSupport (fun _ : ι ⊕ κ => 0)).card ≤ 2
    simp [qmaPauliSupport]
  · change (qmaPauliSupport (Sum.elim (fun _ : ι => 0) (qmaSinglePauliWord e 3))).card ≤ 2
    rw [qmaPauliSupport_join_card,hzι]
    simpa using (hs 3).trans (by norm_num : 1 ≤ 2)
  · change (qmaPauliSupport (Sum.elim v (fun _ : κ => 0))).card ≤ 2
    simpa only [qmaPauliSupport_join_card,hzκ,add_zero] using hv
  · change (qmaPauliSupport (Sum.elim c (fun _ : κ => 0))).card ≤ 2
    simpa only [qmaPauliSupport_join_card,hzκ,add_zero] using hc.trans (by norm_num : 1 ≤ 2)
  · change (qmaPauliSupport (Sum.elim c (qmaSinglePauliWord e 3))).card ≤ 2
    rw [qmaPauliSupport_join_card]
    exact (Nat.add_le_add hc (hs 3)).trans (by norm_num)
  · change (qmaPauliSupport (Sum.elim a (qmaSinglePauliWord e 1))).card ≤ 2
    rw [qmaPauliSupport_join_card]
    exact (Nat.add_le_add ha (hs 1)).trans (by norm_num)
  · change (qmaPauliSupport (Sum.elim b (qmaSinglePauliWord e 1))).card ≤ 2
    rw [qmaPauliSupport_join_card]
    exact (Nat.add_le_add hb (hs 1)).trans (by norm_num)

end ContinuumCoulomb

end

end OAI
