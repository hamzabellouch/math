import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPolarizedSubdivision
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumXZThird
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitThirdPhased

namespace OAI

/-! Seven literal rational Pauli words for the real-preserving third-order
gadget.  The two possibly imaginary factors use the same mediator phase. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPolarizedThird
open Matrix
open scoped BigOperators Classical
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def word (a b c v : ι → Fin 4) (e : κ) (m : κ → Bool) :
    Fin 7 → (ι ⊕ κ → Fin 4) :=
  ![fun _ => 0, Sum.elim (fun _ => 0) (qmaSinglePauliWord e 3),
    Sum.elim v (fun _ => 0), Sum.elim c (fun _ => 0),
    Sum.elim c (qmaSinglePauliWord e 3),
    Sum.elim a (qmaSinglePauliWord e (QuantumPolarizedSubdivision.axis (m e))),
    Sum.elim b (qmaSinglePauliWord e (QuantumPolarizedSubdivision.axis (m e)))]

def weight (R j : ℚ) : Fin 7 → ℚ :=
  ![R^3/2+R*(1+(j/2)^2), -R^3/2, R*j, R^2/2-(1+(j/2)^2),
    -R^2/2, R^2, R^2*j/2]

theorem weight_cast (R j : ℚ) (k : Fin 7) :
    (weight R j k : ℝ) = qmaXZThirdWeight (R:ℝ) (j:ℝ) k := by
  fin_cases k <;> simp [weight,qmaXZThirdWeight]

theorem sum_eq (a b c v : ι → Fin 4) (e : κ) (m : κ → Bool) (R j : ℚ)
    (hab : qmaPauliWord a*qmaPauliWord b = qmaPauliWord v) :
    (∑ k, (weight R j k : ℂ) • qmaPauliWord (word a b c v e m k)) =
      ∑ k, qmaThirdPhasedLocalPiece (qmaPauliWord a) (qmaPauliWord b)
        (qmaPauliWord c) e (R:ℝ) (j:ℝ) m k := by
  have hI : qmaJoinMatrix (1 : Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
      (1 : Matrix (κ → Fin 2) (κ → Fin 2) ℂ) = 1 := by
    simp [qmaJoinMatrix,Matrix.submatrix_one_equiv]
  simp only [word,weight,qmaThirdPhasedLocalPiece_eq,
    Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,Matrix.cons_val_succ,add_zero,
    qmaPauliWord_zero,← qmaPauliWord_join,QuantumPolarizedSubdivision.single_flip,
    qmaJoinOccupation_expand,hI,hab]
  have hr (r : ℝ) (M : Matrix (ι ⊕ κ → Fin 2) (ι ⊕ κ → Fin 2) ℂ) :
      r • M = (r:ℂ) • M := rfl
  simp only [hr]
  push_cast
  module

theorem support (a b c v : ι → Fin 4) (e : κ) (m : κ → Bool)
    (ha : (qmaPauliSupport a).card ≤ 1) (hb : (qmaPauliSupport b).card ≤ 1)
    (hc : (qmaPauliSupport c).card ≤ 1) (hv : (qmaPauliSupport v).card ≤ 2) (k : Fin 7) :
    (qmaPauliSupport (word a b c v e m k)).card ≤ 2 := by
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
  · change (qmaPauliSupport (Sum.elim a _)).card ≤ 2
    rw [qmaPauliSupport_join_card]
    exact (Nat.add_le_add ha (hs _)).trans (by norm_num)
  · change (qmaPauliSupport (Sum.elim b _)).card ≤ 2
    rw [qmaPauliSupport_join_card]
    exact (Nat.add_le_add hb (hs _)).trans (by norm_num)

omit [DecidableEq ι] in
theorem even (a b c v : ι → Fin 4) (e : κ) (m : κ → Bool)
    (ha : m e = decide (Odd (qmaPauliYCount a)))
    (hb : m e = decide (Odd (qmaPauliYCount b)))
    (hc : Even (qmaPauliYCount c)) (hv : Even (qmaPauliYCount v)) (k : Fin 7) :
    Even (qmaPauliYCount (word a b c v e m k)) := by
  have hsub := QuantumPolarizedSubdivision.even a b e m ha hb
  have hz : qmaPauliYCount (fun _ : κ => (0:Fin 4)) = 0 := by simp [qmaPauliYCount]
  fin_cases k
  · simp [word,qmaPauliYCount]
  · exact hsub 1
  · change Even (qmaPauliYCount (Sum.elim v (fun _ : κ => 0)))
    simpa only [QuantumPolarizedSubdivision.yCount_join,hz,add_zero] using hv
  · change Even (qmaPauliYCount (Sum.elim c (fun _ : κ => 0)))
    simpa only [QuantumPolarizedSubdivision.yCount_join,hz,add_zero] using hc
  · change Even (qmaPauliYCount (Sum.elim c (qmaSinglePauliWord e 3)))
    simpa only [QuantumPolarizedSubdivision.yCount_join,
      QuantumPolarizedSubdivision.yCount_single,show (3:Fin 4) ≠ 2 by decide,
      ite_false,add_zero] using hc
  · exact hsub 2
  · exact hsub 3

end ContinuumCoulomb.QuantumPolarizedThird

end

end OAI
