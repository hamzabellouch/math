import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumXZSubdivision
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedSplit

namespace OAI

/-! Literal four-word subdivision for even-Y interactions.  The mediator
letter is Y precisely when each input factor has odd Y parity.  All output
coefficients are rational when the input coefficient and scale are rational. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPolarizedSubdivision
open Matrix
open scoped BigOperators Classical
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def axis (p : Bool) : Fin 4 := if p then 2 else 1

theorem single_flip (m : κ → Bool) (e : κ) :
    qmaPauliWord (qmaSinglePauliWord e (axis (m e))) = qmaPolarizedFlip m e := by
  cases hm : m e
  · simpa only [axis,hm,Bool.false_eq_true,ite_false,qmaPolarizedFlip_eq] using
      qmaSinglePauliWord_X e
  · have hY (u v : Fin 2) : qmaPauli 2 u v =
        if u = Equiv.swap (0:Fin 2) 1 v then
          (if v = 1 then -Complex.I else Complex.I) else 0 := by
      fin_cases u <;> fin_cases v <;>
        norm_num [qmaPauli,pauliY,Equiv.swap_apply_def]
    ext s t
    simp only [axis,hm,ite_true,qmaSinglePauliWord_apply,hY,qmaPolarizedFlip]
    by_cases h : s = qmaBitFlip e t
    · subst s
      have he : qmaBitFlip e t e = Equiv.swap (0:Fin 2) 1 (t e) := by simp [qmaBitFlip]
      rw [ite_eq_left he,ite_eq_left rfl]
      have hp : (∏ k ∈ Finset.univ.erase e,
          if qmaBitFlip e t k = t k then (1:ℂ) else 0) = 1 := by
        apply Finset.prod_eq_one
        intro k hk
        simp [qmaBitFlip,(Finset.mem_erase.mp hk).1]
      rw [hp,mul_one]
    · rw [ite_eq_right h]
      obtain ⟨k,hk⟩ := Function.ne_iff.mp h
      by_cases hke : k = e
      · subst k
        have he : s e ≠ Equiv.swap (0:Fin 2) 1 (t e) := by simpa [qmaBitFlip] using hk
        rw [ite_eq_right he,zero_mul]
      · have he : s k ≠ t k := by simpa [qmaBitFlip,hke] using hk
        rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hke,Finset.mem_univ _⟩)
          (ite_eq_right he),mul_zero]

def word (a b : ι → Fin 4) (e : κ) (m : κ → Bool) :
    Fin 4 → (ι ⊕ κ → Fin 4) :=
  ![fun _ => 0,Sum.elim (fun _ => 0) (qmaSinglePauliWord e 3),
    Sum.elim a (qmaSinglePauliWord e (axis (m e))),
    Sum.elim b (qmaSinglePauliWord e (axis (m e)))]

def weight (R j : ℚ) : Fin 4 → ℚ :=
  ![R^2/2+1+(j/2)^2,-R^2/2,R,-R*j/2]

theorem weight_cast (R j : ℚ) (k : Fin 4) :
    (weight R j k : ℝ) = qmaXZSubdivisionWeight (R:ℝ) (j:ℝ) k := by
  fin_cases k <;> simp [weight,qmaXZSubdivisionWeight]

omit [DecidableEq ι] in
theorem sum_eq (a b : ι → Fin 4) (e : κ) (m : κ → Bool) (R j : ℚ) :
    (∑ k, (weight R j k:ℂ) • qmaPauliWord (word a b e m k)) =
      ∑ k, qmaSubdivisionLocalPiece (qmaPauliWord a) (qmaPauliWord b)
        e (R:ℝ) (j:ℝ) m k := by
  have hc (k : Fin 4) : (weight R j k:ℂ) =
      ((qmaXZSubdivisionWeight (R:ℝ) (j:ℝ) k:ℝ):ℂ) := by
    rw [← weight_cast]
    norm_cast
  simp only [hc,word,qmaXZSubdivisionWeight,qmaSubdivisionLocalPiece,
    Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,Matrix.cons_val_succ,add_zero,
    qmaPauliWord_zero,← qmaPauliWord_join,single_flip,qmaJoinOccupation_pauli]
  have hr (r : ℝ) (M : Matrix (ι ⊕ κ → Fin 2) (ι ⊕ κ → Fin 2) ℂ) :
      r • M = (r:ℂ) • M := rfl
  simp only [hr]
  push_cast
  module

theorem support (a b : ι → Fin 4) (e : κ) (m : κ → Bool) {d : ℕ}
    (ha : (qmaPauliSupport a).card ≤ d) (hb : (qmaPauliSupport b).card ≤ d)
    (k : Fin 4) : (qmaPauliSupport (word a b e m k)).card ≤ d+1 := by
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
  · change (qmaPauliSupport (Sum.elim a (qmaSinglePauliWord e (axis (m e))))).card ≤ d+1
    rw [qmaPauliSupport_join_card]
    have := hs (axis (m e))
    omega
  · change (qmaPauliSupport (Sum.elim b (qmaSinglePauliWord e (axis (m e))))).card ≤ d+1
    rw [qmaPauliSupport_join_card]
    have := hs (axis (m e))
    omega

omit [DecidableEq ι] [DecidableEq κ] in
theorem yCount_join (a : ι → Fin 4) (b : κ → Fin 4) :
    qmaPauliYCount (Sum.elim a b) = qmaPauliYCount a+qmaPauliYCount b := by
  simp only [qmaPauliYCount,Finset.card_filter,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr]
  rfl

theorem yCount_single (e : κ) (μ : Fin 4) :
    qmaPauliYCount (qmaSinglePauliWord e μ) = if μ = 2 then 1 else 0 := by
  have hset : Finset.univ.filter (fun i => qmaSinglePauliWord e μ i = 2) =
      if μ = 2 then {e} else ∅ := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    by_cases hm : μ = 2 <;> by_cases hi : i = e <;>
      simp [qmaSinglePauliWord,hi,hm]
  rw [qmaPauliYCount,hset]
  split_ifs <;> simp

omit [DecidableEq ι] in
private theorem parity_padding (v : ι → Fin 4) :
    Even (qmaPauliYCount v+if axis (decide (Odd (qmaPauliYCount v))) = 2 then 1 else 0) := by
  by_cases h : Odd (qmaPauliYCount v)
  · simp [axis,h]
  · simpa [axis,h] using (Nat.even_or_odd (qmaPauliYCount v)).resolve_right h

omit [DecidableEq ι] in
theorem even (a b : ι → Fin 4) (e : κ) (m : κ → Bool)
    (ha : m e = decide (Odd (qmaPauliYCount a)))
    (hb : m e = decide (Odd (qmaPauliYCount b))) (k : Fin 4) :
    Even (qmaPauliYCount (word a b e m k)) := by
  fin_cases k
  · simp [word,qmaPauliYCount]
  · change Even (qmaPauliYCount (Sum.elim (fun _ : ι => 0) (qmaSinglePauliWord e 3)))
    rw [yCount_join,yCount_single]
    simp [qmaPauliYCount]
  · change Even (qmaPauliYCount (Sum.elim a (qmaSinglePauliWord e (axis (m e)))))
    rw [yCount_join,yCount_single,ha]
    exact parity_padding a
  · change Even (qmaPauliYCount (Sum.elim b (qmaSinglePauliWord e (axis (m e)))))
    rw [yCount_join,yCount_single,hb]
    exact parity_padding b

end ContinuumCoulomb.QuantumPolarizedSubdivision

end

end OAI
