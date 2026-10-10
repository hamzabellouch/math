import OAI.NumberTheory.TotientAsymptotic.PPTTerminalSelection
import OAI.NumberTheory.TotientAsymptotic.PPTPreimageTerminal
import OAI.NumberTheory.TotientAsymptotic.ActualComparisonCutoffs

namespace OAI

/-! Convert the chosen vacant height window into the actual preimage prefix. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

/-- A vacant prime-height window with its proved error budget supplies
all cutoffs for the actual unequal-list preimage truncation. -/
theorem ppt_terminal_window_preimage : ∀ᶠ z : ℝ in atTop,
    ∀ (N H J d F : ℕ) (p : Fin N → ℕ) (S L U : ℝ),
      ∀ hJ : 0 < J, ∀ hJN : J ≤ N,
      0 < d → 0 < F → N ≤ H → 2 ≤ S → 0 ≤ B S →
      (∀ i, IsNormalPrime S (p i)) → (∀ i, 3 ≤ p i) → StrictAnti p →
      F.totient = d*(∏ i, p i).totient →
      (largestPrimeFactor d : ℝ) ≤ S → SquarefreeAbove F S →
      (∀ q : ℕ, q.Prime → q ∣ F → IsNormalPrime S q) →
      largestPrimeFactor F ≠ p ⟨0,by omega⟩ →
      (∀ i : Fin N, (p i-1 : ℕ) ≤ z) → (F.totient : ℝ) ≤ z →
      (B z)^(2/3 : ℝ) ≤ L → U ≤ 2*(B z)^(2/3 : ℝ) → L < U →
      2*(B z)^(2/3 : ℝ) ≤ B z →
      (∀ i : Fin N, i.val < J → U < B (p i)) →
      (∀ i : Fin N, J ≤ i.val → B (p i) < L) →
      (2*(H : ℝ)+1)*Real.sqrt (B S*B z)+B S+
        (8*(H : ℝ)+20)*(2*((Real.log (B z))^5/Real.sqrt (B z)))*B z < (U-L)/4 →
      let V := Real.exp (Real.exp ((L+U)/2))
      ∃ (l : ℕ) (q : Fin l → ℕ) (E : ℕ) (hJl : J ≤ l),
        S ≤ Real.exp (Real.exp L) ∧ 0 < E ∧
        (largestPrimeFactor E : ℝ) ≤ S ∧ StrictAnti q ∧
        (∀ i, IsNormalPrime S (q i) ∧ 3 ≤ q i) ∧
        d*shiftedProduct p = E*shiftedProduct q ∧
        p ⟨0,by omega⟩ ≠ q ⟨0,by omega⟩ ∧
        (∀ i : Fin N, J ≤ i.val → (largestPrimeFactor (p i-1) : ℝ) ≤ V) ∧
        (∀ i : Fin l, i.val < J → V < (q i-1 : ℕ)) ∧
        (∀ i : Fin l, J ≤ i.val → (largestPrimeFactor (q i-1) : ℝ) ≤ V) ∧
        (∀ i : Fin l, (q i-1 : ℕ) ≤ z) := by
  filter_upwards [ppt_normal_factor_loss_mesh,
    B_tendsto.eventually (eventually_gt_atTop (1 : ℝ)),
    eventually_gt_atTop (1 : ℝ)] with z hloss hB hz
  intro N H J d F p S L U hJ hJN hd hF hNH hS hBS hp hp3 hpa hvalue
    hDS hsq hnormal hmismatch hpz hsize hL hU hLU hUt hhigh hlow hbudget
  dsimp only
  let t := B z
  let δ := 2*((Real.log t)^5/Real.sqrt t)
  let M := (L+U)/2
  let Q := (L+3*U)/4
  let V := Real.exp (Real.exp M)
  let T := Real.exp (Real.exp Q)
  let W := Real.exp (Real.exp L)
  let ε := Real.sqrt (B S*t)
  have ht : 0 < t := zero_lt_one.trans hB
  have hδ : 0 ≤ δ := by
    have hlog : 0 < Real.log t := Real.log_pos hB
    dsimp only [δ]
    positivity
  have hε : 0 ≤ ε := Real.sqrt_nonneg _
  have hL0 : 0 < L := (Real.rpow_pos_of_pos ht (2/3 : ℝ)).trans_le hL
  have hwidth : U-L ≤ L := by linarith only [hL, hU]
  have hgrid0 : 0 ≤ (8*(H : ℝ)+20)*δ*t := by positivity
  have hnormalBudget : (2*(H : ℝ)+1)*ε+B S < (U-L)/4 := by
    change (2*(H : ℝ)+1)*ε+B S+(8*(H : ℝ)+20)*δ*t < _ at hbudget
    linarith only [hbudget, hgrid0]
  have hsL : B S < L := by
    have hh : 0 ≤ (2*(H : ℝ)+1)*ε := by positivity
    linarith only [hnormalBudget, hh, hwidth, hL0]
  have hSW : S ≤ W := by
    have hS1 : 1 < S := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hS
    have hh := Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hsL.le)
    simpa only [exp_exp_doubleLog hS1, W] using hh
  have hWM : W < V := Real.exp_lt_exp.mpr (Real.exp_lt_exp.mpr (by dsimp only [M]; linarith))
  have hVQ : V < T := Real.exp_lt_exp.mpr (Real.exp_lt_exp.mpr (by dsimp only [M,Q]; linarith))
  have hQt : Q ≤ t := by dsimp only [Q,t]; linarith only [hLU.le, hU, hUt]
  have hTz : T ≤ z := by
    have hh := Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hQt)
    simpa only [T,t,exp_exp_doubleLog hz] using hh
  have hSz : S ≤ z := hSW.trans (hWM.le.trans (hVQ.le.trans hTz))
  have hcost : δ*t < (U-L)/4 := by
    have hcoef : 1 ≤ 8*(H : ℝ)+20 := by
      have hh : (0 : ℝ) ≤ H := Nat.cast_nonneg H
      linarith only [hh]
    have hh := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hδ ht.le)
    have hnorm0 : 0 ≤ (2*(H : ℝ)+1)*ε+B S := by positivity
    change (2*(H : ℝ)+1)*ε+B S+(8*(H : ℝ)+20)*δ*t < _ at hbudget
    nlinarith only [hh, hnorm0, hbudget]
  have hlast : T ≤ (p ⟨J-1,by omega⟩-1 : ℕ) := by
    let i : Fin N := ⟨J-1,by omega⟩
    have hi : i.val < J := by dsimp only [i]; omega
    have hband := (hloss (p i) S (hp3 i)
      (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hS) hBS hSz (hp i) (hpz i)).1
    have hh := mul_le_mul_of_nonneg_right hband ht.le
    change (B (p i)/t-δ)*t ≤ (B (largestPrimeFactor (p i-1))/t)*t at hh
    rw [sub_mul, div_mul_cancel₀ _ ht.ne', div_mul_cancel₀ _ ht.ne'] at hh
    have hheight : Q < B (largestPrimeFactor (p i-1)) := by
      have hii := hhigh i hi
      dsimp only [Q]
      linarith only [hh, hii, hcost]
    have hr : (1 : ℝ) < largestPrimeFactor (p i-1) := by
      exact_mod_cast one_lt_largestPrimeFactor (show 2 ≤ p i-1 by have := hp3 i; omega)
    have hb := Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hheight.le)
    rw [exp_exp_doubleLog hr] at hb
    exact hb.trans (Nat.cast_le.mpr (largestPrimeFactor_le_self (by have := hp3 i; omega)))
  have hleftlow (i : Fin N) (hi : J ≤ i.val) :
      (largestPrimeFactor (p i-1) : ℝ) ≤ W := by
    have hp1 : (1 : ℝ) < p i := by exact_mod_cast (hp i).1.one_lt
    have hb := Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (hlow i hi).le)
    rw [exp_exp_doubleLog hp1] at hb
    exact (Nat.cast_le.mpr ((largestPrimeFactor_le_self
      (by have := hp3 i; omega)).trans (Nat.sub_le _ _))).trans hb
  have hεQ : Real.sqrt (B S*B T) ≤ ε := by
    have hQT : B T = Q := B_exp_exp Q
    rw [hQT]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hQt hBS)
  have hindexgap : (2*((J-1 : ℕ) : ℝ)+1)*ε < B T-B V := by
    have hJH : (J-1 : ℕ) ≤ H := (Nat.sub_le _ _).trans (hJN.trans hNH)
    have hjr : ((J-1 : ℕ) : ℝ) ≤ H := by exact_mod_cast hJH
    have hh := mul_le_mul_of_nonneg_right
      (show 2*((J-1 : ℕ) : ℝ)+1 ≤ 2*(H : ℝ)+1 by linarith only [hjr]) hε
    rw [show B T=Q from B_exp_exp Q, show B V=M from B_exp_exp M]
    dsimp only [Q,M]
    linarith only [hh, hnormalBudget, hBS]
  have htailgap : (2*(J : ℝ)+1)*ε < B V-B W := by
    have hjr : (J : ℝ) ≤ H := by exact_mod_cast (hJN.trans hNH)
    have hh := mul_le_mul_of_nonneg_right
      (show 2*(J : ℝ)+1 ≤ 2*(H : ℝ)+1 by linarith only [hjr]) hε
    rw [show B V=M from B_exp_exp M, show B W=L from B_exp_exp L]
    dsimp only [M]
    linarith only [hh, hnormalBudget, hBS, hLU]
  obtain ⟨l,q,E,hJl,hE,hES,hqa,hq,heq,hfirst,hqhigh,hqlow,hqz⟩ :=
    ppt_preimage_terminal_prefix p hJ hJN hd hF hS hBS hSW hWM hVQ hp hpa
      hvalue hDS hsq hnormal hmismatch hlast hleftlow hsize hεQ le_rfl hindexgap htailgap
  exact ⟨l,q,E,hJl,hSW,hE,hES,hqa,hq,heq,hfirst,
    fun i hi => (hleftlow i hi).trans hWM.le,hqhigh,hqlow,hqz⟩

end TotientAsymptotic

end

end OAI
