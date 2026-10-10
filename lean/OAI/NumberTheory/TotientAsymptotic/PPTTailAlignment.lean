import OAI.NumberTheory.TotientAsymptotic.PPTUnequalAlignment

namespace OAI

/-!
The right-tail smoothness argument following Ford (5.35).  If the left
tail is smooth, an additional right prime with a large predecessor factor
would force too many normal shifts across the intervening interval.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

theorem ppt_right_tail_smooth {k l D E J : ℕ}
    (p : Fin k → ℕ) (q : Fin l → ℕ) {S U V z ε : ℝ}
    (hS : 1 < S) (hBS : 0 ≤ B S) (hSU : S ≤ U) (hUV : U < V)
    (hD : D ≠ 0) (hE : E ≠ 0)
    (hp : ∀ i, IsNormalPrime S (p i)) (hq : ∀ i, IsNormalPrime S (q i))
    (hqa : Antitone q) (heq : D*shiftedProduct p = E*shiftedProduct q)
    (hDU : (largestPrimeFactor D : ℝ) ≤ U)
    (hEU : (largestPrimeFactor E : ℝ) ≤ U)
    (hleft : ∀ i : Fin k, J ≤ i.val → (largestPrimeFactor (p i-1) : ℝ) ≤ U)
    (hqz : ∀ i : Fin l, (q i-1 : ℕ) ≤ z)
    (hε : Real.sqrt (B S*B z) ≤ ε)
    (hgap : (2*(J : ℝ)+1)*ε < B V-B U) :
    ∀ i : Fin l, J ≤ i.val → (largestPrimeFactor (q i-1) : ℝ) ≤ V := by
  intro i hJi
  by_contra hbad
  have hVT : V < (largestPrimeFactor (q i-1) : ℝ) := lt_of_not_ge hbad
  let T : ℝ := largestPrimeFactor (q i-1)
  have hV : 1 < V := (hS.trans_le hSU).trans hUV
  have hT : 1 < T := hV.trans hVT
  have hqi : 1 ≤ q i-1 := by have := (hq i).1.two_le; omega
  have hTpred : T ≤ (q i-1 : ℕ) := Nat.cast_le.mpr (largestPrimeFactor_le_self hqi)
  have hTz : T ≤ z := hTpred.trans (hqz i)
  have hBTz : B T ≤ B z := Real.log_le_log (Real.log_pos hT)
    (Real.log_le_log (zero_lt_one.trans hT) hTz)
  have hBVT : B V ≤ B T := Real.log_le_log (Real.log_pos hV)
    (Real.log_le_log (zero_lt_one.trans hV) hVT.le)
  have hJT : J < l := hJi.trans_lt i.isLt
  let j : Fin l := ⟨J, hJT⟩
  have hqT (r : Fin l) (hrj : r ≤ j) : T ≤ (q r-1 : ℕ) := by
    have hrJ : r.val ≤ J := hrj
    have hri : r ≤ i := hrJ.trans hJi
    exact hTpred.trans (Nat.cast_le.mpr (Nat.sub_le_sub_right (hqa hri) 1))
  have hεT : Real.sqrt (B S*B T) ≤ ε :=
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hBTz hBS)).trans hε
  have hbound := ppt_unequal_normality_gap q p j hS hBS hE hD hq hp heq.symm
    hEU hDU hSU (hUV.trans hVT) hεT hqT hleft
  change B T-B U ≤ (2*(J : ℝ)+1)*ε at hbound
  linarith

def pptRightLowFactor {l : ℕ} (q : Fin l → ℕ) (E J : ℕ) : ℕ :=
  E * ∏ i ∈ Finset.univ.filter (fun i : Fin l => J ≤ i.val), (q i-1)

/-- The actual remaining shifted product, not an additional smoothness
hypothesis for an unrelated integer. -/
lemma ppt_right_low_factor_smooth {l E J : ℕ} (q : Fin l → ℕ) {V : ℝ}
    (hV : 1 ≤ V) (hE : (largestPrimeFactor E : ℝ) ≤ V)
    (htail : ∀ i : Fin l, J ≤ i.val → (largestPrimeFactor (q i-1) : ℝ) ≤ V) :
    (largestPrimeFactor (pptRightLowFactor q E J) : ℝ) ≤ V := by
  have hnat : largestPrimeFactor (pptRightLowFactor q E J) ≤ ⌊V⌋₊ := by
    apply largestPrimeFactor_mul_le (Nat.le_floor hE)
    apply largestPrimeFactor_prod_le _ _ (Nat.le_floor (by simpa only [Nat.cast_one] using hV))
    intro i hi
    exact Nat.le_floor (htail i (Finset.mem_filter.mp hi).2)
  exact (Nat.cast_le.mpr hnat).trans (Nat.floor_le (zero_le_one.trans hV))

/-- Splitting the right list at `J` preserves the exact shifted-product
equation with `pptRightLowFactor` as its residual multiplier. -/
lemma ppt_right_low_factor_equation {k l D E J : ℕ}
    (p : Fin k → ℕ) (q : Fin l → ℕ)
    (heq : D*shiftedProduct p = E*shiftedProduct q) :
    D*shiftedProduct p = pptRightLowFactor q E J *
      ∏ i ∈ Finset.univ.filter (fun i : Fin l => i.val < J), (q i-1) := by
  have hsplit := Finset.prod_filter_mul_prod_filter_not Finset.univ
    (fun i : Fin l => i.val < J) (fun i => q i-1)
  simp only [not_lt] at hsplit
  rw [heq, shiftedProduct, ← hsplit]
  unfold pptRightLowFactor
  ring

end TotientAsymptotic

end

end OAI
