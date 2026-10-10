import OAI.Combinatorics.PolynomialVacuum.Algebra.Projectors

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical

 

theorem Pone_image (v : Pair → ℂ) (hv : Pone.mulVec v=v) :
    ∃ w : Spin → ℂ, ∀ ab, v ab = ∑ h : Spin, insertion ab h * w h := by
  refine ⟨fun h => (∑ cd : Pair, insertion cd h*v cd)/nZero,?_⟩
  intro ab
  have hv' := congrFun hv ab
  rw [← hv']
  simp only [Matrix.mulVec,dotProduct,Pone,div_eq_mul_inv,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro cd _
  ring

noncomputable def occupiedSpin (b : Bool) : Spin := if b then .minus else .plus

def allowedSpin (b : Bool) (s : Spin) : Prop := s=.zero ∨ s=occupiedSpin b

def pairSupported (b : Bool) (v : Pair → ℂ) : Prop :=
  ∀ ab, ¬(allowedSpin b ab.1 ∧ allowedSpin b ab.2) → v ab=0

 
theorem pairImage_equal_bits (b : Bool) (v : Pair → ℂ)
    (hv : Pone.mulVec v=v) (hs : pairSupported b v) :
    ∃ c : ℂ, ∀ ab, v ab=insertion ab (occupiedSpin b)*c := by
  obtain ⟨w,hw⟩ := Pone_image v hv
  have hx : xStar ≠ 0 := by
    unfold xStar
    exact_mod_cast inv_ne_zero (Real.sqrt_ne_zero'.mpr (by positivity : (0:ℝ)<2+Real.sqrt 2))
  have hq : q ≠ 0 := Complex.exp_ne_zero _
  cases b with
  | false =>
    have hzero := hs (.plus,.minus) (by simp [allowedSpin,occupiedSpin])
    rw [hw] at hzero
    norm_num [sum_spin,insertion,charge] at hzero
    have hw0 : w .zero=0 := by simpa [hx,hq] using hzero
    have hminus := hs (.zero,.minus) (by simp [allowedSpin,occupiedSpin])
    rw [hw] at hminus
    norm_num [sum_spin,insertion,charge] at hminus
    have hwm : w .minus=0 := by simpa [hx,hq] using hminus
    refine ⟨w .plus,?_⟩
    intro ab
    rw [hw,sum_spin,hw0,hwm]
    simp [occupiedSpin]
  | true =>
    have hzero := hs (.plus,.minus) (by simp [allowedSpin,occupiedSpin])
    rw [hw] at hzero
    norm_num [sum_spin,insertion,charge] at hzero
    have hw0 : w .zero=0 := by simpa [hx,hq] using hzero
    have hplus := hs (.zero,.plus) (by simp [allowedSpin,occupiedSpin])
    rw [hw] at hplus
    norm_num [sum_spin,insertion,charge,zpow_neg] at hplus
    have hwp : w .plus=0 := by simpa [hx,hq] using hplus
    refine ⟨w .minus,?_⟩
    intro ab
    rw [hw,sum_spin,hw0,hwp]
    simp [occupiedSpin]

end PolynomialVacuumAlgebra

end OAI
