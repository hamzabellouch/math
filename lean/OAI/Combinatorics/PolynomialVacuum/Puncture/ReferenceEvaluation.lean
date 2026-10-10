import OAI.Combinatorics.PolynomialVacuum.Puncture.ExactMoments

namespace OAI

namespace PolynomialVacuumCylinder
open Real MeasureTheory Set

 

theorem reference_moment_integral_positive (m : ℕ) :
    (∫ x : ℝ in Ioi 0,x^(2*m)*denominatorReferenceWeight x)=
      ((2*m+1).factorial : ℝ)/(2*(3*Real.pi/8)^(2*m+2)) *
        ∑' k : ℕ,1/(2*(k : ℝ)+1)^(2*m+2) := by
  let a : ℝ := 3*Real.pi/8
  have ha : 0<a := by dsimp [a]; positivity
  have hnorm (k : ℕ) : (∫ x : ℝ in Ioi 0,‖referenceMomentTerm m a k x‖)=
      ((2*m+1).factorial : ℝ)/(2*a^(2*m+2)) * (1/(2*(k : ℝ)+1)^(2*m+2)) := by
    rw [←referenceMomentTerm_integral m ha k]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hx0 : 0<x := hx
    exact Real.norm_of_nonneg (by unfold referenceMomentTerm; positivity)
  have hsum : Summable (fun k : ℕ=>∫ x : ℝ in Ioi 0,‖referenceMomentTerm m a k x‖) := by
    simp_rw [hnorm]
    exact (odd_moment_summable m).mul_left _
  have he := integral_tsum_of_summable_integral_norm
    (fun k=>referenceMomentTerm_integrable m ha k) hsum
  calc
    _ = ∫ x : ℝ in Ioi 0,∑' k,referenceMomentTerm m a k x := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only
      rw [(referenceMoment_series m ha hx).tsum_eq]
      rw [denominatorReferenceWeight,ite_eq_right (ne_of_gt hx)]
      dsimp [a]
      congr 3
      ring_nf
    _ = ∑' k,∫ x : ℝ in Ioi 0,referenceMomentTerm m a k x := he.symm
    _ = _ := by simp_rw [referenceMomentTerm_integral m ha]; rw [tsum_mul_left]

theorem denominatorReferenceWeight_even (x : ℝ) :
    denominatorReferenceWeight (-x)=denominatorReferenceWeight x := by
  by_cases hx : x=0
  · subst x; simp
  · simp [denominatorReferenceWeight,hx,neg_div,div_neg]

theorem reference_moment_integral (m : ℕ) :
    (∫ x : ℝ,x^(2*m)*denominatorReferenceWeight x)=
      ((2*m+1).factorial : ℝ)/(3*Real.pi/8)^(2*m+2) *
        ∑' k : ℕ,1/(2*(k : ℝ)+1)^(2*m+2) := by
  calc
    _ = ∫ x : ℝ,|x|^(2*m)*denominatorReferenceWeight |x| := by
      apply integral_congr_ae
      filter_upwards [] with x
      rcases le_total 0 x with hx|hx
      · rw [abs_of_nonneg hx]
      · rw [abs_of_nonpos hx,denominatorReferenceWeight_even]
        simp only [pow_mul,neg_sq]
    _ = 2*∫ x : ℝ in Ioi 0,x^(2*m)*denominatorReferenceWeight x := integral_comp_abs (f:=fun x : ℝ=>x^(2*m)*denominatorReferenceWeight x)
    _ = _ := by rw [reference_moment_integral_positive]; ring

 

theorem odd_moment_zeta (m : ℕ) :
    (∑' k : ℕ,(1 : ℝ)/(2*(k : ℝ)+1)^(2*m+2))=
      (1-1/(2 : ℝ)^(2*m+2)) * ∑' k : ℕ,1/(k : ℝ)^(2*m+2) := by
  have h : Summable (fun k : ℕ=>(1 : ℝ)/(k : ℝ)^(2*m+2)) :=
    Real.summable_one_div_nat_pow.mpr (by omega)
  have he := h.comp_injective (show Function.Injective (fun k : ℕ=>2*k) by
    intro i j hij; change 2*i=2*j at hij; omega)
  have ho := h.comp_injective (show Function.Injective (fun k : ℕ=>2*k+1) by
    intro i j hij; change 2*i+1=2*j+1 at hij; omega)
  have hs := tsum_even_add_odd (f:=fun k : ℕ=>(1 : ℝ)/(k : ℝ)^(2*m+2)) he ho
  simp only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one] at hs
  have hf : (fun k : ℕ=>(1 : ℝ)/(2*(k : ℝ))^(2*m+2))=
    (fun k : ℕ=>(1/(2 : ℝ)^(2*m+2))*(1/(k : ℝ)^(2*m+2))) := by
      funext k; simp only [mul_pow,one_div,mul_inv_rev,mul_comm]
  rw [hf,tsum_mul_left] at hs
  calc
    _ = (∑' k : ℕ,1/(k : ℝ)^(2*m+2)) -
        (1/(2 : ℝ)^(2*m+2))*(∑' k : ℕ,1/(k : ℝ)^(2*m+2)) := by
          exact eq_sub_of_add_eq' hs
    _ = _ := by ring

end PolynomialVacuumCylinder

end OAI
