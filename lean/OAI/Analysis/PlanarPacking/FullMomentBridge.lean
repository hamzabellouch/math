import OAI.Analysis.PlanarPacking.Entire
import OAI.Analysis.PlanarPacking.KernelDerivative
import OAI.Analysis.PlanarPacking.TableKBridge
import OAI.Analysis.PlanarPacking.HighMomentsBase

namespace OAI

namespace SharpPlanar
open MeasureTheory
open scoped BigOperators
lemma normalized_direct (m t : ℝ) (ell : ℕ) :
    complexDirectFactor m 1 ell t = directKernel ell m t / (ell.factorial:ℂ) := by
  simp only [complexDirectFactor,Complex.ofReal_one,mul_one,directKernel]
  ring
lemma fullMoment_transformed (a : Bool) (m : ℝ) (ell : ℕ) :
    fullMoment a true m ell=K (tableData a) ell m/(ell.factorial:ℝ) :=
  tableMomentK_eq a m ell
lemma fullMoment_direct (a : Bool) (m : ℝ) (ell : ℕ) :
    fullMoment a false m ell=cardinalSeries (tableData a) ell m/(ell.factorial:ℝ) := by
  have hi : fullMomentIntegral a false m ell =
      (∑ j ∈ Finset.range 6,∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,
        density (tableData a) j t*directKernel ell m t)/(ell.factorial:ℂ) := by
    unfold fullMomentIntegral
    rw [← Finset.sum_range (fun j => pieceIntegral (fun t => tableDensity a j t*fullFactor false m ell t) j),Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [pieceIntegral,fullFactor,Bool.false_eq_true,ite_false,normalized_direct,← tableData_density,← mul_div_assoc]
    rw [intervalIntegral.integral_div]
  have ha : fullMomentAtom a false m ell =
      ((tableConstant a:ℝ):ℂ)*(Pcoeff 0*(0:ℂ)^ell+
        ∑ j ∈ Finset.Icc 1 6,2*Pcoeff j*(Complex.I*Real.pi*((j:ℝ)/6))^ell*
          Complex.exp (Complex.I*Real.pi*((j:ℝ)/6)*m))/(ell.factorial:ℂ) := by
    unfold fullMomentAtom
    simp only [fullFactor,Bool.false_eq_true,ite_false,← Complex.ofReal_ofNat 6,← Complex.ofReal_div,normalized_direct,← mul_div_assoc]
    rw [← Finset.sum_div,← mul_div_assoc]
    congr 2
    norm_num [Fin.sum_univ_succ,Finset.sum_Icc_succ_top,directKernel]
    ring
  unfold fullMoment
  rw [hi,ha,← add_div]
  change (_/((ell.factorial:ℝ):ℂ)).re=_
  rw [Complex.div_ofReal_re,Complex.add_re,Complex.mul_re]
  simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [directDensity_series]
  congr 1
  unfold cardinalSeries Pmoment
  change _ = (tableConstant a:ℝ)*_+_+_+_
  simp only [Complex.ofReal_div,Complex.ofReal_ofNat]
  ring
noncomputable def tableH (a : Bool) (s : ℝ) : ℝ :=
  cardinal (tableData a) s+K (tableData (!a)) 0 s
noncomputable def tableHJet (a : Bool) (ell : ℕ) (s : ℝ) : ℝ :=
  cardinalSeries (tableData a) ell s+K (tableData (!a)) ell s
lemma tableHJet_zero (a : Bool) : tableHJet a 0=tableH a := by
  funext s
  rw [tableHJet,← cardinal_eq_cardinalSeries]
  rfl
lemma tableHJet_deriv (a : Bool) (ell : ℕ) (s : ℝ) :
    HasDerivAt (tableHJet a ell) (tableHJet a (ell+1) s) s :=
  (cardinalSeries_hasDerivAt _ _ _).add (K_hasDerivAt _ _ _)
lemma tableH_iteratedDeriv (a : Bool) (ell : ℕ) : iteratedDeriv ell (tableH a)=tableHJet a ell := by
  induction ell with
  | zero => exact (tableHJet_zero a).symm
  | succ ell ih =>
    rw [iteratedDeriv_succ,ih]
    funext s
    exact (tableHJet_deriv a ell s).deriv
end SharpPlanar

end OAI
