import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorCoefficient
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPolynomialPowerLimit

namespace OAI

/-! Large-power convergence of every fixed exterior expansion coefficient. -/

open Polynomial Filter
namespace DefocusingNLS

theorem radialExteriorExpansion_coefficient_limit (ν m : ℕ → ℂ) (ν₀ m₀ : ℂ)
    (hν : Tendsto ν atTop (nhds ν₀)) (hm : Tendsto m atTop (nhds m₀)) (hm₀ : ‖m₀‖ < 1)
    (j k : ℕ) :
    Tendsto (fun n => (radialExteriorExpansion (ν n) n (m n) j).coeff k) atTop
      (nhds ((radialFreeExpansion ν₀ m₀ j).coeff k)) := by
  induction j generalizing k with
  | zero =>
    simpa only [radialExteriorExpansion,radialFreeExpansion,coeff_C] using
      (show Tendsto (fun n => if k=0 then m n else 0) atTop
        (nhds (if k=0 then m₀ else 0)) from by split_ifs; exact hm; exact tendsto_const_nhds)
  | succ j ih =>
    have hp : Tendsto (fun n =>
        (radialPolynomialPower n (radialExteriorExpansion (ν n) n (m n) j)).coeff j)
        atTop (nhds 0) := by
      apply radialPolynomialPower_coefficient_limit _ (radialFreeExpansion ν₀ m₀ j) j j
      · exact Eventually.of_forall (fun n => radialExteriorExpansion_degree _ _ _ _)
      · exact fun k _ => ih k
      · simpa only [radialFreeExpansion_constant] using hm₀
    have hc := (((hν.sub_const (2*(j : ℂ))).mul
      ((hν.add_const 10).sub_const (2*(j : ℂ)))).mul (ih j)).sub hp
    have hdiv := hc.div_const (Complex.I*(j+1 : ℕ))
    simp only [sub_zero] at hdiv
    simp only [radialExteriorExpansion_step,radialFreeExpansion,coeff_add,coeff_monomial]
    by_cases hk : j+1=k
    · simp only [hk,ite_true]
      simpa only [hk] using (ih k).add hdiv
    · simp only [hk,ite_false,add_zero]
      exact ih k

end DefocusingNLS

end OAI
