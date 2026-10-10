import OAI.NumberTheory.DirichletL.PrimeRows.FirstNeighborhood
import OAI.NumberTheory.DirichletL.PrimeRows.Origin

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

theorem continuedCorrection_first_boundary_x (eps : ℝ) (heps : 0<eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+w.re) :
    AnalyticAt ℂ (fun x=>continuedCorrection S hS η u x w z) x := by
  apply AnalyticAt.mul _ ((unramifiedProduct_first_neighborhood_analytic_x (eps/2) S hfirst
    η u w z (by linarith) (by linarith)) x (by change max (101/200:ℝ) (1+eps/2-w.re)<x.re; exact max_lt (by linarith) (by linarith)))
  apply Finset.analyticAt_fun_prod
  intro P hP
  exact (ramifiedCorrection_first_analytic_x η u P.val _
    (by exact_mod_cast hS.tail.norm_four P.val (Finset.mem_filter.mp P.property).2)
    w z (by linarith)) x (by change (1/2:ℝ)<x.re; linarith)

theorem continuedCorrection_first_boundary_w (eps : ℝ) (heps : 0<eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+w.re) :
    AnalyticAt ℂ (fun w=>continuedCorrection S hS η u x w z) w := by
  apply AnalyticAt.mul _ ((unramifiedProduct_first_neighborhood_analytic_w (eps/2) S hfirst
    η u x z (by linarith) (by linarith)) w (by change max (-(3/200:ℝ)) (1+eps/2-x.re)<w.re; exact max_lt (by linarith) (by linarith)))
  apply Finset.analyticAt_fun_prod
  intro P hP
  exact ((ramifiedCorrection_first_analytic_w η u P.val _
    (by exact_mod_cast hS.tail.norm_four P.val (Finset.mem_filter.mp P.property).2)
    x z (by linarith) (by linarith)).differentiableOn.analyticOnNhd
      (isOpen_univ : IsOpen (Set.univ : Set ℂ))) w (Set.mem_univ w)

theorem continuedCorrection_first_boundary_z (eps : ℝ) (heps : 0<eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+w.re) :
    AnalyticAt ℂ (fun z=>continuedCorrection S hS η u x w z) z := by
  apply AnalyticAt.mul _ ((unramifiedProduct_first_neighborhood_analytic_z (eps/2) S hfirst
    η u x w (by linarith) (by linarith) (by linarith)) z (by change (27/80:ℝ)<z.re; linarith))
  apply Finset.analyticAt_fun_prod
  intro P hP
  exact (ramifiedCorrection_first_analytic_z η u P.val _
    (by exact_mod_cast hS.tail.norm_four P.val (Finset.mem_filter.mp P.property).2)
    x w (by linarith)) z (by change (1/3:ℝ)<z.re; linarith)

theorem continuedHighSeries_first_boundary_w (eps : ℝ) (heps : 0<eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+w.re) (hpole : w≠1 ∨ (rowCharacter S hS.prime u).residue≠1) :
    DifferentiableAt ℂ (fun w=>continuedHighSeries S hS η u x w z) w := by
  exact (((HeckeOrigin.continued_differentiableAt _ hpole).const_mul _).mul_const _).mul
    (continuedCorrection_first_boundary_w eps heps S hS hfirst η u x w z hx hw hz hxw).differentiableAt

end SevenEighths.ProbeHighRowFamily

end

end OAI
