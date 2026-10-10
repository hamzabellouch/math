import OAI.MathematicalPhysics.DefocusingNLS.Certificates.LaguerreIteratedSlowJet
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.PolynomialProjection

namespace OAI

/-! # Integrability of every iterated Laguerre operator on the slow solution -/

open Filter Topology Asymptotics MeasureTheory Set Polynomial

namespace DefocusingNLS

theorem laguerreIteratedSlowJet_subexponential (q : ℂ) (m : ℕ) (s : ℂ)
    (hq : -1 < q.re) (hs : s.re = 0) (j n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    laguerreIteratedSlowJet q m s j n =O[atTop] (fun t : ℝ => Real.exp (ε * t)) := by
  induction j generalizing n ε with
  | zero =>
      exact (shiftedSlowDerivative_isBigO_rpow n q m s hq hs).trans
        (isLittleO_rpow_exp_pos_mul_atTop _ hε).isBigO
  | succ j ih =>
      exact laguerreJetOperator_subexponential _ ih n ε hε

theorem continuous_laguerreIteratedSlowJet (q : ℂ) (m : ℕ) (s : ℂ)
    (hq : -1 < q.re) (hs : s.im ≠ 0) (j n : ℕ) :
    Continuous (laguerreIteratedSlowJet q m s j n) :=
  continuous_iff_continuousAt.mpr fun t =>
    (hasDerivAt_laguerreIteratedSlowJet q m s hq hs j n t).continuousAt

theorem memLp_halfWeighted_laguerreIteratedSlowJet (q : ℂ) (m : ℕ) (s : ℂ)
    (hq : -1 < q.re) (hsre : s.re = 0) (hsim : s.im ≠ 0) (j n : ℕ) :
    MemLp (halfWeighted (laguerreIteratedSlowJet q m s j n)) 2 (volume.restrict (Ioi 0)) :=
  memLp_halfWeighted_of_exp_bound _ (continuous_laguerreIteratedSlowJet q m s hq hsim j n)
    (laguerreIteratedSlowJet_subexponential q m s hq hsre j n (1 / 4) (by norm_num))

theorem integrableOn_weightedPolynomial_of_subexponential (f : ℝ → ℂ)
    (hc : Continuous f)
    (hf : ∀ ε : ℝ, 0 < ε → f =O[atTop] (fun t : ℝ => Real.exp (ε * t))) (p : ℂ[X]) :
    IntegrableOn (weightedPolynomialIntegrand f p) (Ioi 0) := by
  have hp := polynomial_eval_isBigO_exp p (1 / 4) (by norm_num)
  have hprod : (fun t : ℝ => f t * p.eval (t : ℂ)) =O[atTop]
      (fun t : ℝ => Real.exp ((1 / 2) * t)) := by
    convert! (hf (1 / 4) (by norm_num)).mul hp using 1
    funext t
    rw [← Real.exp_add]
    congr 1
    ring
  have hcont : ContinuousOn (fun t : ℝ => f t * p.eval (t : ℂ)) (Ici 0) :=
    (hc.mul (p.continuous.comp Complex.continuous_ofReal)).continuousOn
  have hi := integrableOn_exp_neg_smul_of_isBigO_exp
    (hcont.locallyIntegrableOn measurableSet_Ici) hprod (by norm_num : (1 / 2 : ℝ) < 1)
  have hi' := hi.mono_set Ioi_subset_Ici_self
  convert! hi' using 1
  funext t
  simp only [weightedPolynomialIntegrand, neg_mul, one_mul, Complex.real_smul]
  ring

theorem integrableOn_weightedPolynomial_laguerreIteratedSlowJet (q : ℂ) (m : ℕ) (s : ℂ)
    (hq : -1 < q.re) (hsre : s.re = 0) (hsim : s.im ≠ 0) (j n : ℕ) (p : ℂ[X]) :
    IntegrableOn (weightedPolynomialIntegrand (laguerreIteratedSlowJet q m s j n) p) (Ioi 0) :=
  integrableOn_weightedPolynomial_of_subexponential _
    (continuous_laguerreIteratedSlowJet q m s hq hsim j n)
    (laguerreIteratedSlowJet_subexponential q m s hq hsre j n) p

end DefocusingNLS

end OAI
