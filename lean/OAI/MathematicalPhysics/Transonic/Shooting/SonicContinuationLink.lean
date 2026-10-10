import OAI.MathematicalPhysics.Transonic.Core

namespace OAI

section

namespace SepticProfile.SonicContinuation
open Set Filter Polynomial
open scoped Topology ContDiff

/-- Finite arithmetic certificate interface for the *actual* selected weak
sonic Taylor series, retaining the exact normalized septic source equation. -/
structure PolynomialCertificate (sigma kappa s : ℝ) : Prop where
  lower_range : ∀ f : PowerSeries ℝ, PowerSeries.coeff 0 f=1 →
    PowerSeries.coeff 1 f= -s/500 → EulerFormal.residual sigma kappa (3/5) (1/500) f=0 →
    ∀ t ∈ Icc (0:ℝ) (5/6), 1-t/50≤(EulerPolynomial.barrier f (-1/1000)).eval t ∧
      (EulerPolynomial.barrier f (-1/1000)).eval t≤1-t/500
  upper_range : ∀ f : PowerSeries ℝ, PowerSeries.coeff 0 f=1 →
    PowerSeries.coeff 1 f= -s/500 → EulerFormal.residual sigma kappa (3/5) (1/500) f=0 →
    ∀ t ∈ Icc (0:ℝ) (5/6), 1-t/50≤(EulerPolynomial.barrier f (1/1000)).eval t ∧
      (EulerPolynomial.barrier f (1/1000)).eval t≤1-t/500
  lower_residual : ∀ f : PowerSeries ℝ, PowerSeries.coeff 0 f=1 →
    PowerSeries.coeff 1 f= -s/500 → EulerFormal.residual sigma kappa (3/5) (1/500) f=0 →
    ∀ t ∈ Ioc (0:ℝ) (5/6),
      EulerFormal.profileResidual sigma kappa (3/5) (1/500)
        (fun x => (EulerPolynomial.barrier f (-1/1000)).eval x) t<0
  upper_residual : ∀ f : PowerSeries ℝ, PowerSeries.coeff 0 f=1 →
    PowerSeries.coeff 1 f= -s/500 → EulerFormal.residual sigma kappa (3/5) (1/500) f=0 →
    ∀ t ∈ Ioc (0:ℝ) (5/6),
      0<EulerFormal.profileResidual sigma kappa (3/5) (1/500)
        (fun x => (EulerPolynomial.barrier f (1/1000)).eval x) t

/-- Supplies a genuine analytic sonic germ and a genuine solution continued to
z=.99 (Euler t=5/6). The germ is constructed by the regular-singular inverse;
no ordinary Picard assumption is made at the singular point x=0. -/
theorem exists_germ_and_continuation (sigma kappa s rho : ℝ) (hsig : sigma<1)
    (hs : 2*(1-sigma)*s^2-(1-(3/5:ℝ))*(2*kappa+3)*s+3*(1-(3/5:ℝ))=0)
    (hd : 2*(1-sigma)*s≠0)
    (hrho : rho*(2*(1-sigma)*s)=(1-(3/5:ℝ))*(2*kappa+3)-2*(1-sigma)*s)
    (hnr : ∀ n : ℕ, rho≠(n:ℝ)+2) (hcert : PolynomialCertificate sigma kappa s) :
    ∃ f u : ℝ → ℝ, ∃ a : ℝ, 0<a ∧ a<5/6 ∧
      AnalyticAt ℝ f 0 ∧ f 0=1 ∧ deriv f 0= -s/500 ∧
      (∀ᶠ t in 𝓝 (0:ℝ), SourceEuler.residual sigma kappa (3/5) (1/500) t (f t) (deriv f t)=0) ∧
      u a=f a ∧ ContinuousOn u (Icc a (5/6)) ∧
      (∀ t ∈ Icc a (5/6),
        (EulerPolynomial.barrier (SonicJet.jet f) (-1/1000)).eval t≤u t ∧
        u t≤(EulerPolynomial.barrier (SonicJet.jet f) (1/1000)).eval t) ∧
      ∀ t ∈ Icc a (5/6), HasDerivWithinAt u
        (EulerContinuation.N kappa t (u t)/EulerContinuation.D sigma t (u t))
        (Icc a (5/6)) t := by
  obtain ⟨f,hfa,hf0,hf1,hfe⟩ := SourceEuler.exists_real_euler_germ sigma kappa (3/5)
    (1/500) s rho hs hd hrho hnr
  have hf1' : deriv f 0= -s/500 := by rw [hf1];ring
  have hjet0 : PowerSeries.coeff 0 (SonicJet.jet f)=1 := by
    simpa [SonicJet.coeff_jet] using hf0
  have hjet1 : PowerSeries.coeff 1 (SonicJet.jet f)= -s/500 := by
    simpa [SonicJet.coeff_jet] using hf1'
  have hres : EulerFormal.residual sigma kappa (3/5) (1/500) (SonicJet.jet f)=0 := by
    apply EulerFormal.residual_of_solution sigma kappa (3/5) (1/500) hfa.contDiffAt
    filter_upwards [hfe] with t ht
    simpa only [EulerFormal.profileResidual,SourceEuler.residual,SourceEuler.A,SourceEuler.B]
      using ht
  have hentry := EulerPolynomial.exists_barrier_entry f hfa.contDiffAt (1/1000) (by norm_num)
  obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhds_iff.mp (inter_mem hentry (Iio_mem_nhds (by norm_num : (0:ℝ)<5/6)))
  let a : ℝ := min (ε/2) (1/2)
  have ha : 0<a := by dsimp [a];positivity
  have hae : a<ε := (min_le_left _ _).trans_lt (by linarith)
  have ham : a ∈ Metric.ball (0:ℝ) ε := by
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos ha]
    exact hae
  have hab : a<5/6 := (hsub ham).2
  have hbounds := (hsub ham).1 ha
  have hbounds' : f a ∈ Icc
      ((EulerPolynomial.barrier (SonicJet.jet f) (-1/1000)).eval a)
      ((EulerPolynomial.barrier (SonicJet.jet f) (1/1000)).eval a) := by
    constructor
    · simpa only [neg_div] using hbounds.1.le
    · exact hbounds.2.le
  obtain ⟨u,hua,huc,hub,hud⟩ := EulerContinuation.exists_between_polynomials (u0 := f a) hsig ha hab.le
    (EulerPolynomial.barrier (SonicJet.jet f) (-1/1000))
    (EulerPolynomial.barrier (SonicJet.jet f) (1/1000))
    (hcert.lower_range _ hjet0 hjet1 hres) (hcert.upper_range _ hjet0 hjet1 hres)
    (hcert.lower_residual _ hjet0 hjet1 hres) (hcert.upper_residual _ hjet0 hjet1 hres)
    hbounds'
  exact ⟨f,u,a,ha,hab,hfa,hf0,hf1',hfe,hua,huc,hub,hud⟩
end SepticProfile.SonicContinuation


end

end OAI
