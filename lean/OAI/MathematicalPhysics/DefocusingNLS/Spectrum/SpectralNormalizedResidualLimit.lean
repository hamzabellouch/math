import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPolynomialUniformLimit
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPolynomialQuotientLimit

namespace OAI

/-! Uniform convergence of the exactly normalized residuals of the outgoing
columns. This controls all high nonlinear polynomial coefficients together. -/

open Filter Topology Set Polynomial
namespace DefocusingNLS

noncomputable def spectralLinearResidual (h ν η : ℂ) (U : ℂ[X]) : ℂ[X] :=
  spectralPolynomialResidual h ν η 0 0 U 0

theorem spectralLinearResidual_degree (h ν η : ℂ) (U : ℂ[X]) (d : ℕ)
    (hU : U.natDegree ≤ d) : (spectralLinearResidual h ν η U).natDegree ≤ d := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  have h0 : U.coeff k=0 := coeff_eq_zero_of_natDegree_lt (hU.trans_lt hk)
  have h1 : U.coeff (k+1)=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  simp only [spectralLinearResidual,spectralPolynomialResidual,coeff_sub,coeff_add,
    coeff_C_mul,radialPolynomialEuler_coeff,coeff_derivative,zero_mul,sub_zero,h0,h1,mul_zero,add_zero]

theorem spectralLinearResidual_coefficient_limit (h η : ℂ) (ν : ℕ → ℂ) (ν₀ : ℂ)
    (hν : Tendsto ν atTop (𝓝 ν₀)) (U : ℕ → ℂ[X]) (U₀ : ℂ[X])
    (hU : ∀ k, Tendsto (fun n => (U n).coeff k) atTop (𝓝 (U₀.coeff k))) (k : ℕ) :
    Tendsto (fun n => (spectralLinearResidual h (ν n) η (U n)).coeff k) atTop
      (𝓝 ((spectralLinearResidual h ν₀ η U₀).coeff k)) := by
  exact spectralPolynomialResidual_zero_coefficient_limit h η ν ν₀ hν
    (fun _ => 0) (fun _ => 0) U (fun _ => 0) U₀ 0
    (fun _ => by simpa only [coeff_zero] using tendsto_const_nhds (x := (0 : ℂ)))
    (fun _ => by simpa only [coeff_zero] using tendsto_const_nhds (x := (0 : ℂ))) hU
    (fun _ => tendsto_const_nhds) k

theorem spectralPolynomialResidual_uniform_limit (h η : ℂ) (ν : ℕ → ℂ) (ν₀ : ℂ)
    (hν : Tendsto ν atTop (𝓝 ν₀)) (A B U V : ℕ → ℂ[X]) (U₀ V₀ : ℂ[X])
    (d : ℕ) (ε : ℝ) (hε : ε ≤ 1)
    (hA : TendstoUniformlyOn (fun n z => (A n).eval z) (fun _ => 0)
      atTop (Metric.closedBall (0 : ℂ) ε))
    (hB : TendstoUniformlyOn (fun n z => (B n).eval z) (fun _ => 0)
      atTop (Metric.closedBall (0 : ℂ) ε))
    (hdeg : ∀ n, (U n).natDegree ≤ d ∧ (V n).natDegree ≤ d)
    (hdeg₀ : U₀.natDegree ≤ d)
    (hU : ∀ k, Tendsto (fun n => (U n).coeff k) atTop (𝓝 (U₀.coeff k)))
    (hV : ∀ k, Tendsto (fun n => (V n).coeff k) atTop (𝓝 (V₀.coeff k))) :
    TendstoUniformlyOn
      (fun n z => (spectralPolynomialResidual h (ν n) η (A n) (B n) (U n) (V n)).eval z)
      (fun z => (spectralLinearResidual h ν₀ η U₀).eval z)
      atTop (Metric.closedBall (0 : ℂ) ε) := by
  have hL := radialPolynomial_eval_tendstoUniformly
    (fun n => spectralLinearResidual h (ν n) η (U n)) (spectralLinearResidual h ν₀ η U₀) d
    (Eventually.of_forall (fun n => spectralLinearResidual_degree _ _ _ _ d (hdeg n).1))
    (spectralLinearResidual_degree _ _ _ _ d hdeg₀)
    (fun k _ => spectralLinearResidual_coefficient_limit h η ν ν₀ hν U U₀ hU k)
  have hL' := hL.mono (show Metric.closedBall (0 : ℂ) ε ⊆ Metric.closedBall 0 1 from
    fun z hz => Metric.mem_closedBall.mpr ((Metric.mem_closedBall.mp hz).trans hε))
  have hAU := spectralPolynomial_mul_uniform_zero A U U₀ d ε hε hA
    (Eventually.of_forall (fun n => (hdeg n).1)) (fun k _ => hU k)
  have hBV := spectralPolynomial_mul_uniform_zero B V V₀ d ε hε hB
    (Eventually.of_forall (fun n => (hdeg n).2)) (fun k _ => hV k)
  have he (n : ℕ) : spectralPolynomialResidual h (ν n) η (A n) (B n) (U n) (V n)=
      spectralLinearResidual h (ν n) η (U n)-A n*U n-B n*V n := by
    simp only [spectralLinearResidual,spectralPolynomialResidual,zero_mul,sub_zero]
  have ht := (hL'.sub hAU).sub hBV
  change TendstoUniformlyOn
    (fun n z => (spectralLinearResidual h (ν n) η (U n)).eval z-
      (A n*U n).eval z-(B n*V n).eval z)
    (fun z => (spectralLinearResidual h ν₀ η U₀).eval z-0-0)
    atTop (Metric.closedBall (0 : ℂ) ε) at ht
  simpa only [he,eval_sub,sub_zero] using ht

theorem spectralOutgoing_normalized_residual_limit
    (νp νm : ℕ → ℂ) (νp₀ νm₀ η : ℂ)
    (hp : Tendsto νp atTop (𝓝 νp₀)) (hm : Tendsto νm atTop (𝓝 νm₀))
    (P : ℕ → ℂ[X]) (Q : ℂ[X]) (d : ℕ)
    (hdeg : ∀ᶠ n in atTop, (P n).natDegree ≤ d)
    (hP : ∀ k, k ≤ d → Tendsto (fun n => (P n).coeff k) atTop (𝓝 (Q.coeff k)))
    (hzero : ‖Q.coeff 0‖ < 1) (c : ℂ × ℂ) (j : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ R : ℕ → ℂ[X] × ℂ[X], ∃ R₀ : ℂ[X] × ℂ[X],
      (∀ n,
        (spectralPolynomialResidualPair (νp n) (νm n) η n (P n)
          (spectralOutgoingPolynomial (νp n) (νm n) η n (P n) c j)).1=X^j*(R n).1 ∧
        (spectralPolynomialResidualPair (νp n) (νm n) η n (P n)
          (spectralOutgoingPolynomial (νp n) (νm n) η n (P n) c j)).2=X^j*(R n).2) ∧
      (spectralPolynomialResidualPair νp₀ νm₀ η 1 0
        (spectralOutgoingPolynomial νp₀ νm₀ η 1 0 c j)).1=X^j*R₀.1 ∧
      (spectralPolynomialResidualPair νp₀ νm₀ η 1 0
        (spectralOutgoingPolynomial νp₀ νm₀ η 1 0 c j)).2=X^j*R₀.2 ∧
      TendstoUniformlyOn (fun n z => ((R n).1).eval z) (fun z => R₀.1.eval z)
        atTop (Metric.closedBall (0 : ℂ) ε) ∧
      TendstoUniformlyOn (fun n z => ((R n).2).eval z) (fun z => R₀.2.eval z)
        atTop (Metric.closedBall (0 : ℂ) ε) := by
  classical
  obtain ⟨ε,hε,hε1,hA,hB⟩ := spectralPolynomial_subunit_uniform_limit P Q d hdeg hP hzero
  let U := fun n => spectralOutgoingPolynomial (νp n) (νm n) η n (P n) c j
  let U₀ := spectralOutgoingPolynomial νp₀ νm₀ η 1 0 c j
  have hU := spectralOutgoingPolynomial_coefficient_limit νp νm νp₀ νm₀ η hp hm P Q d hdeg hP hzero c j
  have hUp := spectralPolynomialResidual_uniform_limit 1 η νp νp₀ hp
    (fun n => spectralDiagonalPolynomial n (P n)) (fun n => spectralCrossPolynomial n (P n))
    (fun n => (U n).1) (fun n => (U n).2) U₀.1 U₀.2 j ε hε1 hA hB
    (fun n => spectralOutgoingPolynomial_degree _ _ _ _ _ _ _)
    (spectralOutgoingPolynomial_degree _ _ _ _ _ _ _).1 (fun k => (hU k).1) (fun k => (hU k).2)
  have hUm := spectralPolynomialResidual_uniform_limit (-1) η νm νm₀ hm
    (fun n => Polynomial.mapRingHom (starRingEnd ℂ) (spectralDiagonalPolynomial n (P n)))
    (fun n => Polynomial.mapRingHom (starRingEnd ℂ) (spectralCrossPolynomial n (P n)))
    (fun n => (U n).2) (fun n => (U n).1) U₀.2 U₀.1 j ε hε1
    (spectralPolynomial_star_uniform_zero _ ε hA) (spectralPolynomial_star_uniform_zero _ ε hB)
    (fun n => ⟨(spectralOutgoingPolynomial_degree _ _ _ _ _ _ _).2,
      (spectralOutgoingPolynomial_degree _ _ _ _ _ _ _).1⟩)
    (spectralOutgoingPolynomial_degree _ _ _ _ _ _ _).2 (fun k => (hU k).2) (fun k => (hU k).1)
  have hd (n : ℕ) : ∃ R : ℂ[X] × ℂ[X],
      (spectralPolynomialResidualPair (νp n) (νm n) η n (P n) (U n)).1=X^j*R.1 ∧
      (spectralPolynomialResidualPair (νp n) (νm n) η n (P n) (U n)).2=X^j*R.2 := by
    obtain ⟨⟨R₁,h₁⟩,⟨R₂,h₂⟩⟩ := spectralOutgoingPolynomial_residual (νp n) (νm n) η n (P n) c j
    exact ⟨(R₁,R₂),h₁,h₂⟩
  choose R hR using hd
  obtain ⟨⟨R₁,h₁⟩,⟨R₂,h₂⟩⟩ := spectralOutgoingPolynomial_residual νp₀ νm₀ η 1 0 c j
  have hp0 : (spectralPolynomialResidualPair νp₀ νm₀ η 1 0 U₀).1=
      spectralLinearResidual 1 νp₀ η U₀.1 := by
    simp [spectralPolynomialResidualPair,spectralDiagonalPolynomial,spectralCrossPolynomial,
      spectralLinearResidual,spectralPolynomialResidual]
  have hm0 : (spectralPolynomialResidualPair νp₀ νm₀ η 1 0 U₀).2=
      spectralLinearResidual (-1) νm₀ η U₀.2 := by
    simp [spectralPolynomialResidualPair,spectralDiagonalPolynomial,spectralCrossPolynomial,
      spectralLinearResidual,spectralPolynomialResidual]
  have h₁' : spectralLinearResidual 1 νp₀ η U₀.1=X^j*R₁ := hp0.symm.trans h₁
  have h₂' : spectralLinearResidual (-1) νm₀ η U₀.2=X^j*R₂ := hm0.symm.trans h₂
  refine ⟨ε,hε,hε1,R,(R₁,R₂),hR,h₁,h₂,?_,?_⟩
  · apply radialPolynomial_quotient_uniform_limit
      (fun n => (spectralPolynomialResidualPair (νp n) (νm n) η n (P n) (U n)).1)
      (fun n => (R n).1) (spectralLinearResidual 1 νp₀ η U₀.1) R₁ j ε hε
      (fun n => (hR n).1) h₁'
    exact hUp
  · apply radialPolynomial_quotient_uniform_limit
      (fun n => (spectralPolynomialResidualPair (νp n) (νm n) η n (P n) (U n)).2)
      (fun n => (R n).2) (spectralLinearResidual (-1) νm₀ η U₀.2) R₂ j ε hε
      (fun n => (hR n).2) h₂'
    exact hUm

end DefocusingNLS

end OAI
