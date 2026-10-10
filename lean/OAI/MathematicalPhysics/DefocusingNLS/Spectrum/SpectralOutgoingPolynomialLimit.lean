import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPolynomialCoefficientLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPolynomialAnalytic

namespace OAI

/-! The finite normalized outgoing expansions converge to the decoupled
free expansions. No convergence of regular columns through the core is used. -/

open Polynomial Filter Topology
namespace DefocusingNLS

theorem spectralPolynomial_mul_zero_coefficient_limit (A U : ℕ → ℂ[X]) (U₀ : ℂ[X])
    (hA : ∀ k, Tendsto (fun n => (A n).coeff k) atTop (𝓝 0))
    (hU : ∀ k, Tendsto (fun n => (U n).coeff k) atTop (𝓝 (U₀.coeff k))) (k : ℕ) :
    Tendsto (fun n => (A n*U n).coeff k) atTop (𝓝 0) := by
  simp only [Polynomial.coeff_mul]
  simpa only [zero_mul,Finset.sum_const_zero] using
    (tendsto_finsetSum (Finset.HasAntidiagonal.antidiagonal k) (fun i _ => (hA i.1).mul (hU i.2)))

theorem spectralPolynomialResidual_zero_coefficient_limit
    (h η : ℂ) (ν : ℕ → ℂ) (ν₀ : ℂ) (hν : Tendsto ν atTop (𝓝 ν₀))
    (A B U V : ℕ → ℂ[X]) (U₀ V₀ : ℂ[X])
    (hA : ∀ k, Tendsto (fun n => (A n).coeff k) atTop (𝓝 0))
    (hB : ∀ k, Tendsto (fun n => (B n).coeff k) atTop (𝓝 0))
    (hU : ∀ k, Tendsto (fun n => (U n).coeff k) atTop (𝓝 (U₀.coeff k)))
    (hV : ∀ k, Tendsto (fun n => (V n).coeff k) atTop (𝓝 (V₀.coeff k))) (k : ℕ) :
    Tendsto (fun n => (spectralPolynomialResidual h (ν n) η (A n) (B n) (U n) (V n)).coeff k)
      atTop (𝓝 ((spectralPolynomialResidual h ν₀ η 0 0 U₀ V₀).coeff k)) := by
  have hAU := spectralPolynomial_mul_zero_coefficient_limit A U U₀ hA hU k
  have hBV := spectralPolynomial_mul_zero_coefficient_limit B V V₀ hB hV k
  have h₁ := ((hU k).const_mul (-2*(k : ℂ))).const_mul (-2*(k : ℂ))
  have h₂ := ((hν.const_mul 2).add_const 10).mul ((hU k).const_mul (-2*(k : ℂ)))
  have h₃ := ((hν.mul (hν.add_const 10)).sub_const η).mul (hU k)
  have h₄ := ((hU (k+1)).mul_const ((k+1 : ℕ) : ℂ)).const_mul (h*Complex.I)
  have ht := (((h₁.add h₂).add h₃).sub h₄ |>.sub hAU).sub hBV
  simpa only [spectralPolynomialResidual,coeff_sub,coeff_add,coeff_C_mul,
    radialPolynomialEuler_coeff,coeff_derivative,zero_mul,sub_zero,
    Nat.cast_add,Nat.cast_one] using ht

theorem spectralStarPolynomial_zero_coefficient_limit (A : ℕ → ℂ[X])
    (hA : ∀ k, Tendsto (fun n => (A n).coeff k) atTop (𝓝 0)) (k : ℕ) :
    Tendsto (fun n => (Polynomial.mapRingHom (starRingEnd ℂ) (A n)).coeff k)
      atTop (𝓝 0) := by
  simpa only [Polynomial.coe_mapRingHom,Polynomial.coeff_map,starRingEnd_apply,star_zero,Function.comp_def] using
    (continuous_star.continuousAt.tendsto.comp (hA k))

theorem spectralOutgoingPolynomial_coefficient_limit
    (νp νm : ℕ → ℂ) (νp₀ νm₀ η : ℂ)
    (hp : Tendsto νp atTop (𝓝 νp₀)) (hm : Tendsto νm atTop (𝓝 νm₀))
    (P : ℕ → ℂ[X]) (Q : ℂ[X]) (d : ℕ)
    (hdeg : ∀ᶠ n in atTop, (P n).natDegree ≤ d)
    (hP : ∀ k, k ≤ d → Tendsto (fun n => (P n).coeff k) atTop (𝓝 (Q.coeff k)))
    (hzero : ‖Q.coeff 0‖ < 1) (c : ℂ × ℂ) (j k : ℕ) :
    Tendsto (fun n => (spectralOutgoingPolynomial (νp n) (νm n) η n (P n) c j).1.coeff k)
      atTop (𝓝 ((spectralOutgoingPolynomial νp₀ νm₀ η 1 0 c j).1.coeff k)) ∧
    Tendsto (fun n => (spectralOutgoingPolynomial (νp n) (νm n) η n (P n) c j).2.coeff k)
      atTop (𝓝 ((spectralOutgoingPolynomial νp₀ νm₀ η 1 0 c j).2.coeff k)) := by
  have hA := fun k => (spectralPolynomial_coefficient_limit P Q d k hdeg hP hzero).1
  have hB := fun k => (spectralPolynomial_coefficient_limit P Q d k hdeg hP hzero).2
  induction j generalizing k with
  | zero => exact ⟨tendsto_const_nhds,tendsto_const_nhds⟩
  | succ j ih =>
    let Up := fun n => (spectralOutgoingPolynomial (νp n) (νm n) η n (P n) c j).1
    let Um := fun n => (spectralOutgoingPolynomial (νp n) (νm n) η n (P n) c j).2
    let Vp := (spectralOutgoingPolynomial νp₀ νm₀ η 1 0 c j).1
    let Vm := (spectralOutgoingPolynomial νp₀ νm₀ η 1 0 c j).2
    have hRp := spectralPolynomialResidual_zero_coefficient_limit 1 η νp νp₀ hp
      (fun n => spectralDiagonalPolynomial n (P n)) (fun n => spectralCrossPolynomial n (P n))
      Up Um Vp Vm hA hB (fun k => (ih k).1) (fun k => (ih k).2) j
    have hRm := spectralPolynomialResidual_zero_coefficient_limit (-1) η νm νm₀ hm
      (fun n => Polynomial.mapRingHom (starRingEnd ℂ) (spectralDiagonalPolynomial n (P n)))
      (fun n => Polynomial.mapRingHom (starRingEnd ℂ) (spectralCrossPolynomial n (P n)))
      Um Up Vm Vp (spectralStarPolynomial_zero_coefficient_limit _ hA)
      (spectralStarPolynomial_zero_coefficient_limit _ hB) (fun k => (ih k).2) (fun k => (ih k).1) j
    constructor
    · simp only [spectralOutgoingPolynomial,coeff_add,coeff_monomial]
      by_cases he : j+1=k
      · simp only [he,ite_true]
        have hd := (ih k).1.add (hRp.div_const (Complex.I*(j+1 : ℕ)))
        simpa only [he,Up,Um,Vp,Vm,spectralPolynomialResidualPair,
          spectralDiagonalPolynomial,spectralCrossPolynomial,zero_pow (by decide : 1 ≠ 0),
          zero_pow (by decide : 2 ≠ 0),one_pow,mul_zero,zero_mul,map_zero] using hd
      · simp only [he,ite_false,add_zero]
        exact (ih k).1
    · simp only [spectralOutgoingPolynomial,coeff_add,coeff_monomial]
      by_cases he : j+1=k
      · simp only [he,ite_true]
        have hd := (ih k).2.add (hRm.div_const (-Complex.I*(j+1 : ℕ)))
        simpa only [he,Up,Um,Vp,Vm,spectralPolynomialResidualPair,
          spectralDiagonalPolynomial,spectralCrossPolynomial,zero_pow (by decide : 1 ≠ 0),
          zero_pow (by decide : 2 ≠ 0),one_pow,mul_zero,zero_mul,map_zero] using hd
      · simp only [he,ite_false,add_zero]
        exact (ih k).2

end DefocusingNLS

end OAI
