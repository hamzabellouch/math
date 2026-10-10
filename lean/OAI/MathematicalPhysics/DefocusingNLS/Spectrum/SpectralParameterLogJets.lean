import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralParameterSmoothness
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralParameterApproximation
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousOutgoingLogJets

namespace OAI

/-! The parameter derivative has bounded normalized spatial jets of every order. -/

open Set Filter Topology Polynomial
open scoped ContDiff
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem circularPointSlope_shift (νp νm z : ℂ) :
    circularPointSlopeCLM νp νm z=circularPointSlopeCLM (νp-2*z) (νm-2*z) 0 := by
  apply ContinuousLinearMap.ext
  intro v
  change ((0,4*v.1.2+(4*(νp-2*z)+20)*v.1.1),
      (0,4*v.2.2+(4*(νm-2*z)+20)*v.2.1))=_
  simp only [circularPointSlopeCLM,LinearMap.coe_toContinuousLinearMap',
    LinearMap.coe_mk,AddHom.coe_mk,mul_zero,sub_zero]

theorem spectralParameter_positive_derivatives
    (ν νp νm eta : ℂ) (m : ℕ) (q : ℝ → ℂ × ℂ) (Y Z : ℝ → E₄)
    (L U M : ℝ) (hM : 0 ≤ M)
    (hq : ∀ t, L<t → HasDerivAt q (radialExteriorODEField ν m t (q t)) t)
    (hY : ∀ t, L<t → HasDerivAt Y (circularLeadingField t (Y t)+
      circularBoundedField νp νm eta m (q t).1 (Y t)) t)
    (hZ : ∀ t, L<t → HasDerivAt Z (circularLeadingField t (Z t)+
      circularBoundedField νp νm eta m (q t).1 (Z t)+circularPointSlopeCLM νp νm 0 (Y t)) t)
    (hbq : ∀ t, U≤t → ‖q t‖≤M) (hbY : ∀ t, U≤t → ‖Y t‖≤M)
    (hbZ : ∀ t, U≤t → ‖Z t‖≤M) (P : ℕ → ℂ[X] × ℂ[X])
    (happrox : ∀ J : ℕ, ∃ A T : ℝ, 0≤A ∧ ∀ t, T≤t →
      ‖(Z t).1.1-radialExteriorPolynomialFunction (P J).1 t‖≤A*Real.exp (-(2*(J : ℝ))*t) ∧
      ‖(Z t).2.1-radialExteriorPolynomialFunction (P J).2 t‖≤A*Real.exp (-(2*(J : ℝ))*t)) :
    (∀ k : ℕ, 0<k → ∃ A : ℝ, 0≤A ∧ ∀ᶠ t in atTop,
      ‖iteratedDeriv k (fun t => (Z t).1.1) t‖≤A*Real.exp (-2*t)) ∧
    (∀ k : ℕ, 0<k → ∃ A : ℝ, 0≤A ∧ ∀ᶠ t in atTop,
      ‖iteratedDeriv k (fun t => (Z t).2.1) t‖≤A*Real.exp (-2*t)) := by
  have hs := spectralParameter_solution_contDiffOn ν νp νm eta m q Y Z L hq hY hZ
  have hg (i : Fin 10) (k : ℕ) : ∃ C B T : ℝ, 0≤C ∧ 0≤B ∧ ∀ t, T≤t →
      ‖iteratedDeriv k (fun t => spectralParameterState q Y Z t i) t‖≤B*Real.exp (C*t) := by
    obtain ⟨C,B,T,hC,hB,_,hh⟩ := spectralParameter_derivatives_exponential_bound
      ν νp νm eta m q Y Z L U M hM hq hY hZ hbq hbY hbZ i k
    exact ⟨C,B,T,hC,hB,hh⟩
  constructor
  · intro k hk
    apply radial_arbitrary_approximation_positive_derivative_decay
      (fun t => (Z t).1.1) (fun j => (P j).1) L hs.fst.fst _ _ k hk
    · intro j
      simpa only [spectralParameterState_six] using hg 6 j
    · intro J
      obtain ⟨A,T,hA,hAT⟩ := happrox J
      exact ⟨J,le_rfl,A,T,hA,fun t ht => (hAT t ht).1⟩
  · intro k hk
    apply radial_arbitrary_approximation_positive_derivative_decay
      (fun t => (Z t).2.1) (fun j => (P j).2) L hs.snd.fst _ _ k hk
    · intro j
      simpa only [spectralParameterState_eight] using hg 8 j
    · intro J
      obtain ⟨A,T,hA,hAT⟩ := happrox J
      exact ⟨J,le_rfl,A,T,hA,fun t ht => (hAT t ht).2⟩

theorem HasLogJetBound.of_bounded_positive_decay (f : ℝ → ℂ) (L U M : ℝ)
    (hM : 0≤M) (hf : ContDiffOn ℝ ∞ f (Ioi L))
    (hb : ∀ t, U≤t → ‖f t‖≤M)
    (hd : ∀ k : ℕ, 0<k → ∃ A : ℝ, 0≤A ∧ ∀ᶠ t in atTop,
      ‖iteratedDeriv k f t‖≤A*Real.exp (-2*t)) : HasLogJetBound 0 f := by
  refine ⟨⟨L,hf⟩,?_⟩
  intro k
  cases k with
  | zero =>
      refine ⟨M,hM,?_⟩
      filter_upwards [eventually_ge_atTop U] with t ht
      simpa only [iteratedDeriv_zero,zero_mul,Real.exp_zero,mul_one] using hb t ht
  | succ k =>
      obtain ⟨A,hA,hh⟩ := hd (k+1) (by omega)
      refine ⟨A,hA,?_⟩
      filter_upwards [hh,eventually_ge_atTop (0 : ℝ)] with t ht ht₀
      simpa only [zero_mul,Real.exp_zero,mul_one] using ht.trans
        (mul_le_of_le_one_right hA (Real.exp_le_one_iff.mpr (by linarith)))

end DefocusingNLS

end OAI
