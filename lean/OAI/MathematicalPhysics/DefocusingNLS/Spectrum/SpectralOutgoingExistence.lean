import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPolynomialTailData
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPolynomialCorrection

namespace OAI

/-! Exact normalized slow columns for a profile with the required finite expansion. -/

open Filter
open scoped BoundedContinuousFunction
open Polynomial
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem exists_circular_outgoing_expansion (νp νm η : ℂ) (m : ℕ) (hm : 1 ≤ m)
    (P : ℂ[X]) (c : ℂ × ℂ) (j : ℕ) (M : ℝ) (q : ℝ → ℂ)
    (hq : Continuous q) (hqM : ∀ t, ‖q t‖ ≤ M)
    (hj : circularFieldBound νp νm η m M < 2*(j : ℝ)) (e : ℝ →ᵇ ℂ)
    (hqe : ∀ t, 0 ≤ t → q t-radialExteriorPolynomialFunction P t=
      (Real.exp (-(2*(j : ℝ))*t) : ℂ)*e t) :
    ∃ v : CircularTailSpace, ∀ t, 0 ≤ t →
      HasDerivAt (fun s => circularPolynomialJet
        (spectralOutgoingPolynomial νp νm η m P c j) s+circularUnweight (2*(j : ℝ)) v s)
        (circularLeadingField t (circularPolynomialJet
          (spectralOutgoingPolynomial νp νm η m P c j) t+circularUnweight (2*(j : ℝ)) v t)+
          circularBoundedField νp νm η m (q t) (circularPolynomialJet
            (spectralOutgoingPolynomial νp νm η m P c j) t+circularUnweight (2*(j : ℝ)) v t)) t := by
  let U := spectralOutgoingPolynomial νp νm η m P c j
  let Z := boundedCircularPolynomialJet U
  let p := boundedRadialPolynomial P
  have hpM : ∀ t, ‖p t‖ ≤ max M ‖p‖ :=
    fun t => (p.norm_coe_le_norm t).trans (le_max_right _ _)
  have hqM' : ∀ t, ‖q t‖ ≤ max M ‖p‖ :=
    fun t => (hqM t).trans (le_max_left _ _)
  obtain ⟨rE,hrE⟩ := exists_circular_weighted_coefficient_error νp νm η m
    (max M ‖p‖) (2*(j : ℝ)) q p hq p.continuous hqM' hpM e Z (by
      intro t ht
      simpa only [p,boundedRadialPolynomial_nonneg P t ht] using hqe t ht)
  obtain ⟨rR,hrR⟩ := exists_circular_normalized_residual νp νm η m P c j
  have hr : ∀ t, 0 ≤ t →
      Real.exp (-(2*(j : ℝ))*t) • circularTailEvaluation (rE+rR) t=
        (circularBoundedField νp νm η m (q t) (circularPolynomialJet U t)-
          circularBoundedField νp νm η m (radialExteriorPolynomialFunction P t)
            (circularPolynomialJet U t))-circularPolynomialResidualJet νp νm η m P U t := by
    intro t ht
    have he : Real.exp (-(2*(j : ℝ))*t)*Real.exp ((2*(j : ℝ))*t)=1 := by
      rw [← Real.exp_add]
      simp
    have hadd : circularTailEvaluation (rE+rR) t=
        circularTailEvaluation rE t+circularTailEvaluation rR t := rfl
    rw [hadd,smul_add,hrE t ht,smul_smul,he,one_smul,hrR t ht]
    rw [show circularTailEvaluation Z t=circularPolynomialJet U t from
      boundedCircularPolynomialJet_eq U t ht]
    rw [show p t=radialExteriorPolynomialFunction P t from
      boundedRadialPolynomial_nonneg P t ht]
    rfl
  obtain ⟨v,_,hv⟩ := exists_circularPolynomial_solution νp νm η m hm P U M
    (2*(j : ℝ)) 0 q hq hqM hj (rE+rR) hr
  exact ⟨v,hv⟩

theorem exists_circular_outgoing (νp νm η : ℂ) (m : ℕ) (hm : 1 ≤ m)
    (P : ℂ[X]) (c : ℂ × ℂ) (j : ℕ) (M : ℝ) (q : ℝ → ℂ)
    (hq : Continuous q) (hqM : ∀ t, ‖q t‖ ≤ M)
    (hj : circularFieldBound νp νm η m M < 2*(j : ℝ)) (e : ℝ →ᵇ ℂ)
    (hqe : ∀ t, 0 ≤ t → q t-radialExteriorPolynomialFunction P t=
      (Real.exp (-(2*(j : ℝ))*t) : ℂ)*e t) :
    ∃ Y : ℝ → E₄,
      (∀ t, 0 ≤ t → HasDerivAt Y
        (circularLeadingField t (Y t)+circularBoundedField νp νm η m (q t) (Y t)) t) ∧
      Tendsto Y atTop (nhds ((c.1,0),(c.2,0))) := by
  let U := spectralOutgoingPolynomial νp νm η m P c j
  obtain ⟨v,hv⟩ := exists_circular_outgoing_expansion νp νm η m hm P c j M q hq hqM hj e hqe

  refine ⟨fun t => circularPolynomialJet U t+circularUnweight (2*(j : ℝ)) v t,hv,?_⟩
  have hj0 : 0 < 2*(j : ℝ) := lt_of_le_of_lt
    (circularFieldBound_nonneg νp νm η m M) hj
  have hlim := (circularPolynomialJet_tendsto U).add
    (circularUnweight_tendsto (2*(j : ℝ)) hj0 v)
  have hc := spectralOutgoingPolynomial_constant νp νm η m P c j
  simpa only [U,hc.1,hc.2,add_zero] using hlim

end DefocusingNLS

end OAI
