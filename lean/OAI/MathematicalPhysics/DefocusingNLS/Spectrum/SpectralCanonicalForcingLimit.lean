import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralForcingLimit
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorBoundedRemainder

namespace OAI

/-! The normalized forcing limit for the actual canonical nonlinear profile
and its finite outgoing spectral columns. -/

open Filter Topology Set Polynomial
open scoped BoundedContinuousFunction
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem exists_canonical_circular_forcing_limit
    (ν m νp νm : ℕ → ℂ) (ν₀ m₀ νp₀ νm₀ η : ℂ)
    (hν : Tendsto ν atTop (𝓝 ν₀)) (hm : Tendsto m atTop (𝓝 m₀))
    (hp : Tendsto νp atTop (𝓝 νp₀)) (hn : Tendsto νm atTop (𝓝 νm₀))
    (δ L : ℝ) (hδ : 0 < δ) (hsmall : ‖m₀‖+2*δ < 1)
    (hX : ∀ᶠ n in atTop, HasRadialExterior (ν n) n (m n) L)
    (j : ℕ) (hj : radialExteriorMatrixBound ν₀ < 2*(j : ℝ)) (c : ℂ × ℂ) :
    let P := fun n => radialExteriorExpansion (ν n) n (m n) j
    let U := fun n => spectralOutgoingPolynomial (νp n) (νm n) η n (P n) c j
    let U₀ := spectralOutgoingPolynomial νp₀ νm₀ η 1 0 c j
    ∃ T ρ : ℝ, 0 ≤ T ∧ L ≤ T ∧ 0 < ρ ∧ ρ < 1 ∧
      ∃ q : ℕ → ℝ →ᵇ ℂ, ∃ f : ℕ → CircularTailSpace, ∃ f₀ : CircularTailSpace,
        (∀ n t, ‖q n t‖ ≤ ρ) ∧ Tendsto f atTop (𝓝 f₀) ∧
        (∀ᶠ n in atTop, ∀ t, T ≤ t →
          q n t=(radialExteriorCanonical (ν n) n (m n) L t).1 ∧
          Real.exp (-(2*(j : ℝ))*t) • circularTailEvaluation (f n) t=
            (circularBoundedField (νp n) (νm n) η n (q n t) (circularPolynomialJet (U n) t)-
              circularBoundedField (νp n) (νm n) η n
                (radialExteriorPolynomialFunction (P n) t) (circularPolynomialJet (U n) t))-
              circularPolynomialResidualJet (νp n) (νm n) η n (P n) (U n) t) ∧
        ∀ t, T ≤ t → Real.exp (-(2*(j : ℝ))*t) • circularTailEvaluation f₀ t=
          -circularPolynomialResidualJet νp₀ νm₀ η 1 0 U₀ t := by
  intro P U U₀
  have hm01 : ‖m₀‖ < 1 := by linarith
  let Q := radialFreeExpansion ν₀ m₀ j
  have hP (k : ℕ) : Tendsto (fun n => (P n).coeff k) atTop (𝓝 (Q.coeff k)) :=
    radialExteriorExpansion_coefficient_limit ν m ν₀ m₀ hν hm hm01 j k
  have hdeg : ∀ᶠ n in atTop, (P n).natDegree ≤ j :=
    Eventually.of_forall (fun n => radialExteriorExpansion_degree _ _ _ _)
  have hQ : ‖Q.coeff 0‖ < 1 := by simpa only [Q,radialFreeExpansion_constant] using hm01
  obtain ⟨T,ρ,C,hT,hLT,hρ,hρ1,hC,q,e,he,hq,hqe⟩ :=
    radialExteriorCanonical_bounded_remainder ν m ν₀ m₀ hν hm δ L hδ hsmall hX j hj
  obtain ⟨S,hS,r,r₀,hr,hres,hres₀⟩ := exists_spectralOutgoing_residual_tail_limit
    νp νm νp₀ νm₀ η hp hn P Q j hdeg (fun k _ => hP k) hQ c j
  let R := max T S
  have hR : 0 ≤ R := hT.trans (le_max_left _ _)
  have hdata : ∀ᶠ n in atTop, 1 ≤ n ∧ ‖e n‖ ≤ C ∧ ∀ t, R ≤ t →
      ‖q n t‖ ≤ ρ ∧ ‖radialExteriorPolynomialFunction (P n) t‖ ≤ ρ ∧
      q n t-radialExteriorPolynomialFunction (P n) t=
        (Real.exp (-(2*(j : ℝ))*t) : ℂ)*e n t := by
    filter_upwards [hqe,eventually_ge_atTop 1] with n hen hn
    exact ⟨hn,he n,fun t ht => ⟨hq n t,(hen t ((le_max_left T S).trans ht)).2⟩⟩
  have hU : Tendsto (fun n => boundedCircularPolynomialJet (U n)) atTop
      (𝓝 (boundedCircularPolynomialJet U₀)) :=
    spectralOutgoing_bounded_jet_tendsto νp νm νp₀ νm₀ η hp hn P Q j hdeg
      (fun k _ => hP k) hQ c j
  obtain ⟨f,hf,hfr⟩ := exists_circular_normalized_forcing_limit
    (fun n => n) tendsto_id (fun n t => q n t)
    (fun n t => radialExteriorPolynomialFunction (P n) t)
    (fun n => (q n).continuous) (fun n => by unfold radialExteriorPolynomialFunction; fun_prop)
    (2*(j : ℝ)) R ρ C hR hρ hρ1 hC e hdata νp νm η U U₀ hU r r₀ hr
  refine ⟨R,ρ,hR,hLT.trans (le_max_left _ _),hρ,hρ1,q,f,r₀,hq,hf,?_,?_⟩
  · filter_upwards [hqe,hfr] with n hqn hfn t ht
    refine ⟨(hqn t ((le_max_left T S).trans ht)).1,?_⟩
    simpa only [hres n t ((le_max_right T S).trans ht),sub_eq_add_neg] using hfn t ht
  · intro t ht
    exact hres₀ t ((le_max_right T S).trans ht)

end DefocusingNLS

end OAI
