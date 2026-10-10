import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousOutgoingRobin

namespace OAI

/-! # Robin and derivative-row estimates for the canonical outgoing columns

Both estimates follow from the already constructed all-order expansions.
The physical powers cancel between the value matrix and its inverse.
-/

open Set Filter Topology

namespace DefocusingNLS

local notation "V" => ℂ × ℂ
local notation "V₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem homogeneous_canonical_outgoing_log_estimates
    (ν νp νm eta b : ℂ) (m : ℕ) (L : ℝ)
    (hX : HasRadialExterior ν m b L) (hν : νp.re = νm.re)
    (Yp Ym : ℝ → V₄)
    (hYp : ∀ t, 0 ≤ t → HasDerivAt Yp (circularLeadingField t (Yp t) +
      circularBoundedField νp νm eta m (radialExteriorCanonical ν m b L t).1 (Yp t)) t)
    (hYm : ∀ t, 0 ≤ t → HasDerivAt Ym (circularLeadingField t (Ym t) +
      circularBoundedField νp νm eta m (radialExteriorCanonical ν m b L t).1 (Ym t)) t)
    (hplim : Tendsto Yp atTop (𝓝 (((1 : ℂ), 0), (0, 0))))
    (hmlim : Tendsto Ym atTop (𝓝 (((0 : ℂ), 0), (1, 0))))
    (hpall : ∀ J : ℕ, ∃ j : ℕ, J ≤ j ∧ ∃ v : CircularTailSpace, ∀ t, 0 ≤ t →
      Yp t = circularPolynomialJet
        (spectralOutgoingPolynomial νp νm eta m (radialExteriorExpansion ν m b j) (1, 0) j) t +
          circularUnweight (2 * (j : ℝ)) v t)
    (hmall : ∀ J : ℕ, ∃ j : ℕ, J ≤ j ∧ ∃ v : CircularTailSpace, ∀ t, 0 ≤ t →
      Ym t = circularPolynomialJet
        (spectralOutgoingPolynomial νp νm eta m (radialExteriorExpansion ν m b j) (0, 1) j) t +
          circularUnweight (2 * (j : ℝ)) v t) :
    let Fp := homogeneousPhysicalLogColumn νp νm (fun t => (Yp t).1.1) (fun t => (Yp t).2.1)
    let Fm := homogeneousPhysicalLogColumn νp νm (fun t => (Ym t).1.1) (fun t => (Ym t).2.1)
    let Dp := homogeneousPhysicalLogDerivativeColumn νp νm
      (fun t => (Yp t).1.1) (fun t => (Yp t).2.1)
    let Dm := homogeneousPhysicalLogDerivativeColumn νp νm
      (fun t => (Ym t).1.1) (fun t => (Ym t).2.1)
    (∀ N : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ t in atTop,
      spectralValueDet (Fp t) (Fm t) ≠ 0 ∧
      ‖spectralTwoColumns (homogeneousEulerDeriv Fp N t) (homogeneousEulerDeriv Fm N t) *
        spectralValueInverse (Fp t) (Fm t)‖ ≤ K) ∧
    (∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ t in atTop,
      ‖spectralRobinOperator (Fp t) (Fm t) (Dp t) (Dm t) -
        homogeneousDiagonal νp νm‖ ≤ M * Real.exp (-2 * t)) := by
  intro Fp Fm Dp Dm
  obtain ⟨hfp, hgp⟩ := homogeneous_canonical_circular_value_logJets
    ν νp νm eta b m L hX Yp (1, 0) hYp hplim hpall
  obtain ⟨hfm, hgm⟩ := homogeneous_canonical_circular_value_logJets
    ν νp νm eta b m L hX Ym (0, 1) hYm hmlim hmall
  have hp : Tendsto (fun t => ((Yp t).1.1, (Yp t).2.1)) atTop (𝓝 (1, 0)) :=
    hplim.fst_nhds.fst_nhds.prodMk_nhds hplim.snd_nhds.fst_nhds
  have hm : Tendsto (fun t => ((Ym t).1.1, (Ym t).2.1)) atTop (𝓝 (0, 1)) :=
    hmlim.fst_nhds.fst_nhds.prodMk_nhds hmlim.snd_nhds.fst_nhds
  constructor
  · intro N
    exact homogeneousOutgoingDerivativeRows_bound νp νm hν
      _ _ _ _ hfp hgp hfm hgm hp hm N
  · obtain ⟨hdp, hdp'⟩ := homogeneous_canonical_circular_positive_derivatives
      ν νp νm eta b m L hX Yp (1, 0) hYp hplim hpall
    obtain ⟨hdm, hdm'⟩ := homogeneous_canonical_circular_positive_derivatives
      ν νp νm eta b m L hX Ym (0, 1) hYm hmlim hmall
    apply homogeneousOutgoingRobin_error νp νm hν _ _ _ _ hp hm
    · simpa only [iteratedDeriv_one] using hdp 1 zero_lt_one
    · simpa only [iteratedDeriv_one] using hdp' 1 zero_lt_one
    · simpa only [iteratedDeriv_one] using hdm 1 zero_lt_one
    · simpa only [iteratedDeriv_one] using hdm' 1 zero_lt_one

end DefocusingNLS

end OAI
