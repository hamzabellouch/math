import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralAllOrders
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHolomorphicAllOrders
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.ContinuousHalfLineBound
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorAllOrders

namespace OAI

/-! Applying the all-order slow-column construction to the canonical nonlinear profile. -/

open Polynomial Filter Set
open scoped BoundedContinuousFunction
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem canonical_circular_expansion_data (ν b : ℂ) (n : ℕ) (L : ℝ)
    (hX : HasRadialExterior ν n b L) (hb : b ≠ 0) :
    ∃ q : ℝ →ᵇ ℂ,
      (∀ t, 0 ≤ t → q t=(radialExteriorCanonical ν n b L t).1) ∧
      ∀ J : ℕ, ∃ j : ℕ, J ≤ j ∧ ∃ e : ℝ →ᵇ ℂ, ∀ t, 0 ≤ t →
        q t-radialExteriorPolynomialFunction (radialExteriorExpansion ν n b j) t=
          (Real.exp (-(2*(j : ℝ))*t) : ℂ)*e t := by
  obtain ⟨hqcont,hqexp,_⟩ := radialExteriorCanonical_spec hX
  obtain ⟨q,hq⟩ := continuous_tendsto_halfLine_bounded
    (fun t => (radialExteriorCanonical ν n b L t).1) hqcont.fst b hqexp.tendsto.fst_nhds
  refine ⟨q,hq,?_⟩
  intro J
  obtain ⟨j,hJj,v,T,hv⟩ := radialExteriorCanonical_allOrders ν b n L hX hb J
  let P := radialExteriorExpansion ν n b j
  let κ : ℝ := 2*(j : ℝ)
  let f : ℝ → ℂ := fun t => (Real.exp (κ*t) : ℂ)*
    (q t-radialExteriorPolynomialFunction P t)
  have hf : Continuous f := by
    dsimp [f,radialExteriorPolynomialFunction]
    fun_prop
  have hef : ∀ᶠ t in atTop, ‖f t‖ ≤ ‖v‖ := by
    filter_upwards [eventually_ge_atTop (max T 0)] with t ht
    have htT : T ≤ t := (le_max_left _ _).trans ht
    have ht0 : 0 ≤ t := (le_max_right _ _).trans ht
    have he := congrArg Prod.fst (hv t htT)
    simp only [radialPolynomialJet,Prod.fst_add,radialExteriorUnweight,
      Prod.smul_fst,Complex.real_smul] at he
    have hexp : (Real.exp (κ*t) : ℂ)*(Real.exp (-κ*t) : ℂ)=1 := by
      rw [← Complex.ofReal_mul,← Real.exp_add]
      simp
    have heq : f t=(v t).1 := by
      dsimp [f]
      rw [hq t ht0,he]
      change (Real.exp (κ*t) : ℂ)*
        ((radialExteriorPolynomialFunction P t+(Real.exp (-κ*t) : ℂ)*(v t).1)-
          radialExteriorPolynomialFunction P t)=(v t).1
      rw [add_sub_cancel_left,← mul_assoc,hexp,one_mul]
    rw [heq]
    exact (norm_fst_le (v t)).trans (v.norm_coe_le_norm t)
  obtain ⟨e,he⟩ := exists_bounded_extension_nonneg f hf ⟨‖v‖,hef⟩
  refine ⟨j,hJj,e,?_⟩
  intro t ht
  rw [he t ht]
  change q t-radialExteriorPolynomialFunction P t=
    (Real.exp (-κ*t) : ℂ)*((Real.exp (κ*t) : ℂ)*
      (q t-radialExteriorPolynomialFunction P t))
  have hexp : (Real.exp (-κ*t) : ℂ)*(Real.exp (κ*t) : ℂ)=1 := by
    rw [← Complex.ofReal_mul,← Real.exp_add]
    simp
  rw [← mul_assoc,hexp,one_mul]

theorem canonical_circular_allOrders (ν νp νm η b : ℂ) (n : ℕ) (hn : 1 ≤ n)
    (L : ℝ) (hX : HasRadialExterior ν n b L) (hb : b ≠ 0) (c : ℂ × ℂ) :
    ∃ Y : ℝ → E₄,
      (∀ t, 0 ≤ t → HasDerivAt Y
        (circularLeadingField t (Y t)+
          circularBoundedField νp νm η n (radialExteriorCanonical ν n b L t).1 (Y t)) t) ∧
      Tendsto Y atTop (nhds ((c.1,0),(c.2,0))) ∧
      ∀ J : ℕ, ∃ j : ℕ, J ≤ j ∧ ∃ v : CircularTailSpace, ∀ t, 0 ≤ t →
        Y t=circularPolynomialJet (spectralOutgoingPolynomial νp νm η n
          (radialExteriorExpansion ν n b j) c j) t+circularUnweight (2*(j : ℝ)) v t := by
  obtain ⟨q,hq,hP⟩ := canonical_circular_expansion_data ν b n L hX hb
  obtain ⟨Y,hY,hlim,he⟩ := exists_circular_allOrders ν νp νm η b n hn c q hP
  refine ⟨Y,?_,hlim,he⟩
  intro t ht
  simpa only [hq t ht] using hY t ht

theorem canonical_circular_outgoing (ν νp νm η b : ℂ) (n : ℕ) (hn : 1 ≤ n)
    (L : ℝ) (hX : HasRadialExterior ν n b L) (hb : b ≠ 0) (c : ℂ × ℂ) :
    ∃ Y : ℝ → E₄,
      (∀ t, 0 ≤ t → HasDerivAt Y
        (circularLeadingField t (Y t)+
          circularBoundedField νp νm η n (radialExteriorCanonical ν n b L t).1 (Y t)) t) ∧
      Tendsto Y atTop (nhds ((c.1,0),(c.2,0))) := by
  obtain ⟨Y,hY,hlim,_⟩ := canonical_circular_allOrders ν νp νm η b n hn L hX hb c
  exact ⟨Y,hY,hlim⟩

theorem canonical_holomorphic_circular_allOrders (ν νp νm η b : ℂ)
    (n : ℕ) (hn : 1 ≤ n) (L : ℝ) (hX : HasRadialExterior ν n b L) (hb : b ≠ 0)
    (c : ℂ × ℂ) :
    ∃ Y : ℂ → ℝ → E₄,
      (∀ lam t, 0 ≤ t → HasDerivAt (Y lam)
        (circularLeadingField t (Y lam t)+circularBoundedField (νp-2*lam) (νm-2*lam) η n
          (radialExteriorCanonical ν n b L t).1 (Y lam t)) t) ∧
      (∀ lam, Tendsto (Y lam) atTop (nhds ((c.1,0),(c.2,0)))) ∧
      (∀ z t, 0 ≤ t → AnalyticAt ℂ (fun lam => Y lam t) z) ∧
      (∀ lam J, ∃ j : ℕ, J ≤ j ∧ ∃ v : CircularTailSpace, ∀ t, 0 ≤ t →
        Y lam t=circularPolynomialJet
          (spectralOutgoingPolynomial (νp-2*lam) (νm-2*lam) η n
            (radialExteriorExpansion ν n b j) c j) t+circularUnweight (2*(j : ℝ)) v t) := by
  obtain ⟨q,hq,hP⟩ := canonical_circular_expansion_data ν b n L hX hb
  obtain ⟨Y,hY,hlim,ha,he⟩ := exists_holomorphic_circular_allOrders ν νp νm η b n hn c q hP
  refine ⟨Y,?_,hlim,ha,he⟩
  intro lam t ht
  simpa only [hq t ht] using hY lam t ht

end DefocusingNLS

end OAI
