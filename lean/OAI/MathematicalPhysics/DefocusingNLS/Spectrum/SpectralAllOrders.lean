import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralExpansionUniqueness
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralOutgoingExistence

namespace OAI

/-! One exact outgoing solution realizes every sufficiently accurate profile expansion. -/

open Polynomial Filter
open scoped BoundedContinuousFunction
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem exists_circular_allOrders (ν νp νm η b : ℂ) (n : ℕ) (hn : 1 ≤ n)
    (c : ℂ × ℂ) (q : ℝ →ᵇ ℂ)
    (hP : ∀ J : ℕ, ∃ j : ℕ, J ≤ j ∧ ∃ e : ℝ →ᵇ ℂ, ∀ t, 0 ≤ t →
      q t-radialExteriorPolynomialFunction (radialExteriorExpansion ν n b j) t=
        (Real.exp (-(2*(j : ℝ))*t) : ℂ)*e t) :
    ∃ Y : ℝ → E₄,
      (∀ t, 0 ≤ t → HasDerivAt Y
        (circularLeadingField t (Y t)+circularBoundedField νp νm η n (q t) (Y t)) t) ∧
      Tendsto Y atTop (nhds ((c.1,0),(c.2,0))) ∧
      ∀ J : ℕ, ∃ j : ℕ, J ≤ j ∧ ∃ v : CircularTailSpace, ∀ t, 0 ≤ t →
        Y t=circularPolynomialJet (spectralOutgoingPolynomial νp νm η n
          (radialExteriorExpansion ν n b j) c j) t+circularUnweight (2*(j : ℝ)) v t := by
  let C := circularFieldBound νp νm η n ‖q‖
  obtain ⟨N,hN⟩ := exists_nat_gt (C+1)
  have hgap (j : ℕ) (hj : N ≤ j) : C < 2*(j : ℝ) := by
    have hj' : (N : ℝ) ≤ j := by exact_mod_cast hj
    have hpos : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  obtain ⟨j₀,hNj₀,e₀,he₀⟩ := hP N
  let P₀ := radialExteriorExpansion ν n b j₀
  let U₀ := spectralOutgoingPolynomial νp νm η n P₀ c j₀
  obtain ⟨v₀,hv₀⟩ := exists_circular_outgoing_expansion νp νm η n hn P₀ c j₀ ‖q‖ q
    q.continuous q.norm_coe_le_norm (hgap j₀ hNj₀) e₀ he₀
  let Y₀ := fun t => circularPolynomialJet U₀ t+circularUnweight (2*(j₀ : ℝ)) v₀ t
  have hlim : Tendsto Y₀ atTop (nhds ((c.1,0),(c.2,0))) := by
    have hjpos : 0 < 2*(j₀ : ℝ) := lt_of_le_of_lt
      (circularFieldBound_nonneg νp νm η n ‖q‖) (hgap j₀ hNj₀)
    have hl := (circularPolynomialJet_tendsto U₀).add
      (circularUnweight_tendsto (2*(j₀ : ℝ)) hjpos v₀)
    have hc := spectralOutgoingPolynomial_constant νp νm η n P₀ c j₀
    simpa only [Y₀,U₀,hc.1,hc.2,add_zero] using hl
  refine ⟨Y₀,hv₀,hlim,?_⟩
  intro J
  obtain ⟨j,hj,e,he⟩ := hP (max J j₀)
  have hj₀j : j₀ ≤ j := (le_max_right _ _).trans hj
  have hNj : N ≤ j := hNj₀.trans hj₀j
  let P := radialExteriorExpansion ν n b j
  let U := spectralOutgoingPolynomial νp νm η n P c j
  obtain ⟨v,hv⟩ := exists_circular_outgoing_expansion νp νm η n hn P c j ‖q‖ q
    q.continuous q.norm_coe_le_norm (hgap j hNj) e he
  let Y := fun t => circularPolynomialJet U t+circularUnweight (2*(j : ℝ)) v t
  have hsame := circular_outgoing_orders_unique ν νp νm η b n hn c j₀ j hj₀j v₀ v
    ‖q‖ 0 q Y₀ Y (fun t _ => q.norm_coe_le_norm t) hv₀ hv
    (fun _ _ => rfl) (fun _ _ => rfl) (hgap j₀ hNj₀)
  refine ⟨j,(le_max_left _ _).trans hj,v,?_⟩
  intro t ht
  exact hsame t (by simpa only [max_self] using ht)

end DefocusingNLS

end OAI
