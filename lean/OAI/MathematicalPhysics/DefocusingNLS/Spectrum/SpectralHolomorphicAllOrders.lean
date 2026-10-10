import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHolomorphicOutgoing
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralAllOrders

namespace OAI

/-! Local holomorphy of the single outgoing solution realizing all asymptotic orders. -/

open Filter
open scoped BoundedContinuousFunction
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem exists_holomorphic_circular_allOrders (ν νp νm η b : ℂ) (n : ℕ) (hn : 1 ≤ n)
    (c : ℂ × ℂ) (q : ℝ →ᵇ ℂ)
    (hP : ∀ J : ℕ, ∃ j : ℕ, J ≤ j ∧ ∃ e : ℝ →ᵇ ℂ, ∀ t, 0 ≤ t →
      q t-radialExteriorPolynomialFunction (radialExteriorExpansion ν n b j) t=
        (Real.exp (-(2*(j : ℝ))*t) : ℂ)*e t) :
    ∃ Y : ℂ → ℝ → E₄,
      (∀ lam t, 0 ≤ t → HasDerivAt (Y lam)
        (circularLeadingField t (Y lam t)+
          circularBoundedField (νp-2*lam) (νm-2*lam) η n (q t) (Y lam t)) t) ∧
      (∀ lam, Tendsto (Y lam) atTop (nhds ((c.1,0),(c.2,0)))) ∧
      (∀ z t, 0 ≤ t → AnalyticAt ℂ (fun lam => Y lam t) z) ∧
      (∀ lam J, ∃ j : ℕ, J ≤ j ∧ ∃ v : CircularTailSpace, ∀ t, 0 ≤ t →
        Y lam t=circularPolynomialJet
          (spectralOutgoingPolynomial (νp-2*lam) (νm-2*lam) η n
            (radialExteriorExpansion ν n b j) c j) t+circularUnweight (2*(j : ℝ)) v t) := by
  choose Y hY hlim hE using fun lam =>
    exists_circular_allOrders ν (νp-2*lam) (νm-2*lam) η b n hn c q hP
  refine ⟨Y,hY,hlim,?_,hE⟩
  intro z t ht
  let C := circularFieldBound (νp-2*z) (νm-2*z) η n ‖q‖
  have hC : 0 ≤ C := circularFieldBound_nonneg _ _ _ _ _
  obtain ⟨N,hN⟩ := exists_nat_gt (C+1)
  obtain ⟨j,hNj,e,he⟩ := hP N
  have hNj' : (N : ℝ) ≤ j := by exact_mod_cast hNj
  have hj : 0 < j := by
    have hj' : (0 : ℝ) < j := by linarith
    exact_mod_cast hj'
  have hgap : C < 2*(j : ℝ) := by linarith
  obtain ⟨W,hWa,hWd,_hWlim,hWe⟩ := exists_holomorphic_circular_outgoing
    νp νm η n hn (radialExteriorExpansion ν n b j) c j hj q e he
  apply (hWa z hgap t).congr
  have hcont : Continuous (fun lam : ℂ => circularFieldBound (νp-2*lam) (νm-2*lam) η n ‖q‖) := by
    unfold circularFieldBound
    fun_prop
  have hevent : ∀ᶠ lam in nhds z,
      circularFieldBound (νp-2*lam) (νm-2*lam) η n ‖q‖ < 2*(j : ℝ) :=
    hcont.continuousAt.eventually (gt_mem_nhds hgap)
  filter_upwards [hevent] with lam hlam
  obtain ⟨k,hjk,w,hw⟩ := hE lam j
  obtain ⟨v,hv⟩ := hWe lam
  have hsame := circular_outgoing_orders_unique ν (νp-2*lam) (νm-2*lam) η b n hn
    c j k hjk v w ‖q‖ 0 q (W lam) (Y lam)
    (fun s _ => q.norm_coe_le_norm s) (hWd lam hlam) (hY lam)
    (fun s _ => hv s) hw hlam
  exact hsame t (by simpa only [max_self] using ht)

end DefocusingNLS

end OAI
