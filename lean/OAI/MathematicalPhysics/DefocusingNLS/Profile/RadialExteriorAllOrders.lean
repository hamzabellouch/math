import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorCanonical

namespace OAI

/-! Every truncation order represents the same canonical nonlinear outgoing solution. -/

open Set Filter Polynomial
open scoped BoundedContinuousFunction
namespace DefocusingNLS

theorem radialExteriorCanonical_allOrders (ν m : ℂ) (n : ℕ) (L : ℝ)
    (hX : HasRadialExterior ν n m L) (hm : m ≠ 0) (J : ℕ) :
    ∃ j : ℕ, J ≤ j ∧ ∃ v : ℝ →ᵇ ℂ × ℂ, ∃ T : ℝ, ∀ t, T ≤ t →
      radialExteriorCanonical ν n m L t =
        radialPolynomialJet (radialExteriorExpansion ν n m j) t +
          radialExteriorUnweight (2*(j : ℝ)) v t := by
  let δ := ‖m‖/2
  have hm0 : 0 < ‖m‖ := norm_pos_iff.mpr hm
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨S,_hS,hs,T,_hT,j,hJ,v,_hv,hmargin,_hnear,_hc,_hl,hODE⟩ :=
    exists_radialExterior_local_family_order ν m n δ J hδ (by dsimp [δ]; linarith)
  let z : S := ⟨(ν,m),hs⟩
  let W : ℝ → ℂ × ℂ := fun t =>
    radialPolynomialJet (radialExteriorExpansion ν n m j) t +
      radialExteriorUnweight (2*(j : ℝ)) (v z) t
  have hκ : radialExteriorMatrixBound ν+(2*(n : ℝ)+1)*‖m‖^(2*n) < 2*(j : ℝ) := by
    calc
      _ ≤ radialExteriorMatrixBound ν+(2*(n : ℝ)+1)*(‖m‖+2*δ)^(2*n) := by
        gcongr
        linarith
      _ ≤ radialExteriorMatrixBound ν+radialExteriorCutoffRate n m δ := by
        unfold radialExteriorCutoffRate
        have hpos : 0 ≤ (2*(n : ℝ)+1)*(‖m‖+2*δ)^(2*n) := by positivity
        nlinarith
      _ < _ := hmargin z
  have heW : HasRadialOutgoingExpansion ν n m W := ⟨j,v z,T,hκ,fun _ _ => rfl⟩
  have hdW : ∀ t, max L T ≤ t → HasDerivAt W (radialExteriorODEField ν n t (W t)) t := by
    intro t ht
    exact (hODE z t ((le_max_right L T).trans ht)).2.1.prodMk
      (hODE z t ((le_max_right L T).trans ht)).2.2
  obtain ⟨hcont,heZ,hdZ⟩ := radialExteriorCanonical_spec hX
  have he := radialExterior_outgoing_eventually_eq ν n m
    (radialExteriorCanonical ν n m L) W (max L T)
    (fun t ht => (hdZ t ((le_max_left L T).trans ht)).2) hdW heZ heW
  obtain ⟨U,hU⟩ := eventually_atTop.mp he
  exact ⟨j,hJ,v z,U,hU⟩

end DefocusingNLS

end OAI
