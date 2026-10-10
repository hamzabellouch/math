import OAI.Geometry.NodalSets.Elliptic.EnvelopeRegion
import OAI.Geometry.NodalSets.Elliptic.NormalizedJetPolynomialBound

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
open scoped ContDiff
noncomputable section

lemma normalized_jet_neighborhood_derivative_bound
    (u S S0 : Coord → ℝ) (hu : ContDiff ℝ ∞ u) (hS : ContDiff ℝ ∞ S)
    {Ω : Set Coord} {n : ℕ} (hn : 0 < n) {x z : Coord}
    (hx : x ∈ highEnvelopeRegion Ω S S0 n) {A B L : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hL : 0 ≤ L) (hLn : L ≤ (n:ℝ))
    (hsize : 6*(A+1)*B*Real.exp 1 ≤ (n:ℝ))
    (hz : ‖z-x‖ ≤ ((n:ℝ)^2)⁻¹)
    (hgap : (S0 z-S z)-(S0 x-S x) ≤ L*‖z-x‖)
    (hs : ‖fderiv ℝ S z‖ ≤ A)
    (hb : ∀ k : Fin 3, ‖iteratedFDeriv ℝ k.val u z‖ ≤ B*(n:ℝ)^(k.val+3)*
      max (Real.exp ((n:ℝ)*S z)) (Real.exp ((n:ℝ)*S0 z))) :
    ‖fderiv ℝ (fun y ↦ normalizedRealJet u n (S y) y) z‖ ≤ (n:ℝ)^13 := by
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  simp only [Fin.val_zero,zero_add,norm_iteratedFDeriv_zero,Real.norm_eq_abs] at h0
  simp only [Fin.val_one,norm_iteratedFDeriv_one] at h1
  have h := normalizedRealJet_polynomial_derivative_bound u S hu hS z hn1 hA hB
    (by positivity) hs h0 h1 h2
  have henv := high_envelope_neighborhood_bound hn hx hL hLn hz hgap
  calc
    _ ≤ (6*(A+1)*B)*(n:ℝ)^4*
        (max (Real.exp ((n:ℝ)*S z)) (Real.exp ((n:ℝ)*S0 z)))*Real.exp (-(n:ℝ)*S z) := h
    _ ≤ (6*(A+1)*B)*(n:ℝ)^4*(Real.exp 1*(n:ℝ)^8) := by
      rw [mul_assoc ((6*(A+1)*B)*(n:ℝ)^4)]
      gcongr
    _ = (6*(A+1)*B*Real.exp 1)*(n:ℝ)^12 := by ring
    _ ≤ (n:ℝ)*(n:ℝ)^12 := mul_le_mul_of_nonneg_right hsize (by positivity)
    _ = (n:ℝ)^13 := by ring

end
end Yau.Geometry

end OAI
