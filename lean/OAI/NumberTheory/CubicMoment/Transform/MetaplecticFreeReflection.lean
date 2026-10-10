import OAI.NumberTheory.CubicMoment.Transform.MetaplecticFreeBlock
import OAI.NumberTheory.CubicMoment.Estimates.PrimitiveDualConjugation

namespace OAI

/-! Reflection of the free-primary mean for the translated variable
appearing in the actual critical-line Mellin kernel. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma metaplectic_reflected_polynomial_norm (S : Finset Eisenstein)
    (v : Eisenstein → ℂ) (c u t : ℝ) :
    ‖∑ b ∈ S, v b*mellinPhase (u-t) (c*norm b)‖ =
      ‖∑ b ∈ S, star (v b)*mellinPhase (t-u) (c*norm b)‖ := by
  rw [←norm_star (∑ b ∈ S, v b*mellinPhase (u-t) (c*norm b))]
  simp only [star_sum,star_mul,star_mellinPhase,neg_sub,mul_comm]

 theorem metaplectic_reflected_free_mean {ε C : ℝ} (hε : 0 < ε)
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) :
    ∃ D : ℝ, 0 < D ∧ ∀ (S : Finset Eisenstein), (∀ b ∈ S, primary b) →
      ∀ (v : Eisenstein → ℂ) (L K T u c : ℝ),
      1 ≤ L → 0 ≤ K → 0 < T → 0 < c →
      (∀ b ∈ S, L/2 ≤ norm b ∧ norm b ≤ L) →
      (∀ b ∈ S, ‖v b‖^2 ≤ K^2/norm b) →
      (∫ t in T..2*T, ‖∑ b ∈ S, v b*mellinPhase (u-t) (c*norm b)‖)/T ≤
        Real.sqrt (C*D)*L^(ε/2)*K*(1+Real.sqrt (2*L/T)) := by
  obtain ⟨D,hD,hbound⟩ := metaplectic_scaled_free_meanAbsolute hε hMV hC
  refine ⟨D,hD,?_⟩
  intro S hS v L K T u c hL hK hT hc hsize hv
  have h := hbound S hS (fun b => star (v b)) L K T (-u) c 0 hL hK hT hc hsize
    (by intro b hb; simpa only [norm_star] using hv b hb)
  simp only [theta_zero,mul_one] at h
  have he : (fun t : ℝ => ‖∑ b ∈ S, v b*mellinPhase (u-t) (c*norm b)‖) =
      (fun t : ℝ => ‖∑ b ∈ S, star (v b)*mellinPhase (t-u) (c*norm b)‖) :=
    funext (fun t => metaplectic_reflected_polynomial_norm S v c u t)
  rw [he]
  simpa only [sub_eq_add_neg] using h

end CubicFirstMoment

end

end OAI
