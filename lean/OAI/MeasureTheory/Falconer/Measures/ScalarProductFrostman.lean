import OAI.MeasureTheory.Falconer.Measures.ScalarProductInterpolation

namespace OAI

/-! The interpolated Frostman estimate on the actual Cartesian product,
with an explicit exponent strictly larger than one. -/
namespace Falconer

theorem scalarProductPoints_frostman {δ K κ θ : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (X : Finset ℝ) (hX : X.Nonempty)
    (hsep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ |x-y|)
    (hball : ∀ u r : ℝ, δ ≤ r → r ≤ 1 →
      ((X.filter fun x => |x-u| ≤ r).card : ℝ) ≤ K*r^κ*(X.card : ℝ)) :
    NormalizedFiniteBallBound δ (2*θ+2*κ*(1-θ))
      (81^θ*K^(2*(1-θ))*(δ*(X.card : ℝ))^(-(2*θ))) (scalarProductPoints X X) := by
  intro z r hdr hr1
  have hN : 0 < (X.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hX)
  have hh := scalarProductPoints_interpolated_ball hδ hdr hK hθ hθ1 X hsep z
    (fun u => hball u r hdr hr1)
  rw [scalar_product_profile_factor hδ (hδ.trans_le hdr) hK hN] at hh
  simpa only [scalarProductPoints_card,Nat.cast_mul,pow_two,mul_assoc] using hh

noncomputable def productInterpolationWeight (κ : ℝ) : ℝ := (2-3*κ)/(4-4*κ)

theorem productInterpolationWeight_properties {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1/2) :
    0 < productInterpolationWeight κ ∧ productInterpolationWeight κ < 1/2 ∧
      2*productInterpolationWeight κ+2*κ*(1-productInterpolationWeight κ) = 1+κ/2 ∧
      1-2*productInterpolationWeight κ = κ/(2-2*κ) := by
  have hd : 0 < 4-4*κ := by linarith
  have he : 0 < 2-3*κ := by linarith
  have hd2 : 0 < 2-2*κ := by linarith
  have hunit : 1-κ ≠ 0 := by linarith
  refine ⟨div_pos he hd,?_,?_,?_⟩
  · change (2-3*κ)/(4-4*κ) < 1/2
    apply (div_lt_iff₀ hd).2
    linarith
  · unfold productInterpolationWeight
    field_simp [hd.ne',hd2.ne',hunit]
    ring
  · unfold productInterpolationWeight
    field_simp [hd.ne',hd2.ne',hunit]
    ring

theorem scalarProductPoints_frostman_above_one {δ K κ : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1/2) (X : Finset ℝ) (hX : X.Nonempty)
    (hsep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ |x-y|)
    (hball : ∀ u r : ℝ, δ ≤ r → r ≤ 1 →
      ((X.filter fun x => |x-u| ≤ r).card : ℝ) ≤ K*r^κ*(X.card : ℝ)) :
    NormalizedFiniteBallBound δ (1+κ/2)
      (81^(productInterpolationWeight κ)*K^(2*(1-productInterpolationWeight κ))*
        (δ*(X.card : ℝ))^(-(2*productInterpolationWeight κ))) (scalarProductPoints X X) := by
  obtain ⟨hθ,hθ1,hf,_⟩ := productInterpolationWeight_properties hκ hκ1
  have hh := scalarProductPoints_frostman hδ hK hθ.le (by linarith) X hX hsep hball
  rwa [hf] at hh

end Falconer

end OAI
