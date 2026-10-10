import OAI.NumberTheory.CubicMoment.Estimates.PrimeGroupTailHeightSaving
import OAI.NumberTheory.CubicMoment.Estimates.SmallBAllFrequency

namespace OAI

/-! All nonzero frequencies through N^(19/20), including cubes, at arbitrary translated heights. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- Every nonzero frequency in the small-B cutoff has a power-saving
height average, with arbitrary coefficients and no restriction on u. -/
theorem primeGroupTail_all_frequency_height_power
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S H : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z : ℕ) (B T u : ℝ) (ℓ : ℤ), 1 ≤ (Z:ℝ) → 1 ≤ B →
      (Z:ℝ)^(1/50:ℝ) ≤ T →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ (Z:ℝ)) →
      8*B ≤ (Z:ℝ)^(19/20:ℝ) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B) →
      dyadicHeightMean (fun t => ∑ h ∈ H,
        ‖∑ b ∈ S, β b*cubicSymbol b h*theta ℓ b*mellinPhase (t+u) (norm b)‖^2) T ≤
      K*(Z:ℝ)^(1-1/20000:ℝ)*B^(1/3:ℝ)*∑ b ∈ S, ‖β b‖^2 := by
  obtain ⟨K₁,hK₁,hnc⟩ := primeGroupTail_noncube_height_power hMV hC hHuxley
  obtain ⟨K₂,hK₂,hc⟩ := arbitrary_cube_height_power hMV hC
  refine ⟨K₁+K₂,by positivity,?_⟩
  intro S H β Z B T u ℓ hZ hB hT hS hsize hH
  let HC := H.filter (fun h => ∃ a : Eisenstein, a^3 = h)
  let HN := H.filter (fun h => ¬∃ a : Eisenstein, a^3 = h)
  let F := fun (J : Finset Eisenstein) t => ∑ h ∈ J,
    ‖∑ b ∈ S, β b*cubicSymbol b h*theta ℓ b*mellinPhase (t+u) (norm b)‖^2
  have hCsub : HC ⊆ nonzeroCubeNormBall B := by
    intro h hh
    obtain ⟨hh,hcube⟩ := Finset.mem_filter.mp hh
    exact mem_nonzeroCubeNormBall (hH h hh).1 (hH h hh).2 hcube
  have hn := hnc S HN β Z B T u ℓ hZ hB hT hS hsize (fun h hh =>
    ⟨(hH h (Finset.mem_filter.mp hh).1).1,(hH h (Finset.mem_filter.mp hh).1).2,
      (Finset.mem_filter.mp hh).2⟩)
  have hcube := hc S HC β Z B T u ℓ hZ (zero_le_one.trans hB) hT
    (fun b hb => ⟨(hS b hb).1,(hS b hb).2.2⟩) hCsub
  have hcont (J : Finset Eisenstein) : Continuous (F J) :=
    continuous_finsetSum J (fun h _ => (continuous_finite_character_height S β h ℓ u).norm.pow 2)
  have heq : F H = fun t => F HC t+F HN t := by
    funext t
    exact (Finset.sum_filter_add_sum_filter_not H (fun h => ∃ a : Eisenstein, a^3 = h) _).symm
  change dyadicHeightMean (F H) T ≤ _
  rw [heq,dyadicHeightMean_add (hcont HC) (hcont HN)]
  exact (add_le_add hcube hn).trans_eq (by ring)

end CubicFirstMoment

end

end OAI
