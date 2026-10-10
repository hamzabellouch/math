import OAI.NumberTheory.CubicMoment.Estimates.PrimeLogConvolution

namespace OAI

/-! A power saving for the exact higher-prime-power replacement error.
Both the sparse support and the coefficient amplitude are proved. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem primeLogConvolutionError_energy {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ) (M : ι → ℝ) (Y : ℝ), 1 ≤ Y →
      (∀ i, 0 ≤ M i) → (∀ i, ∀ a ∈ S i, primary a ∧ Y^c < norm a) →
      (∀ f ∈ Fintype.piFinset S, norm (∏ i, f i) ≤ Y) →
      (∀ i, ∀ a ∈ S i, ‖w i a‖ ≤ M i) →
      (∑ b ∈ orderedConvolutionSupport S, ‖primeLogConvolutionError S w b‖^2) ≤
        K*Y^(1-c/16)*(∏ i, M i)^2 := by
  obtain ⟨C,hC,hamp⟩ := primeLogConvolutionError_bound (ι := ι)
    (show 0 < c/32 by positivity)
  obtain ⟨D,hD,hcount⟩ := largePrimePowerSupport_card_bound
  refine ⟨D*C^2,by positivity,?_⟩
  intro S w M Y hY hM hS hprod hw
  have hYp : 0 < Y := zero_lt_one.trans_le hY
  let T := (orderedConvolutionSupport S).filter (fun b => primeLogConvolutionError S w b ≠ 0)
  have hsub : T ⊆ largePrimePowerSupport Y c := fun b hb =>
    primeLogConvolutionError_support S w hS hprod (Finset.mem_filter.mp hb).2
  have hcard : (T.card:ℝ) ≤ D*Y^(1-c/8) :=
    (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hcount Y c hYp)
  have hsum : (∑ b ∈ T, ‖primeLogConvolutionError S w b‖^2) =
      ∑ b ∈ orderedConvolutionSupport S, ‖primeLogConvolutionError S w b‖^2 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro b hb hn
    have hz : primeLogConvolutionError S w b = 0 := by
      by_contra h
      exact hn (Finset.mem_filter.mpr ⟨hb,h⟩)
    simp only [hz,norm_zero,zero_pow (by decide : 2 ≠ 0)]
  rw [← hsum]
  have hMp : 0 ≤ ∏ i, M i := Finset.prod_nonneg (fun i _ => hM i)
  have he : Y^(1-c/8)*(Y^(c/32))^2 = Y^(1-c/16) := by
    rw [← Real.rpow_mul_natCast hYp.le,← Real.rpow_add hYp]
    congr 1
    push_cast
    ring
  calc
    _ ≤ ∑ _b ∈ T, (C*Y^(c/32)*(∏ i, M i))^2 := by
      apply Finset.sum_le_sum
      intro b hb
      have hbS := (Finset.mem_filter.mp hb).1
      obtain ⟨f,hf,hfb⟩ := Finset.mem_image.mp hbS
      have hbY : norm b ≤ Y := hfb ▸ hprod f hf
      exact pow_le_pow_left₀ (_root_.norm_nonneg _)
        (hamp S w M Y (fun i a ha => (hS i a ha).1) hM hw hY b hbS hbY) 2
    _ = (T.card:ℝ)*(C*Y^(c/32)*(∏ i, M i))^2 := by simp
    _ ≤ (D*Y^(1-c/8))*(C*Y^(c/32)*(∏ i, M i))^2 :=
      mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
    _ = (D*C^2)*(Y^(1-c/8)*(Y^(c/32))^2)*(∏ i, M i)^2 := by ring
    _ = _ := by rw [he]

end CubicFirstMoment

end

end OAI
