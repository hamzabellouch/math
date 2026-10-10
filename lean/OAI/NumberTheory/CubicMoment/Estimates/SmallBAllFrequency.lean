import OAI.NumberTheory.CubicMoment.Estimates.SmallBHeightSaving
import OAI.NumberTheory.CubicMoment.Estimates.HeightCubeMass

namespace OAI

/-! The absolute power saving includes cube frequencies. Their height
mean uses the same ordinary theorem, with the actual cube count. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma smallB_cube_height_scale {N T : ℝ} (hN : 1 ≤ N) (hT : N^(1/50:ℝ) ≤ T) :
    N^(1/10000:ℝ)*(1+N/T) ≤ 2*N^(1-1/20000:ℝ) := by
  have hp : 0 < N := zero_lt_one.trans_le hN
  have hf : N/T ≤ N^(49/50:ℝ) := by
    calc
      _ ≤ N/N^(1/50:ℝ) := div_le_div_of_nonneg_left hp.le (Real.rpow_pos_of_pos hp _) hT
      _ = _ := by nth_rw 1 [← Real.rpow_one N]; rw [← Real.rpow_sub hp]; norm_num
  have hsum : 1+N/T ≤ 2*N^(49/50:ℝ) := by
    linarith [Real.one_le_rpow hN (by norm_num : (0:ℝ) ≤ 49/50)]
  calc
    _ ≤ N^(1/10000:ℝ)*(2*N^(49/50:ℝ)) :=
      mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hp.le _)
    _ = 2*N^((1/10000:ℝ)+49/50) := by rw [Real.rpow_add hp]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hN (by norm_num)) (by norm_num)

theorem arbitrary_cube_height_power
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S H : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z : ℕ) (B T u : ℝ) (ℓ : ℤ), 1 ≤ (Z:ℝ) → 0 ≤ B →
      (Z:ℝ)^(1/50:ℝ) ≤ T →
      (∀ b ∈ S, primary b ∧ norm b ≤ (Z:ℝ)) →
      H ⊆ nonzeroCubeNormBall B →
      dyadicHeightMean (fun t => ∑ h ∈ H,
        ‖∑ b ∈ S, β b*cubicSymbol b h*theta ℓ b*mellinPhase (t+u) (norm b)‖^2) T ≤
      K*(Z:ℝ)^(1-1/20000:ℝ)*B^(1/3:ℝ)*∑ b ∈ S, ‖β b‖^2 := by
  obtain ⟨D,hD,hmean⟩ := arbitrary_primary_height_mean hMV hC
    (by norm_num : (0:ℝ) < 1/10000)
  refine ⟨72*C*D+1,by positivity,?_⟩
  intro S H β Z B T u ℓ hZ hB hT hS hH
  have hp : 0 < (Z:ℝ) := zero_lt_one.trans_le hZ
  have hTp : 0 < T := (Real.rpow_pos_of_pos hp _).trans_le hT
  have hNorm : ∀ b ∈ S, normNat b ∈ Finset.Icc 1 Z := by
    intro b hb
    apply Finset.mem_Icc.mpr
    refine ⟨Nat.one_le_iff_ne_zero.mpr (normNat_ne_zero (primary_ne_zero (hS b hb).1)),?_⟩
    have h := (hS b hb).2
    rw [← normNat_cast b] at h
    exact_mod_cast h
  have hm := hmean S H β Z (fun b hb => (hS b hb).1) hNorm ℓ u T hTp
  have hcard : (H.card:ℝ) ≤ 18*B^(1/3:ℝ) :=
    (Nat.cast_le.mpr (Finset.card_le_card hH)).trans (nonzeroCubeNormBall_card hB)
  have hs := smallB_cube_height_scale hZ hT
  let E := ∑ b ∈ S, ‖β b‖^2
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  calc
    _ ≤ 2*C*D*(1+(Z:ℝ)/T)*(Z:ℝ)^(1/10000:ℝ)*H.card*E := hm
    _ ≤ 2*C*D*(1+(Z:ℝ)/T)*(Z:ℝ)^(1/10000:ℝ)*(18*B^(1/3:ℝ))*E := by gcongr
    _ = 36*C*D*B^(1/3:ℝ)*E*((Z:ℝ)^(1/10000:ℝ)*(1+(Z:ℝ)/T)) := by ring
    _ ≤ 36*C*D*B^(1/3:ℝ)*E*(2*(Z:ℝ)^(1-1/20000:ℝ)) := by gcongr
    _ ≤ _ := by
      have hn : 0 ≤ (Z:ℝ)^(1-1/20000:ℝ)*B^(1/3:ℝ)*E := by positivity
      nlinarith

/-- Every nonzero frequency in the small-B cutoff has a power-saving
height average, with arbitrary coefficients and no restriction on u. -/
theorem smallB_all_frequency_height_power
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S H : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z : ℕ) (B T u : ℝ) (ℓ : ℤ), 1 ≤ (Z:ℝ) → 1 ≤ B →
      (Z:ℝ)^(1/50:ℝ) ≤ T →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ (Z:ℝ)) →
      8*B ≤ (Z:ℝ)^(3/4:ℝ) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B) →
      dyadicHeightMean (fun t => ∑ h ∈ H,
        ‖∑ b ∈ S, β b*cubicSymbol b h*theta ℓ b*mellinPhase (t+u) (norm b)‖^2) T ≤
      K*(Z:ℝ)^(1-1/20000:ℝ)*B^(1/3:ℝ)*∑ b ∈ S, ‖β b‖^2 := by
  obtain ⟨K₁,hK₁,hnc⟩ := smallB_noncube_height_power hMV hC hHuxley
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
