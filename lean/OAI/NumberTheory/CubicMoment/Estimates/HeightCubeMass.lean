import OAI.NumberTheory.CubicMoment.Estimates.HeightAveraging
import OAI.NumberTheory.CubicMoment.Estimates.LowCoreHeightSaving
import OAI.NumberTheory.CubicMoment.Estimates.CubicCoreCoverage

namespace OAI

/-! Cube frequencies in a height average use the ordinary polynomial
mean, rather than the low-height cube lattice asymptotic. -/
noncomputable section
open scoped BigOperators
open Filter MeasureTheory
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

def nonzeroCubeNormBall (B : ℝ) : Finset Eisenstein :=
  (nonzeroNormBall (B^(1/3:ℝ))).image (fun z => z^3)

lemma mem_nonzeroCubeNormBall {B : ℝ} {h : Eisenstein}
    (hh : h ≠ 0) (hB : norm h ≤ B) (hc : ∃ z : Eisenstein, z^3 = h) :
    h ∈ nonzeroCubeNormBall B := by
  obtain ⟨z,hz⟩ := hc
  have hz0 : z ≠ 0 := by intro he; apply hh; rw [←hz,he]; simp
  have hr := cube_part_norm_bound (h := h) (v := 1) (j := z) one_ne_zero
    (by simpa using hz.symm) hB
  exact Finset.mem_image.mpr ⟨z,mem_nonzeroNormBall.mpr ⟨hr,hz0⟩,hz⟩

lemma nonzeroCubeNormBall_card {B : ℝ} (hB : 0 ≤ B) :
    ((nonzeroCubeNormBall B).card:ℝ) ≤ 18*B^(1/3:ℝ) :=
  (Nat.cast_le.mpr Finset.card_image_le).trans
    (nonzeroNormBall_card_le (Real.rpow_nonneg hB (1/3:ℝ)))

theorem cube_height_log_saving {C R : ℝ} (hMV : MontgomeryVaughanBound C)
    (hC : 0 ≤ C) (hR : 1 ≤ R)
    {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    (hlo : ∀ r i x, x < 1 → W r i x = 0)
    (hhi : ∀ r i x, R < x → W r i x = 0) (k : ℕ) :
    ∃ (K L₀ : ℝ) (m : ℕ), 0 ≤ K ∧
      ∀ (r : γ) (X : ι → ℝ) (B : ℝ) (H : Finset Eisenstein),
      1 ≤ L r → L₀ ≤ L r → (∀ i, 1 ≤ X i) → (∏ i, X i) = L r →
      0 ≤ B → H ⊆ nonzeroCubeNormBall B →
      ∀ (v e : Eisenstein) (ℓ : ℤ) (u T : ℝ), (1+Real.log (L r))^m ≤ T →
      dyadicHeightMean (fullStructuredHeightMass R H v e ℓ u (W r) X) T ≤
        K*B^(1/3:ℝ)*(L r)^2/(1+Real.log (L r))^k := by
  obtain ⟨K,D,b,hK,hD,hmean⟩ := log_energy_dyadic_mean hMV hC hR hW hlo hhi
  have hev := exclusion_log_absorption (c := 1) (d := 0) (ε := 1)
    (by norm_num) (by norm_num) (C := 1) (by norm_num) (b+k) 0
  obtain ⟨L₀,hL₀⟩ := eventually_atTop.mp hev
  refine ⟨18*K*(1+D),L₀,b+k,by positivity,?_⟩
  intro r X B H hL hL₀' hX hprod hB hH v e ℓ u T hT
  have hz : 1 ≤ 1+Real.log (L r) := by linarith [Real.log_nonneg hL]
  have hTp : 0 < T := (pow_pos (zero_lt_one.trans_le hz) _).trans_le hT
  have hlog := hL₀ (L r) hL₀' (L r) 1 (by norm_num) (by simp) (by simp)
  simp only [Real.one_rpow,one_mul,pow_zero,div_one] at hlog
  have hc : (H.card:ℝ) ≤ 18*B^(1/3:ℝ) :=
    (Nat.cast_le.mpr (Finset.card_le_card hH)).trans (nonzeroCubeNormBall_card hB)
  have hm := fullStructuredHeightMass_le H v e ℓ u (W r) X
    (fun h _ => hmean r X hL hX hprod h v e ℓ u T hTp)
  have hf := logarithmic_height_factor (zero_le_one.trans hL) hz
    (zero_le_one.trans hD) b k hlog hT
  apply hm.trans
  calc
    _ ≤ (18*B^(1/3:ℝ))*(K*((1+D*L r/T)*L r*(1+Real.log (L r))^b)) := by
      have hn : 0 ≤ K*(1+D*L r/T)*L r*(1+Real.log (L r))^b := by positivity
      convert mul_le_mul_of_nonneg_right hc hn using 1
      ring
    _ ≤ (18*B^(1/3:ℝ))*(K*((1+D)*(L r)^2/(1+Real.log (L r))^k)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hf hK)
        (mul_nonneg (by norm_num) (Real.rpow_nonneg hB _))
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
