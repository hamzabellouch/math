import OAI.Analysis.KadisonKastler.FourthMomentClipping
import OAI.Analysis.KadisonKastler.RandomizedRMS

namespace OAI

/-! # Averaged pairings controlled by bounded algebra elements -/

namespace KadisonKastler

open Finset
open scoped BigOperators

noncomputable section

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

omit [PartialOrder A] [StarOrderedRing A] in
/-- Rescaling the two algebra arguments extends a unit-ball pairing bound
to any fixed operator-norm ball. -/
theorem pairing_le_of_unitBall (J : A →ₗ[ℂ] H) (V : H →L[ℂ] H) {K s : ℝ}
    (hK : ∀ a b : A, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖inner ℂ (V (J a)) (J b)‖ ≤ K)
    (hs : 0 < s) (a b : A) (ha : ‖a‖ ≤ s) (hb : ‖b‖ ≤ s) :
    ‖inner ℂ (V (J a)) (J b)‖ ≤ s ^ 2 * K := by
  let c : ℂ := (s⁻¹ : ℝ)
  have hc : ‖c‖ = s⁻¹ := by simp [c, hs.le]
  have hca : ‖c • a‖ ≤ 1 := by
    rw [norm_smul, hc]
    exact (mul_le_mul_of_nonneg_left ha (inv_nonneg.mpr hs.le)).trans_eq
      (inv_mul_cancel₀ hs.ne')
  have hcb : ‖c • b‖ ≤ 1 := by
    rw [norm_smul, hc]
    exact (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hs.le)).trans_eq
      (inv_mul_cancel₀ hs.ne')
  have hh := hK (c • a) (c • b) hca hcb
  have he : ‖inner ℂ (V (J (c • a))) (J (c • b))‖ =
      s⁻¹ * s⁻¹ * ‖inner ℂ (V (J a)) (J b)‖ := by
    simp only [map_smul, inner_smul_left, inner_smul_right, norm_mul,
      starRingEnd_apply, norm_star, hc]
    ring
  rw [he] at hh
  calc
    _ = s ^ 2 * (s⁻¹ * s⁻¹ * ‖inner ℂ (V (J a)) (J b)‖) := by
      field_simp [hs.ne']
    _ ≤ s ^ 2 * K := mul_le_mul_of_nonneg_left hh (sq_nonneg s)

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The two tracial clipping errors are controlled in root mean square,
while the retained pairing is tested entirely on bounded elements. -/
theorem averaged_pairing_le_of_fourth_moments (τ : FaithfulTracialState A)
    (J : A →ₗ[ℂ] H) (hJ : ∀ a, ‖J a‖ = traceTwoNorm τ a)
    (V : H →L[ℂ] H) (a b : ι → A) {K s : ℝ} (hs : 0 < s)
    (hK : ∀ x y : A, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → ‖inner ℂ (V (J x)) (J y)‖ ≤ K)
    (ha₂ : (𝔼 i, traceTwoNorm τ (a i) ^ 2) ≤ 1)
    (hb₂ : (𝔼 i, traceTwoNorm τ (b i) ^ 2) ≤ 1)
    (ha₄ : (𝔼 i, (τ.toLinearMap ((star (a i) * a i) ^ 2)).re) ≤ 12)
    (hb₄ : (𝔼 i, (τ.toLinearMap ((star (b i) * b i) ^ 2)).re) ≤ 12) :
    ‖𝔼 i, inner ℂ (V (J (a i))) (J (b i))‖ ≤
      s ^ 2 * K + (2 * Real.sqrt 12 / s) * ‖V‖ := by
  let v : ι → H := fun i => J (a i)
  let w : ι → H := fun i => J (b i)
  let vc : ι → H := fun i => J (spectralClip s (a i))
  let wc : ι → H := fun i => J (spectralClip s (b i))
  have hrms (x : ι → A) (hx : (𝔼 i, traceTwoNorm τ (x i) ^ 2) ≤ 1) :
      finiteRMS (fun i => J (x i)) ≤ 1 := by
    have hsq : finiteRMS (fun i => J (x i)) ^ 2 ≤ 1 := by
      simpa only [finiteRMS_sq, hJ] using hx
    nlinarith [finiteRMS_nonneg (fun i => J (x i))]
  have hv : finiteRMS v ≤ 1 := hrms a ha₂
  have hw : finiteRMS w ≤ 1 := hrms b hb₂
  have hvc : finiteRMS vc ≤ 1 :=
    (finiteRMS_mono vc v fun i => by
      simpa only [vc, v, hJ] using traceTwoNorm_spectralClip_le τ hs (a i)).trans hv
  have htail (x : ι → A)
      (hx : (𝔼 i, (τ.toLinearMap ((star (x i) * x i) ^ 2)).re) ≤ 12) :
      finiteRMS (fun i => J (x i) - J (spectralClip s (x i))) ≤ Real.sqrt 12 / s := by
    have hsq : finiteRMS (fun i => J (x i) - J (spectralClip s (x i))) ^ 2 ≤
        12 / s ^ 2 := by
      simpa only [finiteRMS_sq, ← map_sub, hJ] using
        expect_traceTwoNorm_spectralClip_discard_sq_le τ x hs hx
    have he : (Real.sqrt 12 / s) ^ 2 = 12 / s ^ 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 12)]
    have hp : 0 ≤ Real.sqrt 12 / s := div_nonneg (Real.sqrt_nonneg _) hs.le
    nlinarith [he, finiteRMS_nonneg (fun i => J (x i) - J (spectralClip s (x i)))]
  have hda : finiteRMS (fun i => v i - vc i) ≤ Real.sqrt 12 / s := htail a ha₄
  have hdb : finiteRMS (fun i => w i - wc i) ≤ Real.sqrt 12 / s := htail b hb₄
  have hclip : ‖meanPairing (fun _ : ι => V) vc wc‖ ≤ s ^ 2 * K := by
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    calc
      (𝔼 i, ‖inner ℂ (V (vc i)) (wc i)‖) ≤ 𝔼 _ : ι, s ^ 2 * K :=
        expect_le_expect fun i _ => pairing_le_of_unitBall J V hK hs _ _
          (spectralClip_norm_le hs (a i)) (spectralClip_norm_le hs (b i))
      _ = _ := Fintype.expect_const _
  have herr₁ : ‖meanPairing (fun _ : ι => V) (fun i => v i - vc i) w‖ ≤
      ‖V‖ * (Real.sqrt 12 / s) := by
    apply (norm_mean_operator_pairing_le _ _ _ (norm_nonneg V)
      (fun i => V.le_opNorm _)).trans
    exact mul_le_mul_of_nonneg_left
      ((mul_le_mul hda hw (finiteRMS_nonneg _) (div_nonneg (Real.sqrt_nonneg _) hs.le)).trans_eq
        (mul_one _)) (norm_nonneg V)
  have herr₂ : ‖meanPairing (fun _ : ι => V) vc (fun i => w i - wc i)‖ ≤
      ‖V‖ * (Real.sqrt 12 / s) := by
    apply (norm_mean_operator_pairing_le _ _ _ (norm_nonneg V)
      (fun i => V.le_opNorm _)).trans
    exact mul_le_mul_of_nonneg_left
      ((mul_le_mul hvc hdb (finiteRMS_nonneg _) zero_le_one).trans_eq
        (one_mul _)) (norm_nonneg V)
  have heq : meanPairing (fun _ : ι => V) v w =
      meanPairing (fun _ : ι => V) vc wc +
        meanPairing (fun _ : ι => V) (fun i => v i - vc i) w +
          meanPairing (fun _ : ι => V) vc (fun i => w i - wc i) := by
    unfold meanPairing
    rw [← expect_add_distrib, ← expect_add_distrib]
    apply expect_congr rfl
    intro i _
    simp only [map_sub, inner_sub_left, inner_sub_right]
    ring
  change ‖meanPairing (fun _ : ι => V) v w‖ ≤ _
  rw [heq]
  calc
    _ ≤ (‖meanPairing (fun _ : ι => V) vc wc‖ +
        ‖meanPairing (fun _ : ι => V) (fun i => v i - vc i) w‖) +
        ‖meanPairing (fun _ : ι => V) vc (fun i => w i - wc i)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (s ^ 2 * K + ‖V‖ * (Real.sqrt 12 / s)) + ‖V‖ * (Real.sqrt 12 / s) :=
      add_le_add (add_le_add hclip herr₁) herr₂
    _ = _ := by ring

/-- The cutoff `4 * sqrt 12` makes the two error terms half of the
operator norm, with retained-pairing coefficient `192`. -/
theorem averaged_pairing_le_one_ninety_two (τ : FaithfulTracialState A)
    (J : A →ₗ[ℂ] H) (hJ : ∀ a, ‖J a‖ = traceTwoNorm τ a)
    (V : H →L[ℂ] H) (a b : ι → A) {K : ℝ}
    (hK : ∀ x y : A, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → ‖inner ℂ (V (J x)) (J y)‖ ≤ K)
    (ha₂ : (𝔼 i, traceTwoNorm τ (a i) ^ 2) ≤ 1)
    (hb₂ : (𝔼 i, traceTwoNorm τ (b i) ^ 2) ≤ 1)
    (ha₄ : (𝔼 i, (τ.toLinearMap ((star (a i) * a i) ^ 2)).re) ≤ 12)
    (hb₄ : (𝔼 i, (τ.toLinearMap ((star (b i) * b i) ^ 2)).re) ≤ 12) :
    ‖𝔼 i, inner ℂ (V (J (a i))) (J (b i))‖ ≤ 192 * K + ‖V‖ / 2 := by
  have hs : 0 < Real.sqrt 12 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : (4 * Real.sqrt 12) ^ 2 = 192 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 12)]
  have hratio : 2 * Real.sqrt 12 / (4 * Real.sqrt 12) = (1 / 2 : ℝ) := by
    field_simp [hs.ne']
    ring
  have h := averaged_pairing_le_of_fourth_moments τ J hJ V a b
    (by positivity : 0 < 4 * Real.sqrt 12) hK ha₂ hb₂ ha₄ hb₄
  rw [hsq, hratio] at h
  nlinarith only [h]

end

end KadisonKastler

end OAI
