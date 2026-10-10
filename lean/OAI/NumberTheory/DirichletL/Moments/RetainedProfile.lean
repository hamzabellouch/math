import OAI.NumberTheory.DirichletL.Moments.HeckeHeight
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentRetainedProfile
open CenteredMomentLattice CenteredMomentTwist CenteredMomentHeckeTwist
open CenteredMomentHeckeHeight CenteredMomentHeckeVolume CenteredMomentHeckeCancellation HeckeFamily
open EisensteinSchwartzPoisson QuadraticInitialBound
local notation "O" => ActualEisensteinCubic.O

def dilated (W : ℝ → ℂ) (c : ℝ) : ℝ → ℂ := fun x => W (c * x)

theorem dilated_contDiff (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W) (c : ℝ) :
    ContDiff ℝ ∞ (dilated W c) :=
  hW.comp (contDiff_const.mul contDiff_id)

theorem dilated_support (W : ℝ → ℂ) (a b B c : ℝ) (ha : 0 < a)
    (hB : 1 ≤ B) (hc : 1 ≤ c) (hcB : c ≤ B)
    (hs : Function.support W ⊆ Set.Icc a b) :
    Function.support (dilated W c) ⊆ Set.Icc (a / B) b := by
  intro x hx
  have hv := hs hx
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hx0 : 0 < x := (mul_pos_iff.mp (lt_of_lt_of_le ha hv.1)).resolve_right
    (by intro h; linarith [h.1]) |>.2
  constructor
  · apply (div_le_iff₀ hB0).mpr
    exact hv.1.trans (by nlinarith)
  · exact (show x ≤ c * x by nlinarith).trans hv.2

theorem seminorm_dilation_le (f g : 𝓢(ℝ, ℂ)) (ζ : ℂ) (c B : ℝ)
    (hζ : ‖ζ‖ = 1) (hc : 1 ≤ c) (hcB : c ≤ B)
    (hg : ∀ x, g x = ζ * f (c * x)) (k n : ℕ) :
    SchwartzMap.seminorm ℝ k n g ≤ B ^ n * SchwartzMap.seminorm ℝ k n f := by
  have hc0 : 0 ≤ c := le_trans zero_le_one hc
  have hB0 : 0 ≤ B := hc0.trans hcB
  have he : (g : ℝ → ℂ) = fun x => ζ * f (c * x) := funext hg
  apply SchwartzMap.seminorm_le_bound' ℝ k n g (by positivity)
  intro x
  rw [he, iteratedDeriv_const_mul_field,
    iteratedDeriv_comp_const_smul (f.smooth n), norm_mul, hζ,
    one_mul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hc0 n)]
  have hx : |x| ^ k ≤ |c * x| ^ k := by
    apply pow_le_pow_left₀ (abs_nonneg x)
    rw [abs_mul, abs_of_nonneg hc0]
    nlinarith [abs_nonneg x]
  calc
    _ = c ^ n * (|x| ^ k * ‖iteratedDeriv n f (c * x)‖) := by ring
    _ ≤ c ^ n * (|c * x| ^ k * ‖iteratedDeriv n f (c * x)‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hx (norm_nonneg _)) (pow_nonneg hc0 n)
    _ ≤ c ^ n * SchwartzMap.seminorm ℝ k n f :=
      mul_le_mul_of_nonneg_left (SchwartzMap.le_seminorm' ℝ k n f (c * x))
        (pow_nonneg hc0 n)
    _ ≤ B ^ n * SchwartzMap.seminorm ℝ k n f :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hc0 hcB _) (apply_nonneg _ _)

theorem normPowerProfile_dilated (W : ℝ → ℂ) (a b B c : ℝ) (ha : 0 < a)
    (hB : 1 ≤ B) (hc : 1 ≤ c) (hcB : c ≤ B)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) (t x : ℝ) :
    normPowerProfile (dilated W c) (a / B) b
      (div_pos ha (lt_of_lt_of_le zero_lt_one hB))
      (dilated_support W a b B c ha hB hc hcB hs) (dilated_contDiff W hW c) t x =
      ((c : ℂ) ^ (Complex.I * t))⁻¹ *
        normPowerProfile W a b ha hs hW t (c * x) := by
  rw [normPowerProfile_apply, normPowerProfile_apply]
  by_cases hz : W (c * x) = 0
  · simp [dilated, hz]
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hx : 0 < x := (mul_pos_iff.mp (lt_of_lt_of_le ha (hs hz).1)).resolve_right
    (by intro h; linarith [h.1]) |>.2
  have hp := Complex.mul_cpow_ofReal_nonneg hc0.le hx.le (Complex.I * t)
  rw [← Complex.ofReal_mul] at hp
  rw [hp]
  have hn : (c : ℂ) ^ (Complex.I * t) ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [norm_real_imaginary_power c t hc0]; norm_num)
  dsimp only [dilated]
  simp only [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

theorem normPowerProfile_dilated_seminorm (W : ℝ → ℂ) (a b B c : ℝ) (ha : 0 < a)
    (hB : 1 ≤ B) (hc : 1 ≤ c) (hcB : c ≤ B)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (t : ℝ) (k n : ℕ) :
    SchwartzMap.seminorm ℝ k n
      (normPowerProfile (dilated W c) (a / B) b
        (div_pos ha (lt_of_lt_of_le zero_lt_one hB))
        (dilated_support W a b B c ha hB hc hcB hs) (dilated_contDiff W hW c) t) ≤
      B ^ n * SchwartzMap.seminorm ℝ k n (normPowerProfile W a b ha hs hW t) := by
  apply seminorm_dilation_le _ _ ((c : ℂ) ^ (Complex.I * t))⁻¹ c B
    (by rw [norm_inv, norm_real_imaginary_power c t (lt_of_lt_of_le zero_lt_one hc), inv_one])
    hc hcB
  intro x
  exact normPowerProfile_dilated W a b B c ha hB hc hcB hs hW t x

theorem normPowerProfile_dilated_finite (W : ℝ → ℂ) (a b B c : ℝ) (ha : 0 < a)
    (hB : 1 ≤ B) (hc : 1 ≤ c) (hcB : c ≤ B)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (t : ℝ) (F : Finset (ℕ × ℕ)) :
    F.sup (schwartzSeminormFamily ℝ ℝ ℂ)
      (normPowerProfile (dilated W c) (a / B) b
        (div_pos ha (lt_of_lt_of_le zero_lt_one hB))
        (dilated_support W a b B c ha hB hc hcB hs) (dilated_contDiff W hW c) t) ≤
      B ^ (F.sup Prod.snd) *
        F.sup (schwartzSeminormFamily ℝ ℝ ℂ) (normPowerProfile W a b ha hs hW t) := by
  apply Seminorm.finset_sup_apply_le (by positivity)
  intro z hz
  apply (normPowerProfile_dilated_seminorm W a b B c ha hB hc hcB hs hW t z.1 z.2).trans
  exact mul_le_mul (pow_le_pow_right₀ hB (Finset.le_sup hz))
    (Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℝ ℝ ℂ) hz) (apply_nonneg _ _) (by positivity)

theorem dilated_normPowerProfile_uniform_degree (a b B : ℝ) (ha : 0 < a)
    (hB : 1 ≤ B) (F : Finset (ℕ × ℕ)) :
    ∃ J : ℕ, ∀ W : ℝ → ℂ, ∀ hs : Function.support W ⊆ Set.Icc a b,
      ∀ hW : ContDiff ℝ ∞ W, ∃ C : ℝ, 0 < C ∧
      ∀ c : ℝ, ∀ hc : 1 ≤ c, ∀ hcB : c ≤ B, ∀ t : ℝ,
      F.sup (schwartzSeminormFamily ℝ ℝ ℂ)
        (normPowerProfile (dilated W c) (a / B) b
          (div_pos ha (lt_of_lt_of_le zero_lt_one hB))
          (dilated_support W a b B c ha hB hc hcB hs) (dilated_contDiff W hW c) t) ≤
        C * (1 + ‖t‖) ^ J := by
  obtain ⟨J, hJ⟩ := normPowerProfile_uniform_degree a b ha F
  refine ⟨J, ?_⟩
  intro W hs hW
  obtain ⟨C, hC, hbound⟩ := hJ W hs hW
  refine ⟨B ^ (F.sup Prod.snd) * C, mul_pos (pow_pos (lt_of_lt_of_le zero_lt_one hB) _) hC, ?_⟩
  intro c hc hcB t
  have ht : (1 + ‖t / (2 * Real.pi)‖) ^ J ≤ (1 + ‖t‖) ^ J := by
    gcongr
    exact CenteredMomentHeight.normalized_height_le t
  calc
    _ ≤ B ^ (F.sup Prod.snd) *
        F.sup (schwartzSeminormFamily ℝ ℝ ℂ) (normPowerProfile W a b ha hs hW t) :=
      normPowerProfile_dilated_finite W a b B c ha hB hc hcB hs hW t F
    _ ≤ B ^ (F.sup Prod.snd) * (C * (1 + ‖t‖) ^ J) :=
      mul_le_mul_of_nonneg_left
        ((hbound t).trans (mul_le_mul_of_nonneg_left ht hC.le)) (by positivity)
    _ = _ := by ring

def clippedScale (S : ℝ) : ℝ := max 1 S

def clipDilation (S : ℝ) : ℝ := clippedScale S / S

theorem clippedScale_ge_one (S : ℝ) : 1 ≤ clippedScale S := le_max_left _ _

theorem clipDilation_ge_one (S : ℝ) (hS : 0 < S) : 1 ≤ clipDilation S := by
  rw [clipDilation, le_div_iff₀ hS, one_mul]
  exact le_max_right _ _

theorem clipDilation_le (b S : ℝ) (hS : 0 < S) (hret : 1 ≤ S * b) :
    clipDilation S ≤ max 1 b := by
  rw [clipDilation, div_le_iff₀ hS]
  apply max_le
  · exact hret.trans (by nlinarith [le_max_right (1 : ℝ) b])
  · nlinarith [le_max_left (1 : ℝ) b]

theorem clipDilation_eq_one (S : ℝ) (hS : 1 ≤ S) : clipDilation S = 1 := by
  simp [clipDilation, clippedScale, max_eq_right hS, ne_of_gt (lt_of_lt_of_le zero_lt_one hS)]

theorem clipDilation_subunit (S : ℝ) (hS : S ≤ 1) :
    clipDilation S = 1 / S := by simp [clipDilation, clippedScale, max_eq_left hS]

theorem clipped_source (W : ℝ → ℂ) (S x : ℝ) (hS : 0 < S) :
    dilated W (clipDilation S) (x / clippedScale S) = W (x / S) := by
  have hclip : clippedScale S ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (clippedScale_ge_one S))
  unfold dilated clipDilation
  congr 1
  field_simp

theorem strict_subunit_ideal_zero (W : ℝ → ℂ) (b S : ℝ) (hS : 0 < S)
    (hs : Function.support W ⊆ Set.Iic b) (hstrict : S * b < 1)
    (I : Ideal O) (hI : I ≠ 0) : W ((Ideal.absNorm I : ℝ) / S) = 0 := by
  by_contra h
  have hn : 1 ≤ (Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (fun hz => hI (Ideal.absNorm_eq_zero_iff.mp hz))
  have hu := (div_le_iff₀ hS).mp (hs h)
  nlinarith

theorem strict_subunit_sum_zero (A : Ideal O → ℂ) (hA : A 0 = 0)
    (W : ℝ → ℂ) (b S : ℝ) (hS : 0 < S)
    (hs : Function.support W ⊆ Set.Iic b) (hstrict : S * b < 1) :
    (∑' I : Ideal O, A I * W ((Ideal.absNorm I : ℝ) / S)) = 0 := by
  calc
    _ = ∑' _I : Ideal O, (0 : ℂ) := by
      apply tsum_congr
      intro I
      by_cases hI : I = 0
      · rw [hI, hA, zero_mul]
      · rw [strict_subunit_ideal_zero W b S hS hs hstrict I hI, mul_zero]
    _ = 0 := tsum_zero

theorem clipped_ideal_sum (A : Ideal O → ℂ) (W : ℝ → ℂ) (S : ℝ) (hS : 0 < S) :
    (∑' I : Ideal O, A I * W ((Ideal.absNorm I : ℝ) / S)) =
      ∑' I : Ideal O, A I * dilated W (clipDilation S)
        ((Ideal.absNorm I : ℝ) / clippedScale S) := by
  apply tsum_congr
  intro I
  rw [clipped_source W S _ hS]

theorem clipped_twistedIdealSum (χ : Character) (W : ℝ → ℂ) (t S : ℝ) (hS : 0 < S) :
    twistedIdealSum χ W t S =
      twistedIdealSum χ (dilated W (clipDilation S)) t (clippedScale S) :=
  clipped_ideal_sum _ W S hS

theorem strict_subunit_twistedIdealSum_zero (χ : Character) (W : ℝ → ℂ)
    (b t S : ℝ) (hS : 0 < S) (hs : Function.support W ⊆ Set.Iic b)
    (hstrict : S * b < 1) : twistedIdealSum χ W t S = 0 := by
  apply strict_subunit_sum_zero _ _ W b S hS hs hstrict
  simp only [map_zero, zero_mul]

theorem clipped_rowTwistedSum (η : Character) (m A₀ z : O)
    (W : ℝ → ℂ) (t S : ℝ) (hS : 0 < S) :
    rowTwistedSum η m A₀ z W t S =
      rowTwistedSum η m A₀ z (dilated W (clipDilation S)) t (clippedScale S) :=
  clipped_ideal_sum _ W S hS

theorem strict_subunit_rowTwistedSum_zero (η : Character) (m A₀ z : O)
    (W : ℝ → ℂ) (b t S : ℝ) (hS : 0 < S) (hs : Function.support W ⊆ Set.Iic b)
    (hstrict : S * b < 1) : rowTwistedSum η m A₀ z W t S = 0 := by
  apply strict_subunit_sum_zero _ _ W b S hS hs hstrict
  simp only [map_zero, zero_mul]

def retainedProfile (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (S : ℝ) (hS : 0 < S) (hret : 1 ≤ S * b) (t : ℝ) : 𝓢(ℝ, ℂ) :=
  normPowerProfile (dilated W (clipDilation S)) (a / max 1 b) b
    (div_pos ha (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))
    (dilated_support W a b (max 1 b) (clipDilation S) ha (le_max_left _ _)
      (clipDilation_ge_one S hS) (clipDilation_le b S hS hret) hs)
    (dilated_contDiff W hW (clipDilation S)) t

theorem retainedProfile_apply (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (S : ℝ) (hS : 0 < S) (hret : 1 ≤ S * b) (t x : ℝ) :
    retainedProfile W a b ha hs hW S hS hret t x =
      (x : ℂ) ^ (Complex.I * t) * W (clipDilation S * x) :=
  normPowerProfile_apply _ _ _ _ _ _ _ _

theorem retainedProfile_support (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (S : ℝ) (hS : 0 < S) (hret : 1 ≤ S * b) (t : ℝ) :
    Function.support (retainedProfile W a b ha hs hW S hS hret t : ℝ → ℂ) ⊆
      Set.Icc (a / max 1 b) b := by
  apply (normPowerProfile_support _ _ _ _ _ _ _).trans
  exact dilated_support W a b (max 1 b) (clipDilation S) ha (le_max_left _ _)
    (clipDilation_ge_one S hS) (clipDilation_le b S hS hret) hs

theorem retainedProfile_uniform_degree (a b : ℝ) (ha : 0 < a)
    (F : Finset (ℕ × ℕ)) :
    ∃ J : ℕ, ∀ W : ℝ → ℂ, ∀ hs : Function.support W ⊆ Set.Icc a b,
      ∀ hW : ContDiff ℝ ∞ W, ∃ C : ℝ, 0 < C ∧
      ∀ S : ℝ, ∀ hS : 0 < S, ∀ hret : 1 ≤ S * b, ∀ t : ℝ,
      F.sup (schwartzSeminormFamily ℝ ℝ ℂ)
        (retainedProfile W a b ha hs hW S hS hret t) ≤ C * (1 + ‖t‖) ^ J := by
  obtain ⟨J, hJ⟩ := dilated_normPowerProfile_uniform_degree a b (max 1 b) ha (le_max_left _ _) F
  refine ⟨J, ?_⟩
  intro W hs hW
  obtain ⟨C, hC, hbound⟩ := hJ W hs hW
  exact ⟨C, hC, fun S hS hret t =>
    hbound (clipDilation S) (clipDilation_ge_one S hS) (clipDilation_le b S hS hret) t⟩

theorem two_retainedProfile_uniform_degree (a₁ b₁ a₂ b₂ : ℝ)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (F : Finset (ℕ × ℕ)) :
    ∃ J : ℕ, ∀ W₁ W₂ : ℝ → ℂ,
      ∀ hs₁ : Function.support W₁ ⊆ Set.Icc a₁ b₁,
      ∀ hs₂ : Function.support W₂ ⊆ Set.Icc a₂ b₂,
      ∀ hW₁ : ContDiff ℝ ∞ W₁, ∀ hW₂ : ContDiff ℝ ∞ W₂,
      ∃ C : ℝ, 0 < C ∧ ∀ S₁ S₂ : ℝ, ∀ hS₁ : 0 < S₁, ∀ hS₂ : 0 < S₂,
      ∀ hret₁ : 1 ≤ S₁ * b₁, ∀ hret₂ : 1 ≤ S₂ * b₂, ∀ t : ℝ,
      F.sup (schwartzSeminormFamily ℝ ℝ ℂ)
        (retainedProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ S₁ hS₁ hret₁ t) +
      F.sup (schwartzSeminormFamily ℝ ℝ ℂ)
        (retainedProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ S₂ hS₂ hret₂ t) ≤ C * (1 + ‖t‖) ^ J := by
  obtain ⟨J₁, hJ₁⟩ := retainedProfile_uniform_degree a₁ b₁ ha₁ F
  obtain ⟨J₂, hJ₂⟩ := retainedProfile_uniform_degree a₂ b₂ ha₂ F
  refine ⟨max J₁ J₂, ?_⟩
  intro W₁ W₂ hs₁ hs₂ hW₁ hW₂
  obtain ⟨C₁, hC₁, hb₁⟩ := hJ₁ W₁ hs₁ hW₁
  obtain ⟨C₂, hC₂, hb₂⟩ := hJ₂ W₂ hs₂ hW₂
  refine ⟨C₁ + C₂, add_pos hC₁ hC₂, ?_⟩
  intro S₁ S₂ hS₁ hS₂ hret₁ hret₂ t
  have ht : 1 ≤ 1 + ‖t‖ := by linarith [norm_nonneg t]
  have h₁ := (hb₁ S₁ hS₁ hret₁ t).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht (le_max_left J₁ J₂)) hC₁.le)
  have h₂ := (hb₂ S₂ hS₂ hret₂ t).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht (le_max_right J₁ J₂)) hC₂.le)
  nlinarith

theorem retained_row_rectangle (η : Character) (m A₀ z : O)
    (W₁ W₂ : ℝ → ℂ) (t S₁ S₂ : ℝ) (hS₁ : 0 < S₁) (hS₂ : 0 < S₂) (A : ℂ) :
    A * (rowTwistedSum η m A₀ z W₁ t S₁ * rowTwistedSum η m A₀ z W₂ t S₂) =
      A * (rowTwistedSum η m A₀ z (dilated W₁ (clipDilation S₁)) t (clippedScale S₁) *
        rowTwistedSum η m A₀ z (dilated W₂ (clipDilation S₂)) t (clippedScale S₂)) := by
  rw [clipped_rowTwistedSum η m A₀ z W₁ t S₁ hS₁,
    clipped_rowTwistedSum η m A₀ z W₂ t S₂ hS₂]

theorem strict_subunit_row_rectangle_zero (η : Character) (m A₀ z : O)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ t S₁ S₂ : ℝ) (hS₁ : 0 < S₁) (hS₂ : 0 < S₂)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁) (hs₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hstrict : S₁ * b₁ < 1 ∨ S₂ * b₂ < 1) (A : ℂ) :
    A * (rowTwistedSum η m A₀ z W₁ t S₁ * rowTwistedSum η m A₀ z W₂ t S₂) = 0 := by
  rcases hstrict with h₁ | h₂
  · rw [strict_subunit_rowTwistedSum_zero η m A₀ z W₁ b₁ t S₁ hS₁ hs₁ h₁, zero_mul, mul_zero]
  · rw [strict_subunit_rowTwistedSum_zero η m A₀ z W₂ b₂ t S₂ hS₂ hs₂ h₂, mul_zero, mul_zero]

theorem two_retained_row_rectangles (η : Character) (m A₀ z : O)
    (W₁ W₂ : ℝ → ℂ) (t S₁ S₂ T₁ T₂ : ℝ)
    (hS₁ : 0 < S₁) (hS₂ : 0 < S₂) (hT₁ : 0 < T₁) (hT₂ : 0 < T₂) (A : ℂ) :
    ‖A * (rowTwistedSum η m A₀ z W₁ t S₁ * rowTwistedSum η m A₀ z W₂ t S₂ -
      rowTwistedSum η m A₀ z W₁ t T₁ * rowTwistedSum η m A₀ z W₂ t T₂)‖ ≤
      ‖A * (rowTwistedSum η m A₀ z (dilated W₁ (clipDilation S₁)) t (clippedScale S₁) *
        rowTwistedSum η m A₀ z (dilated W₂ (clipDilation S₂)) t (clippedScale S₂))‖ +
      ‖A * (rowTwistedSum η m A₀ z (dilated W₁ (clipDilation T₁)) t (clippedScale T₁) *
        rowTwistedSum η m A₀ z (dilated W₂ (clipDilation T₂)) t (clippedScale T₂))‖ := by
  rw [mul_sub, retained_row_rectangle η m A₀ z W₁ W₂ t S₁ S₂ hS₁ hS₂ A,
    retained_row_rectangle η m A₀ z W₁ W₂ t T₁ T₂ hT₁ hT₂ A]
  exact norm_sub_le _ _

theorem two_retained_row_energies (η : Character) (m A₀ : O)
    (W₁ W₂ : ℝ → ℂ) (t S₁ S₂ T₁ T₂ : ℝ)
    (hS₁ : 0 < S₁) (hS₂ : 0 < S₂) (hT₁ : 0 < T₁) (hT₂ : 0 < T₂)
    (rows : Finset O) (A : O → ℂ) (w : O → ℝ) (hw : ∀ z ∈ rows, 0 ≤ w z) :
    (∑ z ∈ rows, w z * ‖A z *
      (rowTwistedSum η m A₀ z W₁ t S₁ * rowTwistedSum η m A₀ z W₂ t S₂ -
        rowTwistedSum η m A₀ z W₁ t T₁ * rowTwistedSum η m A₀ z W₂ t T₂)‖ ^ 2) ≤
      2 * (∑ z ∈ rows, w z * ‖A z *
        (rowTwistedSum η m A₀ z (dilated W₁ (clipDilation S₁)) t (clippedScale S₁) *
          rowTwistedSum η m A₀ z (dilated W₂ (clipDilation S₂)) t (clippedScale S₂))‖ ^ 2) +
      2 * (∑ z ∈ rows, w z * ‖A z *
        (rowTwistedSum η m A₀ z (dilated W₁ (clipDilation T₁)) t (clippedScale T₁) *
          rowTwistedSum η m A₀ z (dilated W₂ (clipDilation T₂)) t (clippedScale T₂))‖ ^ 2) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro z hz
  have hb := two_retained_row_rectangles η m A₀ z W₁ W₂ t S₁ S₂ T₁ T₂ hS₁ hS₂ hT₁ hT₂ (A z)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hb 2
  have hnorm : ‖A z *
      (rowTwistedSum η m A₀ z W₁ t S₁ * rowTwistedSum η m A₀ z W₂ t S₂ -
        rowTwistedSum η m A₀ z W₁ t T₁ * rowTwistedSum η m A₀ z W₂ t T₂)‖ ^ 2 ≤
      2 * ‖A z *
        (rowTwistedSum η m A₀ z (dilated W₁ (clipDilation S₁)) t (clippedScale S₁) *
          rowTwistedSum η m A₀ z (dilated W₂ (clipDilation S₂)) t (clippedScale S₂))‖ ^ 2 +
      2 * ‖A z *
        (rowTwistedSum η m A₀ z (dilated W₁ (clipDilation T₁)) t (clippedScale T₁) *
          rowTwistedSum η m A₀ z (dilated W₂ (clipDilation T₂)) t (clippedScale T₂))‖ ^ 2 := by
    nlinarith [sq_nonneg
      (‖A z * (rowTwistedSum η m A₀ z (dilated W₁ (clipDilation S₁)) t (clippedScale S₁) *
          rowTwistedSum η m A₀ z (dilated W₂ (clipDilation S₂)) t (clippedScale S₂))‖ -
       ‖A z * (rowTwistedSum η m A₀ z (dilated W₁ (clipDilation T₁)) t (clippedScale T₁) *
          rowTwistedSum η m A₀ z (dilated W₂ (clipDilation T₂)) t (clippedScale T₂))‖)]
  convert mul_le_mul_of_nonneg_left hnorm (hw z hz) using 1; ring

theorem retained_volumeControl_le (Q : Ideal O) (χ : Character)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (S : ℝ) (hS : 0 < S) (hret : 1 ≤ S * b) (t : ℝ) :
    volumeControl Q χ (retainedProfile W a b ha hs hW S hS hret t) ≤
      (max 1 b) ^ (pvSeminorms.sup Prod.snd) *
        volumeControl Q χ (normPowerProfile W a b ha hs hW t) := by
  have h := normPowerProfile_dilated_finite W a b (max 1 b) (clipDilation S)
    ha (le_max_left _ _) (clipDilation_ge_one S hS) (clipDilation_le b S hS hret) hs hW t pvSeminorms
  change pvSeminorms.sup (schwartzSeminormFamily ℝ ℝ ℂ)
    (retainedProfile W a b ha hs hW S hS hret t) ≤ _ at h
  unfold volumeControl pvControl
  have hh := mul_le_mul_of_nonneg_left h
    (show 0 ≤ ((IdealMobiusDivisorSum.idealDivisors χ.modulus).card : ℝ) *
      (Nat.card (O ⧸ Ideal.span {fixedPeriod Q}) : ℝ) * pvConstant from
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) pvConstant_pos.le)
  convert hh using 1 <;> ring

theorem retained_volumeControl_uniform_degree (Q : Ideal O) (a b ε B : ℝ)
    (ha : 0 < a) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ J : ℕ, ∀ W : ℝ → ℂ, ∀ hs : Function.support W ⊆ Set.Icc a b,
      ∀ hW : ContDiff ℝ ∞ W, ∃ C : ℝ, 0 < C ∧
      ∀ Z : ℝ, 1 ≤ Z → ∀ χ : Character, (Ideal.absNorm χ.modulus : ℝ) ≤ Z ^ B →
      ∀ S : ℝ, ∀ hS : 0 < S, ∀ hret : 1 ≤ S * b, ∀ t : ℝ,
      volumeControl Q χ (retainedProfile W a b ha hs hW S hS hret t) ≤
        C * Z ^ ε * (1 + ‖t‖) ^ J := by
  obtain ⟨J, hJ⟩ := volumeControl_polynomial_height Q a b ε B ha hε hB
  refine ⟨J, ?_⟩
  intro W hs hW
  obtain ⟨C, hC, hbound⟩ := hJ W hs hW
  let D := (max 1 b) ^ (pvSeminorms.sup Prod.snd)
  have hD : 0 < D := pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _
  refine ⟨D * C, mul_pos hD hC, ?_⟩
  intro Z hZ χ hχ S hS hret t
  calc
    _ ≤ D * volumeControl Q χ (normPowerProfile W a b ha hs hW t) :=
      retained_volumeControl_le Q χ W a b ha hs hW S hS hret t
    _ ≤ D * (C * Z ^ ε * (1 + ‖t‖) ^ J) :=
      mul_le_mul_of_nonneg_left (hbound Z hZ χ hχ t) hD.le
    _ = _ := by ring

end SevenEighths.CenteredMomentRetainedProfile

end

end OAI
