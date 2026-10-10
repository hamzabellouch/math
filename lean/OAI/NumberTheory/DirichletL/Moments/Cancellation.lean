import OAI.NumberTheory.DirichletL.Moments.MaskedVolume

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentCancellation
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open IdealMobiusDivisorSum UniqueFactorizationMonoid QuadraticInitialBound
open CenteredMomentPrimary CenteredMomentMaskedVolume

def maskedSum (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' I : Ideal O, (if IsCoprime I R then (1 : ℂ) else 0) *
    (primaryIdealCharacter c χ I * W ((Ideal.absNorm I : ℝ) / X))

def maskedDensity (c : O) (hc : c ≠ 0) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) : ℂ :=
  letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  (∑ D ∈ idealDivisors R, (moebius D : ℂ) * primaryIdealCharacter c χ D /
    (Ideal.absNorm D : ℂ)) * (1 / (‖eisEmbedding c‖ ^ 2 : ℂ)) *
      ∑ r : O ⧸ Ideal.span {c}, primaryResidueValue c χ r

def maskedError (c : O) (hc : c ≠ 0) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (W : 𝓢(ℝ, ℂ)) : ℝ :=
  letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  ((idealDivisors R).card : ℝ) *
    ((∑ r : O ⧸ Ideal.span {c}, ‖primaryResidueValue c χ r‖) * pvControl W)

lemma maskedError_nonneg (c : O) (hc : c ≠ 0) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (W : 𝓢(ℝ, ℂ)) : 0 ≤ maskedError c hc χ R W := by
  unfold maskedError
  exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg
    (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (pvControl_nonneg W))

theorem maskedSum_volume (c : O) (hc : c ≠ 0) (h3 : (3 : O) ∣ c)
    [Nontrivial (O ⧸ Ideal.span {c})] (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (hR : R ≠ 0) (W : 𝓢(ℝ, ℂ)) (b X : ℝ) (hX : 0 < X)
    (hs : Function.support (W : ℝ → ℂ) ⊆ Set.Iic b) :
    ‖maskedSum c χ R W X - (X : ℂ) *
      (maskedDensity c hc χ R * paperRadialFourier W 0)‖ ≤ maskedError c hc χ R W := by
  have h := masked_primary_ideal_volume_error c hc h3 χ R hR W b X hX hs
  convert h using 1
  unfold maskedSum maskedDensity
  congr 1
  ring
  all_goals rfl

theorem masked_rectangle_saving
    (c : O) (hc : c ≠ 0) (h3 : (3 : O) ∣ c)
    [Nontrivial (O ⧸ Ideal.span {c})] (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (hR : R ≠ 0) (W₁ W₂ : 𝓢(ℝ, ℂ)) (b₁ b₂ : ℝ)
    (hs₁ : Function.support (W₁ : ℝ → ℂ) ⊆ Set.Iic b₁)
    (hs₂ : Function.support (W₂ : ℝ → ℂ) ⊆ Set.Iic b₂)
    (X₁ X₂ Y₁ Y₂ T L : ℝ) (hL : 1 ≤ L)
    (hX₁ : L ≤ X₁) (hX₂ : L ≤ X₂) (hY₁ : L ≤ Y₁) (hY₂ : L ≤ Y₂)
    (hprodX : X₁ * X₂ = T) (hprodY : Y₁ * Y₂ = T) :
    let E := maskedError c hc χ R W₁ + maskedError c hc χ R W₂
    let C := ‖maskedDensity c hc χ R * paperRadialFourier W₁ 0‖ +
      ‖maskedDensity c hc χ R * paperRadialFourier W₂ 0‖ + E
    ‖maskedSum c χ R W₁ X₁ * maskedSum c χ R W₂ X₂ -
      maskedSum c χ R W₁ Y₁ * maskedSum c χ R W₂ Y₂‖ ≤ 4 * E * C * (T / L) := by
  let E := maskedError c hc χ R W₁ + maskedError c hc χ R W₂
  let v₁ := maskedDensity c hc χ R * paperRadialFourier W₁ 0
  let v₂ := maskedDensity c hc χ R * paperRadialFourier W₂ 0
  let C := ‖v₁‖ + ‖v₂‖ + E
  have hE₁ := maskedError_nonneg c hc χ R W₁
  have hE₂ := maskedError_nonneg c hc χ R W₂
  have hE : 0 ≤ E := add_nonneg hE₁ hE₂
  have hC : 0 ≤ C := add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) hE
  have hL0 : 0 < L := by linarith
  have ha₁ (X : ℝ) (hX : L ≤ X) : ‖maskedSum c χ R W₁ X - (X : ℂ) * v₁‖ ≤ E :=
    (maskedSum_volume c hc h3 χ R hR W₁ b₁ X (lt_of_lt_of_le hL0 hX) hs₁).trans
      (le_add_of_nonneg_right hE₂)
  have ha₂ (X : ℝ) (hX : L ≤ X) : ‖maskedSum c χ R W₂ X - (X : ℂ) * v₂‖ ≤ E :=
    (maskedSum_volume c hc h3 χ R hR W₂ b₂ X (lt_of_lt_of_le hL0 hX) hs₂).trans
      (le_add_of_nonneg_left hE₁)
  have hv₁ (X : ℝ) (hX : L ≤ X) : ‖(X : ℂ) * v₁‖ ≤ C * X := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_trans hL0.le hX)]
    have hv : ‖v₁‖ ≤ C := by dsimp only [C]; linarith [norm_nonneg v₂]
    nlinarith [mul_le_mul_of_nonneg_right hv (le_trans hL0.le hX)]
  have hv₂ (X : ℝ) (hX : L ≤ X) : ‖maskedSum c χ R W₂ X‖ ≤ C * X := by
    have hb := norm_le_norm_sub_add (maskedSum c χ R W₂ X) ((X : ℂ) * v₂)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_trans hL0.le hX)] at hb
    have hEX : E ≤ E * X := by nlinarith [mul_le_mul_of_nonneg_left (le_trans hL hX) hE]
    have hbound := ha₂ X hX
    dsimp only [C]
    nlinarith [mul_nonneg (norm_nonneg v₁) (le_trans hL0.le hX)]
  have hmain : ((X₁ : ℂ) * v₁) * ((X₂ : ℂ) * v₂) =
      ((Y₁ : ℂ) * v₁) * ((Y₂ : ℂ) * v₂) := by
    have hp : (X₁ : ℂ) * X₂ = (Y₁ : ℂ) * Y₂ := by exact_mod_cast hprodX.trans hprodY.symm
    calc
      _ = ((X₁ : ℂ) * X₂) * (v₁ * v₂) := by ring
      _ = ((Y₁ : ℂ) * Y₂) * (v₁ * v₂) := by rw [hp]
      _ = _ := by ring
  exact CenteredMoment.centered_saving_of_approx _ _ _ _ _ _ _ _
    X₁ X₂ Y₁ Y₂ T L C E hmain hC hE (ha₁ X₁ hX₁) (ha₂ X₂ hX₂)
    (ha₁ Y₁ hY₁) (ha₂ Y₂ hY₂) (hv₂ X₂ hX₂) (hv₁ X₁ hX₁)
    (hv₂ Y₂ hY₂) (hv₁ Y₁ hY₁) hL0 hX₁ hX₂ hY₁ hY₂ hprodX hprodY

end SevenEighths.CenteredMomentCancellation
end

end OAI
