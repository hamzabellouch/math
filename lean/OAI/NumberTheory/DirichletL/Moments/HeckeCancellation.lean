import OAI.NumberTheory.DirichletL.Moments.HeckeVolume
import OAI.NumberTheory.DirichletL.Moments.Cancellation

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentHeckeCancellation
open HeckeFamily CenteredMomentHeckeVolume ConcreteTraceCRT EisensteinSchwartzPoisson
open IdealMobiusDivisorSum QuadraticInitialBound
local notation "O" => ActualEisensteinCubic.O

def idealSum (χ : Character) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' I : Ideal O, idealCoeff χ I*W ((Ideal.absNorm I:ℝ)/X)

def volumeControl (Q : Ideal O) (χ : Character) (W : 𝓢(ℝ,ℂ)) : ℝ :=
  ((idealDivisors χ.modulus).card:ℝ)*(Nat.card (O ⧸ Ideal.span {fixedPeriod Q}):ℝ)*pvControl W

def densityControl (Q : Ideal O) (χ : Character) : ℝ :=
  ((idealDivisors χ.modulus).card:ℝ)*(Nat.card (O ⧸ Ideal.span {fixedPeriod Q}):ℝ)/‖eisEmbedding (fixedPeriod Q)‖^2

lemma volumeControl_nonneg (Q : Ideal O) (χ : Character) (W : 𝓢(ℝ,ℂ)) : 0 ≤ volumeControl Q χ W :=
  mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (pvControl_nonneg W)

lemma densityControl_nonneg (Q : Ideal O) (χ : Character) : 0 ≤ densityControl Q χ := by
  unfold densityControl
  positivity

theorem actual_rectangle_saving (η χ ψ : Character) (Q : Ideal O) (hQ : Q ≠ 0)
    (hQψ : Q ≤ ψ.modulus) (hind : CenteredExceptionalProfile.InducedBy χ ψ)
    (m A₀ z : O) (hmLam : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2:O) ∣ m)
    (hrow : ∀ n, elementCoeff χ n=CanonicalRowCompletion.rowTwist
      (HeckeRowClosure.elementHom η) m 1 (A₀*z) n)
    (W₁ W₂ : 𝓢(ℝ,ℂ)) (b₁ b₂ : ℝ)
    (hs₁ : Function.support (W₁:ℝ→ℂ) ⊆ Set.Iic b₁)
    (hs₂ : Function.support (W₂:ℝ→ℂ) ⊆ Set.Iic b₂)
    (X₁ X₂ Y₁ Y₂ T L : ℝ) (hL : 1 ≤ L)
    (hX₁ : L ≤ X₁) (hX₂ : L ≤ X₂) (hY₁ : L ≤ Y₁) (hY₂ : L ≤ Y₂)
    (hprodX : X₁*X₂=T) (hprodY : Y₁*Y₂=T) :
    let E := volumeControl Q χ W₁+volumeControl Q χ W₂
    let C := densityControl Q χ*(‖paperRadialFourier W₁ 0‖+‖paperRadialFourier W₂ 0‖)+E
    ‖idealSum χ W₁ X₁*idealSum χ W₂ X₂-idealSum χ W₁ Y₁*idealSum χ W₂ Y₂‖ ≤
      4*E*C*(T/L) := by
  let E := volumeControl Q χ W₁+volumeControl Q χ W₂
  let D := densityControl Q χ
  let C := D*(‖paperRadialFourier W₁ 0‖+‖paperRadialFourier W₂ 0‖)+E
  let v₁ := density (fixedPeriod Q) (fixedPeriod_ne_zero Q hQ) ψ χ.modulus*paperRadialFourier W₁ 0
  let v₂ := density (fixedPeriod Q) (fixedPeriod_ne_zero Q hQ) ψ χ.modulus*paperRadialFourier W₂ 0
  have hE₁ := volumeControl_nonneg Q χ W₁
  have hE₂ := volumeControl_nonneg Q χ W₂
  have hE : 0 ≤ E := add_nonneg hE₁ hE₂
  have hD : 0 ≤ D := densityControl_nonneg Q χ
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hL0 : 0 < L := by linarith
  have hden : ‖density (fixedPeriod Q) (fixedPeriod_ne_zero Q hQ) ψ χ.modulus‖ ≤ D :=
    density_norm_le _ _ ψ χ.modulus χ.modulus_ne_bot
  have hvol₁ : ‖v₁‖ ≤ D*‖paperRadialFourier W₁ 0‖ := by
    dsimp only [v₁]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hden (norm_nonneg _)
  have hvol₂ : ‖v₂‖ ≤ D*‖paperRadialFourier W₂ 0‖ := by
    dsimp only [v₂]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hden (norm_nonneg _)
  have ha₁ (X : ℝ) (hX : L ≤ X) : ‖idealSum χ W₁ X-(X:ℂ)*v₁‖ ≤ E :=
    (actual_induced_volume η χ ψ Q hQ hQψ hind m A₀ z hmLam hm2 hrow W₁ b₁ X
      (lt_of_lt_of_le hL0 hX) hs₁).trans (le_add_of_nonneg_right hE₂)
  have ha₂ (X : ℝ) (hX : L ≤ X) : ‖idealSum χ W₂ X-(X:ℂ)*v₂‖ ≤ E :=
    (actual_induced_volume η χ ψ Q hQ hQψ hind m A₀ z hmLam hm2 hrow W₂ b₂ X
      (lt_of_lt_of_le hL0 hX) hs₂).trans (le_add_of_nonneg_left hE₁)
  have hv₁ (X : ℝ) (hX : L ≤ X) : ‖(X:ℂ)*v₁‖ ≤ C*X := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (le_trans hL0.le hX)]
    have hv : ‖v₁‖ ≤ C := by
      dsimp only [C]
      nlinarith [mul_nonneg hD (norm_nonneg (paperRadialFourier W₂ 0))]
    nlinarith [mul_le_mul_of_nonneg_right hv (le_trans hL0.le hX)]
  have hv₂ (X : ℝ) (hX : L ≤ X) : ‖idealSum χ W₂ X‖ ≤ C*X := by
    have hb := norm_le_norm_sub_add (idealSum χ W₂ X) ((X:ℂ)*v₂)
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (le_trans hL0.le hX)] at hb
    have hEX : E ≤ E*X := by nlinarith [mul_le_mul_of_nonneg_left (le_trans hL hX) hE]
    have hbound := ha₂ X hX
    have hv := mul_le_mul_of_nonneg_left hvol₂ (le_trans hL0.le hX)
    dsimp only [C]
    nlinarith [mul_nonneg (mul_nonneg hD (norm_nonneg (paperRadialFourier W₁ 0))) (le_trans hL0.le hX)]
  have hmain : ((X₁:ℂ)*v₁)*((X₂:ℂ)*v₂)=((Y₁:ℂ)*v₁)*((Y₂:ℂ)*v₂) := by
    have hp : (X₁:ℂ)*X₂=(Y₁:ℂ)*Y₂ := by exact_mod_cast hprodX.trans hprodY.symm
    calc
      _ = ((X₁:ℂ)*X₂)*(v₁*v₂) := by ring
      _ = ((Y₁:ℂ)*Y₂)*(v₁*v₂) := by rw [hp]
      _ = _ := by ring
  exact CenteredMoment.centered_saving_of_approx _ _ _ _ _ _ _ _
    X₁ X₂ Y₁ Y₂ T L C E hmain hC hE (ha₁ X₁ hX₁) (ha₂ X₂ hX₂)
    (ha₁ Y₁ hY₁) (ha₂ Y₂ hY₂) (hv₂ X₂ hX₂) (hv₁ X₁ hX₁)
    (hv₂ Y₂ hY₂) (hv₁ Y₁ hY₁) hL0 hX₁ hX₂ hY₁ hY₂ hprodX hprodY

end SevenEighths.CenteredMomentHeckeCancellation

end

end OAI
