import OAI.NumberTheory.DirichletL.Moments.FrequencyScaleSupremum
import OAI.NumberTheory.DirichletL.Moments.PositiveSummability

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentRadialPolynomialEnergy
open HeckeFamily HeckeDyadic CenteredMomentFrequencyScaleSupremum
open CenteredMomentPositiveSummability ConcreteTraceCRT
open HeckeInverseAmplification
local notation "O" => HeckeFamily.O

lemma polynomial_bounded (W : ℝ→ℂ) (a b X : ℝ) (hb : 0≤b) (hX : 0<X)
    (hs : Function.support W⊆Set.Icc a b) :
    ∃B : ℝ,0≤B ∧ ∀χ : Character,∀t : ℝ,‖polynomial χ false W X 0 t‖≤B := by
  let l:=Real.log X
  let S:=scaleSupport l b
  have hx : Real.exp l=X := Real.exp_log hX
  have hc : ∀I : Ideal O,I≠0 → W ((I.absNorm:ℝ)/Real.exp l)≠0 → I∈S :=
    scaleSupport_cover W a b l l hb hs le_rfl
  let B:=‖Complex.exp (-(l:ℂ)/2)‖*∑I∈S,‖W ((I.absNorm:ℝ)*Real.exp (-l))‖
  refine ⟨B,by dsimp [B];positivity,?_⟩
  intro χ t
  rw [←hx,frequencyScaleSum_eq_polynomial χ false W t S l hc,norm_mul,
    FourierBridge.logPhase_norm,one_mul]
  unfold frequencyScaleSum
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro I hI
  rw [norm_mul,norm_mul,FourierBridge.logPhase_norm,mul_one]
  exact mul_le_of_le_one_left (norm_nonneg _) (coefficient_norm_le χ false I)

lemma pair_radial_summable (χ : O→Character) (P : O→ℂ) (t omega : O→ℝ)
    (W₁ W₂ : ℝ→ℂ) (a b c d X Y Pbound : ℝ)
    (hb : 0≤b) (hd : 0≤d) (hX : 0<X) (hY : 0<Y)
    (hs₁ : Function.support W₁⊆Set.Icc a b) (hs₂ : Function.support W₂⊆Set.Icc c d)
    (hP : ∀z,‖P z‖≤Pbound) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    Summable (fun z:O=>if keep z then
      ‖polynomial (χ z) false W₁ X 0 (t z)*polynomial (χ z) false W₂ Y 0 (omega z)*P z‖^2*
        (Φ (‖eisEmbedding z‖^2/K)).re else 0) := by
  obtain ⟨B₁,hB₁,h₁⟩:=polynomial_bounded W₁ a b X hb hX hs₁
  obtain ⟨B₂,hB₂,h₂⟩:=polynomial_bounded W₂ c d Y hd hY hs₂
  apply bounded_radial_summable _ (B₁*B₂*Pbound) _ keep Φ K hK
  intro z
  rw [norm_mul,norm_mul]
  exact mul_le_mul (mul_le_mul (h₁ _ _) (h₂ _ _) (norm_nonneg _) hB₁)
    (hP z) (norm_nonneg _) (mul_nonneg hB₁ hB₂)

lemma single_radial_summable (χ : O→Character) (P : O→ℂ) (t : O→ℝ)
    (W : ℝ→ℂ) (a b X Pbound : ℝ) (hb : 0≤b) (hX : 0<X)
    (hs : Function.support W⊆Set.Icc a b) (hP : ∀z,‖P z‖≤Pbound)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    Summable (fun z:O=>if keep z then ‖polynomial (χ z) false W X 0 (t z)*P z‖^2*
      (Φ (‖eisEmbedding z‖^2/K)).re else 0) := by
  obtain ⟨B,hB,hh⟩:=polynomial_bounded W a b X hb hX hs
  apply bounded_radial_summable _ (B*Pbound) _ keep Φ K hK
  intro z
  rw [norm_mul]
  exact mul_le_mul (hh _ _) (hP z) (norm_nonneg _) hB

end SevenEighths.CenteredMomentRadialPolynomialEnergy

end

end OAI
