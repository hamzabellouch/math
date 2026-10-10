import OAI.NumberTheory.CubicMoment.Estimates.HeckeDiskLowerBound
import OAI.NumberTheory.CubicMoment.Estimates.HeckeZeroFreeAlgebra

namespace OAI

/-! The zero-free step for a nonreal character and its square. The inputs
are the actual entire continuations and proved disk bounds; no prime-sum
or zero-free assertion is assumed. -/
noncomputable section
namespace CubicFirstMoment

def principalPoleConstant : ℝ := principalIdealZeta_real_logDeriv_bound.choose

def principalPoleRadius : ℝ := principalIdealZeta_real_logDeriv_bound.choose_spec.choose

lemma principalPoleConstant_pos : 0 < principalPoleConstant :=
  principalIdealZeta_real_logDeriv_bound.choose_spec.choose_spec.1

lemma principalPoleRadius_pos : 0 < principalPoleRadius :=
  principalIdealZeta_real_logDeriv_bound.choose_spec.choose_spec.2.1

lemma principalPoleBound (σ : ℝ) (hσ : 1 < σ) (hσδ : σ < 1+principalPoleRadius) :
    (-logDeriv principalIdealZeta (σ:ℂ)).re ≤ 1/(σ-1)+principalPoleConstant :=
  principalIdealZeta_real_logDeriv_bound.choose_spec.choose_spec.2.2 σ hσ hσδ

lemma diskLogDerivativeConstant_pos : 0 < diskLogDerivativeConstant := by
  have hl : 0 < Real.log ((7/8:ℝ)/(3/4)) := Real.log_pos (by norm_num)
  unfold diskLogDerivativeConstant
  positivity

def heckePairZeroFreeError (B B2 : ℝ) : ℝ :=
  1+3*principalPoleConstant+
    4*((diskLogDerivativeConstant/3)*Real.log B)+
    (diskLogDerivativeConstant/3)*Real.log B2+1/principalPoleRadius

lemma heckePairZeroFreeError_ge_one {B B2 : ℝ} (hB : 1 < B) (hB2 : 1 < B2) :
    1 ≤ heckePairZeroFreeError B B2 := by
  have h1 := principalPoleConstant_pos
  have h2 := principalPoleRadius_pos
  have h3 := diskLogDerivativeConstant_pos
  have hl1 := Real.log_pos hB
  have hl2 := Real.log_pos hB2
  have hp : 0 ≤ 3*principalPoleConstant+
      4*((diskLogDerivativeConstant/3)*Real.log B)+
      (diskLogDerivativeConstant/3)*Real.log B2+1/principalPoleRadius := by positivity
  unfold heckePairZeroFreeError
  linarith

theorem hecke_zero_free_of_disk_pair
    {χ : EisensteinIdealExponent → ℂ} (hχ : ∀ ν, ‖χ ν‖ ≤ 1)
    (hχ0 : χ 0=1) (hχadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ)
    {L L2 : ℂ → ℂ} (hL : Differentiable ℂ L) (hL2 : Differentiable ℂ L2)
    (hs : ∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s)
    (hs2 : ∀ s : ℂ, 1 < s.re → L2 s=normDirichletSeries (fun ν => (χ ν)^2) idealExponentNorm s)
    {B B2 t : ℝ} (hB : 1 < B) (hB2 : 1 < B2)
    (hb : ∀ z : ℂ, ‖z‖ ≤ (7/8:ℝ) → ‖normalizedHeckeDisk L t z‖ ≤ B)
    (hb2 : ∀ z : ℂ, ‖z‖ ≤ (7/8:ℝ) → ‖normalizedHeckeDisk L2 (2*t) z‖ ≤ B2)
    {β : ℝ} (hβ : 1-1/(32*heckePairZeroFreeError B B2) < β) :
    L ((β:ℂ)+(t:ℂ)*Complex.I) ≠ 0 := by
  intro hzero
  let E := heckePairZeroFreeError B B2
  have hE1 : 1 ≤ E := heckePairZeroFreeError_ge_one hB hB2
  have hE : 0 < E := lt_of_lt_of_le zero_lt_one hE1
  have hβ1 : β ≤ 1 := by
    simpa using heckeZero_real_le_one hχ hχ0 hχadd hs hzero
  have hw : 1/(32*E) ≤ (1/2:ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 32*E)).mpr
    linarith
  have hβhalf : (1/2:ℝ) ≤ β := by change 1-1/(32*E)<β at hβ; linarith
  let d : ℝ := 1/(4*E)
  have hd : 0 < d := by dsimp [d]; positivity
  have hd1 : d ≤ 1 := by
    dsimp [d]
    apply (div_le_iff₀ (by positivity : 0 < 4*E)).mpr
    linarith
  have hEδ : 1/principalPoleRadius < E := by
    have hC := principalPoleConstant_pos
    have hK := diskLogDerivativeConstant_pos
    have hl1 := Real.log_pos hB
    have hl2 := Real.log_pos hB2
    have hp : 0 < 1+3*principalPoleConstant+
        4*((diskLogDerivativeConstant/3)*Real.log B)+
        (diskLogDerivativeConstant/3)*Real.log B2 := by positivity
    dsimp [E,heckePairZeroFreeError]
    linarith
  have hdδ : d < principalPoleRadius := by
    have hδ := principalPoleRadius_pos
    have hδE : 1 < E*principalPoleRadius := (div_lt_iff₀ hδ).mp hEδ
    dsimp [d]
    apply (div_lt_iff₀ (by positivity : 0 < 4*E)).mpr
    nlinarith
  have hσ : 1 < 1+d := by linarith
  have hσ2 : 1+d ≤ 2 := by linarith
  have hlow := hecke_logDeriv_lower_of_disk hχ hχ0 hχadd hL hs hB hb hσ hσ2 hβhalf hzero
  have hχ2 : ∀ ν, ‖(χ ν)^2‖ ≤ 1 := by
    intro ν
    rw [norm_pow]
    exact pow_le_one₀ (_root_.norm_nonneg _) (hχ ν)
  have hχ20 : (χ 0)^2=1 := by rw [hχ0]; norm_num
  have hχ2add : ∀ ν κ, (χ (ν+κ))^2=(χ ν)^2*(χ κ)^2 := by
    intro ν κ
    rw [hχadd,mul_pow]
  have hlow2 := hecke_logDeriv_real_lower_of_disk hχ2 hχ20 hχ2add hL2 hs2 hB2 hb2 hσ hσ2
  have hpole := principalPoleBound (1+d) hσ (by linarith)
  have hpos := idealLogDeriv_vertical_341_nonneg χ hχ hχ0 hχadd hσ t
  rw [←idealSeries_logDeriv_eq (fun s hs => principalIdealZeta_right hs) (by simpa using hσ),
    ←idealSeries_logDeriv_eq hs (by simpa using hσ),
    ←idealSeries_logDeriv_eq hs2 (by simpa using hσ)] at hpos
  simp only [Complex.neg_re] at hpole hpos
  change 0 ≤ 3* -(logDeriv principalIdealZeta ((1+d:ℝ):ℂ)).re+
    4* -(logDeriv L (((1+d:ℝ):ℂ)+(t:ℂ)*Complex.I)).re+
    -(logDeriv L2 (((1+d:ℝ):ℂ)+(2*t:ℝ)*Complex.I)).re at hpos
  have heq : 1+d-β=d+(1-β) := by ring
  have hneg := hecke_zero_free_numerical hE (show 0 ≤ 1-β by linarith)
    (show 1-β ≤ 1/(32*E) by change 1-1/(32*E)<β at hβ; linarith)
  change 3/d-4/(d+(1-β))+E < 0 at hneg
  have hEbound : 3*principalPoleConstant+
      4*((diskLogDerivativeConstant/3)*Real.log B)+
      (diskLogDerivativeConstant/3)*Real.log B2 ≤ E := by
    have hδ := principalPoleRadius_pos
    have hi : 0 < 1/principalPoleRadius := one_div_pos.mpr hδ
    dsimp [E,heckePairZeroFreeError]
    linarith
  rw [heq] at hlow
  have hone : 1+d-1=d := by ring
  rw [hone] at hpole
  simp only [div_eq_mul_inv,one_mul] at hneg hlow hpole
  linarith only [hpos,hpole,hlow,hlow2,hEbound,hneg]

end CubicFirstMoment

end

end OAI
