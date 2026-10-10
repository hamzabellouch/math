import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.ConditionalShellField
import OAI.Analysis.CoulombIonization.FieldAnalysis.ShellBiasField

namespace OAI

noncomputable section

namespace CoulombAtom

lemma innerScale_price_le {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    innerScale (1/s^4) s + (1/s^4)^2 ≤ 4*(1/s^4)^2 := by
  have h82 : s^8 ≤ s^2 := pow_le_pow_of_le_one hs.le hs1 (by omega)
  have h85 : s^8 ≤ s^5 := pow_le_pow_of_le_one hs.le hs1 (by omega)
  have h2 := one_div_le_one_div_of_le (pow_pos hs 8) h82
  have h5 := one_div_le_one_div_of_le (pow_pos hs 8) h85
  have he : (1/s^4)/s = 1/s^5 := by field_simp
  have he2 : (1/s^4)^2 = 1/s^8 := by field_simp
  dsimp only [innerScale]
  rw [he,he2]
  linarith

lemma shellMean_price_absorb_bound {C R s u : ℝ} (hC : 1 ≤ C)
    (hR : 16*Real.sqrt C ≤ R) (hs : 0 < s) (hs1 : s ≤ 1) (hu : R*s ≤ u) :
    (4*s/u)*Real.sqrt (C*(innerScale (1/s^4) s+(1/s^4)^2)) ≤ (1/s^4)/2 := by
  have hCp : 0 < C := by linarith
  have hsq : 0 < Real.sqrt C := Real.sqrt_pos.2 hCp
  have hRp : 0 < R := (mul_pos (by norm_num : (0:ℝ)<16) hsq).trans_le hR
  have hup : 0 < u := (mul_pos hRp hs).trans_le hu
  have hlam : 0 < 1/s^4 := by positivity
  have hh := mul_le_mul_of_nonneg_left (innerScale_price_le hs hs1) hCp.le
  have he : Real.sqrt (C*(4*(1/s^4)^2)) = 2*Real.sqrt C*(1/s^4) := by
    have hsqr : (2*Real.sqrt C*(1/s^4))^2 = C*(4*(1/s^4)^2) := by
      rw [mul_pow,mul_pow,Real.sq_sqrt hCp.le]
      ring
    rw [←hsqr,Real.sqrt_sq (by positivity)]
  calc
    _ ≤ (4*s/u)*Real.sqrt (C*(4*(1/s^4)^2)) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hh) (by positivity)
    _ = (8*Real.sqrt C*s/u)*(1/s^4) := by rw [he]; ring
    _ ≤ (1/2:ℝ)*(1/s^4) := by
      apply mul_le_mul_of_nonneg_right _ hlam.le
      apply (div_le_iff₀ hup).2
      have h1 := mul_le_mul_of_nonneg_right hR hs.le
      linarith
    _ = _ := by ring

open MeasureTheory Filter
open scoped BigOperators InnerProductSpace
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph
  FermionMultiplier.apply FermionLipschitzMultiplier.apply oneBodySquareTotal
  formEnergy energy sectorExcessOperator fermionGraphValue shellBiasMultiplier
  rawFormPair formMass weightedMass oneBodyGradientError corePriceExcess shellMeanField innerScale

def actualShellRadius : ℝ := max 16 (16*Real.sqrt (Classical.choose exists_actual_shellMean_constant))
lemma actualShellRadius_ge : 16 ≤ actualShellRadius := le_max_left _ _

lemma shellBias_pair_absorb {Z s u : ℝ} {N : ℕ} (hZ : 0 ≤ Z)
    (hs : 0 < s) (hs1 : s ≤ 1) (hu : actualShellRadius*s ≤ u)
    (F : fermionGraph N) (p : SmoothMultiplier spaceDirections)
    (hc : HasCompactSupport p.value)
    (hp : ∀ y, p.value y ≠ 0 → u/2 ≤ ‖y‖ ∧ ‖y‖ ≤ 4*u)
    (hm : 0 < formMass (graphFormVector ((shellBiasMultiplier p hc).apply F)))
    (hex : corePriceExcess Z (1/s^4) (graphFormVector ((shellBiasMultiplier p hc).apply F)) ≤
      (1/s^4)*formMass (graphFormVector ((shellBiasMultiplier p hc).apply F))) :
    rawFormPair (graphFormVector ((shellBiasMultiplier p hc).apply F)) (shellMeanField p Z s) ≤
      formMass (graphFormVector ((shellBiasMultiplier p hc).apply F))*((1/s^4)/2) := by
  let C := Classical.choose exists_actual_shellMean_constant
  have hC : 1 ≤ C := (Classical.choose_spec exists_actual_shellMean_constant).1
  have hmean := (Classical.choose_spec exists_actual_shellMean_constant).2
  have hlam : 0 < 1/s^4 := by positivity
  have hsu : 16*s ≤ u := (mul_le_mul_of_nonneg_right actualShellRadius_ge hs.le).trans hu
  have hsa : s < u/4 := by linarith
  let psi := graphFormVector ((shellBiasMultiplier p hc).apply F)
  let m := formMass psi
  let phi := scaleForm (Real.sqrt m)⁻¹ psi
  have hphi : FormAdmissible phi := (graphFormVector_sobolev _).normalize hm
  have hphim : formMass phi = 1 := by unfold formMass; exact hphi.2.2.2.2.1
  have he : max (corePriceExcess Z (1/s^4) phi) 0 ≤ 1/s^4 :=
    shellBias_normalized_excess hZ hlam F p hc hm hex
  have hb := hmean Z (1/s^4) N phi hphi.sobolevFermion hphim
    hZ hlam (1/s^4) s u hlam.le hs hsa he p hp
  have hn := shellMean_price_absorb_bound hC (le_max_right 16 (16*Real.sqrt C)) hs hs1 hu
  have hb' : rawFormPair phi (shellMeanField p Z s) ≤ (1/s^4)/2 := hb.trans hn
  have heq : rawFormPair phi (shellMeanField p Z s) = m⁻¹*rawFormPair psi (shellMeanField p Z s) := by
    rw [rawFormPair_scale,inv_pow,Real.sq_sqrt hm.le]
  have hi := mul_le_mul_of_nonneg_left hb' hm.le
  rw [heq,←mul_assoc,mul_inv_cancel₀ hm.ne',one_mul] at hi
  exact hi

 theorem actual_shell_number {Z s u : ℝ} {N : ℕ} (hZ : 0 ≤ Z)
    (hs : 0 < s) (hs1 : s ≤ 1) (hu : actualShellRadius*s ≤ u)
    (hN : PriceMinimizes (energy Z) (1/s^4) (N+1))
    (F : fermionGraph (N+1)) (p : SmoothMultiplier spaceDirections)
    (hc : HasCompactSupport p.value)
    (hp : ∀ y, p.value y ≠ 0 → u/2 ≤ ‖y‖ ∧ ‖y‖ ≤ 4*u) :
    (1/s^4)*weightedMass F (oneBodySquareTotal p).value ≤ oneBodyGradientError p F+
      2*(⟪(oneBodySquareTotal p).apply F,sectorExcessOperator Z (N+1) F⟫_ℂ).re := by
  have hlam : 0 < 1/s^4 := by positivity
  have hsu : 16*s ≤ u := (mul_le_mul_of_nonneg_right actualShellRadius_ge hs.le).trans hu
  let psi := graphFormVector ((shellBiasMultiplier p hc).apply F)
  let m := formMass psi
  let X := (1/2:ℝ)*oneBodyGradientError p F+
    (⟪(oneBodySquareTotal p).apply F,sectorExcessOperator Z (N+1) F⟫_ℂ).re
  have hX : corePriceExcess Z (1/s^4) psi ≤ X := shellBias_price_excess_le hN p hc F
  have hXn : 0 ≤ X := (corePriceExcess_nonneg (graphFormVector_sobolev _) hZ hlam).trans hX
  have hmass : m = weightedMass F (oneBodySquareTotal p).value := formMass_shellBias p hc F
  have hmasslam := congrArg (fun t : ℝ => (1/s^4)*t) hmass
  have hgoal : (1/s^4)*m ≤ 2*X := by
    by_contra hfalse
    have hlt : 2*X < (1/s^4)*m := lt_of_not_ge hfalse
    have hm : 0 < m := (mul_pos_iff_of_pos_left hlam).mp
      (lt_of_le_of_lt (by linarith : (0:ℝ) ≤ 2*X) hlt)
    have hb := shellBias_pair_absorb hZ hs hs1 hu F p hc hp hm (hX.trans (by linarith))
    have hfield := shellInnerIntegral_le_biasPair p hc Z (by linarith : 0 < u/4)
      (by linarith : s ≤ u/4) (by linarith : s < 2*s) (fun y hy => by linarith [(hp y hy).1]) F
    have hstep : energy Z (N+1)+(1/s^4) ≤ energy Z N := by
      have hh := hN N
      rw [Nat.cast_add,Nat.cast_one] at hh
      nlinarith only [hh]
    have hshell := quantum_shell_inner_field_residual hZ p F (2*s) hstep
    have hf := hfield.trans hb
    change _ ≤ m*((1/s^4)/2) at hf
    dsimp only [X] at hlt
    nlinarith only [hshell,hf,hlt,hmasslam]
  dsimp only [X] at hgoal
  linarith only [hgoal,hmasslam]

 theorem exists_actual_shell_number_constant : ∃ R : ℝ, 16 ≤ R ∧
    ∀ (Z s u : ℝ) (N : ℕ), 0 ≤ Z → 0 < s → s ≤ 1 → R*s ≤ u →
    PriceMinimizes (energy Z) (1/s^4) (N+1) →
    ∀ (F : fermionGraph (N+1)) (p : SmoothMultiplier spaceDirections),
      HasCompactSupport p.value →
      (∀ y, p.value y ≠ 0 → u/2 ≤ ‖y‖ ∧ ‖y‖ ≤ 4*u) →
      (1/s^4)*weightedMass F (oneBodySquareTotal p).value ≤ oneBodyGradientError p F+
        2*(⟪(oneBodySquareTotal p).apply F,sectorExcessOperator Z (N+1) F⟫_ℂ).re :=
  ⟨actualShellRadius,actualShellRadius_ge,fun _ _ _ _ => actual_shell_number⟩

end CoulombAtom

end

end OAI
