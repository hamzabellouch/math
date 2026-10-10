import OAI.NumberTheory.CubicMoment.Estimates.IdealHeatMellin
import OAI.NumberTheory.CubicMoment.Estimates.ShiftedThetaCompletion
import OAI.NumberTheory.CubicMoment.Estimates.ThetaMellinGrowth

namespace OAI

/-! Entire angular Hecke completion from the actual normalized heat
transformation. No continuation or finite-order assumption is used here. -/
noncomputable section
open Filter Asymptotics MeasureTheory
namespace CubicFirstMoment

def idealHeatFEPair {A κ : ℝ} (hA : 0 < A) (hκ : 0 ≤ κ)
    (χ χdual : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (hχdual : ∀ ν, ‖χdual ν‖ ≤ 1)
    {ε : ℂ} (hε : ε ≠ 0)
    (hFE : ∀ t : ℝ, 0 < t →
      idealHeatTheta A κ χ (1/t) = ε*(t:ℂ)*idealHeatTheta A κ χdual t) : WeakFEPair ℂ where
  f := idealHeatTheta A κ χ
  g := idealHeatTheta A κ χdual
  k := 1
  ε := ε
  f₀ := 0
  g₀ := 0
  hf_int := (idealHeatTheta_continuousOn hA hκ χ hχ).locallyIntegrableOn measurableSet_Ioi
  hg_int := (idealHeatTheta_continuousOn hA hκ χdual hχdual).locallyIntegrableOn measurableSet_Ioi
  hk := zero_lt_one
  hε := hε
  hf_top r := by simpa only [sub_zero] using idealHeatTheta_isBigO_rpow hA hκ χ hχ r
  hg_top r := by simpa only [sub_zero] using idealHeatTheta_isBigO_rpow hA hκ χdual hχdual r
  h_feq t ht := by simpa only [Real.rpow_one,smul_eq_mul] using hFE t ht

lemma shiftedThetaHeckeL_eq_series {A κ : ℝ} (hA : 0 < A) (hκ : 0 ≤ κ)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    shiftedThetaHeckeL A κ (mellin (idealHeatTheta A κ χ)) s =
      normDirichletSeries χ idealExponentNorm s := by
  rw [shiftedThetaHeckeL,idealHeatTheta_mellin hA hκ χ hχ hs,Complex.cpow_neg]
  have hAp : (A:ℂ)^s ≠ 0 := Complex.cpow_ne_zero_iff.mpr
    (Or.inl (Complex.ofReal_ne_zero.mpr hA.ne'))
  have hG := Complex.Gamma_ne_zero_of_re_pos
    (show 0 < (s+(κ:ℂ)).re by simp only [Complex.add_re,Complex.ofReal_re]; linarith)
  field_simp

lemma idealHeat_completion {A κ : ℝ} (hA : 0 < A) (hκ : 0 ≤ κ)
    (χ χdual : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (hχdual : ∀ ν, ‖χdual ν‖ ≤ 1)
    {ε : ℂ} (hε : ε ≠ 0)
    (hFE : ∀ t : ℝ, 0 < t →
      idealHeatTheta A κ χ (1/t) = ε*(t:ℂ)*idealHeatTheta A κ χdual t) :
    ∃ L Ldual : ℂ → ℂ, Differentiable ℂ L ∧
      (∀ s : ℂ, 1 < s.re → L s = normDirichletSeries χ idealExponentNorm s) ∧
      (∀ s : ℂ, 1 < s.re → Ldual s = normDirichletSeries χdual idealExponentNorm s) ∧
      HeckeFunctionalEquation A κ ε L Ldual ∧ ShiftedCompletedHeckeFiniteOrder A κ L := by
  let P := idealHeatFEPair hA hκ χ χdual hχ hχdual hε hFE
  have hP : IsStrongFEPair P := ⟨rfl,rfl⟩
  refine ⟨shiftedThetaHeckeL A κ P.Λ,shiftedThetaHeckeL A κ P.symm.Λ,
    shiftedThetaHeckeL_differentiable hA hP.differentiable_Λ,?_,?_,
    shiftedThetaHeckeL_functionalEquation hA P rfl,?_⟩
  · intro s hs
    rw [hP.Λ_eq]
    exact shiftedThetaHeckeL_eq_series hA hκ χ hχ hs
  · intro s hs
    rw [hP.symm_Λ_eq]
    exact shiftedThetaHeckeL_eq_series hA hκ χdual hχdual hs
  · obtain ⟨C,hC,hfb⟩ := idealHeatTheta_norm_bound hA hκ χ hχ
    obtain ⟨D,hD,hgb⟩ := idealHeatTheta_norm_bound hA hκ χdual hχdual
    have hf (t : ℝ) (ht : 1 ≤ t) :
        ‖idealHeatTheta A κ χ t‖ ≤ C*Real.exp (-(1/(4*A))*t) := by
      convert hfb t ht using 1
      congr 2
      ring
    have hg (t : ℝ) (ht : 1 ≤ t) :
        ‖idealHeatTheta A κ χdual t‖ ≤ D*Real.exp (-(1/(4*A))*t) := by
      convert hgb t ht using 1
      congr 2
      ring
    obtain ⟨B,hB,hbound⟩ := theta_mellin_growth (show 0 < 1/(4*A) by positivity)
      hC hD (idealHeatTheta_continuousOn hA hκ χ hχ)
      (idealHeatTheta_continuousOn hA hκ χdual hχdual) hf hg hFE
    apply shiftedThetaHeckeL_finiteOrder hA hP.differentiable_Λ hB
    intro s
    rw [hP.Λ_eq]
    exact hbound s

end CubicFirstMoment

end

end OAI
