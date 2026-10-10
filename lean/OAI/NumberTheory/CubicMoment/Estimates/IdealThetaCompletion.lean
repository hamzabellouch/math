import OAI.NumberTheory.CubicMoment.Estimates.IdealThetaMellin
import OAI.NumberTheory.CubicMoment.Estimates.HeckeThetaCompletion

namespace OAI

/-! Analytic continuation from the exact ideal theta transformation. The
hypotheses concern the theta series itself and follow from the
finite-character Poisson formula. -/
noncomputable section
open Filter Asymptotics MeasureTheory
namespace CubicFirstMoment

def idealThetaFEPair {A : ℝ} (hA : 0 < A)
    (χ χdual : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (hχdual : ∀ ν, ‖χdual ν‖ ≤ 1)
    {ε : ℂ} (hε : ε ≠ 0)
    (hFE : ∀ t : ℝ, 0 < t →
      idealTheta A χ (1/t) = ε*(t:ℂ)*idealTheta A χdual t) : WeakFEPair ℂ where
  f := idealTheta A χ
  g := idealTheta A χdual
  k := 1
  ε := ε
  f₀ := 0
  g₀ := 0
  hf_int := (idealTheta_continuousOn hA χ hχ).locallyIntegrableOn measurableSet_Ioi
  hg_int := (idealTheta_continuousOn hA χdual hχdual).locallyIntegrableOn measurableSet_Ioi
  hk := zero_lt_one
  hε := hε
  hf_top r := by simpa only [sub_zero] using idealTheta_isBigO_rpow hA χ hχ r
  hg_top r := by simpa only [sub_zero] using idealTheta_isBigO_rpow hA χdual hχdual r
  h_feq t ht := by simpa only [Real.rpow_one,smul_eq_mul] using hFE t ht

lemma idealThetaFEPair_strong {A : ℝ} (hA : 0 < A)
    (χ χdual : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (hχdual : ∀ ν, ‖χdual ν‖ ≤ 1)
    {ε : ℂ} (hε : ε ≠ 0)
    (hFE : ∀ t : ℝ, 0 < t →
      idealTheta A χ (1/t) = ε*(t:ℂ)*idealTheta A χdual t) :
    IsStrongFEPair (idealThetaFEPair hA χ χdual hχ hχdual hε hFE) := ⟨rfl,rfl⟩

lemma thetaHeckeL_eq_series {A : ℝ} (hA : 0 < A)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    thetaHeckeL A (mellin (idealTheta A χ)) s =
      normDirichletSeries χ idealExponentNorm s := by
  rw [thetaHeckeL,idealTheta_mellin hA χ hχ hs,Complex.cpow_neg]
  have hAp : (A:ℂ)^s ≠ 0 := Complex.cpow_ne_zero_iff.mpr
    (Or.inl (Complex.ofReal_ne_zero.mpr hA.ne'))
  have hG := Complex.Gamma_ne_zero_of_re_pos (show 0 < s.re by linarith)
  field_simp

lemma idealThetaFEPair_hecke {A : ℝ} (hA : 0 < A)
    (χ χdual : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (hχdual : ∀ ν, ‖χdual ν‖ ≤ 1)
    {ε : ℂ} (hε : ε ≠ 0)
    (hFE : ∀ t : ℝ, 0 < t →
      idealTheta A χ (1/t) = ε*(t:ℂ)*idealTheta A χdual t) :
    let P := idealThetaFEPair hA χ χdual hχ hχdual hε hFE
    Differentiable ℂ (thetaHeckeL A P.Λ) ∧
    Differentiable ℂ (thetaHeckeL A P.symm.Λ) ∧
    (∀ s : ℂ, 1 < s.re → thetaHeckeL A P.Λ s =
      normDirichletSeries χ idealExponentNorm s) ∧
    (∀ s : ℂ, 1 < s.re → thetaHeckeL A P.symm.Λ s =
      normDirichletSeries χdual idealExponentNorm s) ∧
    HeckeFunctionalEquation A 0 ε (thetaHeckeL A P.Λ) (thetaHeckeL A P.symm.Λ) := by
  dsimp only
  let P := idealThetaFEPair hA χ χdual hχ hχdual hε hFE
  have hP := idealThetaFEPair_strong hA χ χdual hχ hχdual hε hFE
  have he := thetaHeckeL_entire P hP hA
  refine ⟨he.1,he.2,?_,?_,thetaHeckeL_functionalEquation hA P rfl⟩
  · intro s hs
    rw [hP.Λ_eq]
    exact thetaHeckeL_eq_series hA χ hχ hs
  · intro s hs
    rw [hP.symm_Λ_eq]
    exact thetaHeckeL_eq_series hA χdual hχdual hs

end CubicFirstMoment

end

end OAI
