import OAI.NumberTheory.CubicMoment.Estimates.HeckePrimeControlled
import OAI.NumberTheory.CubicMoment.Estimates.PrimeContourOptimization
import OAI.NumberTheory.CubicMoment.Estimates.PrimeDyadicError

namespace OAI

/-! Sharp dyadic prime-ideal cancellation from the actual Hecke functional
equations for a character and its square. No prime estimate is assumed. -/
noncomputable section
namespace CubicFirstMoment

theorem hecke_dyadic_prime_bound_of_analytic_pair :
    ∃ B c X0 : ℝ, 0 < B ∧ 0 < c ∧ c ≤ 1/2 ∧ 1 < X0 ∧
    ∀ {χ χdual χ2dual : EisensteinIdealExponent → ℂ}, (∀ ν, ‖χ ν‖ ≤ 1) →
    χ 0=1 → (∀ ν κ, χ (ν+κ)=χ ν*χ κ) →
    (∀ ν, ‖χdual ν‖ ≤ 1) → (∀ ν, ‖χ2dual ν‖ ≤ 1) →
    ∀ {L Ldual L2 L2dual : ℂ → ℂ}, Differentiable ℂ L → Differentiable ℂ L2 →
    (∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s) →
    (∀ s : ℂ, 1 < s.re → L2 s=normDirichletSeries (fun ν => (χ ν)^2) idealExponentNorm s) →
    (∀ s : ℂ, 1 < s.re → Ldual s=normDirichletSeries χdual idealExponentNorm s) →
    (∀ s : ℂ, 1 < s.re → L2dual s=normDirichletSeries χ2dual idealExponentNorm s) →
    ∀ {A A2 k k2 Q : ℝ} {ε ε2 : ℂ},
    0 < A → 0 < A2 → 0 ≤ k → 0 ≤ k2 → ‖ε‖ ≤ 1 → ‖ε2‖ ≤ 1 →
    1 ≤ Q → A ≤ Q → A2 ≤ Q → k+7 ≤ Q → k2+7 ≤ Q →
    HeckeFunctionalEquation A k ε L Ldual →
    HeckeFunctionalEquation A2 k2 ε2 L2 L2dual →
    ShiftedCompletedHeckeFiniteOrder A k L → ShiftedCompletedHeckeFiniteOrder A2 k2 L2 →
    ∀ X : ℝ, X0 ≤ X →
      ‖idealMangoldtDyadic χ X‖ ≤
        B*(X*(Real.log (X*Q))^2*Real.exp (-c*Real.log X/primeContourDenominator Q X)) := by
  obtain ⟨C,δ,hC,hδ,hbound⟩ := hecke_smooth_prime_bound_controlled
  obtain ⟨d,K,hK,hcontrol⟩ := primeDyadicWeight_mellin_control
  let M := 6*K*((1+Real.exp 1)*(heckeLogSquaredConstant*(2+Real.log 32)^2)+Real.exp 1*(1+C))
  let X0 := Real.exp (max 2 (2/δ))
  have hM : 0 < M := by
    have hlog32 : 0 < 2+Real.log 32 := by positivity
    dsimp [M]
    positivity [heckeLogSquaredConstant_pos]
  have hlog6 : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
  have hX0 : 1 < X0 := by
    apply Real.one_lt_exp_iff.mpr
    exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨M+64*(1+Real.log 6),primeSmoothingRate d,X0,by positivity,
    primeSmoothingRate_pos d,(primeSmoothingRate_bounds d).2.2,hX0,?_⟩
  intro χ χdual χ2dual hχ hχ0 hχadd hχdual hχ2dual L Ldual L2 L2dual hL hL2
    hs hs2 hds hds2 A A2 k k2 Q ε ε2 hA hA2 hk hk2 hε hε2 hQ hQA hQA2 hQk hQk2
    hFE hFE2 hcomp hcomp2 X hX
  have hXp : 0 < X := zero_lt_one.trans (hX0.trans_le hX)
  have hLX : max 2 (2/δ) ≤ Real.log X := by
    have hh := Real.log_le_log (Real.exp_pos (max 2 (2/δ))) hX
    rwa [Real.log_exp] at hh
  have hLX1 : 1 ≤ Real.log X := by linarith [le_max_left (2:ℝ) (2/δ)]
  have hLXpos : 0 < Real.log X := by linarith
  have hrec : 1/Real.log X < δ := by
    have hh : 2 ≤ Real.log X*δ := (div_le_iff₀ hδ).mp ((le_max_right _ _).trans hLX)
    exact (div_lt_iff₀ hLXpos).mpr (by linarith)
  have hXe : Real.exp 1 ≤ X := by
    have hh := Real.exp_le_exp.mpr hLX1
    rwa [Real.exp_log hXp] at hh
  let J := primeSmoothingParameter d Q X
  have hJ : 1 ≤ J := primeSmoothingParameter_ge_one d hQ hLX1
  have hu := primeContourSize_bounds hQ (X := X)
  have hpre := hbound (primeDyadicWeight J hJ) (primeDyadicWeight_compact hJ)
    (primeDyadicWeight_positive_support hJ) (primeDyadicWeight_smooth hJ)
    (K*J^d) (hcontrol J hJ) hχ hχ0 hχadd hχdual hχ2dual hL hL2 hs hs2 hds hds2
    hA hA2 hk hk2 hε hε2 hu.1 (hQA.trans hu.2.1) (hQA2.trans hu.2.1)
    (hQk.trans hu.2.1) (hQk2.trans hu.2.1) hu.2.2 hFE hFE2 hcomp hcomp2
    X (1+1/Real.log X) (by linarith)
    (by have hh := one_div_pos.mpr hLXpos; linarith) (by linarith)
    (by have hh := (div_le_one hLXpos).mpr hLX1; linarith) (Real.exp_pos _)
  have hmain : ‖idealMangoldtSmooth χ (primeDyadicWeight J hJ) X‖ ≤
      M*(X*(Real.log (X*Q))^2*
        Real.exp (-primeSmoothingRate d*Real.log X/primeContourDenominator Q X)) :=
    hpre.trans (primeContour_optimized_bound d hK.le hC.le hQ hXp hLX1)
  have herr := (idealMangoldt_dyadic_smoothing_bound χ hχ hJ hXe).trans
    (primeSmoothing_cutoff_error d hQ hXp hLX1)
  calc
    _ = ‖idealMangoldtSmooth χ (primeDyadicWeight J hJ) X-
        (idealMangoldtSmooth χ (primeDyadicWeight J hJ) X-idealMangoldtDyadic χ X)‖ := by
      congr 1
      abel
    _ ≤ ‖idealMangoldtSmooth χ (primeDyadicWeight J hJ) X‖+
        ‖idealMangoldtSmooth χ (primeDyadicWeight J hJ) X-idealMangoldtDyadic χ X‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add hmain herr
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
