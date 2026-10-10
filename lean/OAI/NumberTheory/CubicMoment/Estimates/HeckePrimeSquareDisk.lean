import OAI.NumberTheory.CubicMoment.Estimates.HeckeSquareDisk
import OAI.NumberTheory.CubicMoment.Estimates.HeckePrimeIdealEstimate

namespace OAI

/-! Sharp prime bounds from the actual square series and its proved disk
bound. This accommodates finite Euler corrections in angular characters. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

theorem hecke_smooth_prime_bound_square_disk :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
    ∀ (W : ℝ → ℂ) (_hW : HasCompactSupport W),
    tsupport W ⊆ Ioi 0 → ContDiff ℝ ∞ W →
    ∀ D : ℝ, PrimeMellinControl W D →
    ∀ {χ χdual : EisensteinIdealExponent → ℂ}, (∀ ν, ‖χ ν‖ ≤ 1) →
    χ 0=1 → (∀ ν κ, χ (ν+κ)=χ ν*χ κ) →
    (∀ ν, ‖χdual ν‖ ≤ 1) →
    ∀ {L Ldual L2 : ℂ → ℂ}, Differentiable ℂ L → Differentiable ℂ L2 →
    (∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s) →
    (∀ s : ℂ, 1 < s.re → L2 s=normDirichletSeries (fun ν => (χ ν)^2) idealExponentNorm s) →
    (∀ s : ℂ, 1 < s.re → Ldual s=normDirichletSeries χdual idealExponentNorm s) →
    ∀ {A A2 k k2 u T : ℝ} {ε ε2 : ℂ},
    0 < A → 0 < A2 → 0 ≤ k → 0 ≤ k2 → ‖ε‖ ≤ 1 → ‖ε2‖ ≤ 1 →
    10 ≤ u → A ≤ u → A2 ≤ u → k+7 ≤ u → k2+7 ≤ u → 4+2*(T+3) ≤ u →
    HeckeFunctionalEquation A k ε L Ldual →
    ShiftedCompletedHeckeFiniteOrder A k L →
    (∀ t z, ‖z‖ ≤ (7/8:ℝ) →
      ‖normalizedHeckeDisk L2 t z‖ ≤ normalizedHeckeDiskBound A2 k2 ε2 t) →
    ∀ X b : ℝ, 1 ≤ X → 1 < b → b < 1+δ → b ≤ 2 → 0 < T →
      ‖idealMangoldtSmooth χ W X‖ ≤ 6*D*
        (X^(1-heckeZeroFreeWidth u/2)*(heckeLogSquaredConstant*(1+Real.log u)^2)+
          X^b*(heckeLogSquaredConstant*(1+Real.log u)^2+(1/(b-1)+C))/T^2) := by
  obtain ⟨C,δ,hC,hδ,hbound⟩ := idealMangoldt_smooth_bound_controlled
  refine ⟨C,δ,hC,hδ,?_⟩
  intro W hW hpos hsm D hD χ χdual hχ hχ0 hχadd hχdual L Ldual L2 hL hL2
    hs hs2 hds A A2 k k2 u T ε ε2 hA hA2 hk hk2 hε hε2 hu huA huA2 huk huk2 huT
    hFE hcomp hdisk2 X b hX hb hbδ hb2 hT
  have hw := heckeZeroFreeWidth_pos hu
  have hw1 := heckeZeroFreeWidth_le_one hu
  have ha : 0 ≤ 1-heckeZeroFreeWidth u/2 := by linarith
  have hab : 1-heckeZeroFreeWidth u/2 ≤ b := by linarith
  apply hbound W hW hpos hsm D hD χ hχ hχ0 hχadd L hL hs X (1-heckeZeroFreeWidth u/2) b T
    (heckeLogSquaredConstant*(1+Real.log u)^2) hX ha hab hb hbδ hb2 hT
    (mul_nonneg heckeLogSquaredConstant_pos.le (sq_nonneg _))
  · intro s hmem
    have hparts : s.re ∈ Icc (1-heckeZeroFreeWidth u/2) b ∧ s.im ∈ Icc (-T) T := hmem
    have him : |s.im| ≤ T := abs_le.mpr hparts.2
    have hheight : 4+|s.im| ≤ u := by linarith
    have hheight2 : 4+|2*s.im| ≤ u := by
      rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
      linarith
    rw [←Complex.re_add_im s]
    apply hecke_zero_free_log_from_square_disk hχ hχ0 hχadd hχdual hL hL2
      hs hs2 hds hA hA2 hk hk2 hε hε2 hu huA huA2 huk huk2 hheight hheight2
      hFE hcomp hdisk2
    have hwidth := heckeZeroFreeWidth_le_log hu
    linarith [hparts.1.1]
  · intro s hmem
    have hparts : s.re ∈ Icc (1-heckeZeroFreeWidth u/2) b ∧ s.im ∈ Icc (-T) T := hmem
    rw [←Complex.re_add_im s]
    exact hecke_logDeriv_norm_uniform_from_square_disk hχ hχ0 hχadd hχdual hL hL2
      hs hs2 hds hA hA2 hk hk2 hε hε2 hu huA huA2 huk huk2 huT hFE hcomp hdisk2
      hparts.1.1 (hparts.1.2.trans hb2) (abs_le.mpr hparts.2)

theorem hecke_dyadic_prime_bound_of_square_disk :
    ∃ B c X0 : ℝ, 0 < B ∧ 0 < c ∧ c ≤ 1/2 ∧ 1 < X0 ∧
    ∀ {χ χdual : EisensteinIdealExponent → ℂ}, (∀ ν, ‖χ ν‖ ≤ 1) →
    χ 0=1 → (∀ ν κ, χ (ν+κ)=χ ν*χ κ) →
    (∀ ν, ‖χdual ν‖ ≤ 1) →
    ∀ {L Ldual L2 : ℂ → ℂ}, Differentiable ℂ L → Differentiable ℂ L2 →
    (∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s) →
    (∀ s : ℂ, 1 < s.re → L2 s=normDirichletSeries (fun ν => (χ ν)^2) idealExponentNorm s) →
    (∀ s : ℂ, 1 < s.re → Ldual s=normDirichletSeries χdual idealExponentNorm s) →
    ∀ {A A2 k k2 Q : ℝ} {ε ε2 : ℂ},
    0 < A → 0 < A2 → 0 ≤ k → 0 ≤ k2 → ‖ε‖ ≤ 1 → ‖ε2‖ ≤ 1 →
    1 ≤ Q → A ≤ Q → A2 ≤ Q → k+7 ≤ Q → k2+7 ≤ Q →
    HeckeFunctionalEquation A k ε L Ldual →
    ShiftedCompletedHeckeFiniteOrder A k L →
    (∀ t z, ‖z‖ ≤ (7/8:ℝ) →
      ‖normalizedHeckeDisk L2 t z‖ ≤ normalizedHeckeDiskBound A2 k2 ε2 t) →
    ∀ X : ℝ, X0 ≤ X →
      ‖idealMangoldtDyadic χ X‖ ≤
        B*(X*(Real.log (X*Q))^2*Real.exp (-c*Real.log X/primeContourDenominator Q X)) := by
  obtain ⟨C,δ,hC,hδ,hbound⟩ := hecke_smooth_prime_bound_square_disk
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
  intro χ χdual hχ hχ0 hχadd hχdual L Ldual L2 hL hL2
    hs hs2 hds A A2 k k2 Q ε ε2 hA hA2 hk hk2 hε hε2 hQ hQA hQA2 hQk hQk2
    hFE hcomp hdisk2 X hX
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
    (K*J^d) (hcontrol J hJ) hχ hχ0 hχadd hχdual hL hL2 hs hs2 hds
    hA hA2 hk hk2 hε hε2 hu.1 (hQA.trans hu.2.1) (hQA2.trans hu.2.1)
    (hQk.trans hu.2.1) (hQk2.trans hu.2.1) hu.2.2 hFE hcomp hdisk2
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

theorem hecke_full_prime_bound_of_square_disk :
    ∃ B c X0 : ℝ, 0 < B ∧ 0 < c ∧ c ≤ 1/4 ∧ 1 < X0 ∧
    ∀ {χ χdual : EisensteinIdealExponent → ℂ}, (∀ ν, ‖χ ν‖ ≤ 1) →
    χ 0=1 → (∀ ν κ, χ (ν+κ)=χ ν*χ κ) →
    (∀ ν, ‖χdual ν‖ ≤ 1) →
    ∀ {L Ldual L2 : ℂ → ℂ}, Differentiable ℂ L → Differentiable ℂ L2 →
    (∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s) →
    (∀ s : ℂ, 1 < s.re → L2 s=normDirichletSeries (fun ν => (χ ν)^2) idealExponentNorm s) →
    (∀ s : ℂ, 1 < s.re → Ldual s=normDirichletSeries χdual idealExponentNorm s) →
    ∀ {A A2 k k2 Q : ℝ} {ε ε2 : ℂ},
    0 < A → 0 < A2 → 0 ≤ k → 0 ≤ k2 → ‖ε‖ ≤ 1 → ‖ε2‖ ≤ 1 →
    1 ≤ Q → A ≤ Q → A2 ≤ Q → k+7 ≤ Q → k2+7 ≤ Q →
    HeckeFunctionalEquation A k ε L Ldual →
    ShiftedCompletedHeckeFiniteOrder A k L →
    (∀ t z, ‖z‖ ≤ (7/8:ℝ) →
      ‖normalizedHeckeDisk L2 t z‖ ≤ normalizedHeckeDiskBound A2 k2 ε2 t) →
    ∀ X : ℝ, X0 ≤ X →
      ‖idealMangoldtSum χ X‖ ≤
        B*(X*(Real.log (X*Q))^2*Real.exp (-c*Real.log X/primeContourDenominator Q X)) := by
  obtain ⟨B,c,Y0,hB,hc,hc1,hY0,hbound⟩ := hecke_dyadic_prime_bound_of_square_disk
  let X0 := max (Real.exp 2) (Y0^2)
  have hX0 : 1 < X0 := lt_of_lt_of_le
    (Real.one_lt_exp_iff.mpr (by norm_num)) (le_max_left _ _)
  refine ⟨B+24,c/2,X0,by linarith,by positivity,by linarith,hX0,?_⟩
  intro χ χdual hχ hχ0 hχadd hχdual L Ldual L2 hL hL2
    hs hs2 hds A A2 k k2 Q ε ε2 hA hA2 hk hk2 hε hε2 hQ hQA hQA2 hQk hQk2
    hFE hcomp hdisk2 X hX
  have hXp : 0 < X := zero_lt_one.trans (hX0.trans_le hX)
  have hLX : 2 ≤ Real.log X := by
    have hh := Real.log_le_log (Real.exp_pos 2) ((le_max_left _ _).trans hX)
    rwa [Real.log_exp] at hh
  have hwindow (t : ℝ) (ht : Y0 ≤ t) :
      ‖idealMangoldtDyadic χ t‖ ≤ B*primeCancellationWeight c Q t :=
    hbound hχ hχ0 hχadd hχdual hL hL2 hs hs2 hds hA hA2 hk hk2 hε hε2
      hQ hQA hQA2 hQk hQk2 hFE hcomp hdisk2 t ht
  exact idealMangoldt_full_from_dyadic χ hχ hB.le hc.le hc1 hQ hY0.le hwindow hXp hLX
    ((le_max_right _ _).trans hX)

theorem hecke_prime_ideal_bound_of_square_disk :
    ∃ B c X0 : ℝ, 0 < B ∧ 0 < c ∧ c ≤ 1/4 ∧ 1 < X0 ∧
    ∀ {χ χdual : EisensteinIdealExponent → ℂ}, (∀ ν, ‖χ ν‖ ≤ 1) →
    χ 0=1 → (∀ ν κ, χ (ν+κ)=χ ν*χ κ) →
    (∀ ν, ‖χdual ν‖ ≤ 1) →
    ∀ {L Ldual L2 : ℂ → ℂ}, Differentiable ℂ L → Differentiable ℂ L2 →
    (∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s) →
    (∀ s : ℂ, 1 < s.re → L2 s=normDirichletSeries (fun ν => (χ ν)^2) idealExponentNorm s) →
    (∀ s : ℂ, 1 < s.re → Ldual s=normDirichletSeries χdual idealExponentNorm s) →
    ∀ {A A2 k k2 Q : ℝ} {ε ε2 : ℂ},
    0 < A → 0 < A2 → 0 ≤ k → 0 ≤ k2 → ‖ε‖ ≤ 1 → ‖ε2‖ ≤ 1 →
    1 ≤ Q → A ≤ Q → A2 ≤ Q → k+7 ≤ Q → k2+7 ≤ Q →
    HeckeFunctionalEquation A k ε L Ldual →
    ShiftedCompletedHeckeFiniteOrder A k L →
    (∀ t z, ‖z‖ ≤ (7/8:ℝ) →
      ‖normalizedHeckeDisk L2 t z‖ ≤ normalizedHeckeDiskBound A2 k2 ε2 t) →
    ∀ X : ℝ, X0 ≤ X →
      ‖idealPrimeChebyshev χ X‖ ≤
        B*(X*(Real.log (X*Q))^2*Real.exp (-c*Real.log X/primeContourDenominator Q X)) := by
  obtain ⟨B,c,Y0,hB,hc,hc1,hY0,hbound⟩ := hecke_full_prime_bound_of_square_disk
  let X0 := max Y0 (Real.exp 2)
  have hX0 : 1 < X0 := hY0.trans_le (le_max_left _ _)
  refine ⟨B+idealPrimePowerErrorConstant,c,X0,add_pos hB idealPrimePowerErrorConstant_pos,
    hc,hc1,hX0,?_⟩
  intro χ χdual hχ hχ0 hχadd hχdual L Ldual L2 hL hL2
    hs hs2 hds A A2 k k2 Q ε ε2 hA hA2 hk hk2 hε hε2 hQ hQA hQA2 hQk hQk2
    hFE hcomp hdisk2 X hX
  have hXp : 0 < X := zero_lt_one.trans (hX0.trans_le hX)
  have hLX : 2 ≤ Real.log X := by
    have hh := Real.log_le_log (Real.exp_pos 2) ((le_max_right _ _).trans hX)
    rwa [Real.log_exp] at hh
  have hmain := hbound hχ hχ0 hχadd hχdual hL hL2 hs hs2 hds hA hA2 hk hk2 hε hε2
    hQ hQA hQA2 hQk hQk2 hFE hcomp hdisk2 X ((le_max_left _ _).trans hX)
  exact idealPrimeChebyshev_bound_of_mangoldt χ hχ hc.le hc1 hQ hXp hLX hmain

end CubicFirstMoment

end

end OAI
