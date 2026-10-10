import OAI.NumberTheory.TwoPoint.Fourier.MajorArcCorrectedMean
import OAI.NumberTheory.TwoPoint.Fourier.MajorArcCorrectedRate
import OAI.NumberTheory.TwoPoint.Fourier.MajorArcCorrectionGeometry
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWorkingParameters
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTShortSubdivisionSharp

namespace OAI

/-! The major arcs at the actual common parameter and working length.
The only band hypothesis is the geometry of the common final index,
which is supplied independently by `mrt_working_parameters`. -/
namespace TwoPointCorrelations

open Finset Filter

theorem major_arc_actual_working_mean
    (hprime : HalaszPrimeSparseInput) (hhigh : HalaszHighPrimeInput) :
    ∃ C : ℝ, 0 < C ∧ ∃ W₀ : ℝ, ∃ X₀ : ℕ,
    ∀ X H : ℕ, X₀ ≤ X → 10 ≤ H → H ≤ X →
      1 ≤ Real.log (H:ℝ) → 1 ≤ Real.log (Real.log (H:ℝ)) →
    ∀ M : ℝ, 0 ≤ M →
      let W := majorArcParameter (Real.log X) H M
      let h := majorArcWorkingLength H W
      let P := W^(500000:ℕ)
      let Q := (h:ℝ)/W^3
      W₀ ≤ W → ∀ Y : ℕ, X ≤ Y → Y+h ≤ 2*X → ∀ J : ℕ, 1 ≤ J →
      (∀ n : ℕ, ⌈Real.sqrt (X:ℝ)⌉₊ ≤ n → n ≤ 2*X →
        200*Real.log (Real.log n)+1 ≤ Real.log (mrtBandLower P Q J) ∧
        ∀ j ∈ Icc 1 J, mrtBandUpper Q j ≤ Real.exp (Real.sqrt (Real.log n))) →
    ∀ F : ℕ → ℂ, F 1=1 → Multiplicative F → OneBounded F →
      MRTDistanceLowerBound F X H M → ∀ r : ℤ, ∀ q : ℕ,
      0 < q → (q:ℝ) ≤ W → ∀ β : ℝ, |β| ≤ W/((h:ℝ)*q) →
      shortExponentialIntegral (mrtTypicalCoefficient (Icc 1 J)
        (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) Y h ((r:ℝ)/q+β) ≤
      C*(Y:ℝ)*h*(Real.exp (-M/20)+mrtShortError X H) := by
  obtain ⟨C,hC,N₀,hcorrect⟩ := major_arc_corrected_typical_mean hprime hhigh
  obtain ⟨W₁,X₁,hparams⟩ := mrt_working_parameters
  obtain ⟨W₂,hpower⟩ := eventually_atTop.mp (major_arc_working_length_power 252)
  let D := 2500*mrtCorrectionBound*(C+1)*(1+4*Real.pi)
  have hCB : 0 < mrtCorrectionBound := Real.exp_pos _
  have hD : 0 < D := by dsimp [D]; positivity
  have hlog : Tendsto (fun X:ℕ => Real.log X) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlarge := (hlog.eventually (major_arc_corrected_published_rate C hC.le)).and
    (hlog.eventually major_arc_parameter_rate)
  obtain ⟨X₂,hX₂⟩ := eventually_atTop.mp
    (hlarge.and (mrt_working_length_add_two_below_sqrt.and
      (mrt_working_quotient_boundary.and
        ((hlog.eventually (eventually_ge_atTop (1:ℝ))).and
          (eventually_ge_atTop (max X₁ (max 2 (N₀^2))))))))
  refine ⟨2*D+21,by positivity,max 2 (max W₁ W₂),X₂,?_⟩
  intro X H hXX₂ hH hHX hLH hLL M hM
  dsimp only
  intro hW₀ Y hXY hY J hJ hbands F hF1 hFm hFb hd r q hq hqW β hβ
  let W := majorArcParameter (Real.log X) H M
  let h := majorArcWorkingLength H W
  let K := ⌈Real.sqrt (X:ℝ)⌉₊
  let P := W^(500000:ℕ)
  let Q := (h:ℝ)/W^3
  change Y+h ≤ 2*X at hY
  obtain ⟨hfinal,houter⟩ := hX₂ X hXX₂
  obtain ⟨hcap,hboundary,hLX,hxmin⟩ := houter
  have hX : 2 ≤ X := (le_max_left _ _).trans ((le_max_right _ _).trans hxmin)
  have hXX : X₁ ≤ X := (le_max_left _ _).trans hxmin
  have hN : N₀^2 ≤ X := (le_max_right _ _).trans ((le_max_right _ _).trans hxmin)
  have hW : 2 ≤ W := (le_max_left _ _).trans hW₀
  have hWW₁ : W₁ ≤ W := (le_max_left _ _).trans ((le_max_right _ _).trans hW₀)
  have hWW₂ : W₂ ≤ W := (le_max_right _ _).trans ((le_max_right _ _).trans hW₀)
  have hW1 : 1 ≤ W := by linarith
  have hW0 : 0 < W := by linarith
  obtain ⟨_,hWH,hWX,_⟩ := major_arc_parameter_bounds hLX hLH hM
  have hpow : W^252 ≤ (h:ℝ) := hpower W hWW₂ H (by omega) hLH hWH
  have hpow250 : W^250 ≤ (h:ℝ) :=
    (pow_le_pow_right₀ hW1 (by norm_num : (250:ℕ)≤252)).trans hpow
  have hh : 0 < h := by
    have hp : (0:ℝ) < h := (pow_pos hW0 252).trans_le hpow
    exact_mod_cast hp
  have hhX : h ≤ X := (major_arc_working_length_le H W).trans hHX
  have hcapK : h+2 ≤ K := hcap W hW1 hWX H
  have hKX : K ≤ X := by
    apply Nat.ceil_le.mpr
    exact Real.sqrt_le_self_iff.mpr (Or.inr (by exact_mod_cast (show 1≤X by omega)))
  have hK : 1 ≤ K := by omega
  have hNK : N₀ ≤ K := by
    have hn : (N₀:ℝ)^2 ≤ X := by exact_mod_cast hN
    have hs : (N₀:ℝ) ≤ Real.sqrt (X:ℝ) := by
      nlinarith only [hn,Real.sq_sqrt (Nat.cast_nonneg X),Real.sqrt_nonneg (X:ℝ),(show (0:ℝ)≤N₀ from Nat.cast_nonneg N₀)]
    exact_mod_cast hs.trans (Nat.le_ceil (Real.sqrt (X:ℝ)))
  obtain ⟨hprimepars,_,_⟩ := hparams W hWW₁ H (by omega) hLH hWH X hXX hWX
  obtain ⟨hP,hPQ,hLP,hLQ,hbudget,hres100,hres⟩ := hprimepars
  have hQK : 2*Q ≤ K := by
    have hp := (hparams W hWW₁ H (by omega) hLH hWH X hXX hWX).2.1.2
    exact hp
  have hWK : W ≤ K :=
    ((le_self_pow₀ hW1 (by decide : (252:ℕ)≠0)).trans hpow).trans
      (by exact_mod_cast (show h≤K by omega))
  have hWR : W^9 ≤ mrtBaseResolution P Q (1/100) :=
    (pow_le_pow_right₀ hW1 (by norm_num : (9:ℕ)≤100)).trans hres100
  have hWP : W^5 ≤ P := pow_le_pow_right₀ hW1 (by norm_num : (5:ℕ)≤500000)
  let s := mrtArcSubdivisionLength h W
  obtain ⟨hs, hsh, hslo, _⟩ := mrt_arc_subdivision_bounds hW hpow250
  let V := Y+h-s
  have hVH : s ≤ V := by dsimp [V]; omega
  have hwin := major_arc_correction_window_data hW hpow hslo hsh hVH hcapK
    (le_refl Q) hq hqW
  have houter' := major_arc_correction_outer (show X≤V by dsimp [V]; omega)
    (show V+1≤2*X by dsimp [V]; omega)
    (fun d hdp hdD => by
      have hdpow : (d:ℝ) ≤ W^5 :=
        (show (d:ℝ) ≤ mrtCorrectionCutoff W by exact_mod_cast hdD).trans
          (mrt_correction_cutoff_bounds hW).2.2
      simpa only [K,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using
        hboundary W hW1 hWX d hdp hdpow)
  have hqmax : (q:ℝ) ≤ mrtModulusCutoff X H :=
    hqW.trans (le_min hWX hWH)
  have hqinv : 1/(q:ℝ) ≤ 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1)
      (show (1:ℝ)≤q by exact_mod_cast hq)
  have hphase : |β| *(s:ℝ) ≤ 1 :=
    (mrt_arc_subdivision_phase hW hpow250 hq hβ).trans hqinv
  have hm := hcorrect X V s K H hX hLX hVH hNK hK (Nat.le_ceil _)
    P Q hP hPQ hLP hLQ hbudget hres hQK J hJ hbands W hW hWK hWR hWP
    hwin.1 houter' q hq hqW hqmax hwin.2 F hF1 hFm hFb M hM hd r β hphase
  let E := Real.exp (-M/20)+mrtShortError X H
  have hE : 0 ≤ E := by
    unfold E mrtShortError
    positivity
  have hrate := hfinal.1 H M hLH hLL hM
  have hm' : shortExponentialIntegral (mrtTypicalCoefficient (Icc 1 J)
      (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F)
      V s ((r:ℝ)/q+β) ≤ (D*E)*(V:ℝ)*s := by
    apply hm.trans
    have hrate' : mrtCorrectionBound*(4*(1+4*Real.pi)*
        (4*C*(Real.sqrt W*(1+Real.log W))*(Real.exp (-2*M/5)+
          Real.sqrt (Real.log (Real.log X)/(Real.log X)^(1/80:ℝ))+W⁻¹)+3/W)+
          5*W^(-5/4:ℝ)) ≤ D*E := by
      simpa only [W,D,E,mrtShortError,add_assoc] using hrate
    exact major_arc_rate_volume (Nat.cast_nonneg V) (Nat.cast_nonneg s) hrate'
  have hsfull := mrt_arc_subdivision_integral_sharp _
    (mrtTypicalCoefficient_oneBounded _ _ F hFb) Y h (hhX.trans hXY) hW hpow250
    (mul_nonneg hD.le hE) ((r:ℝ)/q+β) hm'
  have htail : W^(-1/4:ℝ) ≤ 21*E := by
    have hk := hfinal.2 H M hLH hLL hM
    have hsmall : W^(-1/4:ℝ) ≤ majorArcWorkingError W := by
      apply (Real.rpow_le_rpow_of_exponent_le hW1 (show (-1/4:ℝ)≤-1/5 by norm_num)).trans
      exact le_mul_of_one_le_left (Real.rpow_nonneg hW0.le _)
        (by linarith [Real.log_nonneg hW1])
    have hshort : 0 ≤ Real.log (Real.log (H:ℝ))/Real.log H := by positivity
    have hlogerr : 0 ≤ (Real.log X)^(-1/700:ℝ) := Real.rpow_nonneg (by linarith) _
    have hexp := Real.exp_pos (-M/20)
    rw [mul_div_assoc] at hk
    dsimp [E,mrtShortError]
    linarith only [hk,hsmall,hshort,hlogerr,hexp]
  calc
    _ ≤ (Y:ℝ)*h*(2*(D*E)+W^(-1/4:ℝ)) := by simpa only [neg_div] using hsfull
    _ ≤ (Y:ℝ)*h*(2*(D*E)+21*E) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl htail) (by positivity)
    _ = _ := by dsimp only [E]; ring

end TwoPointCorrelations

end OAI
