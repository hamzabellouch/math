import OAI.NumberTheory.TwoPoint.Halasz.HalaszTypicalNoSmallSharp
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCommonFinalBand

namespace OAI

/-! The lower half of the short-window kernel uses distance information
only up to the original published cutoff and height. -/

namespace TwoPointCorrelations

open Finset Filter MeasureTheory
open scoped Classical

lemma halasz_dyadic_log_error_sharp {N k : ℕ} (hN : 2 ≤ N)
    (hL : 1 ≤ Real.log (N:ℝ)) (hLL : 1 ≤ Real.log (Real.log (N:ℝ)))
    (hNk : N ≤ k) (hk : k ≤ 2*N) :
    Real.log (Real.log (k:ℝ))/(Real.log k)^(1/80:ℝ) ≤
      2*(Real.log (Real.log (N:ℝ))/(Real.log N)^(1/80:ℝ)) := by
  obtain ⟨hlow,_,hu⟩ := mrt_dyadic_log_comparison hN hL hLL hNk hk
  have hLN0 : 0 < Real.log (N:ℝ) := by linarith
  have hlpow := Real.rpow_le_rpow hLN0.le hlow (show (0:ℝ)≤1/80 by norm_num)
  calc
    _ ≤ (2*Real.log (Real.log (N:ℝ)))/(Real.log k)^(1/80:ℝ) :=
      div_le_div_of_nonneg_right hu (by positivity)
    _ ≤ (2*Real.log (Real.log (N:ℝ)))/(Real.log N)^(1/80:ℝ) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hlpow
    _ = _ := by ring

theorem halasz_typical_kernel_bound_sharp
    (hprime : HalaszPrimeSparseInput) (hhigh : HalaszHighPrimeInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ F : ℕ → ℂ, F 1=1 → (∀ a b, 0<a → 0<b → F (a*b)=F a*F b) → OneBounded F →
      ∀ P Q : ℝ, 2 ≤ P → P ≤ Q → 1 < Real.log P → 1 ≤ Real.log Q →
        2 ≤ mrtBaseResolution P Q (1/100) →
      ∀ J : ℕ, 1 ≤ J →
      (∀ k ∈ ({N,2*N}:Finset ℕ),
        200*Real.log (Real.log k)+1 ≤ Real.log (mrtBandLower P Q J) ∧
        mrtBandUpper Q J ≤ Real.exp (Real.sqrt (Real.log k))) →
      ∀ X : ℕ, N ≤ X → X ≤ N^3 →
      ∀ M : ℝ, 0 ≤ M →
      (∀ u:ℝ, |u| ≤ X → M ≤ squaredDistance F (mrtArchimedeanTwist u) X) →
      ∀ k ∈ ({N,2*N}:Finset ℕ), ∀ v:ℝ, 0 ≤ v → v ≤ (k:ℝ)/4 →
      (∫ t in Set.Ioc (-v) v ∩ mrtNoSmallBand (mrtLogFamilyBins P Q (1/100))
          (mrtLogFamilyPolynomial
            (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F P Q (1/100))
          (mrtLogFamilyThreshold P Q (1/100)) J,
        ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Icc 1 J)
          (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) k t‖^2) ≤
        C*(Real.exp (-4*M/5)+
          Real.log (Real.log N)/(Real.log N)^(1/80:ℝ))*(v/k+1) := by
  obtain ⟨C,hC,henergy⟩ := halasz_original_typical_no_small_energy_sharp hprime hhigh
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp henergy
  refine ⟨2*C,by positivity,?_⟩
  have hlog : Tendsto (fun N:ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop N₀,eventually_ge_atTop 2,
    hlog.eventually (eventually_ge_atTop (1:ℝ)),
    (Real.tendsto_log_atTop.comp hlog).eventually (eventually_ge_atTop (1:ℝ))]
    with N hNN hN2 hL hLL
  intro F hF1 hFm hFb P Q hP hPQ hlogP hQ hres J hJ hband X hNX hXN M hM hd k hk v hv hvk
  have hNk : N ≤ k := by simp only [mem_insert,mem_singleton] at hk; omega
  have hkN : k ≤ 2*N := by simp only [mem_insert,mem_singleton] at hk; omega
  have hk0 : 0 < (k:ℝ) := by exact_mod_cast (show 0<k by omega)
  obtain ⟨hlo,hu⟩ := hband k hk
  have he := hN₀ k (hNN.trans hNk) F hF1 hFm hFb P Q hP hPQ hlogP hQ hres J hJ hlo hu
    X (by omega) (hXN.trans (by gcongr)) M hM
    (fun u hu => hd u (hu.trans (by
      have hh : (k:ℝ) ≤ 2*(N:ℝ) := by exact_mod_cast hkN
      have hNXr : (N:ℝ) ≤ X := by exact_mod_cast hNX
      linarith)))
  let B := mrtTypicalCoefficient (Icc 1 J)
    (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F
  let G := fun t:ℝ => ‖mrtDyadicPolynomial B k t‖^2
  let E := Set.Ioc (-v) v ∩ mrtNoSmallBand (mrtLogFamilyBins P Q (1/100))
    (mrtLogFamilyPolynomial
      (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F P Q (1/100))
    (mrtLogFamilyThreshold P Q (1/100)) J
  let E₀ := mrtActualNoSmall P Q J k F ∩ Set.Ioc (-((k:ℝ)/4)) ((k:ℝ)/4)
  have hsub : E ⊆ E₀ := by
    intro t ht
    refine ⟨⟨⟨?_,?_⟩,ht.2⟩,⟨?_,?_⟩⟩ <;> linarith [ht.1.1,ht.1.2]
  have hGc : Continuous G := (mrtExponentialPolynomial_continuous _ _ _).norm.pow 2
  have hGi : IntegrableOn G E₀ := by
    apply ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : -(k:ℝ)≤k)).mp
      (hGc.intervalIntegrable (-(k:ℝ)) k)).mono_set
    exact fun _ ht => ht.1.1
  have htrunc : (∫ t in E,G t) ≤ ∫ t in E₀,G t :=
    setIntegral_mono_set hGi (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
      (Filter.Eventually.of_forall hsub)
  have hδ := halasz_dyadic_log_error_sharp hN2 hL hLL hNk hkN
  let R := Real.exp (-4*M/5)
  let δ := Real.log (Real.log N)/(Real.log N)^(1/80:ℝ)
  have hR : 0 ≤ R := (Real.exp_pos _).le
  have hδ0 : 0 ≤ δ := div_nonneg (zero_le_one.trans hLL) (by positivity)
  have hb : (∫ t in E,G t) ≤ (2*C)*(R+δ) := by
    apply htrunc.trans (he.trans ?_)
    dsimp only [R,δ] at ⊢
    nlinarith [mul_le_mul_of_nonneg_left hδ hC.le, mul_nonneg hC.le hR]
  change (∫ t in E,G t) ≤ _
  apply hb.trans
  change (2*C)*(R+δ) ≤ (2*C)*(R+δ)*(v/k+1)
  exact le_mul_of_one_le_right (by positivity) (by
    have hh : 0 ≤ v/(k:ℝ) := div_nonneg hv hk0.le
    linarith)

end TwoPointCorrelations

end OAI
