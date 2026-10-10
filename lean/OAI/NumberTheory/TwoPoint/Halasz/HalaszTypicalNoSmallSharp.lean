import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTNoSmallFull
import OAI.NumberTheory.TwoPoint.Halasz.HalaszLargeMinimum
import OAI.NumberTheory.TwoPoint.Halasz.HalaszTypicalNearRestriction

namespace OAI

/-! Low-frequency no-small energy with the original published distance
cutoff and height. The upper half of the kernel is handled by its decay. -/
namespace TwoPointCorrelations

open Filter Finset MeasureTheory
open scoped Classical

theorem halasz_original_typical_no_small_energy_sharp
    (hprime : HalaszPrimeSparseInput) (hhigh : HalaszHighPrimeInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ F : ℕ → ℂ, F 1=1 → (∀ a b, 0<a → 0<b → F (a*b)=F a*F b) → OneBounded F →
      ∀ P Q : ℝ, 2 ≤ P → P ≤ Q → 1 < Real.log P → 1 ≤ Real.log Q →
        2 ≤ mrtBaseResolution P Q (1/100) →
      ∀ J : ℕ, 1 ≤ J →
        200*Real.log (Real.log N)+1 ≤ Real.log (mrtBandLower P Q J) →
        mrtBandUpper Q J ≤ Real.exp (Real.sqrt (Real.log N)) →
      ∀ X : ℕ, N ≤ 2*X → X ≤ N^3 →
      ∀ M : ℝ, 0 ≤ M →
        (∀ v : ℝ, |v| ≤ (N:ℝ)/2 → M ≤ squaredDistance F (mrtArchimedeanTwist v) X) →
      (∫ t in mrtActualNoSmall P Q J N F ∩ Set.Ioc (-((N:ℝ)/4)) ((N:ℝ)/4),
        ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Icc 1 J)
          (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) N t‖^2) ≤
        C*(Real.exp (-4*M/5)+
          Real.log (Real.log N)/(Real.log N)^(1/80:ℝ)) := by
  obtain ⟨C₁,hC₁,hnear⟩ := halasz_typical_near_original_restriction
  obtain ⟨C₂,hC₂,hoff⟩ := mrt_no_small_off_center_energy_sharp hprime hhigh
  obtain ⟨C₃,hC₃,hfull⟩ := mrt_no_small_full_energy_sharp hprime
  refine ⟨C₁+C₂+C₃,by positivity,?_⟩
  have hlog : Tendsto (fun N:ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hnear,hoff,hfull,halasz_large_minimum_extra_cofactor,
    hlog.eventually (eventually_ge_atTop (1:ℝ)),
    (Real.tendsto_log_atTop.comp hlog).eventually (eventually_ge_atTop (1:ℝ))]
    with N hnear hoff hfull hlarge hL hLL
  intro F hF1 hFc hFb P Q hP hPQ hlogP hQ hres J hJ hlo hu X hNX hXN M hM hd
  have hFm : Multiplicative F := fun a b ha hb _ => hFc a b ha hb
  let V := fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)
  let B := mrtTypicalCoefficient (Icc 1 J) V F
  let E := mrtActualNoSmall P Q J N F ∩ Set.Ioc (-((N:ℝ)/4)) ((N:ℝ)/4)
  let G := fun t:ℝ => ‖mrtDyadicPolynomial B N t‖^2
  let δ := Real.log (Real.log N)/(Real.log N)^(1/80:ℝ)
  let R : ℝ := 0
  have hR : 0 ≤ R := le_rfl
  have hδ : 0 ≤ δ := div_nonneg (by exact hLL.trans' (by norm_num)) (by positivity)
  have hE : E ⊆ Set.Ioc (-(N:ℝ)) N := fun _ ht => ht.1.1
  have hmax : ∀ j ∈ Icc 1 J, mrtBandUpper Q j ≤ Real.exp (Real.sqrt (Real.log N)) := by
    intro j hj
    have hh := Real.exp_le_exp.mpr (mrt_band_upper_log_mono hQ
      (mem_Icc.mp hj).1 (mem_Icc.mp hj).2)
    rw [Real.exp_log (show 0 < mrtBandUpper Q j from Real.exp_pos _),
      Real.exp_log (show 0 < mrtBandUpper Q J from Real.exp_pos _)] at hh
    exact hh.trans hu
  have hGc : Continuous G := (mrtExponentialPolynomial_continuous _ _ _).norm.pow 2
  have hGi : IntegrableOn G (Set.Ioc (-(N:ℝ)) N) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [Nat.cast_nonneg (α:=ℝ) N])).mp
      (hGc.intervalIntegrable _ _)
  obtain ⟨τ,hτ,hmin⟩ := halasz_minimizing_twist F (2*N)
  have hτ' : |τ| ≤ 2*(N:ℝ) := by simpa only [Nat.cast_mul,Nat.cast_ofNat] using hτ
  have hmin' : ∀ v:ℝ, |v| ≤ 2*N →
      squaredDistance F (mrtArchimedeanTwist τ) (2*N) ≤
        squaredDistance F (mrtArchimedeanTwist v) (2*N) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using hmin
  by_cases hsmall : squaredDistance F (mrtArchimedeanTwist τ) (2*N) ≤
      Real.log (Real.log (2*N:ℕ))/10
  · let I := Set.Ioc (τ-(Real.log N)^(1/16:ℝ)) (τ+(Real.log N)^(1/16:ℝ))
    have hn := hnear P Q J hP hPQ hlogP hJ hmax X hNX hXN
      F hF1 hFc hFb τ M hM hd hsmall (E∩I)
      (fun _ ht => ht.1.2) Set.inter_subset_right
    have ho := hoff F hF1 hFm hFb P Q (by linarith) hPQ hQ hres J hJ hlo hu τ hτ' hmin'
    have hsub : E \ I ⊆ mrtNoSmallOffCenter P Q J N F τ := by
      intro t ht
      refine ⟨ht.1.1,?_⟩
      change (Real.log N)^(1/16:ℝ) ≤ |t-τ|
      have hout := ht.2
      change ¬(τ-(Real.log N)^(1/16:ℝ) < t ∧ t ≤ τ+(Real.log N)^(1/16:ℝ)) at hout
      by_cases htlo : τ-(Real.log N)^(1/16:ℝ) < t
      · have hhi : τ+(Real.log N)^(1/16:ℝ) < t := by
          push Not at hout
          exact hout htlo
        rw [abs_of_nonneg (by
          have hp := Real.rpow_nonneg (show 0≤Real.log (N:ℝ) by linarith) (1/16:ℝ)
          linarith)]
        linarith
      · have hle : t ≤ τ-(Real.log N)^(1/16:ℝ) := le_of_not_gt htlo
        rw [abs_of_nonpos (by
          have hp := Real.rpow_nonneg (show 0≤Real.log (N:ℝ) by linarith) (1/16:ℝ)
          linarith)]
        linarith
    have hOff : mrtNoSmallOffCenter P Q J N F τ ⊆ Set.Ioc (-(N:ℝ)) N :=
      fun _ ht => ht.1.1
    have ho₀ : (∫ t in mrtNoSmallOffCenter P Q J N F τ, G t) ≤ C₂*δ := by
      simpa only [G,B,V,δ,mul_div_assoc] using ho
    have ho' : (∫ t in E \ I, G t) ≤ C₂*δ := by
      apply le_trans _ ho₀
      exact setIntegral_mono_set (hGi.mono_set hOff)
        (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
        (Filter.Eventually.of_forall hsub)
    have hpow : (Real.log N)^(-1/32:ℝ) ≤ δ := by
      calc
        _ ≤ (Real.log N)^(-1/80:ℝ) := Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
        _ = 1/(Real.log N)^(1/80:ℝ) := by
          rw [show (-1/80:ℝ)=-(1/80:ℝ) by ring,Real.rpow_neg (by linarith : 0≤Real.log (N:ℝ))]
          simp only [one_div]
        _ ≤ δ := div_le_div_of_nonneg_right hLL (by positivity)
    have hn' : (∫ t in E∩I, G t) ≤ C₁*(R+Real.exp (-4*M/5)+δ) := by
      apply hn.trans
      apply mul_le_mul_of_nonneg_left _ hC₁.le
      dsimp only [R]
      linarith
    have hsplit := integral_inter_add_sdiff (f := G) (s := E) (t := I)
      measurableSet_Ioc (hGi.mono_set hE)
    change (∫ t in E, G t) ≤ _
    rw [← hsplit]
    have hs := add_le_add hn' ho'
    have he : 0 ≤ Real.exp (-4*M/5) := (Real.exp_pos _).le
    dsimp [R] at *
    nlinarith [mul_nonneg hC₂.le (add_nonneg hR he),
      mul_nonneg hC₃.le (add_nonneg (add_nonneg hR he) hδ)]
  · have hminlarge : ∀ v:ℝ, |v| ≤ 2*N →
        (1/10:ℝ)*Real.log (Real.log (2*N:ℕ)) ≤
          squaredDistance F (mrtArchimedeanTwist v) (2*N) := by
      intro v hv
      have hh := hmin' v hv
      linarith
    have hb := hlarge F hF1 hFm hFb hminlarge P Q J hQ hu
      (mrtPrimeBand (mrtExtraPrimeLower (Real.log N)) (mrtExtraPrimeUpper (Real.log N)))
      (fun _ hp => mrtPrimeBand_prime hp)
    have hh := hfull F hFm hFb P Q (by linarith) hPQ hQ hres J hJ hlo hu hb
    change (∫ t in E, G t) ≤ _
    have hh' : (∫ t in E, G t) ≤ C₃*δ := by
      apply le_trans _ (show (∫ t in mrtActualNoSmall P Q J N F,G t) ≤ C₃*δ by
        simpa only [G,B,V,δ,mul_div_assoc] using hh)
      exact setIntegral_mono_set
        (hGi.mono_set (fun _ ht => ht.1))
        (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
        (Filter.Eventually.of_forall (fun _ ht => ht.1))
    have he : 0 ≤ Real.exp (-4*M/5) := (Real.exp_pos _).le
    dsimp [R] at *
    nlinarith [mul_nonneg (add_nonneg hC₁.le hC₂.le) hδ,
      mul_nonneg (show 0≤C₁+C₂+C₃ by positivity) (add_nonneg hR he)]

end TwoPointCorrelations

end OAI
