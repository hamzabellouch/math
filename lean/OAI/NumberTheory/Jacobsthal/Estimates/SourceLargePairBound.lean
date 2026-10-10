import OAI.NumberTheory.Jacobsthal.Sieve.OriginalPairSieve

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Filter
namespace ErdosVarianceLargeCount
open NumberTheoryLean ErdosHyperbolaError ErdosPrimeInputs.PrimeProductOmissions
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem finite_large_pair_bound : ∃ C : ℝ,0 < C ∧ ∀ᶠ R : ℝ in atTop,1 < R ∧
    ∀ (H T0 T1 : ℕ),2 ≤ H → 0 < T0 → 0 < T1 → Squarefree T0 →
      (∀ t : ℕ,t.Prime → t ∣ T0 → t ∣ H) → T1.Coprime (H*T0) →
      ∀ (C0 k0 p0 p1 m1 : ℤ),Int.gcd C0 (H : ℤ) = 1 → Int.gcd p0 (T0 : ℤ) = 1 →
        Int.gcd p1 (T1 : ℤ) = 1 →
      ∀ (x0 x1 y0 y1 : ℝ),x0 ≤ x1 → y0 ≤ y1 → y1-y0 ≤ 2*(H : ℝ) →
      ∀ (lcI rcI lcJ rcJ : Bool),
      ((siftedSourcePairs H T0 T1 C0 k0 p0 p1 m1 x0 x1 y0 y1 lcI rcI lcJ rcJ
        (reducedPrimes ⌊largeSieveCutoff R⌋₊ (H*T1))).card : ℝ) ≤
        C*(x1-x0)/((patternCard T0 T1 : ℝ)*Real.log R)+
        hyperbolaEnvelope H T0*(2*R^((1 : ℝ)/10)*(1+(y1-y0)/((H*T0 : ℕ) : ℝ))+
          ((x1-x0)/((H*T0 : ℕ) : ℝ))*(1+Real.log (R^((1 : ℝ)/10)))) := by
  obtain ⟨C,hC,hmain⟩ := source_main_R_upper
  refine ⟨C,hC,?_⟩
  filter_upwards [hmain] with R hR
  refine ⟨hR.1,?_⟩
  intro H T0 T1 hH hT0 hT1 hSF hsupport hT1N C0 k0 p0 p1 m1 hC0 hp0 hp1
    x0 x1 y0 y1 hx hy hVH lcI rcI lcJ rcJ
  have hH0 : 0 < H := by omega
  have hq : 0 < H*T1 := mul_pos hH0 hT1
  let P := reducedPrimes ⌊largeSieveCutoff R⌋₊ (H*T1)
  have hP (t : ℕ) (ht : t ∈ P) : t.Prime :=
    (LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_sdiff.mp ht).1).1
  have hPv (t : ℕ) (ht : t ∈ P) : (t : ℝ) ≤ largeSieveCutoff R :=
    (Nat.le_floor_iff (by linarith [hR.2.1])).mp
      (LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_sdiff.mp ht).1).2
  have hPcop (t : ℕ) (ht : t ∈ P) : t.Coprime (H*T1) := by
    apply (hP t ht).coprime_iff_not_dvd.mpr
    intro hdiv
    exact (Finset.mem_sdiff.mp ht).2 (Nat.mem_primeFactors.mpr ⟨hP t ht,hdiv,hq.ne'⟩)
  have hb := source_pair_sieve_upper H T0 T1 hH hT0 hT1 hSF hsupport hT1N C0 k0 p0 p1 m1
    hC0 hp0 hp1 P hP hPcop (largeSieveCutoff R) largeSieveLevel hR.2.1 (by norm_num [largeSieveLevel]) hPv
    x0 x1 y0 y1 hx hy lcI rcI lcJ rcJ
  have hT0H := source_restriction_divides H T0 hH0 hSF hsupport
  have hcop : H.Coprime T1 := hT1N.symm.of_dvd_left (dvd_mul_right H T0)
  have hm := hR.2.2 H T0 T1 hH0 hT0 hT1 hT0H hcop (x1-x0) (y1-y0)
    (sub_nonneg.mpr hx) (sub_nonneg.mpr hy) hVH
  have hD : 1 ≤ (largeSieveCutoff R)^largeSieveLevel :=
    Real.one_le_rpow (by linarith [hR.2.1]) (by norm_num [largeSieveLevel])
  have he := hyperbola_level_sum_bound H T0 P (largeSieveCutoff R) largeSieveLevel
    (x1-x0) (y1-y0) hD (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)
  rw [largeSieveCutoff_level R (by linarith [hR.1])] at he
  exact hb.trans (add_le_add hm he)

end ErdosVarianceLargeCount

end

section

open _root_.Filter
namespace ErdosVarianceLargeScale
open NumberTheoryLean ErdosHyperbolaError ErdosHyperbolaWeighted ErdosVarianceLargeCount
  ErdosInverseBoxHeight ErdosInverseEuler ErdosVarianceSmallModel

noncomputable def slowHyperbolaFactor (N T0 : ℕ) : ℝ :=
  completionConstant*(N.divisors.card : ℝ)^3*(Real.log (2*(N : ℝ)))^2*Real.sqrt T0

theorem hyperbolaEnvelope_factor (H T0 : ℕ) :
    hyperbolaEnvelope H T0 = slowHyperbolaFactor (H*T0) T0*((H*T0 : ℕ) : ℝ)^((3 : ℝ)/4) := by
  unfold hyperbolaEnvelope slowHyperbolaFactor
  ring

theorem source_hyperbola_scales (alpha : ℝ) (halpha : 0 < alpha) :
    ∀ᶠ z : ℝ in atTop,1 < z ∧ ∀ (R : ℝ),z^alpha ≤ R →
      ∀ (H T0 : ℕ),1 ≤ H → 1 ≤ T0 →
        (H : ℝ) ≤ R*(sourceZ z)^11 → T0 ≤ smallModulus (sourceW z) →
        1 < R ∧ ((H*T0 : ℕ) : ℝ) ≤ R^((101 : ℝ)/100) ∧
          slowHyperbolaFactor (H*T0) T0 ≤ R^((1 : ℝ)/100) := by
  obtain ⟨A,hA,hdiv⟩ := divisor_log_square_subpower 3 (by norm_num : (0 : ℝ) < 1/1000)
  let C := completionConstant*A
  have hconst := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3/1000)).comp
    (tendsto_rpow_atTop halpha)).eventually_ge_atTop C
  filter_upwards [source_Z_power_R alpha (1/100) 12 halpha (by norm_num) (by decide),
    source_Z_power_R alpha (1/100) 1 halpha (by norm_num) (by decide),
    smallModulus_source_power 1 1 zero_lt_one,hconst]
    with z hZ12 hZ1 hM hconstz
  refine ⟨hZ12.1,?_⟩
  intro R hRlo H T0 hH hT0 hHhi hT0M
  have hz0 : 0 < z := by linarith [hZ12.1]
  have hR1 : 1 < R := (Real.one_lt_rpow hZ12.1 halpha).trans_le hRlo
  have hR : 0 < R := by linarith
  have hZ : 0 < sourceZ z := Real.exp_pos _
  have hMZ : (smallModulus (sourceW z) : ℝ) ≤ sourceZ z := by
    simpa only [pow_one,Real.rpow_one] using hM
  have hT0Z : (T0 : ℝ) ≤ sourceZ z := (by exact_mod_cast hT0M : (T0 : ℝ) ≤ smallModulus (sourceW z)).trans hMZ
  have hT0R : (T0 : ℝ) ≤ R^((1 : ℝ)/100) := hT0Z.trans (by
    simpa only [pow_one] using hZ1.2 R hRlo)
  have hN : ((H*T0 : ℕ) : ℝ) ≤ R^((101 : ℝ)/100) := by
    calc
      _ = (H : ℝ)*(T0 : ℝ) := Nat.cast_mul _ _
      _ ≤ (R*(sourceZ z)^11)*sourceZ z := mul_le_mul hHhi hT0Z (Nat.cast_nonneg _) (by positivity)
      _ = R*(sourceZ z)^12 := by ring
      _ ≤ R*R^((1 : ℝ)/100) := mul_le_mul_of_nonneg_left (hZ12.2 R hRlo) hR.le
      _ = R^(1 : ℝ)*R^((1 : ℝ)/100) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hR];norm_num
  have hN1 : 1 ≤ H*T0 := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (by omega))
  have hN2 : ((H*T0 : ℕ) : ℝ) ≤ R^(2 : ℝ) :=
    hN.trans (Real.rpow_le_rpow_of_exponent_le hR1.le (by norm_num))
  have hNp : (((H*T0 : ℕ) : ℝ)^((1 : ℝ)/1000)) ≤ R^((1 : ℝ)/500) := by
    calc
      _ ≤ (R^(2 : ℝ))^((1 : ℝ)/1000) := Real.rpow_le_rpow (Nat.cast_nonneg _) hN2 (by norm_num)
      _ = _ := by rw [← Real.rpow_mul hR.le];norm_num
  have hsqrt : Real.sqrt T0 ≤ R^((1 : ℝ)/200) := by
    calc
      _ ≤ Real.sqrt (R^((1 : ℝ)/100)) := Real.sqrt_le_sqrt hT0R
      _ = _ := by rw [Real.sqrt_eq_rpow,← Real.rpow_mul hR.le];norm_num
  have hC : C ≤ R^((3 : ℝ)/1000) :=
    hconstz.trans (Real.rpow_le_rpow (Real.rpow_nonneg hz0.le alpha) hRlo (by norm_num))
  have hfactor : slowHyperbolaFactor (H*T0) T0 ≤ R^((1 : ℝ)/100) := by
    calc
      _ = completionConstant*((H*T0).divisors.card : ℝ)^3*
          (Real.log (2*((H*T0 : ℕ) : ℝ)))^2*Real.sqrt T0 := rfl
      _ ≤ completionConstant*(A*(((H*T0 : ℕ) : ℝ)^((1 : ℝ)/1000)))*Real.sqrt T0 := by
        exact mul_le_mul_of_nonneg_right (by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hdiv (H*T0) hN1) completionConstant_pos.le)
          (Real.sqrt_nonneg _)
      _ = C*(((H*T0 : ℕ) : ℝ)^((1 : ℝ)/1000))*Real.sqrt T0 := by dsimp [C];ring
      _ ≤ R^((3 : ℝ)/1000)*R^((1 : ℝ)/500)*R^((1 : ℝ)/200) := by
        exact mul_le_mul (mul_le_mul hC hNp (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by positivity))
          hsqrt (Real.sqrt_nonneg _) (by positivity)
      _ = _ := by rw [← Real.rpow_add hR,← Real.rpow_add hR];norm_num
  exact ⟨hR1,hN,hfactor⟩

end ErdosVarianceLargeScale

end


namespace ErdosVarianceLargeScale

theorem large_error_algebra (R N F U V : ℝ) (hR : 1 < R) (hN : 0 < N)
    (_hFlow : 0 ≤ F) (hF : F ≤ R^((1 : ℝ)/100))
    (hNlo : R^((4 : ℝ)/5) ≤ N) (hNhi : N ≤ R^((101 : ℝ)/100))
    (hU : 0 ≤ U) (hUR : U ≤ R) (hV : 0 ≤ V) (hVN : V ≤ 2*N)
    (hlog : 1+Real.log (R^((1 : ℝ)/10)) ≤ 2*R^((1 : ℝ)/20))
    (hconstant : 8 ≤ R^((1 : ℝ)/40)) :
    F*N^((3 : ℝ)/4)*(2*R^((1 : ℝ)/10)*(1+V/N)+(U/N)*(1+Real.log (R^((1 : ℝ)/10)))) ≤
      R^((9 : ℝ)/10) := by
  have hR0 : 0 < R := by linarith
  have hNp : N^((3 : ℝ)/4) ≤ R^((303 : ℝ)/400) := by
    calc
      _ ≤ (R^((101 : ℝ)/100))^((3 : ℝ)/4) := Real.rpow_le_rpow hN.le hNhi (by norm_num)
      _ = _ := by rw [← Real.rpow_mul hR0.le];norm_num
  have hVdiv : V/N ≤ 2 := (div_le_iff₀ hN).mpr hVN
  have hfirst : F*N^((3 : ℝ)/4)*(2*R^((1 : ℝ)/10)*(1+V/N)) ≤ 6*R^((347 : ℝ)/400) := by
    have hfac : 2*R^((1 : ℝ)/10)*(1+V/N) ≤ 6*R^((1 : ℝ)/10) := by
      have hh := mul_le_mul_of_nonneg_left (show 1+V/N ≤ 3 by linarith)
        (show 0 ≤ 2*R^((1 : ℝ)/10) by positivity)
      nlinarith
    calc
      _ ≤ (R^((1 : ℝ)/100)*R^((303 : ℝ)/400))*(6*R^((1 : ℝ)/10)) :=
        mul_le_mul (mul_le_mul hF hNp (Real.rpow_nonneg hN.le _) (by positivity)) hfac
          (by positivity) (by positivity)
      _ = 6*(R^((1 : ℝ)/100)*R^((303 : ℝ)/400)*R^((1 : ℝ)/10)) := by ring
      _ = _ := by rw [← Real.rpow_add hR0,← Real.rpow_add hR0];norm_num
  have hNroot : R^((1 : ℝ)/5) ≤ N^((1 : ℝ)/4) := by
    have hh := Real.rpow_le_rpow (Real.rpow_nonneg hR0.le _) hNlo (by norm_num : (0 : ℝ) ≤ 1/4)
    rw [← Real.rpow_mul hR0.le] at hh
    norm_num at hh
    exact hh
  have hratio : N^((3 : ℝ)/4)/N ≤ 1/R^((1 : ℝ)/5) := by
    have he : N^((3 : ℝ)/4)/N = 1/N^((1 : ℝ)/4) := by
      apply (div_eq_div_iff hN.ne' (Real.rpow_pos_of_pos hN _).ne').mpr
      rw [← Real.rpow_add hN]
      norm_num
    rw [he]
    exact div_le_div_of_nonneg_left zero_le_one (Real.rpow_pos_of_pos hR0 _) hNroot
  have hlog0 : 0 ≤ 1+Real.log (R^((1 : ℝ)/10)) := by
    have hh := Real.log_nonneg (Real.one_le_rpow hR.le (by norm_num : (0 : ℝ) ≤ 1/10))
    linarith
  have hsecond : F*N^((3 : ℝ)/4)*((U/N)*(1+Real.log (R^((1 : ℝ)/10)))) ≤ 2*R^((43 : ℝ)/50) := by
    calc
      _ = (F*U)*(N^((3 : ℝ)/4)/N)*(1+Real.log (R^((1 : ℝ)/10))) := by ring
      _ ≤ ((R^((1 : ℝ)/100)*R)*(1/R^((1 : ℝ)/5)))*(2*R^((1 : ℝ)/20)) :=
        mul_le_mul
          (mul_le_mul (mul_le_mul hF hUR hU (by positivity)) hratio (by positivity) (by positivity))
          hlog hlog0 (by positivity)
      _ = 2*((R^((1 : ℝ)/100)*R^(1 : ℝ)/R^((1 : ℝ)/5))*R^((1 : ℝ)/20)) := by
        rw [Real.rpow_one]
        ring
      _ = _ := by rw [← Real.rpow_add hR0,← Real.rpow_sub hR0,← Real.rpow_add hR0];norm_num
  have hp1 : R^((347 : ℝ)/400) ≤ R^((7 : ℝ)/8) := Real.rpow_le_rpow_of_exponent_le hR.le (by norm_num)
  have hp2 : R^((43 : ℝ)/50) ≤ R^((7 : ℝ)/8) := Real.rpow_le_rpow_of_exponent_le hR.le (by norm_num)
  have hsum : F*N^((3 : ℝ)/4)*(2*R^((1 : ℝ)/10)*(1+V/N)+(U/N)*(1+Real.log (R^((1 : ℝ)/10)))) ≤
      8*R^((7 : ℝ)/8) := by
    rw [mul_add]
    nlinarith
  apply hsum.trans
  calc
    _ ≤ R^((1 : ℝ)/40)*R^((7 : ℝ)/8) := mul_le_mul_of_nonneg_right hconstant (by positivity)
    _ = _ := by rw [← Real.rpow_add hR0];norm_num

end ErdosVarianceLargeScale


section

open _root_.Filter
namespace ErdosVarianceLargeScale

theorem eventual_large_error_budgets : ∀ᶠ R : ℝ in atTop,1 < R ∧
    1+Real.log (R^((1 : ℝ)/10)) ≤ 2*R^((1 : ℝ)/20) ∧ 8 ≤ R^((1 : ℝ)/40) := by
  have hlog := (isLittleO_log_rpow_rpow_atTop (1 : ℝ) (by norm_num : (0 : ℝ) < 1/20)).bound zero_lt_one
  filter_upwards [hlog,(tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/40)).eventually_ge_atTop 8,
    eventually_gt_atTop (1 : ℝ)] with R hlog hconstant hR
  have hR0 : 0 < R := by linarith
  have hlog0 : 0 ≤ Real.log R := (Real.log_pos hR).le
  have hl : Real.log R ≤ R^((1 : ℝ)/20) := by
    simpa only [Real.rpow_one,Real.norm_eq_abs,abs_of_nonneg hlog0,
      abs_of_nonneg (Real.rpow_nonneg hR0.le _),one_mul] using hlog
  have hone : 1 ≤ R^((1 : ℝ)/20) := Real.one_le_rpow hR.le (by norm_num)
  refine ⟨hR,?_,hconstant⟩
  rw [Real.log_rpow hR0]
  nlinarith

end ErdosVarianceLargeScale

end

section

open _root_.Filter
namespace ErdosVarianceLargeScale
open NumberTheoryLean ErdosHyperbolaError ErdosVarianceLargeCount
  ErdosInverseBoxHeight ErdosInverseEuler ErdosVarianceSmallModel

theorem source_large_error (alpha : ℝ) (halpha : 0 < alpha) :
    ∀ᶠ z : ℝ in atTop,1 < z ∧ ∀ (R : ℝ),z^alpha ≤ R →
      ∀ (H T0 : ℕ),1 ≤ H → 1 ≤ T0 →
        R^((4 : ℝ)/5) ≤ (H : ℝ) → (H : ℝ) ≤ R*(sourceZ z)^11 → T0 ≤ smallModulus (sourceW z) →
      ∀ (U V : ℝ),0 ≤ U → U ≤ R → 0 ≤ V → V ≤ 2*(H : ℝ) →
        hyperbolaEnvelope H T0*(2*R^((1 : ℝ)/10)*(1+V/((H*T0 : ℕ) : ℝ))+
          (U/((H*T0 : ℕ) : ℝ))*(1+Real.log (R^((1 : ℝ)/10)))) ≤ R^((9 : ℝ)/10) := by
  obtain ⟨R0,hR0⟩ := eventually_atTop.mp eventual_large_error_budgets
  filter_upwards [source_hyperbola_scales alpha halpha,(tendsto_rpow_atTop halpha).eventually_ge_atTop R0]
    with z hscale hzR
  refine ⟨hscale.1,?_⟩
  intro R hRlo H T0 hH hT0 hHlo hHhi hT0M U V hU hUR hV hVH
  have hs := hscale.2 R hRlo H T0 hH hT0 hHhi hT0M
  have hb := hR0 R (hzR.trans hRlo)
  have hHN : (H : ℝ) ≤ ((H*T0 : ℕ) : ℝ) := by
    have ht : (1 : ℝ) ≤ T0 := by exact_mod_cast hT0
    have hh := mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg H)
    simpa only [mul_one,Nat.cast_mul] using hh
  have hN : (0 : ℝ) < ((H*T0 : ℕ) : ℝ) := by
    exact_mod_cast mul_pos (show 0 < H by omega) (show 0 < T0 by omega)
  have hF : 0 ≤ slowHyperbolaFactor (H*T0) T0 := by
    have hc := completionConstant_pos.le
    dsimp [slowHyperbolaFactor]
    positivity
  rw [hyperbolaEnvelope_factor]
  exact large_error_algebra R ((H*T0 : ℕ) : ℝ) (slowHyperbolaFactor (H*T0) T0) U V
    hs.1 hN hF hs.2.2 (hHlo.trans hHN) hs.2.1 hU hUR hV
    (hVH.trans (mul_le_mul_of_nonneg_left hHN (by norm_num))) hb.2.1 hb.2.2

end ErdosVarianceLargeScale

end


open _root_.Filter
namespace ErdosVarianceLargeScale
open NumberTheoryLean ErdosHyperbolaError ErdosVarianceLargeCount
  ErdosInverseBoxHeight ErdosInverseEuler ErdosPrimeInputs.PrimeProductOmissions

theorem source_large_pair_bound (alpha : ℝ) (halpha : 0 < alpha) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ z : ℝ in atTop,1 < z ∧
      ∀ (R : ℝ),z^alpha ≤ R → ∀ (H T0 T1 : ℕ),2 ≤ H → 0 < T0 → 0 < T1 →
        Squarefree T0 → (∀ t : ℕ,t.Prime → t ∣ T0 → t ∣ H) → T1.Coprime (H*T0) →
        R^((4 : ℝ)/5) ≤ (H : ℝ) → (H : ℝ) ≤ R*(sourceZ z)^11 → T0 ≤ smallModulus (sourceW z) →
      ∀ (C0 k0 p0 p1 m1 : ℤ),Int.gcd C0 (H : ℤ) = 1 → Int.gcd p0 (T0 : ℤ) = 1 →
        Int.gcd p1 (T1 : ℤ) = 1 →
      ∀ (x0 x1 y0 y1 : ℝ),x0 ≤ x1 → x1-x0 ≤ R → y0 ≤ y1 → y1-y0 ≤ 2*(H : ℝ) →
      ∀ (lcI rcI lcJ rcJ : Bool),
      ((siftedSourcePairs H T0 T1 C0 k0 p0 p1 m1 x0 x1 y0 y1 lcI rcI lcJ rcJ
        (reducedPrimes ⌊largeSieveCutoff R⌋₊ (H*T1))).card : ℝ) ≤
          C*(x1-x0)/((patternCard T0 T1 : ℝ)*Real.log R)+R^((9 : ℝ)/10) := by
  obtain ⟨C,hC,hfinite⟩ := finite_large_pair_bound
  obtain ⟨R0,hR0⟩ := eventually_atTop.mp hfinite
  refine ⟨C,hC,?_⟩
  filter_upwards [source_large_error alpha halpha,(tendsto_rpow_atTop halpha).eventually_ge_atTop R0]
    with z herr hzR
  refine ⟨herr.1,?_⟩
  intro R hRlo H T0 T1 hH hT0 hT1 hSF hsupport hT1N hHlo hHhi hT0M
    C0 k0 p0 p1 m1 hC0 hp0 hp1 x0 x1 y0 y1 hx hUR hy hVH lcI rcI lcJ rcJ
  have hb := (hR0 R (hzR.trans hRlo)).2 H T0 T1 hH hT0 hT1 hSF hsupport hT1N C0 k0 p0 p1 m1
    hC0 hp0 hp1 x0 x1 y0 y1 hx hy hVH lcI rcI lcJ rcJ
  have he := herr.2 R hRlo H T0 (by omega) hT0 hHlo hHhi hT0M (x1-x0) (y1-y0)
    (sub_nonneg.mpr hx) hUR (sub_nonneg.mpr hy) hVH
  exact hb.trans (add_le_add le_rfl he)

end ErdosVarianceLargeScale


end Erdos970

end OAI
