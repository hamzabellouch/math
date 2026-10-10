import Mathlib
import OAI.NumberTheory.PrimePackets.LocalEuler

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
namespace PrimeDegreePackets

lemma cast_div_gt_sub_one (m d : ℕ) (hd : 0 < d) :
    (m:ℝ)/d - 1 < (m/d : ℕ) := by
  have hmod : ((m%d : ℕ):ℝ) < d := by exact_mod_cast Nat.mod_lt m hd
  have heq : (d:ℝ)*(m/d : ℕ) + (m%d : ℕ) = m := by exact_mod_cast Nat.div_add_mod m d
  have H : (m:ℝ)/d < (m/d : ℕ)+1 := by
    apply (div_lt_iff₀ (Nat.cast_pos.mpr hd)).mpr
    nlinarith
  linarith

lemma cast_div_interval_bounds (a b d : ℕ) (hd : 0 < d) :
    ((b:ℝ)-a)/d - 1 ≤ ((b/d : ℕ):ℝ)-(a/d : ℕ) ∧
      ((b/d : ℕ):ℝ)-(a/d : ℕ) ≤ ((b:ℝ)-a)/d + 1 := by
  have ha := cast_div_gt_sub_one a d hd
  have hb := cast_div_gt_sub_one b d hd
  have ha' : ((a/d : ℕ):ℝ) ≤ (a:ℝ)/d := Nat.cast_div_le
  have hb' : ((b/d : ℕ):ℝ) ≤ (b:ℝ)/d := Nat.cast_div_le
  rw [sub_div]
  constructor <;> linarith

lemma cast_div_interval_relative (a b d : ℕ) (hd : 0 < d)
    (η : ℝ) (hη : 0 < η) (hrel : η*b ≤ (b:ℝ)-a)
    (hlong : 2 ≤ η*(b/d : ℕ)) :
    (η/2)*(b/d : ℕ) ≤ ((b/d : ℕ):ℝ)-(a/d : ℕ) := by
  have H := (cast_div_interval_bounds a b d hd).1
  have hdR : 0 < (d:ℝ) := Nat.cast_pos.mpr hd
  have hob : η*(b/d : ℕ) ≤ ((b:ℝ)-a)/d := by
    calc
      _ ≤ η*((b:ℝ)/d) := mul_le_mul_of_nonneg_left Nat.cast_div_le hη.le
      _ = (η*b)/d := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hrel hdR.le
  nlinarith

lemma cast_div_interval_width (a b d : ℕ) (hd : 0 < d)
    (hwidth : (d:ℝ) ≤ (b:ℝ)-a) :
    ((b/d : ℕ):ℝ)-(a/d : ℕ) ≤ 2*((b:ℝ)-a)/d := by
  have H := (cast_div_interval_bounds a b d hd).2
  have H' : (1:ℝ) ≤ ((b:ℝ)-a)/d := (le_div_iff₀ (Nat.cast_pos.mpr hd)).mpr (by simpa using hwidth)
  calc
    _ ≤ ((b:ℝ)-a)/d+1 := H
    _ ≤ 2*(((b:ℝ)-a)/d) := by linarith
    _ = _ := by ring

lemma div_square_lower {b d : ℕ} (hd : 0 < d) (hbd : 4*d^2 ≤ b) :
    2 ≤ b/d ∧ b ≤ (b/d)^2 := by
  have hu4 : 4*d ≤ b/d := (Nat.le_div_iff_mul_le hd).mpr (by nlinarith)
  have hu : 0 < b/d := by omega
  have hmod : b%d ≤ d := (Nat.mod_lt b hd).le
  have heq := Nat.div_add_mod b d
  refine ⟨by omega,?_⟩
  calc
    b = (b/d)*d+b%d := by nlinarith [heq]
    _ ≤ (b/d)*d+d := Nat.add_le_add_left hmod _
    _ ≤ (b/d)*d+(b/d)*d := Nat.add_le_add_left (Nat.le_mul_of_pos_left d hu) _
    _ = (b/d)*(2*d) := by ring
    _ ≤ (b/d)*(b/d) := Nat.mul_le_mul_left _ (by omega)
    _ = _ := by ring

end PrimeDegreePackets


namespace PrimeDegreePackets
open NumberField Finset
open scoped BigOperators ENNReal nonZeroDivisors

lemma weightedIdealInterval_split {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (a b T : ℕ) :
    weightedIdealInterval M a b =
      (∑' I : primaryIntegralIdeals K (saturationIndex M).primeFactors,
        if Ideal.absNorm I.1.1 ≤ T then globalIdealWeight M (nonzeroIntegralIdealUnit I.1) *
          ENNReal.ofReal (∑ m ∈ Ioc (a / Ideal.absNorm I.1.1) (b / Ideal.absNorm I.1.1),
            coprimeIdealCoefficient K (saturationIndex M) m) else 0) +
      ∑' I : primaryIntegralIdeals K (saturationIndex M).primeFactors,
        if T < Ideal.absNorm I.1.1 then globalIdealWeight M (nonzeroIntegralIdealUnit I.1) *
          ENNReal.ofReal (∑ m ∈ Ioc (a / Ideal.absNorm I.1.1) (b / Ideal.absNorm I.1.1),
            coprimeIdealCoefficient K (saturationIndex M) m) else 0 := by
  classical
  rw [weightedIdealInterval_convolution, ← ENNReal.tsum_add]
  apply tsum_congr
  intro I
  by_cases h : Ideal.absNorm I.1.1 ≤ T
  · simp only [h,not_lt.mpr h,ite_true,ite_false,add_zero]
  · simp only [h,lt_of_not_ge h,ite_true,ite_false,zero_add]

 

theorem weightedIdeal_small_norm_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → ∃ R : ℕ,
      ∀ (K : Type*) [Field K] [NumberField K]
        (M : FullLattice n K), Module.finrank ℚ K = n →
        ∀ a b T : ℕ, 0 < T → R ≤ b/T →
          Real.log (saturationIndex M) ≤ (b/T : ℕ) →
          4*T^2 ≤ b → a ≤ b → η*b ≤ (b:ℝ)-a →
          2 ≤ η*(b/T : ℕ) →
          (∑' I : primaryIntegralIdeals K (saturationIndex M).primeFactors,
            if Ideal.absNorm I.1.1 ≤ T then globalIdealWeight M (nonzeroIntegralIdealUnit I.1) *
              ENNReal.ofReal (∑ m ∈ Ioc (a / Ideal.absNorm I.1.1) (b / Ideal.absNorm I.1.1),
                coprimeIdealCoefficient K (saturationIndex M) m) else 0) ≤
          (saturationIndex M : ℝ≥0∞)⁻¹ *
            ENNReal.ofReal (C * ((b:ℝ)-a) *
              ((NumberField.dedekindZeta K (1+1/Real.log b)).re / Real.log b)) := by
  classical
  obtain ⟨C,hC,hInt⟩ := coprime_ideal_scaled_interval n
  refine ⟨C,hC,?_⟩
  intro η hη
  obtain ⟨R,hR⟩ := hInt (η/2) (by positivity)
  refine ⟨R,?_⟩
  intro K _ _ M hn a b T hT hRT hqT hsq hab hrel hlong
  have hnZ : Module.finrank ℤ (𝓞 K) = n := by rw [NumberField.RingOfIntegers.rank]; exact hn
  have hq : 0 < saturationIndex M := Nat.pos_of_ne_zero (saturationIndex_ne_zero M)
  have hwide : (T:ℝ) ≤ (b:ℝ)-a := by
    have H : 2 ≤ ((b:ℝ)-a)/T := by
      calc
        _ ≤ η*(b/T : ℕ) := hlong
        _ ≤ η*((b:ℝ)/T) := mul_le_mul_of_nonneg_left Nat.cast_div_le hη.le
        _ = (η*b)/T := by ring
        _ ≤ _ := div_le_div_of_nonneg_right hrel (Nat.cast_nonneg _)
    have H' := (le_div_iff₀ (Nat.cast_pos.mpr hT)).mp H
    linarith [show (0:ℝ) ≤ T by positivity]
  let B : ℝ := C * ((b:ℝ)-a) *
    ((NumberField.dedekindZeta K (1+1/Real.log b)).re / Real.log b)
  let E : ℝ := badPrimeEuler K (saturationIndex M)
  have hE : 0 < E := badPrimeEuler_pos K _
  have hZ : actualLocalZ M = ENNReal.ofReal E := actualLocalZ_eq_badPrimeEuler M
  calc
    _ ≤ ENNReal.ofReal (B/E) *
        ∑' I : primaryIntegralIdeals K (saturationIndex M).primeFactors,
          globalIdealWeight M (nonzeroIntegralIdealUnit I.1) / (Ideal.absNorm I.1.1 : ℝ≥0∞) := by
      rw [← ENNReal.tsum_mul_left]
      apply ENNReal.tsum_le_tsum
      intro I
      split_ifs with hIT
      · have hd : 0 < Ideal.absNorm I.1.1 :=
          Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr I.1.2)
        have huT : b/T ≤ b/Ideal.absNorm I.1.1 := Nat.div_le_div_left hIT hd
        have huR : ((b/T : ℕ):ℝ) ≤ (b/Ideal.absNorm I.1.1 : ℕ) := by exact_mod_cast huT
        have hlongI : 2 ≤ η*(b/Ideal.absNorm I.1.1 : ℕ) :=
          hlong.trans (mul_le_mul_of_nonneg_left huR hη.le)
        have hsqI : 4*(Ideal.absNorm I.1.1)^2 ≤ b := by
          exact (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hIT 2)).trans hsq
        have H := hR K hnZ (saturationIndex M) a b (Ideal.absNorm I.1.1) hq hd
          (hqT.trans huR) (hRT.trans huT) hab
          (cast_div_interval_relative a b _ hd η hη hrel hlongI)
          (div_square_lower hd hsqI).2
          (cast_div_interval_width a b _ hd
            ((show (Ideal.absNorm I.1.1 : ℝ) ≤ T by exact_mod_cast hIT).trans hwide))
        have H' := ENNReal.ofReal_le_ofReal H
        refine (mul_le_mul_right H' _).trans_eq ?_
        have heq : C * (((b:ℝ)-a)/Ideal.absNorm I.1.1) *
            ((NumberField.dedekindZeta K (1+1/Real.log b)).re / Real.log b) /
              badPrimeEuler K (saturationIndex M) = (B/E)/Ideal.absNorm I.1.1 := by
          dsimp only [B,E]
          ring
        rw [heq, ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr hd), ENNReal.ofReal_natCast]
        simp only [div_eq_mul_inv]
        ac_rfl
      · exact bot_le
    _ ≤ ENNReal.ofReal (B/E) * ((saturationIndex M : ℝ≥0∞)⁻¹ * actualLocalZ M) :=
      mul_le_mul_right (primaryIdeal_reciprocal_sum_le M hn) _
    _ = _ := by
      rw [hZ, ENNReal.ofReal_div_of_pos hE]
      have hE0 : ENNReal.ofReal E ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hE)
      have hEt : ENNReal.ofReal E ≠ ∞ := ENNReal.ofReal_ne_top
      calc
        ENNReal.ofReal B / ENNReal.ofReal E *
            ((saturationIndex M : ℝ≥0∞)⁻¹ * ENNReal.ofReal E) =
          (saturationIndex M : ℝ≥0∞)⁻¹ *
            ((ENNReal.ofReal B / ENNReal.ofReal E) * ENNReal.ofReal E) := by ac_rfl
        _ = _ := by rw [ENNReal.div_mul_cancel hE0 hEt]

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma weighted_cutoff_div_lower {Q : ℝ} (hQ : 1 ≤ Q) {b : ℕ}
    (hb : Q^(3/4:ℝ) ≤ (b:ℝ)) :
    Q^(5/8:ℝ)-1 < (b / ⌊Q^(1/8:ℝ)⌋₊ : ℕ) := by
  let T : ℕ := ⌊Q^(1/8:ℝ)⌋₊
  have hQ0 : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hT : 0 < T := Nat.floor_pos.mpr (Real.one_le_rpow hQ (by norm_num))
  have hTle : (T:ℝ) ≤ Q^(1/8:ℝ) := Nat.floor_le (Real.rpow_nonneg hQ0.le _)
  have hT0 : (0:ℝ) < T := Nat.cast_pos.mpr hT
  have hratio : Q^(5/8:ℝ) ≤ (b:ℝ)/T := by
    apply (le_div_iff₀ hT0).mpr
    calc
      _ ≤ Q^(5/8:ℝ) * Q^(1/8:ℝ) := mul_le_mul_of_nonneg_left hTle (by positivity)
      _ = Q^(3/4:ℝ) := by rw [← Real.rpow_add hQ0]; norm_num
      _ ≤ _ := hb
  have hmod : ((b%T:ℕ):ℝ) < T := by exact_mod_cast Nat.mod_lt b hT
  have heq : (T:ℝ)*(b/T:ℕ)+(b%T:ℕ)=b := by exact_mod_cast Nat.div_add_mod b T
  have hbdiv : (b:ℝ)/T < (b/T:ℕ)+1 := by
    apply (div_lt_iff₀ hT0).mpr
    nlinarith
  exact (sub_lt_iff_lt_add.mpr (hratio.trans_lt hbdiv))

 

lemma eventual_weighted_small_parameters (R : ℕ) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ Q : ℝ in atTop, 1 ≤ Q ∧ ∀ q b : ℕ, 0 < q → (q:ℝ) ≤ Q →
      Q^(3/4:ℝ) ≤ (b:ℝ) →
      0 < ⌊Q^(1/8:ℝ)⌋₊ ∧ R ≤ b/⌊Q^(1/8:ℝ)⌋₊ ∧
      Real.log q ≤ (b/⌊Q^(1/8:ℝ)⌋₊:ℕ) ∧
      4*⌊Q^(1/8:ℝ)⌋₊^2 ≤ b ∧ 2 ≤ η*(b/⌊Q^(1/8:ℝ)⌋₊:ℕ) := by
  have hlog := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<5/8)).bound
    (by norm_num : (0:ℝ)<1/2)
  filter_upwards [eventually_ge_atTop (1:ℝ),hlog,
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<5/8)).eventually_ge_atTop
      (max ((R:ℝ)+1) (max 2 (2/η+1))),
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/2)).eventually_ge_atTop 4]
    with Q hQ hlog hbig hhalf
  refine ⟨hQ,?_⟩
  intro q b hq hqQ hb
  let T : ℕ := ⌊Q^(1/8:ℝ)⌋₊
  have hQ0 : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hT : 0 < T := Nat.floor_pos.mpr (Real.one_le_rpow hQ (by norm_num))
  have hTle : (T:ℝ) ≤ Q^(1/8:ℝ) := Nat.floor_le (Real.rpow_nonneg hQ0.le _)
  have hdiv := weighted_cutoff_div_lower hQ hb
  have hbig1 : (R:ℝ)+1 ≤ Q^(5/8:ℝ) := (le_max_left _ _).trans hbig
  have hbig2 : 2 ≤ Q^(5/8:ℝ) := (le_max_left _ _).trans ((le_max_right _ _).trans hbig)
  have hbig3 : 2/η+1 ≤ Q^(5/8:ℝ) := (le_max_right _ _).trans ((le_max_right _ _).trans hbig)
  have hRT : R ≤ b/T := by exact_mod_cast (show (R:ℝ) ≤ (b/T:ℕ) by linarith)
  have hqlog : Real.log q ≤ (b/T:ℕ) := by
    have hqq : Real.log q ≤ Real.log Q := Real.log_le_log (Nat.cast_pos.mpr hq) hqQ
    simp only [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg hQ),
      abs_of_nonneg (Real.rpow_nonneg hQ0.le _)] at hlog
    linarith
  have hsq : 4*T^2 ≤ b := by
    have H : (4:ℝ)*(T:ℝ)^2 ≤ b := by
      calc
        _ ≤ 4*(Q^(1/8:ℝ))^2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hTle 2) (by norm_num)
        _ = Q^(1/4:ℝ)*4 := by rw [← Real.rpow_mul_natCast hQ0.le]; norm_num; ring
        _ ≤ Q^(1/4:ℝ)*Q^(1/2:ℝ) := mul_le_mul_of_nonneg_left hhalf (by positivity)
        _ = Q^(3/4:ℝ) := by rw [← Real.rpow_add hQ0]; norm_num
        _ ≤ _ := hb
    exact_mod_cast H
  refine ⟨hT,hRT,hqlog,hsq,?_⟩
  have H : 2/η ≤ (b/T:ℕ) := by linarith
  have := (div_le_iff₀ hη).mp H
  simpa only [mul_comm] using this

lemma weighted_cutoff_large_iff {Q : ℝ} (hQ : 0 ≤ Q) (d : ℕ) :
    ⌊Q^(1/8:ℝ)⌋₊ < d ↔ ENNReal.ofReal Q ^ (1/8:ℝ) < (d:ℝ≥0∞) := by
  rw [Nat.floor_lt (Real.rpow_nonneg hQ _), ENNReal.ofReal_rpow_of_nonneg hQ (by norm_num)]
  by_cases hd : d = 0
  · simp [hd,Real.rpow_nonneg hQ _]
  · rw [← ENNReal.ofReal_natCast, ENNReal.ofReal_lt_ofReal_iff (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hd))]

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma weighted_log_power_error (n : ℕ) (ε C : ℝ) (hε : 0 < ε) :
    Tendsto (fun Q : ℝ => C * (2*3^n) * (Real.log Q)^(n+1) / Q^ε) atTop (𝓝 0) := by
  have H := (isLittleO_log_rpow_rpow_atTop ((n+1:ℕ):ℝ) hε).tendsto_div_nhds_zero
  simp only [Real.rpow_natCast] at H
  simpa only [mul_div_assoc,mul_zero] using
    (tendsto_const_nhds.mul H : Tendsto (fun Q : ℝ =>
      (C*(2*3^n))*((Real.log Q)^(n+1)/Q^ε)) atTop (𝓝 ((C*(2*3^n))*0)))

 

lemma eventual_weighted_tail_absorption (n : ℕ) (ε C η A₀ : ℝ)
    (hε : 0 < ε) (hC : 0 ≤ C) (hη : 0 < η) (hA : 1 ≤ A₀) :
    ∀ᶠ Q : ℝ in atTop, 0 < Q ∧ ∀ a b : ℕ, 2 ≤ b →
      (b:ℝ) ≤ A₀*Q → η*b ≤ (b:ℝ)-a →
      C * ((b:ℝ)*(1+Real.log b)^n) * Q^(-ε) ≤ ((b:ℝ)-a)/Real.log b := by
  filter_upwards [eventually_ge_atTop (max 1 A₀),
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    (weighted_log_power_error n ε C hε).eventually_le_const hη]
    with Q hQ hlogQ herr
  have hQ1 : 1 ≤ Q := (le_max_left _ _).trans hQ
  have hQ0 : 0 < Q := lt_of_lt_of_le zero_lt_one hQ1
  have hAQ : A₀ ≤ Q := (le_max_right _ _).trans hQ
  have hA0 : 0 < A₀ := lt_of_lt_of_le zero_lt_one hA
  refine ⟨hQ0,?_⟩
  intro a b hb hbQ hrel
  have hb0 : (0:ℝ) < b := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hb)
  have hlogb : 0 < Real.log (b:ℝ) := Real.log_pos (by exact_mod_cast hb : (1:ℝ)<b)
  have hlog : Real.log (b:ℝ) ≤ 2*Real.log Q := by
    have Hb := Real.log_le_log hb0 hbQ
    rw [Real.log_mul hA0.ne' hQ0.ne'] at Hb
    have HA := Real.log_le_log hA0 hAQ
    linarith
  have hbase : 0 ≤ 1+Real.log (b:ℝ) := by linarith
  have hbaseQ : 1+Real.log (b:ℝ) ≤ 3*Real.log Q := by linarith
  have hkernel : (Real.log (b:ℝ)*(1+Real.log b)^n)*Q^(-ε) ≤
      (2*3^n)*(Real.log Q)^(n+1)/Q^ε := by
    calc
      _ ≤ ((2*Real.log Q)*(3*Real.log Q)^n)*Q^(-ε) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hQ0.le _)
        exact mul_le_mul hlog (pow_le_pow_left₀ hbase hbaseQ n)
          (pow_nonneg hbase n) (by linarith)
      _ = _ := by rw [Real.rpow_neg hQ0.le,mul_pow,pow_succ]; ring
  have hkernelC : C*((Real.log (b:ℝ)*(1+Real.log b)^n)*Q^(-ε)) ≤ η := by
    calc
      _ ≤ C*((2*3^n)*(Real.log Q)^(n+1)/Q^ε) := mul_le_mul_of_nonneg_left hkernel hC
      _ = C*(2*3^n)*(Real.log Q)^(n+1)/Q^ε := by ring
      _ ≤ _ := herr
  apply (le_div_iff₀ hlogb).mpr
  have H := mul_le_mul_of_nonneg_left hkernelC hb0.le
  calc
    _ = (b:ℝ)*(C*((Real.log (b:ℝ)*(1+Real.log b)^n)*Q^(-ε))) := by ring
    _ ≤ (b:ℝ)*η := H
    _ ≤ _ := by simpa only [mul_comm] using hrel

end PrimeDegreePackets


namespace PrimeDegreePackets
open NumberField Finset Filter Topology
open scoped BigOperators ENNReal nonZeroDivisors

lemma dedekindZeta_real_one_le (K : Type*) [Field K] [NumberField K]
    {s : ℝ} (hs : 1 < s) : 1 ≤ (NumberField.dedekindZeta K s).re := by
  rw [dedekindZeta_real_eq_terms]
  have H := (idealCoefficient_real_summable K hs).le_tsum 1
    (fun m _ => realDirichletTerm_nonneg (idealCoefficientReal_nonneg K) s m)
  simpa [realDirichletTerm,idealCoefficientReal,idealCoefficient_one] using H

 

theorem weightedIdeal_interval_zeta_bound (n : ℕ) (hn0 : 0 < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ A₀ : ℝ, 1 ≤ A₀ → ∀ η : ℝ, 0 < η →
      ∀ᶠ Q : ℝ in atTop,
      ∀ (K : Type*) [Field K] [NumberField K] (M : FullLattice n K),
        Module.finrank ℚ K = n → (saturationIndex M : ℝ) ≤ Q →
        ∀ a b : ℕ, Q^(3/4:ℝ) ≤ (b:ℝ) → (b:ℝ) ≤ A₀*Q →
          a ≤ b → η*b ≤ (b:ℝ)-a →
          weightedIdealInterval M a b ≤ (saturationIndex M : ℝ≥0∞)⁻¹ *
            ENNReal.ofReal (C * ((b:ℝ)-a) *
              ((NumberField.dedekindZeta K (1+1/Real.log b)).re / Real.log b)) := by
  classical
  obtain ⟨C,hC,Hsmall⟩ := weightedIdeal_small_norm_bound n
  refine ⟨C+1,by linarith,?_⟩
  intro A₀ hA η hη
  obtain ⟨R,hR⟩ := Hsmall η hη
  let s : ℝ := 1/(2*(n:ℝ))
  have hs : 0 < s := by dsimp [s]; positivity
  have hε : 0 < s/16 := by positivity
  let Ctail : ℝ := localProductConstant n (s/16) hε
  have hCtail : 0 < Ctail := localProductConstant_pos n _ hε
  filter_upwards [eventual_weighted_small_parameters R η hη,
    eventual_weighted_tail_absorption n (s/16) Ctail η A₀ hε hCtail.le hη hA,
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<3/4)).eventually_ge_atTop 2]
    with Q hparam htail hQb
  intro K _ _ M hn hqQ a b hQb' hbQ hab hrel
  have hQ0 : 0 < Q := htail.1
  have hb : 2 ≤ b := by exact_mod_cast hQb.trans hQb'
  have hb0 : 0 < b := lt_of_lt_of_le (by decide : 0 < 2) hb
  have hlogb : 0 < Real.log (b:ℝ) := Real.log_pos (by exact_mod_cast hb : (1:ℝ)<b)
  have hΔ : 0 ≤ (b:ℝ)-a := sub_nonneg.mpr (by exact_mod_cast hab)
  have hz : 1 ≤ (NumberField.dedekindZeta K (1+1/Real.log b)).re := by
    have H := dedekindZeta_real_one_le K
      (show 1 < 1+1/Real.log (b:ℝ) by linarith [one_div_pos.mpr hlogb])
    simpa only [Complex.ofReal_add,Complex.ofReal_div,Complex.ofReal_one] using H
  let Z : ℝ := (NumberField.dedekindZeta K (1+1/Real.log b)).re / Real.log b
  have hZ : 0 ≤ Z := div_nonneg (by linarith) hlogb.le
  let T : ℕ := ⌊Q^(1/8:ℝ)⌋₊
  obtain ⟨hT,hRT,hqlog,hsquare,hlong⟩ := hparam.2 (saturationIndex M) b
    (Nat.pos_of_ne_zero (saturationIndex_ne_zero M)) hqQ hQb'
  have HS := hR K M hn a b T hT hRT hqlog hsquare hab hrel hlong
  have HL := weightedIdeal_large_norm_bound M hn hn0 a b hb0 Q hQ0 hqQ
  change (∑' I : primaryIntegralIdeals K (saturationIndex M).primeFactors,
      if ENNReal.ofReal Q^(1/8:ℝ) < (Ideal.absNorm I.1.1:ℝ≥0∞)
      then globalIdealWeight M (nonzeroIntegralIdealUnit I.1) *
        ENNReal.ofReal (∑ m ∈ Ioc (a/Ideal.absNorm I.1.1) (b/Ideal.absNorm I.1.1),
          coprimeIdealCoefficient K (saturationIndex M) m) else 0) ≤
      ENNReal.ofReal ((b:ℝ)*(1+Real.log b)^n) *
        ((saturationIndex M:ℝ≥0∞)⁻¹*ENNReal.ofReal Ctail*ENNReal.ofReal Q^(-s/16)) at HL
  have hbase : 0 ≤ (b:ℝ)*(1+Real.log b)^n :=
    mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by linarith) n)
  have htailZ : Ctail*((b:ℝ)*(1+Real.log b)^n)*Q^(-s/16) ≤ ((b:ℝ)-a)*Z := by
    calc
      _ ≤ ((b:ℝ)-a)/Real.log b := by
        simpa only [neg_div] using htail.2 a b hb hbQ hrel
      _ ≤ _ := by
        dsimp [Z]
        have := mul_le_mul_of_nonneg_left hz hΔ
        exact (div_le_div_of_nonneg_right (by simpa only [mul_one] using this) hlogb.le).trans_eq (by ring)
  have HL' : (∑' I : primaryIntegralIdeals K (saturationIndex M).primeFactors,
      if T < Ideal.absNorm I.1.1 then globalIdealWeight M (nonzeroIntegralIdealUnit I.1) *
        ENNReal.ofReal (∑ m ∈ Ioc (a/Ideal.absNorm I.1.1) (b/Ideal.absNorm I.1.1),
          coprimeIdealCoefficient K (saturationIndex M) m) else 0) ≤
        (saturationIndex M:ℝ≥0∞)⁻¹ * ENNReal.ofReal (((b:ℝ)-a)*Z) := by
    simp_rw [show T = ⌊Q^(1/8:ℝ)⌋₊ from rfl,weighted_cutoff_large_iff hQ0.le]
    apply HL.trans
    calc
      _ = (saturationIndex M:ℝ≥0∞)⁻¹ *
          ENNReal.ofReal (Ctail*((b:ℝ)*(1+Real.log b)^n)*Q^(-s/16)) := by
        rw [ENNReal.ofReal_mul (mul_nonneg hCtail.le hbase),ENNReal.ofReal_mul hCtail.le,
          ENNReal.ofReal_rpow_of_pos hQ0]
        ac_rfl
      _ ≤ _ := mul_le_mul_right (ENNReal.ofReal_le_ofReal htailZ) _
  calc
    weightedIdealInterval M a b ≤
        (saturationIndex M:ℝ≥0∞)⁻¹ * ENNReal.ofReal (C*((b:ℝ)-a)*Z) +
        (saturationIndex M:ℝ≥0∞)⁻¹ * ENNReal.ofReal (((b:ℝ)-a)*Z) := by
      rw [weightedIdealInterval_split M a b T]
      exact add_le_add HS HL'
    _ = _ := by
      rw [← mul_add, ← ENNReal.ofReal_add (mul_nonneg (mul_nonneg hC.le hΔ) hZ)
        (mul_nonneg hΔ hZ)]
      congr 2
      change C*((b:ℝ)-a)*Z+((b:ℝ)-a)*Z = (C+1)*((b:ℝ)-a)*Z
      ring

end PrimeDegreePackets
end
end

end OAI
