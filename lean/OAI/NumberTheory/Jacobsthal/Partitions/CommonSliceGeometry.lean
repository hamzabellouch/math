import Mathlib
import OAI.NumberTheory.Jacobsthal.Estimates.HeightBlockCount
import OAI.NumberTheory.Jacobsthal.Estimates.HypotheticalPairRows

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosCommonParameterInterval

noncomputable def commonLower (a R T : ℝ) : ℝ := max (a/R) (a/T)
noncomputable def commonUpper (b R T : ℝ) : ℝ := min (b/R) (b/T)

theorem div_between_endpoints (a : ℝ) {R p T : ℝ} (hR : 0 < R)
    (hRp : R ≤ p) (hpT : p ≤ T) :
    min (a/R) (a/T) ≤ a/p ∧ a/p ≤ max (a/R) (a/T) := by
  have hp : 0 < p := hR.trans_le hRp
  have hT : 0 < T := hp.trans_le hpT
  by_cases ha : 0 ≤ a
  · exact ⟨(min_le_right _ _).trans (div_le_div_of_nonneg_left ha hp hpT),
      (div_le_div_of_nonneg_left ha hR hRp).trans (le_max_left _ _)⟩
  · have han : 0 ≤ -a := by linarith
    have h1 := div_le_div_of_nonneg_left han hp hpT
    have h2 := div_le_div_of_nonneg_left han hR hRp
    simp only [neg_div] at h1 h2
    exact ⟨(min_le_left _ _).trans (by linarith),
      (show a/p ≤ a/T by linarith).trans (le_max_right _ _)⟩

theorem common_interval_subset (a b : ℝ) {R p T : ℝ} (hR : 0 < R)
    (hRp : R ≤ p) (hpT : p ≤ T) :
    Set.Ioc (commonLower a R T) (commonUpper b R T) ⊆ Set.Ioc (a/p) (b/p) := by
  intro m hm
  exact ⟨(div_between_endpoints a hR hRp hpT).2.trans_lt hm.1,
    hm.2.trans (div_between_endpoints b hR hRp hpT).1⟩

theorem commonLower_error (a : ℝ) {R T : ℝ} (hR : 0 < R) (hRT : R ≤ T) :
    commonLower a R T ≤ a/T+|a| *(1/R-1/T) := by
  have hT : 0 < T := hR.trans_le hRT
  have hd : 0 ≤ 1/R-1/T := sub_nonneg.mpr (one_div_le_one_div_of_le hR hRT)
  have he : a/R=a/T+a*(1/R-1/T) := by ring
  apply max_le
  · rw [he]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (le_abs_self a) hd)
  · exact le_add_of_nonneg_right (mul_nonneg (abs_nonneg a) hd)

theorem commonUpper_error (b : ℝ) {R T : ℝ} (hR : 0 < R) (hRT : R ≤ T) :
    b/T-|b| *(1/R-1/T) ≤ commonUpper b R T := by
  have hT : 0 < T := hR.trans_le hRT
  have hd : 0 ≤ 1/R-1/T := sub_nonneg.mpr (one_div_le_one_div_of_le hR hRT)
  have he : b/R=b/T+b*(1/R-1/T) := by ring
  apply le_min
  · rw [he]
    have h := mul_le_mul_of_nonneg_right (neg_abs_le b) hd
    nlinarith
  · exact sub_le_self _ (mul_nonneg (abs_nonneg b) hd)

theorem common_length_lower (a b : ℝ) {R T : ℝ} (hR : 0 < R) (hRT : R ≤ T) :
    (b-a)/T-(|a|+|b|)*(1/R-1/T) ≤ commonUpper b R T-commonLower a R T := by
  have hl := commonLower_error a hR hRT
  have hu := commonUpper_error b hR hRT
  have he : (b-a)/T-(|a|+|b|)*(1/R-1/T) =
      (b/T-|b| *(1/R-1/T))-(a/T+|a| *(1/R-1/T)) := by ring
  rw [he]
  exact sub_le_sub hu hl

theorem common_height_bound (a b m : ℝ) {R T : ℝ} (hR : 0 < R)
    (hm : m ∈ Set.Ioc (commonLower a R T) (commonUpper b R T)) :
    |m| ≤ max |a| |b|/R := by
  apply abs_le.mpr
  constructor
  · have h1 : -(max |a| |b|) ≤ a :=
      (neg_le_neg (le_max_left _ _)).trans (neg_abs_le a)
    have h2 := div_le_div_of_nonneg_right h1 hR.le
    have h3 : a/R ≤ commonLower a R T := le_max_left _ _
    rw [neg_div] at h2
    exact h2.trans (h3.trans hm.1.le)
  · have h1 : b ≤ max |a| |b| := (le_abs_self b).trans (le_max_right _ _)
    have h2 := div_le_div_of_nonneg_right h1 hR.le
    exact hm.2.trans ((min_le_left _ _).trans h2)





theorem reciprocal_width_bound {R T epsilon : ℝ} (hR : 0 < R) (hRT : R ≤ T)
    (hwidth : T ≤ (1+epsilon)*R) : 1/R-1/T ≤ epsilon/T := by
  have hT : 0 < T := hR.trans_le hRT
  have hdiv : T/R ≤ 1+epsilon := (div_le_iff₀ hR).mpr hwidth
  have he : (1/R-1/T)*T=T/R-1 := by field_simp
  apply (le_div_iff₀ hT).mpr
  rw [he]
  linarith

theorem common_length_lower_relative (a b : ℝ) {R T epsilon : ℝ}
    (hR : 0 < R) (hRT : R ≤ T) (hwidth : T ≤ (1+epsilon)*R) :
    ((b-a)-epsilon*(|a|+|b|))/T ≤ commonUpper b R T-commonLower a R T := by
  have hd := reciprocal_width_bound hR hRT hwidth
  have hmul := mul_le_mul_of_nonneg_left hd (add_nonneg (abs_nonneg a) (abs_nonneg b))
  calc
    _ = (b-a)/T-(|a|+|b|)*(epsilon/T) := by ring
    _ ≤ (b-a)/T-(|a|+|b|)*(1/R-1/T) := sub_le_sub_left hmul _
    _ ≤ _ := common_length_lower a b hR hRT

theorem affine_common_interval (A D Y q m : ℝ) {R p T : ℝ}
    (hq : 0 < q) (hR : 0 < R) (hRp : R ≤ p) (hpT : p ≤ T)
    (hm : m ∈ Set.Ioc (commonLower (-A/q) R T) (commonUpper ((D*Y-A)/q) R T)) :
    0 < A+p*q*m ∧ A+p*q*m ≤ D*Y := by
  have hp : 0 < p := hR.trans_le hRp
  have hc := common_interval_subset (-A/q) ((D*Y-A)/q) hR hRp hpT hm
  simp only [div_div] at hc
  have hl := (div_lt_iff₀ (mul_pos hq hp)).mp hc.1
  have hu := (le_div_iff₀ (mul_pos hq hp)).mp hc.2
  constructor <;> nlinarith

end ErdosCommonParameterInterval



namespace ErdosCommonMInterval
open ErdosCommonParameterInterval

noncomputable def lower (A q R T : ℝ) : ℝ := commonLower (-A/q) R T + 1
noncomputable def upper (A D Y q R T : ℝ) : ℝ := commonUpper ((D*Y-A)/q) R T
noncomputable def interval (A D Y q R T : ℝ) : Set ℝ :=
  Set.Icc (lower A q R T) (upper A D Y q R T)
noncomputable def referenceLength (Y R q : ℝ) : ℝ := Y/(R*q)
noncomputable def lengthExponent (P Y R q : ℝ) : ℝ := Real.log (referenceLength Y R q)/Real.log P

theorem closed_subset (A D Y q R T : ℝ) :
    interval A D Y q R T ⊆
      Set.Ioc (commonLower (-A/q) R T) (commonUpper ((D*Y-A)/q) R T) := by
  intro m hm
  exact ⟨by have := hm.1; dsimp [interval,lower] at this; linarith, hm.2⟩

theorem closed_affine {A D Y q R T m p : ℝ}
    (hq : 0 < q) (hR : 0 < R) (hRp : R ≤ p) (hpT : p ≤ T)
    (hm : m ∈ interval A D Y q R T) :
    0 < A+p*q*m ∧ A+p*q*m ≤ D*Y :=
  affine_common_interval A D Y q m hq hR hRp hpT (closed_subset A D Y q R T hm)

theorem integer_decode {A m : ℤ} {D Y q p : ℕ} {R T : ℝ}
    (hD : 0 < D) (hq : 0 < q) (hR : 0 < R)
    (hRp : R ≤ (p : ℝ)) (hpT : (p : ℝ) ≤ T)
    (hm : (m : ℝ) ∈ interval A D Y q R T)
    (hdvd : (D : ℤ) ∣ A+(p : ℤ)*q*m) :
    ∃ n : ℕ, 1 ≤ n ∧ n ≤ Y ∧ (D : ℤ)*n=A+(p : ℤ)*q*m := by
  have hb := closed_affine (by exact_mod_cast hq) hR hRp hpT hm
  obtain ⟨k,hk⟩ := hdvd
  have he : (A : ℝ)+(p : ℝ)*q*m=(D : ℝ)*(k : ℝ) := by exact_mod_cast hk
  have hDp : (0 : ℝ) < D := by exact_mod_cast hD
  have hkpos : (0 : ℝ) < k := by nlinarith [hb.1]
  have hkY : (k : ℝ) ≤ Y := by nlinarith [hb.2]
  have hkint : 0 ≤ k := le_of_lt (by exact_mod_cast hkpos : (0 : ℤ) < k)
  refine ⟨k.toNat, ?_, ?_, ?_⟩
  · have : (1 : ℤ) ≤ k := by exact_mod_cast (by exact_mod_cast hkpos : (0 : ℤ) < k)
    exact_mod_cast (show (1 : ℤ) ≤ (k.toNat : ℤ) by simpa [Int.toNat_of_nonneg hkint] using this)
  · have : k ≤ (Y : ℤ) := by exact_mod_cast hkY
    exact_mod_cast (show (k.toNat : ℤ) ≤ (Y : ℤ) by simpa [Int.toNat_of_nonneg hkint] using this)
  · simpa [Int.toNat_of_nonneg hkint] using hk.symm

def decode (A m : ℤ) (D q p : ℕ) : ℕ :=
  ((A+(p : ℤ)*q*m)/(D : ℤ)).toNat

theorem decode_spec {A m : ℤ} {D Y q p : ℕ} {R T : ℝ}
    (hD : 0 < D) (hq : 0 < q) (hR : 0 < R)
    (hRp : R ≤ (p : ℝ)) (hpT : (p : ℝ) ≤ T)
    (hm : (m : ℝ) ∈ interval A D Y q R T)
    (hdvd : (D : ℤ) ∣ A+(p : ℤ)*q*m) :
    1 ≤ decode A m D q p ∧ decode A m D q p ≤ Y ∧
      (D : ℤ)*decode A m D q p=A+(p : ℤ)*q*m := by
  obtain ⟨n,hn1,hnY,hn⟩ := integer_decode hD hq hR hRp hpT hm hdvd
  have hDn : (D : ℤ) ≠ 0 := by exact_mod_cast hD.ne'
  have hid : decode A m D q p=n := by
    unfold decode
    rw [← hn,Int.mul_ediv_cancel_left _ hDn]
    simp
  simpa only [hid] using And.intro hn1 (And.intro hnY hn)

theorem reference_rpow {P Y R q : ℝ} (hP : 1 < P)
    (hY : 0 < Y) (hR : 0 < R) (hq : 0 < q) :
    P ^ lengthExponent P Y R q = referenceLength Y R q := by
  have hJ : 0 < referenceLength Y R q := div_pos hY (mul_pos hR hq)
  rw [lengthExponent,Real.rpow_def_of_pos (by linarith : 0 < P)]
  rw [mul_div_cancel₀ _ (Real.log_pos hP).ne']
  exact Real.exp_log hJ

end ErdosCommonMInterval



namespace ErdosCommonMInterval
open ErdosCommonParameterInterval

theorem endpoint_magnitude {A D Y q : ℝ} (hD : 0 ≤ D) (hY : 0 ≤ Y) (hq : 0 < q) :
    |-A/q|+|(D*Y-A)/q| ≤ (D*Y+2*|A|)/q := by
  rw [abs_div,abs_div,abs_of_pos hq,abs_neg,← add_div]
  apply div_le_div_of_nonneg_right _ hq.le
  have h : |D*Y-A| ≤ |D*Y|+|A| := by
    simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (D*Y) 0 A
  rw [abs_of_nonneg (mul_nonneg hD hY)] at h
  linarith

theorem closed_length_lower {A D Y q R T H e : ℝ}
    (hD : 1 ≤ D) (hY : 0 < Y) (hq : 0 < q) (hR : 0 < R) (hRT : R ≤ T)
    (hH : 0 ≤ H) (he : 0 ≤ e) (hwidth : T ≤ (1+e)*R) (hA : |A| ≤ Y*H) :
    (1-2*e*(1+H))*D*referenceLength Y R q-1 ≤
      upper A D Y q R T-lower A q R T := by
  have hT : 0 < T := hR.trans_le hRT
  have hD0 : 0 < D := by linarith
  have hd0 : 0 ≤ 1/R-1/T := sub_nonneg.mpr (one_div_le_one_div_of_le hR hRT)
  have hd := (reciprocal_width_bound hR hRT hwidth).trans
    (div_le_div_of_nonneg_left he hR hRT)
  have hmag := endpoint_magnitude (A := A) hD0.le hY.le hq
  have hbase : (D*Y-A)/q-(-A/q) = D*Y/q := by ring
  have hnorm : D*Y/q+|-A/q|+|(D*Y-A)/q| ≤ 2*D*Y*(1+H)/q := by
    have hDH : Y*H ≤ D*Y*H := by nlinarith [mul_nonneg hY.le hH]
    have : (D*Y+2*|A|)/q ≤ (D*Y+2*D*Y*H)/q :=
      div_le_div_of_nonneg_right (by linarith) hq.le
    calc
      _ ≤ D*Y/q+(D*Y+2*D*Y*H)/q := by linarith
      _ = _ := by ring
  have hnorm0 : 0 ≤ D*Y/q+|-A/q|+|(D*Y-A)/q| := by positivity
  have hprod := mul_le_mul hnorm hd hd0 (by positivity : 0 ≤ 2*D*Y*(1+H)/q)
  have hf := common_length_lower (-A/q) ((D*Y-A)/q) hR hRT
  rw [hbase] at hf
  have heq : (D*Y/q)/T-(|-A/q|+|(D*Y-A)/q|)*(1/R-1/T) =
      D*Y/(R*q)-(D*Y/q+|-A/q|+|(D*Y-A)/q|)*(1/R-1/T) := by ring
  rw [heq] at hf
  dsimp [upper,lower,referenceLength]
  have heq2 : D*Y/(R*q)-(2*D*Y*(1+H)/q)*(e/R) =
      (1-2*e*(1+H))*D*(Y/(R*q)) := by ring
  linarith

theorem closed_length_upper (A D Y q R T : ℝ) :
    upper A D Y q R T-lower A q R T ≤ D*referenceLength Y R q-1 := by
  have hU : upper A D Y q R T ≤ ((D*Y-A)/q)/R := min_le_left _ _
  have hL : (-A/q)/R+1 ≤ lower A q R T := by
    have h : (-A/q)/R ≤ ErdosCommonParameterInterval.commonLower (-A/q) R T := le_max_left _ _
    dsimp [lower];linarith
  have heq : ((D*Y-A)/q)/R-((-A/q)/R+1)=D*referenceLength Y R q-1 := by
    dsimp [referenceLength];ring
  linarith

theorem closed_height {A D Y q R T H m : ℝ}
    (hD : 0 ≤ D) (hY : 0 < Y) (hq : 0 < q) (hR : 0 < R)
    (hA : |A| ≤ Y*H) (hm : m ∈ interval A D Y q R T) :
    |m| ≤ (D+H)*referenceLength Y R q := by
  have hb := common_height_bound (-A/q) ((D*Y-A)/q) m hR
    (closed_subset A D Y q R T hm)
  have ha : |-A/q| ≤ (D*Y+Y*H)/q := by
    rw [abs_div,abs_neg,abs_of_pos hq]
    exact div_le_div_of_nonneg_right (by nlinarith) hq.le
  have hc : |(D*Y-A)/q| ≤ (D*Y+Y*H)/q := by
    rw [abs_div,abs_of_pos hq]
    apply div_le_div_of_nonneg_right _ hq.le
    have h : |D*Y-A| ≤ |D*Y|+|A| := by
      simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (D*Y) 0 A
    rw [abs_of_nonneg (mul_nonneg hD hY.le)] at h
    linarith
  calc
    _ ≤ max |-A/q| |(D*Y-A)/q|/R := hb
    _ ≤ ((D*Y+Y*H)/q)/R := div_le_div_of_nonneg_right (max_le ha hc) hR.le
    _ = _ := by dsimp [referenceLength];ring

end ErdosCommonMInterval


section

open _root_.Filter
open scoped Topology
namespace ErdosCommonMInterval

theorem eventual_polynomial_cutoff (B K : ℝ) (hB : 0 ≤ B) (hK : 0 < K) :
    ∀ᶠ w : ℝ in atTop, 2 ≤ w ∧ w^B ≤ Real.exp (K*(Real.log w)^3) := by
  filter_upwards [eventually_ge_atTop (2 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (max 1 (B/K))] with w hw hL
  have hw0 : 0 < w := by linarith
  have hL1 : 1 ≤ Real.log w := (le_max_left _ _).trans hL
  have hBL : B ≤ K*Real.log w := by
    have := (div_le_iff₀ hK).mp (show B/K ≤ Real.log w from (le_max_right _ _).trans hL)
    nlinarith
  refine ⟨hw, ?_⟩
  rw [Real.rpow_def_of_pos hw0]
  apply Real.exp_le_exp.mpr
  have hsq : Real.log w ≤ (Real.log w)^2 := by nlinarith
  have hpow : (Real.log w)^2 ≤ (Real.log w)^3 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hBL (by linarith : 0 ≤ Real.log w)]

theorem subbin_loss {w C : ℝ} (hw : 1 ≤ w) (hC : 0 ≤ C) :
    2*w^(-2*C-10)*(1+w^(C+2)) ≤ 4*w^(-8 : ℝ) := by
  have hw0 : 0 < w := by linarith
  have hH : 1 ≤ w^(C+2) := Real.one_le_rpow hw (by linarith)
  have hmul : w^(-2*C-10)*w^(C+2) = w^(-C-8) := by
    rw [← Real.rpow_add hw0];congr 1;ring
  have hcmp : w^(-C-8) ≤ w^(-8 : ℝ) := Real.rpow_le_rpow_of_exponent_le hw (by linarith)
  have hnon : 0 ≤ w^(-2*C-10) := Real.rpow_nonneg hw0.le _
  have hle : w^(-2*C-10) ≤ w^(-2*C-10)*w^(C+2) := by nlinarith
  nlinarith

theorem height_absorption {w P C : ℝ} (hw : 2 ≤ w)
    (hP : w^(50*(C+3)) ≤ P) : 2*w^(C+2) ≤ P^((2 : ℝ)/100) := by
  have hw0 : 0 < w := by linarith
  have h1 : 2*w^(C+2) ≤ w^(C+3) := by
    have he : w^(C+3)=w*w^(C+2) := by
      calc w^(C+3) = w^((1 : ℝ)+(C+2)) := by congr 1;ring
           _ = w*w^(C+2) := by rw [Real.rpow_add hw0,Real.rpow_one]
    rw [he]
    exact mul_le_mul_of_nonneg_right hw (Real.rpow_nonneg hw0.le _)
  have h2 := Real.rpow_le_rpow (Real.rpow_nonneg hw0.le (50*(C+3))) hP
    (by norm_num : (0 : ℝ) ≤ 2/100)
  have he : (w^(50*(C+3)))^((2 : ℝ)/100)=w^(C+3) := by
    rw [← Real.rpow_mul hw0.le];congr 1;ring
  exact h1.trans (by rwa [he] at h2)

noncomputable def relativeError (w : ℝ) : ℝ := 4*w^(-8 : ℝ)+w^(-2 : ℝ)

theorem relativeError_tends_zero : Tendsto relativeError atTop (𝓝 0) := by
  have h8 := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 8)
  have h2 := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2)
  change Tendsto (fun w : ℝ => 4*w^(-8 : ℝ)+w^(-2 : ℝ)) atTop (𝓝 0)
  simpa only [mul_zero,add_zero] using (h8.const_mul 4).add h2

theorem uniform_common_interval (C K delta : ℝ) (hC : 0 ≤ C) (hK : 0 < K)
    (hd0 : 0 < delta) (hd1 : delta < 1) :
    ∃ W : ℝ, ∀ w : ℝ, W ≤ w → ∀ P A D Y q R T : ℝ,
      Real.exp (K*(Real.log w)^3) ≤ P →
      1 ≤ D → D ≤ w^C → 0 < Y → 0 < q → 0 < R → R ≤ T →
      T ≤ (1+w^(-2*C-10))*R → |A| ≤ Y*w^(C+2) →
      2 ≤ lengthExponent P Y R q →
      (1-delta)*D*referenceLength Y R q ≤ upper A D Y q R T-lower A q R T ∧
      upper A D Y q R T-lower A q R T ≤ D*referenceLength Y R q ∧
      (interval A D Y q R T).Nonempty ∧
      ∀ m ∈ interval A D Y q R T, |m| ≤ P^(lengthExponent P Y R q+(2 : ℝ)/100) := by
  have hE := relativeError_tends_zero.eventually (gt_mem_nhds hd0)
  have hpoly := eventual_polynomial_cutoff (50*(C+3)) K (by positivity) hK
  obtain ⟨W,hW⟩ := eventually_atTop.mp (hE.and hpoly)
  refine ⟨W, ?_⟩
  intro w hw P A D Y q R T hP hD hDu hY hq hR hRT hwidth hA hs
  obtain ⟨hErr,hw2,hpow⟩ := hW w hw
  have hw0 : 0 < w := by linarith
  have hw1 : 1 ≤ w := by linarith
  have hwpow : w ≤ w^(50*(C+3)) := by
    calc w = w^(1 : ℝ) := (Real.rpow_one _).symm
         _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hw1 (by nlinarith)
  have hwP : w ≤ P := hwpow.trans (hpow.trans hP)
  have hP1 : 1 < P := by linarith
  have hD0 : 0 < D := by linarith
  have hJ : 0 < referenceLength Y R q := div_pos hY (mul_pos hR hq)
  have hJid := reference_rpow hP1 hY hR hq
  have hJlow : P^2 ≤ referenceLength Y R q := by
    rw [← hJid]
    simpa only [Real.rpow_ofNat] using Real.rpow_le_rpow_of_exponent_le hP1.le hs
  have hJw : w^2 ≤ referenceLength Y R q := by nlinarith
  have hpay : 1 ≤ w^(-2 : ℝ)*D*referenceLength Y R q := by
    have hid : w^(-2 : ℝ)*w^2=1 := by
      rw [← Real.rpow_ofNat,← Real.rpow_add hw0];norm_num
    have hn : 0 ≤ w^(-2 : ℝ) := Real.rpow_nonneg hw0.le _
    have hm : w^2 ≤ D*referenceLength Y R q := by nlinarith
    have := mul_le_mul_of_nonneg_left hm hn
    nlinarith
  have hraw := closed_length_lower hD hY hq hR hRT
    (Real.rpow_nonneg hw0.le (C+2)) (Real.rpow_nonneg hw0.le (-2*C-10)) hwidth hA
  have hcost := subbin_loss hw1 hC
  have hlen : (1-delta)*D*referenceLength Y R q ≤
      upper A D Y q R T-lower A q R T := by
    have hmul := mul_le_mul_of_nonneg_right hcost (mul_pos hD0 hJ).le
    have herrmul := mul_le_mul_of_nonneg_right hErr.le (mul_pos hD0 hJ).le
    dsimp [relativeError] at herrmul
    nlinarith
  refine ⟨hlen, (closed_length_upper A D Y q R T).trans (by linarith), ?_, ?_⟩
  · apply Set.nonempty_Icc.mpr
    have := mul_pos (mul_pos (by linarith : 0 < 1-delta) hD0) hJ
    linarith
  · intro m hm
    have hheight := closed_height hD0.le hY hq hR hA hm
    have hDC : D ≤ w^(C+2) := hDu.trans
      (Real.rpow_le_rpow_of_exponent_le hw1 (by linarith))
    have habs := height_absorption hw2 (hpow.trans hP)
    have hp02 : D+w^(C+2) ≤ P^((2 : ℝ)/100) := by linarith
    calc
      |m| ≤ (D+w^(C+2))*referenceLength Y R q := hheight
      _ ≤ P^((2 : ℝ)/100)*referenceLength Y R q := mul_le_mul_of_nonneg_right hp02 hJ.le
      _ = P^(lengthExponent P Y R q+(2 : ℝ)/100) := by
        rw [← hJid,← Real.rpow_add (by linarith : 0 < P)];congr 1;ring

theorem uniform_integer_common_interval (C K delta : ℝ) (hC : 0 ≤ C) (hK : 0 < K)
    (hd0 : 0 < delta) (hd1 : delta < 1) :
    ∃ W : ℝ, ∀ w : ℝ, W ≤ w → ∀ P R T : ℝ, ∀ A : ℤ, ∀ D Y q : ℕ,
      Real.exp (K*(Real.log w)^3) ≤ P →
      0 < D → (D : ℝ) ≤ w^C → 0 < Y → 0 < q → 0 < R → R ≤ T →
      T ≤ (1+w^(-2*C-10))*R → |(A : ℝ)| ≤ (Y : ℝ)*w^(C+2) →
      2 ≤ lengthExponent P Y R q →
      (1-delta)*(D : ℝ)*referenceLength Y R q ≤ upper A D Y q R T-lower A q R T ∧
      upper A D Y q R T-lower A q R T ≤ (D : ℝ)*referenceLength Y R q ∧
      (interval A D Y q R T).Nonempty ∧
      (∀ m ∈ interval A D Y q R T, |m| ≤ P^(lengthExponent P Y R q+(2 : ℝ)/100)) ∧
      ∀ p : ℕ, ∀ m : ℤ, R ≤ (p : ℝ) → (p : ℝ) ≤ T →
        (m : ℝ) ∈ interval A D Y q R T → (D : ℤ) ∣ A+(p : ℤ)*q*m →
        1 ≤ decode A m D q p ∧ decode A m D q p ≤ Y ∧
          (D : ℤ)*decode A m D q p=A+(p : ℤ)*q*m := by
  obtain ⟨W,hW⟩ := uniform_common_interval C K delta hC hK hd0 hd1
  refine ⟨W, ?_⟩
  intro w hw P R T A D Y q hP hD hDu hY hq hR hRT hwidth hA hs
  have hb := hW w hw P A D Y q R T hP
    (by exact_mod_cast (show 1 ≤ D from hD)) hDu
    (by exact_mod_cast hY) (by exact_mod_cast hq) hR hRT hwidth hA hs
  refine ⟨hb.1,hb.2.1,hb.2.2.1,hb.2.2.2,?_⟩
  intro p m hRp hpT hm hdvd
  exact decode_spec hD hq hR hRp hpT hm hdvd

end ErdosCommonMInterval

end


namespace ErdosLargeHeightBlocks

noncomputable def blockLeft (C0 : ℤ) (R xi : ℝ) (H i : ℕ) : ℝ :=
  ErdosTagSubbins.left R xi (blockCount C0 R xi H) i
noncomputable def blockRight (C0 : ℤ) (R xi : ℝ) (H i : ℕ) : ℝ :=
  ErdosTagSubbins.right R xi (blockCount C0 R xi H) i

theorem block_reciprocal_variation (C0 : ℤ) (R xi : ℝ) (H i : ℕ)
    (hR : 0 < R) (hxi : 0 < xi) (hH : 0 < H) :
    |(C0 : ℝ)/blockLeft C0 R xi H i-(C0 : ℝ)/blockRight C0 R xi H i| ≤ (H : ℝ) := by
  let N := blockCount C0 R xi H
  let a := blockLeft C0 R xi H i
  let b := blockRight C0 R xi H i
  have hN : 0 < N := blockCount_pos C0 R xi H
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hs := ErdosTagSubbins.step_pos hR hxi hN
  have ha : R ≤ a := ErdosTagSubbins.left_lower hs.le
  have hab : a < b := ErdosTagSubbins.left_lt_right hR hxi hN
  have hb : R ≤ b := ha.trans hab.le
  have ha0 : 0 < a := hR.trans_le ha
  have hb0 : 0 < b := hR.trans_le hb
  have hd : b-a = ErdosTagSubbins.step R xi N := ErdosTagSubbins.right_sub_left R xi N i
  have hden : R^2 ≤ a*b := by
    simpa only [pow_two] using mul_le_mul ha hb hR.le ha0.le
  have he : (C0 : ℝ)/a-(C0 : ℝ)/b=(C0 : ℝ)*(b-a)/(a*b) := by
    field_simp
  have hcount := (div_le_iff₀ (mul_pos hR hHr)).mp (blockCount_lower C0 R xi H)
  change |(C0 : ℝ)/a-(C0 : ℝ)/b| ≤ (H : ℝ)
  rw [he,abs_div,abs_mul,abs_of_nonneg (sub_nonneg.mpr hab.le),abs_of_pos (mul_pos ha0 hb0)]
  calc
    _ ≤ |(C0 : ℝ)| * (b-a)/R^2 :=
      div_le_div_of_nonneg_left (mul_nonneg (abs_nonneg _) (sub_nonneg.mpr hab.le)) (sq_pos_of_pos hR) hden
    _ = xi*|(C0 : ℝ)|/(R*(N : ℝ)) := by
      rw [hd]
      dsimp [ErdosTagSubbins.step]
      field_simp
    _ ≤ _ := by
      apply (div_le_iff₀ (mul_pos hR hNr)).mpr
      change xi*|(C0 : ℝ)| ≤ (N : ℝ)*(R*(H : ℝ)) at hcount
      nlinarith

noncomputable def coordinateLower (C0 : ℤ) (R xi : ℝ) (H i : ℕ) : ℝ :=
  min ((C0 : ℝ)/blockLeft C0 R xi H i) ((C0 : ℝ)/blockRight C0 R xi H i)
noncomputable def coordinateUpper (C0 : ℤ) (R xi : ℝ) (H i : ℕ) : ℝ :=
  max ((C0 : ℝ)/blockLeft C0 R xi H i) ((C0 : ℝ)/blockRight C0 R xi H i)+(H : ℝ)

theorem block_coordinate_containment (C0 : ℤ) (R xi : ℝ) (H i : ℕ)
    (hR : 0 < R) (hxi : 0 < xi) (p m : ℝ)
    (hpL : blockLeft C0 R xi H i ≤ p) (hpU : p ≤ blockRight C0 R xi H i)
    (hmL : (C0 : ℝ)/p ≤ m) (hmU : m < (C0 : ℝ)/p+(H : ℝ)) :
    m ∈ Set.Ico (coordinateLower C0 R xi H i) (coordinateUpper C0 R xi H i) := by
  have hL : 0 < blockLeft C0 R xi H i :=
    ErdosTagSubbins.left_pos hR hxi (blockCount_pos C0 R xi H)
  have hb := ErdosCommonParameterInterval.div_between_endpoints (C0 : ℝ) hL hpL hpU
  refine ⟨hb.1.trans hmL,?_⟩
  dsimp only [coordinateUpper]
  linarith [hb.2]

theorem block_coordinate_width (C0 : ℤ) (R xi : ℝ) (H i : ℕ)
    (hR : 0 < R) (hxi : 0 < xi) (hH : 0 < H) :
    coordinateUpper C0 R xi H i-coordinateLower C0 R xi H i ≤ 2*(H : ℝ) := by
  have hv := block_reciprocal_variation C0 R xi H i hR hxi hH
  have he (x y : ℝ) : max x y-min x y=|x-y| := by
    rw [max_sub_min_eq_abs,abs_sub_comm]
  dsimp [coordinateUpper,coordinateLower]
  rw [show max ((C0 : ℝ)/blockLeft C0 R xi H i) ((C0 : ℝ)/blockRight C0 R xi H i)+(H : ℝ)-
      min ((C0 : ℝ)/blockLeft C0 R xi H i) ((C0 : ℝ)/blockRight C0 R xi H i) =
      (max ((C0 : ℝ)/blockLeft C0 R xi H i) ((C0 : ℝ)/blockRight C0 R xi H i)-
      min ((C0 : ℝ)/blockLeft C0 R xi H i) ((C0 : ℝ)/blockRight C0 R xi H i))+(H : ℝ) by ring,
    he]
  linarith

end ErdosLargeHeightBlocks



namespace ErdosStoppedArithmetic
open ErdosCommonMInterval ErdosAlignedProgression

theorem common_slice_mem_parameter (Y q p : ℕ) (r : ℚ) (R T : ℝ) (m : ℤ)
    (hq : 0 < q) (hR : 0 < R) (hRp : R ≤ (p : ℝ)) (hpT : (p : ℝ) ≤ T)
    (hm : (m : ℝ) ∈ interval r.num r.den Y q R T)
    (hdiv : (r.den : ℤ) ∣ r.num+((p*q : ℕ) : ℤ)*m) :
    m ∈ parameterInterval Y r (p*q) := by
  have hp : 0 < p := by exact_mod_cast hR.trans_le hRp
  have hdiv' : (r.den : ℤ) ∣ r.num+(p : ℤ)*q*m := by
    simpa only [Nat.cast_mul] using hdiv
  obtain ⟨n,hn,hY,he⟩ := integer_decode r.den_pos hq hR hRp hpT hm hdiv'
  apply (mem_parameterInterval Y r (p*q) (Nat.mul_pos hp hq) m).mpr
  have hD : (0 : ℤ) ≤ r.den := Int.natCast_nonneg _
  have hn' : (1 : ℤ) ≤ n := by exact_mod_cast hn
  have hY' : (n : ℤ) ≤ Y := by exact_mod_cast hY
  have hlo := mul_le_mul_of_nonneg_left hn' hD
  have hhi := mul_le_mul_of_nonneg_left hY' hD
  simp only [mul_one,he] at hlo hhi
  simpa only [Nat.cast_mul] using And.intro hlo hhi

theorem common_slice_endpoint_height (w Cs P R T : ℝ) (A : ℤ) (D Y q : ℕ)
    (hw : 1 ≤ w) (hP : 1 < P) (hDw : (D : ℝ) ≤ w^Cs)
    (hY : 0 < Y) (hq : 0 < q) (hR : 0 < R)
    (hA : |(A : ℝ)| ≤ (Y : ℝ)*w^(Cs+2))
    (hne : (interval A D Y q R T).Nonempty) :
    max |lower A q R T| |upper A D Y q R T| ≤
      2*w^(Cs+2)*P^(lengthExponent P Y R q) := by
  have hY' : (0 : ℝ) < Y := by exact_mod_cast hY
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hD' : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hEnds : lower A q R T ≤ upper A D Y q R T := Set.nonempty_Icc.mp hne
  have hLo := closed_height hD' hY' hq' hR hA
    (show lower A q R T ∈ interval A D Y q R T from ⟨le_rfl,hEnds⟩)
  have hHi := closed_height hD' hY' hq' hR hA
    (show upper A D Y q R T ∈ interval A D Y q R T from ⟨hEnds,le_rfl⟩)
  have hDC : (D : ℝ) ≤ w^(Cs+2) := hDw.trans
    (Real.rpow_le_rpow_of_exponent_le hw (by linarith))
  have hJ : 0 ≤ referenceLength Y R q := (div_pos hY' (mul_pos hR hq')).le
  have hBound := mul_le_mul_of_nonneg_right
    (show (D : ℝ)+w^(Cs+2) ≤ 2*w^(Cs+2) by linarith) hJ
  rw [reference_rpow hP hY' hR hq']
  exact (max_le hLo hHi).trans (by simpa only [mul_assoc] using hBound)

end ErdosStoppedArithmetic


end Erdos970

end OAI
