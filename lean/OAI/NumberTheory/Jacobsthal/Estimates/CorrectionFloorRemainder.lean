import OAI.NumberTheory.Jacobsthal.Analysis.ContinuousCorrectionLimit
import OAI.NumberTheory.Jacobsthal.Conclusions.JacobsthalSourceScale
import OAI.NumberTheory.Jacobsthal.Harmonic.AuxiliaryPolynomialLifting
import OAI.NumberTheory.Jacobsthal.Partitions.BoxInflation

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseBoxHeight

noncomputable def sourceW (z : ℝ) : ℝ := Real.log z/(Real.log (Real.log z))^2
noncomputable def sourceB (z : ℝ) : ℝ := Real.log z/Real.log (sourceW z)
noncomputable def sourceY (z : ℝ) : ℕ := ⌊z^2/(Real.log z)^2⌋₊

theorem source_B_bounds : ∀ᶠ z : ℝ in atTop,
    Real.exp 1 ≤ sourceW z ∧ 1 ≤ sourceB z ∧ sourceB z ≤ Real.log z := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop (2:ℝ) (by norm_num : (0:ℝ)<1)).bound (Real.exp_pos (-1))
  have hl := Real.tendsto_log_atTop.eventually hsmall
  have hlarge := Real.tendsto_log_atTop.eventually_ge_atTop (Real.exp 1)
  filter_upwards [hl,hlarge] with z hz hL
  let L := Real.log z
  have hL0 : 0 < L := (Real.exp_pos 1).trans_le hL
  have hLL : 1 ≤ Real.log L := by
    have h := Real.log_le_log (Real.exp_pos 1) hL
    simpa only [Real.log_exp] using h
  have hsq0 : 0 < (Real.log L)^2 := sq_pos_of_pos (by linarith)
  have hsq1 : 1 ≤ (Real.log L)^2 := by nlinarith
  have hbound : (Real.log L)^2 ≤ Real.exp (-1)*L := by
    change ‖(Real.log L)^(2:ℝ)‖ ≤ Real.exp (-1)*‖L^(1:ℝ)‖ at hz
    simpa only [Real.norm_eq_abs,Real.rpow_two,Real.rpow_one,
      abs_of_nonneg (sq_nonneg (Real.log L)),abs_of_pos hL0] using hz
  have hW : Real.exp 1 ≤ sourceW z := by
    apply (le_div_iff₀ hsq0).mpr
    have h := mul_le_mul_of_nonneg_left hbound (Real.exp_pos 1).le
    have he : Real.exp 1*Real.exp (-1)=1 := by rw [← Real.exp_add]; norm_num
    nlinarith
  have hW0 : 0 < sourceW z := (Real.exp_pos 1).trans_le hW
  have hlogW : 1 ≤ Real.log (sourceW z) := by
    have h := Real.log_le_log (Real.exp_pos 1) hW
    simpa only [Real.log_exp] using h
  have hWle : sourceW z ≤ L := div_le_self hL0.le hsq1
  have hlogle : Real.log (sourceW z) ≤ L := by
    have h := Real.log_le_log hW0 hWle
    have h' := Real.log_le_sub_one_of_pos hL0
    linarith
  refine ⟨hW,?_,?_⟩
  · exact (one_le_div (by linarith : 0 < Real.log (sourceW z))).mpr hlogle
  · exact div_le_self hL0.le hlogW

theorem sourceY_le_square {z : ℝ} (hL : 1 ≤ Real.log z) : (sourceY z : ℝ) ≤ z^2 := by
  have hden : 1 ≤ (Real.log z)^2 := by nlinarith
  exact (Nat.floor_le (div_nonneg (sq_nonneg z) (sq_nonneg _))).trans
    (div_le_self (sq_nonneg z) hden)

theorem source_cofactor_le_square {z p q : ℝ} (hL : 1 ≤ Real.log z)
    (hp : 1 ≤ p) (hq : 0 ≤ q) (hpq : p*q ≤ (sourceY z : ℝ)) : q ≤ z^2 := by
  have hmul : q ≤ p*q := by nlinarith [mul_le_mul_of_nonneg_right hp hq]
  exact hmul.trans (hpq.trans (sourceY_le_square hL))

end ErdosInverseBoxHeight

end

section

open _root_.Filter
open scoped Topology
namespace ErdosSourceLineBudget
open ErdosInverseBoxHeight

theorem source_W_power_quarter (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ z : ℝ in atTop, 1 < sourceW z ∧ (sourceW z)^C ≤ z^((1 : ℝ)/4) := by
  have hs := (isLittleO_log_rpow_rpow_atTop C (by norm_num : (0 : ℝ) < 1/4)).bound zero_lt_one
  have hLL := Real.tendsto_log_atTop.eventually_ge_atTop (Real.exp 1)
  filter_upwards [source_B_bounds,hs,hLL,eventually_gt_atTop (1 : ℝ)] with z hB hz hlog hz1
  have hz0 : 0 < z := by linarith
  have hL0 : 0 < Real.log z := Real.log_pos hz1
  have hLL1 : 1 ≤ Real.log (Real.log z) := by
    have h := Real.log_le_log (Real.exp_pos 1) hlog
    simpa only [Real.log_exp] using h
  have hsquare : 1 ≤ (Real.log (Real.log z))^2 := by nlinarith
  have hWL : sourceW z ≤ Real.log z := div_le_self hL0.le hsquare
  have hW1 : 1 < sourceW z := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le hB.1
  refine ⟨hW1,?_⟩
  have hh : (Real.log z)^C ≤ z^((1 : ℝ)/4) := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hL0.le C),
      abs_of_nonneg (Real.rpow_nonneg hz0.le ((1 : ℝ)/4)),one_mul] using hz
  exact (Real.rpow_le_rpow (by linarith) hWL hC).trans hh

theorem source_Y_three_halves :
    ∀ᶠ z : ℝ in atTop, z^((3 : ℝ)/2) ≤ (sourceY z : ℝ) := by
  have hs := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1/2)).bound
    (by norm_num : (0 : ℝ) < 1/2)
  filter_upwards [hs,eventually_ge_atTop (2 : ℝ)] with z hz hz2
  have hz0 : 0 < z := by linarith
  have hL : 0 < Real.log z := Real.log_pos (by linarith)
  have hL2 : 0 < (Real.log z)^2 := sq_pos_of_pos hL
  have hh : (Real.log z)^2 ≤ (1/2 : ℝ)*z^((1 : ℝ)/2) := by
    simpa only [Real.norm_eq_abs,Real.rpow_two,abs_of_nonneg (sq_nonneg (Real.log z)),
      abs_of_nonneg (Real.rpow_nonneg hz0.le ((1 : ℝ)/2))] using hz
  have hp : z^((1 : ℝ)/2)*z^((3 : ℝ)/2) = z^2 := by
    rw [← Real.rpow_add hz0]
    norm_num
  have hmul : 2*z^((3 : ℝ)/2)*(Real.log z)^2 ≤ z^2 := by
    nlinarith [mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hz0.le ((3 : ℝ)/2))]
  have hquot : 2*z^((3 : ℝ)/2) ≤ z^2/(Real.log z)^2 := (le_div_iff₀ hL2).mpr hmul
  have hfloor := Nat.lt_floor_add_one (z^2/(Real.log z)^2)
  have hone : 1 ≤ z^((3 : ℝ)/2) := Real.one_le_rpow (by linarith) (by norm_num)
  change z^((3 : ℝ)/2) ≤ (⌊z^2/(Real.log z)^2⌋₊ : ℝ)
  linarith

end ErdosSourceLineBudget

end

section

open _root_.Filter
open scoped Topology
namespace ErdosSourceLineBudget
open ErdosInverseBoxHeight

theorem source_parent_square_lower (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ z : ℝ in atTop, 1 < z ∧ ∀ p q R S : ℝ,
      0 < p → 0 < q → p ≤ 2*R → R ≤ z^((1 : ℝ)/100) → q ≤ S →
      Real.logb (sourceW z) ((sourceY z : ℝ)/(p*q)) ≤ C → z ≤ S := by
  have hquarter := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 24/100)).eventually_ge_atTop 2
  filter_upwards [source_W_power_quarter C hC,source_Y_three_halves,hquarter,
    eventually_gt_atTop (1 : ℝ)] with z hW hY htwo hz
  have hz0 : 0 < z := by linarith
  refine ⟨hz,?_⟩
  intro p q R S hp hq hpR hR hqS hlen
  have hY0 : (0 : ℝ) < sourceY z := (Real.rpow_pos_of_pos hz0 _).trans_le hY
  have hP : p ≤ z^((1 : ℝ)/4) := by
    calc
      p ≤ 2*R := hpR
      _ ≤ 2*z^((1 : ℝ)/100) := mul_le_mul_of_nonneg_left hR (by norm_num)
      _ ≤ z^((24 : ℝ)/100)*z^((1 : ℝ)/100) :=
        mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hz0.le _)
      _ = z^((1 : ℝ)/4) := by rw [← Real.rpow_add hz0];norm_num
  have hratio := (Real.logb_le_iff_le_rpow hW.1 (div_pos hY0 (mul_pos hp hq))).mp hlen
  have hmul : (sourceY z : ℝ) ≤ (sourceW z)^C*(p*q) := (div_le_iff₀ (mul_pos hp hq)).mp hratio
  have hsmall : (sourceW z)^C*p ≤ z^((1 : ℝ)/2) := by
    calc
      _ ≤ z^((1 : ℝ)/4)*z^((1 : ℝ)/4) := mul_le_mul hW.2 hP hp.le
        (Real.rpow_nonneg hz0.le _)
      _ = _ := by rw [← Real.rpow_add hz0];norm_num
  have hle : z^((3 : ℝ)/2) ≤ z^((1 : ℝ)/2)*q := by
    apply hY.trans
    apply hmul.trans
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hsmall hq.le
  have he : z^((3 : ℝ)/2) = z^((1 : ℝ)/2)*z := by
    have hh := Real.rpow_add hz0 ((1 : ℝ)/2) 1
    norm_num at hh
    exact hh
  rw [he] at hle
  exact (le_of_mul_le_mul_left hle (Real.rpow_pos_of_pos hz0 ((1 : ℝ)/2))).trans hqS

end ErdosSourceLineBudget

end

section

open _root_.Filter
open scoped Topology
namespace ErdosSourceLineBudget
open ErdosInverseBoxHeight

theorem source_Z_ge_two : ∀ᶠ z : ℝ in atTop, 2 ≤ sourceZ z := by
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (Real.exp 1)] with z hz
  have hL : 0 < Real.log z := (Real.exp_pos 1).trans_le hz
  have hLL : 1 ≤ Real.log (Real.log z) := by
    have hh := Real.log_le_log (Real.exp_pos 1) hz
    simpa only [Real.log_exp] using hh
  have hLLL : Real.log (Real.log z) ≤ Real.log z := by
    have hh := Real.log_le_sub_one_of_pos hL
    linarith
  have hratio : 1 ≤ Real.log z/Real.log (Real.log z) :=
    (one_le_div (by linarith)).mpr hLLL
  have hexp : (2 : ℝ) ≤ Real.exp 1 := by
    have hh := Real.add_one_le_exp (1 : ℝ)
    norm_num at hh ⊢
    exact hh
  exact hexp.trans (Real.exp_le_exp.mpr hratio)

theorem extraction_small_power {z R S Z : ℝ} (hz : 1 < z) (hR : 0 ≤ R) (hZ : 0 ≤ Z)
    (hRz : R ≤ z^((1 : ℝ)/100)) (hZz : Z ≤ z^((1 : ℝ)/100)) (hSz : z ≤ S)
    (hbig : 728 < z^((19 : ℝ)/75)) :
    728*R^4*Z^4 < S^((1 : ℝ)/3) := by
  have hz0 : 0 < z := by linarith
  have hR4 : R^4 ≤ z^((4 : ℝ)/100) := by
    calc
      _ ≤ (z^((1 : ℝ)/100))^4 := by gcongr
      _ = _ := by rw [← Real.rpow_mul_natCast hz0.le];norm_num
  have hZ4 : Z^4 ≤ z^((4 : ℝ)/100) := by
    calc
      _ ≤ (z^((1 : ℝ)/100))^4 := by gcongr
      _ = _ := by rw [← Real.rpow_mul_natCast hz0.le];norm_num
  calc
    _ ≤ 728*z^((4 : ℝ)/100)*z^((4 : ℝ)/100) := by gcongr
    _ = 728*z^((2 : ℝ)/25) := by rw [mul_assoc,← Real.rpow_add hz0];norm_num
    _ < z^((19 : ℝ)/75)*z^((2 : ℝ)/25) :=
      mul_lt_mul_of_pos_right hbig (Real.rpow_pos_of_pos hz0 _)
    _ = z^((1 : ℝ)/3) := by rw [← Real.rpow_add hz0];norm_num
    _ ≤ S^((1 : ℝ)/3) := Real.rpow_le_rpow hz0.le hSz (by norm_num)

theorem minimum_line_size_power {z R S Z : ℝ} (hz : 1 < z) (hR : 0 < R) (hZ : 0 < Z)
    (hRz : R ≤ z^((1 : ℝ)/100)) (hZz : Z ≤ z^((1 : ℝ)/100)) (hSz : z ≤ S) :
    z^((93 : ℝ)/100) ≤ S/(R*Z^6) := by
  have hz0 : 0 < z := by linarith
  have hZ6 : Z^6 ≤ z^((6 : ℝ)/100) := by
    calc
      _ ≤ (z^((1 : ℝ)/100))^6 := by gcongr
      _ = _ := by rw [← Real.rpow_mul_natCast hz0.le];norm_num
  have hprod : R*Z^6 ≤ z^((7 : ℝ)/100) := by
    calc
      _ ≤ z^((1 : ℝ)/100)*z^((6 : ℝ)/100) := by gcongr
      _ = _ := by rw [← Real.rpow_add hz0];norm_num
  apply (le_div_iff₀ (mul_pos hR (pow_pos hZ 6))).mpr
  calc
    _ ≤ z^((93 : ℝ)/100)*z^((7 : ℝ)/100) :=
      mul_le_mul_of_nonneg_left hprod (Real.rpow_nonneg hz0.le _)
    _ = z := by rw [← Real.rpow_add hz0];norm_num
    _ ≤ S := hSz

end ErdosSourceLineBudget

end

section

namespace ErdosSourceLineBudget

theorem finite_extraction_budget (D : ℕ) (R S Z : ℝ) (hD : (D : ℝ) ≤ R)
    (hR : 0 < R) (hS : 1 ≤ S) (hZ : 2 ≤ Z)
    (hsmall : 728*R^4*Z^4 < S^((1 : ℝ)/3)) :
    182*(D : ℝ)^4*(1+S^((2 : ℝ)/3))+(D : ℝ)*(S/(R*Z^6)) < S/Z^4 := by
  have hS0 : 0 < S := by linarith
  have hZ0 : 0 < Z := by linarith
  have hu : 1 ≤ S^((2 : ℝ)/3) := Real.one_le_rpow hS (by norm_num)
  have hprod : S^((1 : ℝ)/3)*S^((2 : ℝ)/3) = S := by
    rw [← Real.rpow_add hS0]
    norm_num
  have hlarge : 728*R^4*Z^4*S^((2 : ℝ)/3) < S := by
    have hh := mul_lt_mul_of_pos_right hsmall (Real.rpow_pos_of_pos hS0 ((2 : ℝ)/3))
    rwa [hprod] at hh
  have hnonlinear : 182*(D : ℝ)^4*(1+S^((2 : ℝ)/3)) < S/(2*Z^4) := by
    have hpower : (D : ℝ)^4 ≤ R^4 := by gcongr
    have hfirst : 182*(D : ℝ)^4*(1+S^((2 : ℝ)/3)) ≤ 364*R^4*S^((2 : ℝ)/3) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hpower) (show 0 ≤ 1+S^((2 : ℝ)/3) by positivity),
        mul_nonneg (pow_nonneg hR.le 4) (sub_nonneg.mpr hu)]
    apply hfirst.trans_lt
    apply (lt_div_iff₀ (by positivity : 0 < 2*Z^4)).mpr
    nlinarith
  have hlinear : (D : ℝ)*(S/(R*Z^6)) ≤ S/(2*Z^4) := by
    calc
      _ ≤ R*(S/(R*Z^6)) := mul_le_mul_of_nonneg_right hD (by positivity)
      _ = S/Z^6 := by field_simp
      _ ≤ S/(2*Z^4) := by
        apply div_le_div_of_nonneg_left hS0.le (by positivity)
        have hs : 2 ≤ Z^2 := by nlinarith
        nlinarith [mul_nonneg (pow_nonneg hZ0.le 4) (sub_nonneg.mpr hs)]
  calc
    _ < S/(2*Z^4)+S/(2*Z^4) := add_lt_add_of_lt_of_le hnonlinear hlinear
    _ = _ := by ring

end ErdosSourceLineBudget

end

section

namespace ErdosSourcePolynomial
open ErdosAuxiliaryPolynomial

noncomputable def sourceDegree (z R : ℝ) : ℕ := ⌊R/(Real.log z)^2⌋₊

theorem sourceDegree_le {z R : ℝ} (hR : 0 ≤ R) :
    (sourceDegree z R : ℝ) ≤ R/(Real.log z)^2 :=
  Nat.floor_le (div_nonneg hR (sq_nonneg _))

theorem sourceDegree_le_R {z R : ℝ} (hR : 0 ≤ R) (hL : 1 ≤ Real.log z) :
    (sourceDegree z R : ℝ) ≤ R :=
  (sourceDegree_le hR).trans (div_le_self hR (by nlinarith))

theorem source_degree_factor {z R : ℝ} (hR : 0 < R) (hL : 0 < Real.log z) :
    2/((sourceDegree z R : ℝ)+2) ≤ 2*(Real.log z)^2/R := by
  have hf := Nat.lt_floor_add_one (R/(Real.log z)^2)
  change R/(Real.log z)^2 < (sourceDegree z R : ℝ)+1 at hf
  have hden : (0 : ℝ) < (sourceDegree z R : ℝ)+2 := by positivity
  have hsq : 0 < (Real.log z)^2 := sq_pos_of_pos hL
  have hprod : R ≤ ((sourceDegree z R : ℝ)+2)*(Real.log z)^2 :=
    (div_le_iff₀ hsq).mp (by linarith)
  apply (div_le_div_iff₀ hden hR).mpr
  convert! (mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 2)) using 1
  ring

theorem dimension_le_square (D : ℕ) : ((D+2).choose 2 : ℝ) ≤ ((D : ℝ)+2)^2 := by
  have h := Nat.choose_le_pow (D+2) 2
  exact_mod_cast h

theorem source_dimension_log_bound {z R : ℝ} (hz : 2 ≤ z) (hR : 0 ≤ R)
    (hRz : R ≤ z) (hL : 1 ≤ Real.log z) :
    Real.log ((sourceDegree z R+2).choose 2 : ℝ) ≤ 4*Real.log z := by
  have hd := sourceDegree_le_R hR hL
  have hn := dimension_le_square (sourceDegree z R)
  have hz0 : 0 ≤ z := by linarith
  have hD2 : (sourceDegree z R : ℝ)+2 ≤ z^2 := by nlinarith
  have hN : ((sourceDegree z R+2).choose 2 : ℝ) ≤ z^4 := by
    apply hn.trans
    calc
      _ ≤ (z^2)^2 := by gcongr
      _ = z^4 := by ring
  have hpos : (0 : ℝ) < ((sourceDegree z R+2).choose 2 : ℝ) := by
    exact_mod_cast dimension_pos (sourceDegree z R)
  have h := Real.log_le_log hpos hN
  simpa only [Real.log_pow,Nat.cast_ofNat] using h

end ErdosSourcePolynomial

end

section

open _root_.Filter
open scoped Topology
namespace ErdosSourceLineBudget
open ErdosInverseBoxHeight ErdosSourcePolynomial

theorem uniform_extraction_budget (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ z : ℝ in atTop, 1 < z ∧ ∀ p q R S : ℝ,
      0 < p → 0 < q → p ≤ 2*R → R ≤ z^((1 : ℝ)/100) → q ≤ S →
      Real.logb (sourceW z) ((sourceY z : ℝ)/(p*q)) ≤ C →
      z^((93 : ℝ)/100) ≤ S/(R*(sourceZ z)^6) ∧ 1 ≤ S/(R*(sourceZ z)^6) ∧
      182*(sourceDegree z R : ℝ)^4*(1+S^((2 : ℝ)/3))+
        (sourceDegree z R : ℝ)*(S/(R*(sourceZ z)^6)) < S/(sourceZ z)^4 := by
  have hbig := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 19/75)).eventually_gt_atTop 728
  filter_upwards [source_parent_square_lower C hC,sourceZ_le_small_power,source_Z_ge_two,hbig,
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with z hparent hZ hZ2 hlarge hL
  refine ⟨hparent.1,?_⟩
  intro p q R S hp hq hpR hR hqS hlen
  have hSz := hparent.2 p q R S hp hq hpR hR hqS hlen
  have hR0 : 0 < R := by linarith
  have hS1 : 1 ≤ S := hparent.1.le.trans hSz
  have hmin := minimum_line_size_power hparent.1 hR0 hZ.2.1 hR hZ.2.2 hSz
  have hmin1 : 1 ≤ S/(R*(sourceZ z)^6) :=
    (Real.one_le_rpow hparent.1.le (by norm_num : (0 : ℝ) ≤ 93/100)).trans hmin
  have hsmall := extraction_small_power hparent.1 hR0.le hZ.2.1.le hR hZ.2.2 hSz hlarge
  exact ⟨hmin,hmin1,finite_extraction_budget (sourceDegree z R) R S (sourceZ z)
    (sourceDegree_le_R hR0.le hL) hR0 hS1 hZ2 hsmall⟩

end ErdosSourceLineBudget

end

section

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped Topology
namespace ErdosCorrectionLimit
open ErdosContinuousAnomaly ErdosBoundaryIntegral
open NumberTheoryLean.DerivativeWeights NumberTheoryLean.BuchstabBridge
open NumberTheoryLean.JacobsthalSourceScale

noncomputable def sourcePrefactor (s : ℝ) : ℝ := phiEven s/s^2

theorem sourcePrefactor_continuousAt : ContinuousAt sourcePrefactor 2 := by
  exact (phiEven_continuousAt (by norm_num : (1:ℝ)<2)).div (continuousAt_id.pow 2) (by norm_num)

theorem sourcePrefactor_two : sourcePrefactor 2=Real.exp Real.eulerMascheroniConstant := by
  unfold sourcePrefactor
  rw [phiEven_initial (s := 2) le_rfl]
  norm_num [evenInitial,sieveA]
  ring

theorem sourcePrefactor_limit {s : ℝ → ℝ} (hs : Tendsto s atTop (𝓝 2)) :
    Tendsto (fun L => sourcePrefactor (s L)) atTop (𝓝 (Real.exp Real.eulerMascheroniConstant)) := by
  simpa only [sourcePrefactor_two] using! sourcePrefactor_continuousAt.tendsto.comp hs

noncomputable def paperGap (a : ℝ) (e : ℝ → ℝ) (L : ℝ) : ℝ :=
  2*sourceB L-a+2-2*Real.log L/Real.log (sourceW L)+e L

theorem paper_ratio_tendsto (a : ℝ) {e : ℝ → ℝ} (he : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun L => paperGap a e L/sourceB L) atTop (𝓝 2) := by
  have hn : Tendsto (fun L : ℝ => (-a+2+e L)/sourceB L) atTop (𝓝 0) :=
    ((tendsto_const_nhds.add he).div_atTop sourceB_tendsto)
  have hl : Tendsto (fun L : ℝ => Real.log L/L) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have ht : Tendsto (fun L : ℝ => 2+(-a+2+e L)/sourceB L-2*(Real.log L/L)) atTop (𝓝 2) := by
    simpa only [add_zero,mul_zero,sub_zero] using (tendsto_const_nhds.add hn).sub (hl.const_mul 2)
  apply ht.congr'
  filter_upwards [source_scale_eventually,eventually_gt_atTop (0:ℝ)] with L hs hL
  have hw : Real.log (sourceW L) ≠ 0 := (Real.log_pos hs.1).ne'
  unfold paperGap sourceB
  field_simp
  ring

theorem paper_prefactor_tendsto (a : ℝ) {e : ℝ → ℝ} (he : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun L => (sourceB L)^2*phiEven (paperGap a e L/sourceB L)/(paperGap a e L)^2)
      atTop (𝓝 (Real.exp Real.eulerMascheroniConstant)) := by
  have ht := sourcePrefactor_limit (paper_ratio_tendsto a he)
  apply ht.congr'
  filter_upwards [source_scale_eventually] with L hs
  unfold sourcePrefactor
  field_simp

end ErdosCorrectionLimit

end

section

open _root_.Filter
open scoped Topology
namespace ErdosCorrectionLimit
open NumberTheoryLean.JacobsthalSourceScale

noncomputable def unroundedY (L : ℝ) : ℝ := Real.exp (2*L)/L^2

noncomputable def floorRemainder (L : ℝ) : ℝ :=
  (Real.log (⌊unroundedY L⌋₊ : ℝ)-(2*L-2*Real.log L))/Real.log (sourceW L)

theorem unroundedY_tendsto : Tendsto unroundedY atTop atTop := by
  simpa only [unroundedY,Real.rpow_two] using! tendsto_exp_mul_div_rpow_atTop 2 2 (by norm_num)

theorem floor_log_error_tendsto :
    Tendsto (fun L => Real.log (⌊unroundedY L⌋₊ : ℝ)-(2*L-2*Real.log L)) atTop (𝓝 0) := by
  have hratio := (tendsto_nat_floor_div_atTop (R := ℝ)).comp unroundedY_tendsto
  have hh := (Real.continuousAt_log (by norm_num : (1:ℝ)≠0)).tendsto.comp hratio
  simp only [Real.log_one] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ),unroundedY_tendsto.eventually (eventually_ge_atTop (2:ℝ))] with L hL hY
  have hYpos : 0 < unroundedY L := by linarith
  have hfloor : 0 < (⌊unroundedY L⌋₊ : ℝ) := by
    exact_mod_cast (Nat.floor_pos.mpr (by linarith : 1 ≤ unroundedY L))
  have hL0 : L ≠ 0 := by linarith
  change Real.log ((⌊unroundedY L⌋₊ : ℝ)/unroundedY L)=_
  rw [Real.log_div hfloor.ne' hYpos.ne']
  congr 1
  rw [unroundedY,Real.log_div (Real.exp_ne_zero _) (pow_ne_zero 2 hL0),Real.log_exp,Real.log_pow]
  norm_num

theorem floorRemainder_tendsto : Tendsto floorRemainder atTop (𝓝 0) := by
  exact floor_log_error_tendsto.div_atTop (Real.tendsto_log_atTop.comp sourceW_tendsto)

theorem sourceY_exp (L : ℝ) :
    ErdosInverseBoxHeight.sourceY (Real.exp L)=⌊unroundedY L⌋₊ := by
  unfold ErdosInverseBoxHeight.sourceY unroundedY
  rw [Real.log_exp,pow_two,← Real.exp_add]
  congr 2
  ring_nf

theorem paperGap_floor_eq (a : ℝ) {L : ℝ} (hW : 1 < sourceW L) :
    paperGap a floorRemainder L=
      Real.log (ErdosInverseBoxHeight.sourceY (Real.exp L):ℝ)/Real.log (sourceW L)-a+2 := by
  rw [sourceY_exp]
  have hw0 : Real.log (sourceW L) ≠ 0 := (Real.log_pos hW).ne'
  unfold paperGap floorRemainder sourceB
  field_simp
  ring

end ErdosCorrectionLimit

end

end Erdos970

end OAI
