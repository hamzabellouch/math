import OAI.Geometry.LatticeCovering.Transport

namespace OAI

section
noncomputable section
noncomputable section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
noncomputable section
noncomputable section

namespace SingleLatticeCovering.SimplexYoung
open MeasureTheory
open scoped ENNReal



theorem volume_weightedSimplexConfiguration_sharp {r d : ℕ} (hr : 0 < r)
    {J : Set (Fin d → ℝ)} (hJ : IsCompact J) (c : Fin r → ℝ) (hc : ∀ j, c j ≠ 0) :
    volume (weightedSimplexConfiguration J c) ≤
      ENNReal.ofReal ((simplexConstant r)^d *
        (∏ j, |c j|^(-((d:ℝ)/(r+1:ℕ)))) * (volume J).toReal^r) := by
  convert volume_weightedSimplexConfiguration_le hr hJ c hc using 1
  congr 1
  exact (weightedCircuitFactor hr (fun j => |c j|) (fun j => abs_pos.mpr (hc j))
    _ _ ENNReal.toReal_nonneg).symm


end SingleLatticeCovering.SimplexYoung

namespace SingleLatticeCovering.SimplexYoung
open scoped ENNReal BigOperators

lemma tsum_int_inv_sq_le_four : (∑' z : ℤ, 1/(z:ℝ)^2) ≤ 4 := by
  have hs : Summable (fun z : ℤ => 1/(z:ℝ)^2) :=
    Real.summable_one_div_int_pow.mpr (by norm_num)
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat (by intro z; simp) hs]
  have he : (∑' z : ℕ+, 1/((z:ℕ):ℝ)^2) = Real.pi^2/6 := by
    rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ => 1/(n:ℝ)^2)]
    have hh := hasSum_zeta_two.summable.tsum_eq_zero_add
    simpa only [hasSum_zeta_two.tsum_eq, Nat.cast_zero, zero_pow (by omega : 2 ≠ 0),
      div_zero, zero_add] using hh.symm
  simp only [Int.cast_zero, zero_pow (by omega : 2 ≠ 0), div_zero, zero_add,
    Int.cast_natCast, he, two_smul]
  nlinarith [Real.pi_lt_d2, Real.pi_pos]

lemma int_circuit_weight_le_sq (q : ℝ) (hq : 2 ≤ q) (z : ℤ) :
    |(z:ℝ)|^(-q) ≤ 1/(z:ℝ)^2 := by
  by_cases hz : z = 0
  · simp [hz, Real.zero_rpow (by linarith : -q ≠ 0)]
  have habs : (1:ℝ) ≤ |(z:ℝ)| := by exact_mod_cast Int.one_le_abs hz
  calc
    _ ≤ |(z:ℝ)|^(-(2:ℝ)) := Real.rpow_le_rpow_of_exponent_le habs (by linarith)
    _ = _ := by rw [Real.rpow_neg (abs_nonneg _), Real.rpow_two, sq_abs, one_div]

lemma tsum_ennreal_int_circuit_weight_le (q : ℝ) (hq : 2 ≤ q) :
    (∑' z : ℤ, ENNReal.ofReal (|(z:ℝ)|^(-q))) ≤ 4 := by
  calc
    _ ≤ ∑' z : ℤ, ENNReal.ofReal (1/(z:ℝ)^2) :=
      ENNReal.tsum_le_tsum (fun z => ENNReal.ofReal_le_ofReal (int_circuit_weight_le_sq q hq z))
    _ = ENNReal.ofReal (∑' z : ℤ, 1/(z:ℝ)^2) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity)
        (Real.summable_one_div_int_pow.mpr (by norm_num))).symm
    _ ≤ 4 := by exact_mod_cast ENNReal.ofReal_le_ofReal tsum_int_inv_sq_le_four

lemma tsum_ennreal_fin_prod (r : ℕ) (f : ℤ → ℝ≥0∞) :
    (∑' a : Fin r → ℤ, ∏ j, f (a j)) = (∑' z, f z)^r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [←(Fin.consEquiv (fun _ : Fin (r+1) => ℤ)).tsum_eq]
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [ENNReal.tsum_prod (f := fun (z : ℤ) (a : Fin r → ℤ) => f z * ∏ j, f (a j))]
    simp_rw [ENNReal.tsum_mul_left]
    rw [ih, ENNReal.tsum_mul_right, pow_succ']



theorem tsum_integerCircuitWeight_le (r : ℕ) (q : ℝ) (hq : 2 ≤ q) :
    (∑' a : Fin r → ℤ, ENNReal.ofReal (∏ j, |(a j:ℝ)|^(-q))) ≤ 4^r := by
  simp_rw [ENNReal.ofReal_prod_of_nonneg (fun _ _ => Real.rpow_nonneg (abs_nonneg _) _)]
  rw [tsum_ennreal_fin_prod r (fun z : ℤ => ENNReal.ofReal (|(z:ℝ)|^(-q)))]
  exact pow_le_pow_left' (tsum_ennreal_int_circuit_weight_le q hq) _


end SingleLatticeCovering.SimplexYoung


namespace SingleLatticeCovering.SimplexYoung
open MeasureTheory
open scoped ENNReal BigOperators


def integerCircuitVolumeSum {r d : ℕ} (J : Set (Fin d → ℝ)) : ℝ≥0∞ :=
  ∑' c : Fin r → ℤ, if ∀ j, c j ≠ 0 then
    volume (weightedSimplexConfiguration J (fun j => (c j:ℝ))) else 0




theorem integerCircuitVolumeSum_le {r d : ℕ} (hr : 0 < r) (hd : 2*(r+1) ≤ d)
    {J : Set (Fin d → ℝ)} (hJ : IsCompact J) :
    integerCircuitVolumeSum (r := r) J ≤
      ENNReal.ofReal ((4:ℝ)^r * (simplexConstant r)^d * (volume J).toReal^r) := by
  have hq : (2:ℝ) ≤ (d:ℝ)/(r+1:ℕ) := by
    apply (le_div_iff₀ (by positivity)).mpr
    exact_mod_cast hd
  let B : ℝ≥0∞ := ENNReal.ofReal ((simplexConstant r)^d * (volume J).toReal^r)
  have h (c : Fin r → ℤ) :
      (if ∀ j, c j ≠ 0 then volume (weightedSimplexConfiguration J (fun j => (c j:ℝ))) else 0) ≤
        B * ENNReal.ofReal (∏ j, |(c j:ℝ)|^(-((d:ℝ)/(r+1:ℕ)))) := by
    split_ifs with hc
    · apply (volume_weightedSimplexConfiguration_sharp hr hJ (fun j => (c j:ℝ))
        (fun j => Int.cast_ne_zero.mpr (hc j))).trans_eq
      dsimp [B]
      rw [←ENNReal.ofReal_mul (mul_nonneg (pow_nonneg (by unfold simplexConstant; positivity) _) (pow_nonneg ENNReal.toReal_nonneg _))]
      congr 1
      ring
    · exact bot_le
  calc
    _ ≤ ∑' c : Fin r → ℤ, B * ENNReal.ofReal (∏ j, |(c j:ℝ)|^(-((d:ℝ)/(r+1:ℕ)))) :=
      ENNReal.tsum_le_tsum h
    _ = B * (∑' c : Fin r → ℤ, ENNReal.ofReal (∏ j, |(c j:ℝ)|^(-((d:ℝ)/(r+1:ℕ))))) :=
      ENNReal.tsum_mul_left
    _ ≤ B * 4^r := mul_le_mul_right (tsum_integerCircuitWeight_le r _ hq) _
    _ = _ := by
      dsimp [B]
      rw [←ENNReal.ofReal_ofNat, ←ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 4),
        ←ENNReal.ofReal_mul (mul_nonneg (pow_nonneg (by unfold simplexConstant; positivity) _) (pow_nonneg ENNReal.toReal_nonneg _))]
      congr 1
      ring


end SingleLatticeCovering.SimplexYoung

namespace SingleLatticeCovering.SimplexYoung
open MeasureTheory
open scoped ENNReal BigOperators

lemma rationalCircuitFactor {r d : ℕ} (a : Fin (r+1) → ℝ) (ha : ∀ j, 0 < a j) :
    (a 0)⁻¹^d * (∏ j : Fin r, (a j.succ / a 0)^(-((d:ℝ)/(r+1:ℕ)))) =
      ∏ j : Fin (r+1), a j^(-((d:ℝ)/(r+1:ℕ))) := by
  let s : ℝ := (d:ℝ)/(r+1:ℕ)
  change (a 0)⁻¹^d * (∏ j : Fin r, (a j.succ / a 0)^(-s)) = ∏ j, a j^(-s)
  simp_rw [Real.div_rpow (ha _).le (ha 0).le]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Fin.prod_univ_succ]
  have he : (a 0)⁻¹^d / ((a 0)^(-s))^r = (a 0)^(-s) := by
    rw [←Real.rpow_natCast, ←Real.rpow_neg_one, ←Real.rpow_mul (ha 0).le,
      ←Real.rpow_natCast, ←Real.rpow_mul (ha 0).le, ←Real.rpow_sub (ha 0)]
    congr 1
    dsimp [s]
    push_cast
    field_simp
    ring
  calc
    _ = ((a 0)⁻¹^d / ((a 0)^(-s))^r) * ∏ j : Fin r, a j.succ^(-s) := by ring
    _ = _ := by rw [he]



def rationalCircuitVolume {r d : ℕ} (J : Set (Fin d → ℝ))
    (a : Fin (r+1) → ℤ) : ℝ≥0∞ :=
  if ∀ j, a j ≠ 0 then ENNReal.ofReal (|(a 0:ℝ)|⁻¹^d) *
    volume (weightedSimplexConfiguration J (fun j => -(a j.succ:ℝ)/(a 0:ℝ))) else 0

lemma rationalCircuitVolume_le {r d : ℕ} (hr : 0 < r)
    {J : Set (Fin d → ℝ)} (hJ : IsCompact J) (a : Fin (r+1) → ℤ) :
    rationalCircuitVolume J a ≤ ENNReal.ofReal ((simplexConstant r)^d *
      (∏ j, |(a j:ℝ)|^(-((d:ℝ)/(r+1:ℕ)))) * (volume J).toReal^r) := by
  classical
  unfold rationalCircuitVolume
  split_ifs with ha
  · have hc (j : Fin r) : -(a j.succ:ℝ)/(a 0:ℝ) ≠ 0 :=
      div_ne_zero (neg_ne_zero.mpr (Int.cast_ne_zero.mpr (ha j.succ))) (Int.cast_ne_zero.mpr (ha 0))
    have hb := volume_weightedSimplexConfiguration_sharp hr hJ _ hc
    apply (mul_le_mul_right hb _).trans_eq
    rw [←ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp_rw [abs_div, abs_neg]
    calc
      _ = (simplexConstant r)^d *
          (|(a 0:ℝ)|⁻¹^d * (∏ j : Fin r, (|(a j.succ:ℝ)|/|(a 0:ℝ)|)^(-((d:ℝ)/(r+1:ℕ))))) *
          (volume J).toReal^r := by ring
      _ = _ := by rw [rationalCircuitFactor _ (fun j => abs_pos.mpr (Int.cast_ne_zero.mpr (ha j)))]
  · exact bot_le



def rationalCircuitVolumeSum {r d : ℕ} (J : Set (Fin d → ℝ)) : ℝ≥0∞ :=
  ∑' a : Fin (r+1) → ℤ, rationalCircuitVolume J a

theorem rationalCircuitVolumeSum_le {r d : ℕ} (hr : 0 < r) (hd : 2*(r+1) ≤ d)
    {J : Set (Fin d → ℝ)} (hJ : IsCompact J) :
    rationalCircuitVolumeSum (r := r) J ≤
      ENNReal.ofReal ((4:ℝ)^(r+1) * (simplexConstant r)^d * (volume J).toReal^r) := by
  have hq : (2:ℝ) ≤ (d:ℝ)/(r+1:ℕ) := by
    apply (le_div_iff₀ (by positivity)).mpr
    exact_mod_cast hd
  let B : ℝ≥0∞ := ENNReal.ofReal ((simplexConstant r)^d * (volume J).toReal^r)
  calc
    _ ≤ ∑' a : Fin (r+1) → ℤ, B * ENNReal.ofReal (∏ j, |(a j:ℝ)|^(-((d:ℝ)/(r+1:ℕ)))) := by
      apply ENNReal.tsum_le_tsum
      intro a
      apply (rationalCircuitVolume_le hr hJ a).trans_eq
      dsimp [B]
      rw [←ENNReal.ofReal_mul (mul_nonneg (pow_nonneg (by unfold simplexConstant; positivity) _) (pow_nonneg ENNReal.toReal_nonneg _))]
      congr 1
      ring
    _ = B * (∑' a : Fin (r+1) → ℤ, ENNReal.ofReal (∏ j, |(a j:ℝ)|^(-((d:ℝ)/(r+1:ℕ))))) :=
      ENNReal.tsum_mul_left
    _ ≤ B * 4^(r+1) := mul_le_mul_right (tsum_integerCircuitWeight_le (r+1) _ hq) _
    _ = _ := by
      dsimp [B]
      rw [←ENNReal.ofReal_ofNat, ←ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 4),
        ←ENNReal.ofReal_mul (mul_nonneg (pow_nonneg (by unfold simplexConstant; positivity) _) (pow_nonneg ENNReal.toReal_nonneg _))]
      congr 1
      ring




end SingleLatticeCovering.SimplexYoung

namespace SingleLatticeCovering.SimplexYoung
open scoped ENNReal BigOperators

lemma affine_three_product_abs_ge_two (a : Fin 3 → ℤ)
    (ha : ∀ j, a j ≠ 0) (hs : ∑ j, a j = 0) :
    (2:ℝ) ≤ ∏ j, |(a j:ℝ)| := by
  have hm (j : Fin 3) : (1:ℝ) ≤ |(a j:ℝ)| := by exact_mod_cast Int.one_le_abs (ha j)
  have hl : 2 ≤ |a 0| ∨ 2 ≤ |a 1| ∨ 2 ≤ |a 2| := by
    by_contra h
    push Not at h
    have h0 := le_abs_self (a 0)
    have h0' := neg_le_abs (a 0)
    have h1 := le_abs_self (a 1)
    have h1' := neg_le_abs (a 1)
    have h2 := le_abs_self (a 2)
    have h2' := neg_le_abs (a 2)
    have hz0 := ha 0
    have hz1 := ha 1
    have hz2 := ha 2
    rw [Fin.sum_univ_three] at hs
    omega
  rw [Fin.prod_univ_three]
  have h01 : (1:ℝ) ≤ |(a 0:ℝ)| * |(a 1:ℝ)| := by nlinarith [hm 0,hm 1]
  have h02 : (1:ℝ) ≤ |(a 0:ℝ)| * |(a 2:ℝ)| := by nlinarith [hm 0,hm 2]
  have h12 : (1:ℝ) ≤ |(a 1:ℝ)| * |(a 2:ℝ)| := by nlinarith [hm 1,hm 2]
  rcases hl with hl | hl | hl
  · have hl' : (2:ℝ) ≤ |(a 0:ℝ)| := by exact_mod_cast hl
    nlinarith [mul_le_mul_of_nonneg_left h12 (abs_nonneg (a 0:ℝ))]
  · have hl' : (2:ℝ) ≤ |(a 1:ℝ)| := by exact_mod_cast hl
    nlinarith [mul_le_mul_of_nonneg_left h02 (abs_nonneg (a 1:ℝ))]
  · have hl' : (2:ℝ) ≤ |(a 2:ℝ)| := by exact_mod_cast hl
    nlinarith [mul_le_mul_of_nonneg_right h01 (abs_nonneg (a 2:ℝ))]

lemma prod_circuit_weight_with_saving {r : ℕ} (b : Fin r → ℝ) (hb : ∀ j, 0 < b j)
    {s : ℝ} (hs : 2 ≤ s) (hp : 2 ≤ ∏ j, b j) :
    (∏ j, b j^(-s)) ≤ (2:ℝ)^(2-s) * ∏ j, b j^(-(2:ℝ)) := by
  have hprod : 0 < ∏ j, b j := Finset.prod_pos (fun j _ => hb j)
  rw [Real.finsetProd_rpow _ _ (fun j _ => (hb j).le),
    Real.finsetProd_rpow _ _ (fun j _ => (hb j).le)]
  calc
    _ = (∏ j, b j)^(2-s) * (∏ j, b j)^(-(2:ℝ)) := by
      rw [←Real.rpow_add hprod]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos (by norm_num) hp (by linarith)) (by positivity)


theorem tsum_affine_three_weight_le {s : ℝ} (hs : 2 ≤ s) :
    (∑' a : Fin 3 → ℤ, if (∀ j, a j ≠ 0) ∧ (∑ j, a j = 0) then
      ENNReal.ofReal (∏ j, |(a j:ℝ)|^(-s)) else 0) ≤
        ENNReal.ofReal ((2:ℝ)^(2-s)) * 4^3 := by
  classical
  calc
    _ ≤ ∑' a : Fin 3 → ℤ, ENNReal.ofReal ((2:ℝ)^(2-s)) *
        ENNReal.ofReal (∏ j, |(a j:ℝ)|^(-(2:ℝ))) := by
      apply ENNReal.tsum_le_tsum
      intro a
      split_ifs with h
      · rw [←ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        exact prod_circuit_weight_with_saving _
          (fun j => abs_pos.mpr (Int.cast_ne_zero.mpr (h.1 j))) hs
          (affine_three_product_abs_ge_two a h.1 h.2)
      · exact bot_le
    _ = ENNReal.ofReal ((2:ℝ)^(2-s)) *
        (∑' a : Fin 3 → ℤ, ENNReal.ofReal (∏ j, |(a j:ℝ)|^(-(2:ℝ)))) := ENNReal.tsum_mul_left
    _ ≤ _ := mul_le_mul_right (tsum_integerCircuitWeight_le 3 2 le_rfl) _

lemma two_neg_third_le : (2:ℝ)^(-(1:ℝ)/3) ≤ 8/9 := by
  have hc : ((2:ℝ)^(-(1:ℝ)/3))^3 = (1:ℝ)/2 := by
    rw [←Real.rpow_mul_natCast (by norm_num)]
    norm_num
  have hn : 0 ≤ (2:ℝ)^(-(1:ℝ)/3) := by positivity
  nlinarith [sq_nonneg ((2:ℝ)^(-(1:ℝ)/3) - 8/9)]




end SingleLatticeCovering.SimplexYoung
namespace SingleLatticeCovering.SimplexYoung
lemma simplexConstant_sq {r : ℕ} (hr : 0 < r) :
    (simplexConstant r)^2 = (1 + (r:ℝ)⁻¹)^r / (r+1:ℕ) := by
  have h : 0 < (r:ℝ) := Nat.cast_pos.mpr hr
  unfold simplexConstant
  rw [div_pow, ←pow_mul, mul_comm r 2, pow_mul, inv_pow,
    Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  congr 1
  congr 1
  push_cast
  field_simp

end SingleLatticeCovering.SimplexYoung
namespace SingleLatticeCovering.SimplexYoung
open MeasureTheory
open scoped ENNReal BigOperators

lemma rank_two_saved_constant : simplexConstant 2 * (2:ℝ)^(-(1:ℝ)/3) ≤ simplexConstant 3 := by
  have htwo : (simplexConstant 2)^2 = (3:ℝ)/4 := by rw [simplexConstant_sq (by norm_num)]; norm_num
  have hthree : (simplexConstant 3)^2 = (16:ℝ)/27 := by rw [simplexConstant_sq (by norm_num)]; norm_num
  have he : simplexConstant 2 * (8/9:ℝ) = simplexConstant 3 := by
    have h2 := simplexConstant_nonneg 2
    have h3 := simplexConstant_nonneg 3
    nlinarith
  exact (mul_le_mul_of_nonneg_left two_neg_third_le (simplexConstant_nonneg 2)).trans_eq he

lemma rank_two_saved_power (d : ℕ) :
    (simplexConstant 2)^d * (2:ℝ)^(2-(d:ℝ)/3) ≤ 4*(simplexConstant 3)^d := by
  have he : (2:ℝ)^(2-(d:ℝ)/3) = 4*((2:ℝ)^(-(1:ℝ)/3))^d := by
    rw [←Real.rpow_mul_natCast (by norm_num), ←show (2:ℝ)^(2:ℝ) = 4 by norm_num,
      ←Real.rpow_add (by norm_num)]
    congr 1
    ring
  rw [he]
  calc
    _ = 4*(simplexConstant 2 * (2:ℝ)^(-(1:ℝ)/3))^d := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (mul_nonneg (simplexConstant_nonneg 2) (by positivity)) rank_two_saved_constant d) (by norm_num)



def affineCircuitVolumeSum {r d : ℕ} (J : Set (Fin d → ℝ)) : ℝ≥0∞ :=
  ∑' a : Fin (r+1) → ℤ, if ∑ j, a j = 0 then rationalCircuitVolume J a else 0



theorem affineRankTwoCircuitVolumeSum_le {d : ℕ} (hd : 6 ≤ d)
    {J : Set (Fin d → ℝ)} (hJ : IsCompact J) :
    affineCircuitVolumeSum (r := 2) J ≤
      ENNReal.ofReal (256 * (simplexConstant 3)^d * (volume J).toReal^2) := by
  classical
  have hs : (2:ℝ) ≤ (d:ℝ)/3 := by
    apply (le_div_iff₀ (by norm_num)).mpr
    exact_mod_cast hd
  let B : ℝ≥0∞ := ENNReal.ofReal ((simplexConstant 2)^d * (volume J).toReal^2)
  have h (a : Fin 3 → ℤ) :
      (if ∑ j, a j = 0 then rationalCircuitVolume J a else 0) ≤
        B * (if (∀ j, a j ≠ 0) ∧ ∑ j, a j = 0 then
          ENNReal.ofReal (∏ j, |(a j:ℝ)|^(-((d:ℝ)/3))) else 0) := by
    by_cases ha : ∀ j, a j ≠ 0
    · by_cases hz : ∑ j, a j = 0
      · rw [ite_eq_left hz, ite_eq_left ⟨ha,hz⟩]
        apply (rationalCircuitVolume_le (r := 2) (by norm_num) hJ a).trans_eq
        dsimp [B]
        rw [←ENNReal.ofReal_mul (mul_nonneg (pow_nonneg (simplexConstant_nonneg 2) _) (sq_nonneg _))]
        congr 1
        ring
      · simp [hz]
    · simp [rationalCircuitVolume, ha]
  calc
    _ ≤ ∑' a : Fin 3 → ℤ, B * (if (∀ j, a j ≠ 0) ∧ ∑ j, a j = 0 then
          ENNReal.ofReal (∏ j, |(a j:ℝ)|^(-((d:ℝ)/3))) else 0) := ENNReal.tsum_le_tsum h
    _ = B * (∑' a : Fin 3 → ℤ, if (∀ j, a j ≠ 0) ∧ ∑ j, a j = 0 then
          ENNReal.ofReal (∏ j, |(a j:ℝ)|^(-((d:ℝ)/3))) else 0) := ENNReal.tsum_mul_left
    _ ≤ B * (ENNReal.ofReal ((2:ℝ)^(2-(d:ℝ)/3)) * 4^3) :=
      mul_le_mul_right (tsum_affine_three_weight_le hs) _
    _ = ENNReal.ofReal (64*((simplexConstant 2)^d*(2:ℝ)^(2-(d:ℝ)/3))*(volume J).toReal^2) := by
      dsimp [B]
      rw [show (4:ℝ≥0∞)^3 = ENNReal.ofReal (64:ℝ) by norm_num,
        ←ENNReal.ofReal_mul (by positivity),
        ←ENNReal.ofReal_mul (mul_nonneg (pow_nonneg (simplexConstant_nonneg 2) _) (sq_nonneg _))]
      congr 1
      ring
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have hh := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (rank_two_saved_power d) (by norm_num : (0:ℝ) ≤ 64))
        (sq_nonneg (volume J).toReal)
      nlinarith only [hh]




end SingleLatticeCovering.SimplexYoung




noncomputable section
namespace SingleLatticeCovering.GridCoordinates
open MeasureTheory Measure Set TopologicalSpace.PositiveCompacts
open scoped BigOperators


def flatten {r d : ℕ} : (Fin d → Fin r → ℝ) ≃ₗ[ℝ] (Fin r × Fin d → ℝ) where
  toFun x ij := x ij.2 ij.1
  invFun x j i := x (i,j)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma flatten_unit_preimage {r d : ℕ} :
    (flatten (r:=r) (d:=d)) ⁻¹' (piIcc01 (Fin r × Fin d) : Set (Fin r × Fin d → ℝ)) =
      Set.pi Set.univ (fun _ : Fin d => Set.pi Set.univ (fun _ : Fin r => Set.Icc (0:ℝ) 1)) := by
  ext x
  simp only [Set.mem_preimage, piIcc01, TopologicalSpace.PositiveCompacts.coe_mk,
    TopologicalSpace.Compacts.coe_mk, Set.mem_univ_pi, flatten, LinearEquiv.coe_mk,
    LinearMap.coe_mk, AddHom.coe_mk, Prod.forall]
  exact forall_comm



theorem flatten_measurePreserving {r d : ℕ} :
    MeasurePreserving (flatten (r:=r) (d:=d)) volume volume := by
  have hm : Measurable (flatten (r:=r) (d:=d) : (Fin d → Fin r → ℝ) → (Fin r × Fin d → ℝ)) :=
    flatten.toContinuousLinearEquiv.continuous.measurable
  have : IsAddHaarMeasure (volume.map (flatten (r:=r) (d:=d))) :=
    flatten.toContinuousLinearEquiv.isAddHaarMeasure_map volume
  refine ⟨hm, ?_⟩
  have hunit : (volume.map (flatten (r:=r) (d:=d))) (piIcc01 (Fin r × Fin d)) = 1 := by
    rw [Measure.map_apply hm
      (piIcc01 (Fin r × Fin d)).isCompact.measurableSet, flatten_unit_preimage]
    simp only [volume_pi, Measure.pi_pi, Real.volume_Icc, sub_zero,
      ENNReal.ofReal_one, Finset.prod_const_one]
  have he := (addHaarMeasure_eq_iff (piIcc01 (Fin r × Fin d))
    (volume.map (flatten (r:=r) (d:=d)))).mpr hunit
  rw [addHaarMeasure_eq_volume_pi] at he
  exact he.symm


end SingleLatticeCovering.GridCoordinates

namespace SingleLatticeCovering.CircuitVolume
open MeasureTheory Measure Set Filter
open GridCoordinates GridGeometry SimplexYoung
open scoped Topology Pointwise BigOperators

lemma configuration_preimage {r d : ℕ} (J : Set (Fin d → ℝ)) (c : Fin r → ℝ) :
    flatten ⁻¹' weightedGridConfiguration J c = weightedSimplexConfiguration J c := rfl

lemma configuration_volume {r d : ℕ} {J : Set (Fin d → ℝ)} (hJ : IsCompact J)
    (c : Fin r → ℝ) :
    volume (weightedGridConfiguration J c) = volume (weightedSimplexConfiguration J c) := by
  have h := (flatten_measurePreserving (r:=r) (d:=d)).measure_preimage
    (weightedGridConfiguration_compact hJ c).measurableSet.nullMeasurableSet
  simpa only [configuration_preimage] using h.symm

lemma rationalCircuitVolume_toReal {r d : ℕ} {J : Set (Fin d → ℝ)} (hJ : IsCompact J)
    (a : Fin (r+1) → ℤ) (ha : ∀ i, a i ≠ 0) :
    (rationalCircuitVolume J a).toReal =
      volume.real (weightedGridConfiguration J (fun i => -(a i.succ:ℝ)/(a 0:ℝ))) /
        |(a 0:ℝ)|^d := by
  rw [rationalCircuitVolume, ite_eq_left ha, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity), measureReal_def, configuration_volume hJ]
  rw [inv_pow, div_eq_mul_inv, mul_comm]

lemma summable_rationalCircuitVolume_toReal {r d : ℕ} (hr : 0 < r)
    (hd : 2*(r+1) ≤ d) {J : Set (Fin d → ℝ)} (hJ : IsCompact J) :
    Summable (fun a : Fin (r+1) → ℤ => (rationalCircuitVolume J a).toReal) := by
  apply ENNReal.summable_toReal
  exact ne_of_lt (lt_of_le_of_lt (rationalCircuitVolumeSum_le hr hd hJ) ENNReal.ofReal_lt_top)

lemma affineCircuitVolumeSum_ne_top {r d : ℕ} (hr : 0 < r)
    (hd : 2*(r+1) ≤ d) {J : Set (Fin d → ℝ)} (hJ : IsCompact J) :
    affineCircuitVolumeSum (r:=r) J ≠ ⊤ := by
  have hh : affineCircuitVolumeSum (r:=r) J ≤ rationalCircuitVolumeSum (r:=r) J := by
    apply ENNReal.tsum_le_tsum
    intro a
    split_ifs <;> simp
  exact ne_of_lt (lt_of_le_of_lt (hh.trans (rationalCircuitVolumeSum_le hr hd hJ)) ENNReal.ofReal_lt_top)


def PrimitiveAffineCoefficients (r : ℕ) :=
  {a : Fin (r+1) → ℤ // (∀ i, a i ≠ 0) ∧ Finset.univ.gcd a = 1 ∧ ∑ i, a i = 0}

lemma primitive_volume_sum_le {r d : ℕ} (hr : 0 < r)
    (hd : 2*(r+1) ≤ d) {J : Set (Fin d → ℝ)} (hJ : IsCompact J) :
    (∑' a : PrimitiveAffineCoefficients r, (rationalCircuitVolume J a.val).toReal) ≤
      (affineCircuitVolumeSum (r:=r) J).toReal := by
  have hsub : (∑' a : PrimitiveAffineCoefficients r, rationalCircuitVolume J a.val) ≤
      affineCircuitVolumeSum (r:=r) J := by
    have hh := ENNReal.tsum_comp_le_tsum_of_injective
      (Subtype.val_injective (p:=fun a : Fin (r+1) → ℤ =>
        (∀ i, a i ≠ 0) ∧ Finset.univ.gcd a = 1 ∧ ∑ i, a i = 0))
      (fun a : Fin (r+1) → ℤ => if ∑ i, a i = 0 then rationalCircuitVolume J a else 0)
    change (∑' a : PrimitiveAffineCoefficients r,
      if ∑ i, a.val i = 0 then rationalCircuitVolume J a.val else 0) ≤ _ at hh
    have he (a : PrimitiveAffineCoefficients r) :
        (if ∑ i, a.val i = 0 then rationalCircuitVolume J a.val else 0) =
          rationalCircuitVolume J a.val := ite_eq_left a.property.2.2
    simpa only [he,affineCircuitVolumeSum] using hh
  have hn := affineCircuitVolumeSum_ne_top hr hd hJ
  have hsubn : (∑' a : PrimitiveAffineCoefficients r, rationalCircuitVolume J a.val) ≠ ⊤ :=
    ne_top_of_le_ne_top hn hsub
  rw [← ENNReal.tsum_toReal_eq (fun a => ENNReal.ne_top_of_tsum_ne_top hsubn a)]
  exact ENNReal.toReal_mono hn hsub



end SingleLatticeCovering.CircuitVolume





noncomputable section
namespace SingleLatticeCovering.CircuitPacking
open MeasureTheory Module
open scoped ENNReal BigOperators Pointwise

lemma colored_packing_bound {E ι Q : Type*} [MeasurableSpace E] [Fintype Q]
    (μ : Measure E) (S : Finset ι) (color : ι → Q) (P : ι → Set E)
    (U : Set E) (v : ℝ≥0∞)
    (hm : ∀ i ∈ S, MeasurableSet (P i))
    (hv : ∀ i ∈ S, μ (P i) = v)
    (hd : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → color i = color j → Disjoint (P i) (P j))
    (hU : ∀ i ∈ S, P i ⊆ U) :
    (S.card : ℝ≥0∞) * v ≤ (Fintype.card Q : ℝ≥0∞) * μ U := by
  classical
  calc
    _ = ∑ i ∈ S, μ (P i) := by
      symm
      calc
        _ = ∑ _i ∈ S, v := Finset.sum_congr rfl hv
        _ = _ := by simp
    _ = ∑ q : Q, ∑ i ∈ S.filter (fun i => color i = q), μ (P i) :=
      (Finset.sum_fiberwise S color _).symm
    _ ≤ ∑ _q : Q, μ U := by
      apply Finset.sum_le_sum
      intro q _
      rw [←measure_biUnion_finset]
      · apply measure_mono
        simp only [Set.iUnion_subset_iff]
        intro i hi
        exact hU i ((Finset.mem_filter.mp hi).1)
      · intro i hi j hj hne
        obtain ⟨hiS,hiq⟩ := Finset.mem_filter.mp hi
        obtain ⟨hjS,hjq⟩ := Finset.mem_filter.mp hj
        exact hd i hiS j hjS hne (hiq.trans hjq.symm)
      · intro i hi
        exact hm i ((Finset.mem_filter.mp hi).1)
    _ = _ := by simp



lemma fundamental_translate_disjoint {r : ℕ}
    (b : Basis (Fin r) ℝ (Fin r → ℝ)) {x y : Fin r → ℝ}
    (hxy : x-y ∈ Submodule.span ℤ (Set.range b)) (hne : x ≠ y) :
    Disjoint (x +ᵥ ZSpan.fundamentalDomain b) (y +ᵥ ZSpan.fundamentalDomain b) := by
  rw [Set.disjoint_left]
  intro z hz hz'
  obtain ⟨u,hu,huz⟩ := hz
  obtain ⟨v,hv,hvz⟩ := hz'
  change x+u=z at huz
  change y+v=z at hvz
  have huv : -u+v=x-y := by
    have hv' : v = -y+(x+u) := by rw [huz, ←hvz]; abel
    rw [hv']
    abel
  have hf := (ZSpan.fract_eq_fract b u v).mpr (huv ▸ hxy)
  rw [(ZSpan.fract_eq_self (b := b)).mpr hu, (ZSpan.fract_eq_self (b := b)).mpr hv] at hf
  apply hne
  simpa [hf] using huz.trans hvz.symm


lemma fundamental_coord_bound {r : ℕ} (b : Basis (Fin r) ℝ (Fin r → ℝ))
    {R : ℝ} (hR : 0 ≤ R) (hb : ∀ i j, |b i j| ≤ R)
    {u : Fin r → ℝ} (hu : u ∈ ZSpan.fundamentalDomain b) (j : Fin r) :
    |u j| ≤ r*R := by
  have he : u j = ∑ i, b.repr u i * b i j := by
    simpa using congr_fun (b.sum_repr u).symm j
  rw [he]
  calc
    _ ≤ ∑ i, |b.repr u i * b i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin r, R := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (hu i).1]
      exact (mul_le_mul_of_nonneg_left (hb i j) (hu i).1).trans
        (by nlinarith [(hu i).2])
    _ = _ := by simp

lemma sublattice_index_ne_zero {r : ℕ}
    (L0 L : Submodule ℤ (Fin r → ℝ))
    [DiscreteTopology L0] [IsZLattice ℝ L0]
    [DiscreteTopology L] [IsZLattice ℝ L] (hL : L0 ≤ L) :
    (L0.toAddSubgroup.comap L.toAddSubgroup.subtype).index ≠ 0 := by
  have hi := ZLattice.covolume_div_covolume_eq_relIndex L0 L hL
  intro hz
  change (L0.toAddSubgroup.relIndex L.toAddSubgroup) = 0 at hz
  rw [hz, Nat.cast_zero] at hi
  exact (div_ne_zero (ZLattice.covolume_ne_zero L0 volume)
    (ZLattice.covolume_ne_zero L volume)) hi

lemma fundamental_volume {r : ℕ} (b : Basis (Fin r) ℝ (Fin r → ℝ)) :
    volume (ZSpan.fundamentalDomain b) =
      ENNReal.ofReal (ZLattice.covolume (Submodule.span ℤ (Set.range b))) := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume
    (ZSpan.isAddFundamentalDomain b volume)]
  exact (ENNReal.ofReal_toReal
    (ne_of_lt ((ZSpan.fundamentalDomain_isBounded b).measure_lt_top))).symm

lemma cancel_packing_ratio {a b c u : ℝ≥0∞}
    (ha : a ≠ 0) (hat : a ≠ ⊤) (hb : b ≠ 0) (hbt : b ≠ ⊤)
    (h : c*a ≤ a/b*u) : c*b ≤ u := by
  apply (ENNReal.mul_le_mul_iff_right ha hat).mp
  calc
    a*(c*b) = (c*a)*b := by ring
    _ ≤ (a/b*u)*b := mul_le_mul_left h _
    _ = a*u := by rw [mul_right_comm, ENNReal.div_mul_cancel hb hbt]

lemma sublattice_card_ratio {r : ℕ}
    (L0 L : Submodule ℤ (Fin r → ℝ))
    [DiscreteTopology L0] [IsZLattice ℝ L0]
    [DiscreteTopology L] [IsZLattice ℝ L] (hL : L0 ≤ L)
    [Fintype (L ⧸ (L0.toAddSubgroup.comap L.toAddSubgroup.subtype))] :
    (Fintype.card (L ⧸ (L0.toAddSubgroup.comap L.toAddSubgroup.subtype)) : ℝ≥0∞) =
      ENNReal.ofReal (ZLattice.covolume L0) / ENNReal.ofReal (ZLattice.covolume L) := by
  rw [←ENNReal.ofReal_natCast, ←ENNReal.ofReal_div_of_pos (ZLattice.covolume_pos L volume)]
  congr 1
  rw [←Nat.card_eq_fintype_card,
    ZLattice.covolume_div_covolume_eq_relIndex L0 L hL]
  rfl


lemma lattice_coset_packing {r : ℕ}
    (L : Submodule ℤ (Fin r → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis (Fin r) ℝ (Fin r → ℝ)) (hbL : ∀ i, b i ∈ L)
    (S : Finset L) (U : Set (Fin r → ℝ))
    (hU : ∀ x ∈ S, (x:Fin r → ℝ) +ᵥ ZSpan.fundamentalDomain b ⊆ U) :
    (S.card : ℝ≥0∞) * ENNReal.ofReal (ZLattice.covolume L) ≤ volume U := by
  classical
  let L0 : Submodule ℤ (Fin r → ℝ) := Submodule.span ℤ (Set.range b)
  have hL : L0 ≤ L := Submodule.span_le.mpr (by rintro _ ⟨i,rfl⟩; exact hbL i)
  let H : AddSubgroup L := L0.toAddSubgroup.comap L.toAddSubgroup.subtype
  let : Fintype (L ⧸ H) := AddSubgroup.fintypeOfIndexNeZero
    (sublattice_index_ne_zero L0 L hL)
  let color : L → L ⧸ H := fun x => QuotientAddGroup.mk x
  let P := ZSpan.fundamentalDomain b
  have hp := colored_packing_bound volume S color (fun x : L => (x:Fin r → ℝ) +ᵥ P) U (volume P)
    (fun x _ => (ZSpan.fundamentalDomain_measurableSet b).const_vadd (x:Fin r → ℝ))
    (fun x _ => measure_vadd volume (x:Fin r → ℝ) P)
    (by
      intro x hx y hy hne hc
      apply fundamental_translate_disjoint b
      · exact (QuotientAddGroup.eq_iff_sub_mem.mp hc : x-y ∈ H)
      · exact fun he => hne (Subtype.ext he)) hU
  rw [fundamental_volume b, sublattice_card_ratio L0 L hL] at hp
  exact cancel_packing_ratio
    (ENNReal.ofReal_ne_zero_iff.mpr (ZLattice.covolume_pos L0 volume))
    ENNReal.ofReal_ne_top
    (ENNReal.ofReal_ne_zero_iff.mpr (ZLattice.covolume_pos L volume))
    ENNReal.ofReal_ne_top hp


theorem short_basis_lattice_packing {r : ℕ}
    (L : Submodule ℤ (Fin r → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis (Fin r) ℝ (Fin r → ℝ)) (hbL : ∀ i, b i ∈ L)
    (S : Finset L) {R : ℝ} (hR : 0 ≤ R)
    (hb : ∀ i j, |b i j| ≤ R) (hS : ∀ x ∈ S, ∀ j, |(x:Fin r → ℝ) j| ≤ R) :
    (S.card : ℝ≥0∞) * ENNReal.ofReal (ZLattice.covolume L) ≤
      volume (Set.pi Set.univ (fun _ : Fin r => Set.Icc (-((r+1:ℕ):ℝ)*R) (((r+1:ℕ):ℝ)*R))) := by
  apply lattice_coset_packing L b hbL S
  intro x hx z hz
  obtain ⟨u,hu,rfl⟩ := hz
  intro j _
  have huj := fundamental_coord_bound b hR hb hu j
  have hxj := hS x hx j
  change -((r+1:ℕ):ℝ)*R ≤ (x:Fin r → ℝ) j + u j ∧
    (x:Fin r → ℝ) j + u j ≤ ((r+1:ℕ):ℝ)*R
  have ht := (abs_add_le ((x:Fin r → ℝ) j) (u j)).trans (add_le_add hxj huj)
  have ht' := abs_le.mp ht
  push_cast
  constructor <;> linarith

lemma volume_symmetric_box (r : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    volume (Set.pi Set.univ (fun _ : Fin r => Set.Icc (-R) R)) =
      ENNReal.ofReal (2*R)^r := by
  have _ := hR
  rw [volume_pi, Measure.pi_pi]
  simp [Real.volume_Icc, sub_neg_eq_add, ←two_mul]

lemma short_basis_lattice_count {r : ℕ}
    (L : Submodule ℤ (Fin r → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis (Fin r) ℝ (Fin r → ℝ)) (hbL : ∀ i, b i ∈ L)
    (S : Finset L) {R : ℝ} (hR : 0 ≤ R)
    (hb : ∀ i j, |b i j| ≤ R)
    (hS : ∀ x ∈ S, ∀ j, |(x:Fin r → ℝ) j| ≤ R) :
    (S.card : ℝ) * ZLattice.covolume L ≤ (2*(r+1)*R)^r := by
  have h := short_basis_lattice_packing L b hbL S hR hb hS
  simp only [neg_mul] at h
  rw [volume_symmetric_box r (by positivity)] at h
  have h' := ENNReal.toReal_mono (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) h
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (ZLattice.covolume_pos L volume).le,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity)] at h'
  simpa only [Nat.cast_add, Nat.cast_one, mul_assoc] using h'


end SingleLatticeCovering.CircuitPacking


noncomputable section

end
end
end
end
end
end
end
end
end
end

end OAI
