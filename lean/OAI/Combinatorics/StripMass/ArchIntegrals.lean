import Mathlib
import OAI.Combinatorics.StripMass.PfaffianConfluentLimit

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators
open Set MeasureTheory
theorem pointwiseArchIntegral_lower {N : ℕ} {y : Fin N → ℝ}
    (hy : y ∈ orderedDomain N) (i : Fin N) (hsmall : ∀ j, y i ≤ y j) :
    (1 / 96 : ℝ) * (y i) ^ (-(1 / 4 : ℝ)) ≤ pointwiseArchIntegral N y := by
  have hyi := (hy.2 i).1
  have hyi1 := (hy.2 i).2
  have hab : y i / 3 ≤ y i / 2 := by linarith
  have hsub : Ioo (y i / 3) (y i / 2) ⊆ Ioo (0 : ℝ) 1 := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  have hint := integrableOn_pointwiseArchIntegrand hy
  have hlocal : ∀ x ∈ Ioo (y i / 3) (y i / 2),
      (1 / 16 : ℝ) * (y i) ^ (-(1 / 4 : ℝ)) / y i ≤ pointwiseArchIntegrand N y x := by
    intro x hx
    have hx0 : 0 < x := (hsub hx).1
    have hxi : x ≤ y i := by linarith [hx.2]
    have hr := Real.rpow_le_rpow_of_nonpos hx0 hxi (by norm_num : -(1 / 4 : ℝ) ≤ 0)
    have homega : (1 / 8 : ℝ) * (y i) ^ (-(1 / 4 : ℝ)) ≤ omega x :=
      (mul_le_mul_of_nonneg_left hr (by norm_num)).trans
        (rpow_le_eight_omega ⟨hx0, by linarith [hx.2]⟩)
    have hmul : (1 / 16 : ℝ) * (y i) ^ (-(1 / 4 : ℝ)) ≤
        (1 - reflectionProduct N x y) * omega x := by
      calc
        (1 / 16 : ℝ) * (y i) ^ (-(1 / 4 : ℝ)) =
            (1 / 2 : ℝ) * ((1 / 8 : ℝ) * (y i) ^ (-(1 / 4 : ℝ))) := by ring
        _ ≤ (1 - reflectionProduct N x y) * omega x :=
          mul_le_mul (reflection_deficit_lower hy i hsmall hx) homega
            (by positivity) (reflection_deficit_bounds hy hx0).1
    exact (div_le_div_of_nonneg_left (by positivity) hx0 hxi).trans
      (div_le_div_of_nonneg_right hmul hx0.le)
  have hinterval : (1 / 96 : ℝ) * (y i) ^ (-(1 / 4 : ℝ)) ≤
      ∫ x in Ioo (y i / 3) (y i / 2), pointwiseArchIntegrand N y x := by
    have h := setIntegral_mono_on
      (show IntegrableOn (fun _ : ℝ => (1 / 16 : ℝ) * (y i) ^ (-(1 / 4 : ℝ)) / y i)
        (Ioo (y i / 3) (y i / 2)) from integrable_const _)
      (hint.mono_set hsub) measurableSet_Ioo hlocal
    calc
      (1 / 96 : ℝ) * (y i) ^ (-(1 / 4 : ℝ)) =
          ∫ _x in Ioo (y i / 3) (y i / 2), (1 / 16 : ℝ) * (y i) ^ (-(1 / 4 : ℝ)) / y i := by
        rw [setIntegral_const, Real.volume_real_Ioo_of_le hab, smul_eq_mul]
        field_simp
        ring
      _ ≤ _ := h
  apply hinterval.trans
  apply setIntegral_mono_set hint
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact (pointwiseArchIntegrand_bounds hy hx).1
  · exact Filter.Eventually.of_forall hsub

 
theorem pointwiseArchIntegrand_two_majorants {N : ℕ} {y : Fin N → ℝ}
    (hy : y ∈ orderedDomain N) {x : ℝ} (hx : x ∈ Ioo 0 1) :
    pointwiseArchIntegrand N y x ≤
      (2 * ∑ i, (y i)⁻¹) * x ^ (-(1 / 4 : ℝ)) ∧
    pointwiseArchIntegrand N y x ≤ 2 * x ^ (-(5 / 4 : ℝ)) := by
  have hx0 := hx.1
  have hS : 0 ≤ ∑ i, (y i)⁻¹ := Finset.sum_nonneg fun i _ => inv_nonneg.mpr (hy.2 i).1.le
  have hdef := (reflection_deficit_bounds hy hx0).2
  have h₁ : 1 - reflectionProduct N x y ≤ 2 * (x * ∑ i, (y i)⁻¹) :=
    hdef.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num))
  have h₂ : 1 - reflectionProduct N x y ≤ (2 : ℝ) := by
    simpa only [mul_one] using hdef.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num))
  constructor
  · calc
      pointwiseArchIntegrand N y x ≤
          (2 * (x * ∑ i, (y i)⁻¹)) * x ^ (-(1 / 4 : ℝ)) / x :=
        div_le_div_of_nonneg_right (mul_le_mul h₁ (omega_le_rpow hx)
          (omega_nonneg x) (by positivity)) hx0.le
      _ = _ := by field_simp
  · calc
      pointwiseArchIntegrand N y x ≤ 2 * x ^ (-(1 / 4 : ℝ)) / x :=
        div_le_div_of_nonneg_right (mul_le_mul h₂ (omega_le_rpow hx)
          (omega_nonneg x) (by norm_num)) hx0.le
      _ = 2 * x ^ (-(5 / 4 : ℝ)) := by
        rw [show -(5 / 4 : ℝ) = -(1 / 4 : ℝ) - 1 by norm_num,
          Real.rpow_sub hx0, Real.rpow_one]
        ring

 

theorem pointwiseArchIntegral_upper {N : ℕ} (hN : 1 ≤ N) {y : Fin N → ℝ}
    (hy : y ∈ orderedDomain N) :
    pointwiseArchIntegral N y ≤ (32 / 3 : ℝ) * (∑ i, (y i)⁻¹) ^ (1 / 4 : ℝ) := by
  let S : ℝ := ∑ i, (y i)⁻¹
  let t : ℝ := S⁻¹
  have hS : 1 ≤ S := by
    let i : Fin N := ⟨0, by omega⟩
    calc
      1 ≤ (y i)⁻¹ := (one_le_inv₀ (hy.2 i).1).mpr (hy.2 i).2.le
      _ ≤ S := Finset.single_le_sum (fun j _ => inv_nonneg.mpr (hy.2 j).1.le) (Finset.mem_univ _)
  have hSpos : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have htpos : 0 < t := inv_pos.mpr hSpos
  have ht1 : t ≤ 1 := (inv_le_one₀ hSpos).mpr hS
  have hsub₁ : Ioo 0 t ⊆ Ioo (0 : ℝ) 1 := Ioo_subset_Ioo le_rfl ht1
  have hsub₂ : Ioo t 1 ⊆ Ioo (0 : ℝ) 1 := Ioo_subset_Ioo htpos.le le_rfl
  have hi := integrableOn_pointwiseArchIntegrand hy
  have hi₁ := hi.mono_set hsub₁
  have hi₂ := hi.mono_set hsub₂
  have hit₁ := (intervalIntegrable_iff_integrableOn_Ioo_of_le htpos.le).mpr hi₁
  have hit₂ := (intervalIntegrable_iff_integrableOn_Ioo_of_le ht1).mpr hi₂
  have hpow₁ : S * t ^ (3 / 4 : ℝ) = S ^ (1 / 4 : ℝ) := by
    calc
      S * t ^ (3 / 4 : ℝ) = S ^ (1 : ℝ) * S ^ (-(3 / 4 : ℝ)) := by
        rw [Real.rpow_one, Real.rpow_neg hSpos.le, ← Real.inv_rpow hSpos.le]
      _ = S ^ ((1 : ℝ) + -(3 / 4 : ℝ)) := (Real.rpow_add hSpos _ _).symm
      _ = S ^ (1 / 4 : ℝ) := by norm_num
  have hpow₂ : t ^ (-(1 / 4 : ℝ)) = S ^ (1 / 4 : ℝ) := by
    change (S⁻¹) ^ (-(1 / 4 : ℝ)) = _
    rw [Real.inv_rpow hSpos.le, Real.rpow_neg hSpos.le, inv_inv]
  have hbound₁ : ∫ x in Ioo 0 t, pointwiseArchIntegrand N y x ≤
      (8 / 3 : ℝ) * S ^ (1 / 4 : ℝ) := by
    have hir : IntegrableOn (fun x : ℝ => x ^ (-(1 / 4 : ℝ))) (Ioo 0 t) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff htpos).mpr (by norm_num)
    calc
      ∫ x in Ioo 0 t, pointwiseArchIntegrand N y x ≤
          ∫ x in Ioo 0 t, (2 * S) * x ^ (-(1 / 4 : ℝ)) :=
        setIntegral_mono_on hi₁ (hir.const_mul _) measurableSet_Ioo
          (fun x hx => (pointwiseArchIntegrand_two_majorants hy (hsub₁ hx)).1)
      _ = (8 / 3 : ℝ) * S ^ (1 / 4 : ℝ) := by
        rw [integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
          ← intervalIntegral.integral_of_le htpos.le,
          integral_rpow (Or.inl (by norm_num : -(1 : ℝ) < -(1 / 4 : ℝ)))]
        norm_num only [show -(1 / 4 : ℝ) + 1 = 3 / 4 by norm_num,
          Real.zero_rpow (by norm_num : (3 / 4 : ℝ) ≠ 0), sub_zero]
        calc
          (2 * S) * (t ^ (3 / 4 : ℝ) / (3 / 4 : ℝ)) =
              (8 / 3 : ℝ) * (S * t ^ (3 / 4 : ℝ)) := by ring
          _ = _ := by rw [hpow₁]
  have hbound₂ : ∫ x in Ioo t 1, pointwiseArchIntegrand N y x ≤
      8 * S ^ (1 / 4 : ℝ) := by
    have hzero : (0 : ℝ) ∉ uIcc t 1 := by
      rw [uIcc_of_le ht1]
      intro hz
      linarith [hz.1]
    have hir' : IntervalIntegrable (fun x : ℝ => x ^ (-(5 / 4 : ℝ))) volume t 1 :=
      intervalIntegral.intervalIntegrable_rpow (Or.inr hzero)
    have hir := (intervalIntegrable_iff_integrableOn_Ioo_of_le ht1).mp hir'
    calc
      ∫ x in Ioo t 1, pointwiseArchIntegrand N y x ≤
          ∫ x in Ioo t 1, 2 * x ^ (-(5 / 4 : ℝ)) :=
        setIntegral_mono_on hi₂ (hir.const_mul _) measurableSet_Ioo
          (fun x hx => (pointwiseArchIntegrand_two_majorants hy (hsub₂ hx)).2)
      _ = 8 * (S ^ (1 / 4 : ℝ) - 1) := by
        rw [integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
          ← intervalIntegral.integral_of_le ht1,
          integral_rpow (Or.inr ⟨by norm_num, hzero⟩)]
        norm_num only [show -(5 / 4 : ℝ) + 1 = -(1 / 4 : ℝ) by norm_num,
          Real.one_rpow, hpow₂]
        ring
      _ ≤ 8 * S ^ (1 / 4 : ℝ) := by linarith
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hit₁ hit₂
  rw [intervalIntegral.integral_of_le htpos.le, intervalIntegral.integral_of_le ht1,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo] at hsplit
  change pointwiseArchIntegral N y ≤ (32 / 3 : ℝ) * S ^ (1 / 4 : ℝ)
  unfold pointwiseArchIntegral
  rw [← hsplit]
  linarith



 

theorem integrable_jointArchIntegrand (N : ℕ) :
    Integrable (fun p : ℝ × (Fin N → ℝ) =>
      pointwiseArchIntegrand N p.2 p.1 * density N p.2)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (orderedDomain N))) := by
  have hp : IntegrableOn (fun x : ℝ => x ^ (-(3 / 4 : ℝ))) (Ioo 0 1) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1)).2 (by norm_num)
  have hm : Measurable (fun p : ℝ × (Fin N → ℝ) =>
      pointwiseArchIntegrand N p.2 p.1 * density N p.2) := by
    exact (((measurable_const.sub (measurable_reflectionProduct N)).mul
      (measurable_omega.comp measurable_fst)).div measurable_fst).mul
        ((measurable_density N).comp measurable_snd)
  apply (hp.mul_prod (integrableOn_inverseHalfSum_density N)).mono' hm.aestronglyMeasurable
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod (isOpen_orderedDomain N).measurableSet)] with p hp
  have hb := pointwiseArchIntegrand_bounds hp.2 hp.1
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hb.1 (density_pos hp.2).le)]
  exact (mul_le_mul_of_nonneg_right hb.2 (density_pos hp.2).le).trans_eq (by ring)

theorem integrableOn_pointwiseArchIntegral_density (N : ℕ) :
    IntegrableOn (fun y => pointwiseArchIntegral N y * density N y) (orderedDomain N) := by
  simpa only [IntegrableOn, pointwiseArchIntegral, integral_mul_const] using
    (integrable_jointArchIntegrand N).integral_prod_right

theorem expectation_pointwiseArchIntegrand (N : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    expectation N (fun y => pointwiseArchIntegrand N y x) = momentIntegrand N x := by
  have he (y : Fin N → ℝ) :
      pointwiseArchIntegrand N y x * density N y =
        ((1 - reflectionProduct N x y) * density N y) * (omega x / x) := by
    unfold pointwiseArchIntegrand
    ring
  unfold expectation
  simp_rw [he]
  rw [integral_mul_const]
  unfold momentIntegrand
  rw [← expectation_deficit N hx]
  unfold expectation
  ring

 
theorem integral_momentIntegrand_eq_expectation (N : ℕ) :
    (∫ x in Ioo 0 1, momentIntegrand N x) = expectation N (pointwiseArchIntegral N) := by
  calc
    (∫ x in Ioo 0 1, momentIntegrand N x) =
        ∫ x in Ioo 0 1, expectation N (fun y => pointwiseArchIntegrand N y x) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro x hx
      exact (expectation_pointwiseArchIntegrand N hx.1.le).symm
    _ = (∫ x in Ioo 0 1, ∫ y in orderedDomain N,
        pointwiseArchIntegrand N y x * density N y) / normalizer N := by
      simp only [expectation, integral_div]
    _ = expectation N (pointwiseArchIntegral N) := by
      rw [integral_integral_swap (integrable_jointArchIntegrand N)]
      simp only [expectation, pointwiseArchIntegral, integral_mul_const]

 
theorem fourthRoot_sum_le_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) :
    (∑ i ∈ s, a i) ^ (1 / 4 : ℝ) ≤ ∑ i ∈ s, (a i) ^ (1 / 4 : ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hai := ha i (Finset.mem_insert_self _ _)
    have has : ∀ j ∈ s, 0 ≤ a j := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (Real.rpow_add_le_add_rpow hai (Finset.sum_nonneg has) (by norm_num) (by norm_num)).trans
      (add_le_add_right (ih has) _)

theorem inverseQuarterSum_le_inverseHalfSum {N : ℕ} {y : Fin N → ℝ}
    (hy : y ∈ orderedDomain N) :
    (∑ i, (y i)⁻¹) ^ (1 / 4 : ℝ) ≤ inverseHalfSum N y := by
  refine (fourthRoot_sum_le_sum Finset.univ (fun i => (y i)⁻¹)
    (fun i _ => inv_nonneg.mpr (hy.2 i).1.le)).trans ?_
  apply Finset.sum_le_sum
  intro i _
  rw [Real.inv_rpow (hy.2 i).1.le, ← Real.rpow_neg (hy.2 i).1.le]
  exact Real.rpow_le_rpow_of_exponent_ge (hy.2 i).1 (hy.2 i).2.le (by norm_num)

theorem integrableOn_inverseQuarterSum_density (N : ℕ) :
    IntegrableOn (fun y => (∑ i, (y i)⁻¹) ^ (1 / 4 : ℝ) * density N y) (orderedDomain N) := by
  have hm : Measurable (fun y : Fin N → ℝ => (∑ i, (y i)⁻¹) ^ (1 / 4 : ℝ) * density N y) :=
    ((Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).inv).pow_const _).mul (measurable_density N)
  apply (integrableOn_inverseHalfSum_density N).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem (isOpen_orderedDomain N).measurableSet] with y hy
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (Finset.sum_nonneg
    fun i _ => inv_nonneg.mpr (hy.2 i).1.le) _) (density_pos hy).le)]
  exact mul_le_mul_of_nonneg_right (inverseQuarterSum_le_inverseHalfSum hy) (density_pos hy).le

theorem integrableOn_inverseQuarterCoordinate_density (N : ℕ) (i : Fin N) :
    IntegrableOn (fun y => (y i) ^ (-(1 / 4 : ℝ)) * density N y) (orderedDomain N) := by
  have hm : Measurable (fun y : Fin N → ℝ => (y i) ^ (-(1 / 4 : ℝ)) * density N y) :=
    ((measurable_pi_apply i).pow_const _).mul (measurable_density N)
  apply (integrableOn_coordinate_weight N i).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem (isOpen_orderedDomain N).measurableSet] with y hy
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_pos_of_pos (hy.2 i).1 _).le (density_pos hy).le)]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_ge (hy.2 i).1 (hy.2 i).2.le (by norm_num)) (density_pos hy).le

theorem expectation_mono {N : ℕ} {f g : (Fin N → ℝ) → ℝ}
    (hf : IntegrableOn (fun y => f y * density N y) (orderedDomain N))
    (hg : IntegrableOn (fun y => g y * density N y) (orderedDomain N))
    (hfg : ∀ y ∈ orderedDomain N, f y ≤ g y) : expectation N f ≤ expectation N g := by
  apply div_le_div_of_nonneg_right _ (normalizer_pos N).le
  apply setIntegral_mono_on hf hg (isOpen_orderedDomain N).measurableSet
  intro y hy
  exact mul_le_mul_of_nonneg_right (hfg y hy) (density_pos hy).le

theorem expectation_const_mul (N : ℕ) (a : ℝ) (f : (Fin N → ℝ) → ℝ) :
    expectation N (fun y => a * f y) = a * expectation N f := by
  simp only [expectation, mul_assoc, integral_const_mul, mul_div_assoc]

 

theorem integral_inverse_comparison {N : ℕ} (hN : 1 ≤ N) :
    (1 / 96 : ℝ) * expectation N (fun y => (y ⟨0, by omega⟩) ^ (-(1 / 4 : ℝ))) ≤
      (∫ x in Ioo 0 1, momentIntegrand N x) ∧
    (∫ x in Ioo 0 1, momentIntegrand N x) ≤
      (32 / 3 : ℝ) * expectation N (fun y => (∑ i, (y i)⁻¹) ^ (1 / 4 : ℝ)) := by
  let i : Fin N := ⟨0, by omega⟩
  rw [integral_momentIntegrand_eq_expectation]
  constructor
  · rw [← expectation_const_mul]
    apply expectation_mono
    · simpa only [IntegrableOn, i, mul_assoc] using (integrableOn_inverseQuarterCoordinate_density N i).const_mul (1 / 96 : ℝ)
    · exact integrableOn_pointwiseArchIntegral_density N
    · intro y hy
      apply pointwiseArchIntegral_lower hy i
      intro j
      exact hy.1.monotone (show i ≤ j by exact Nat.zero_le _)
  · rw [← expectation_const_mul]
    apply expectation_mono (integrableOn_pointwiseArchIntegral_density N)
    · simpa only [IntegrableOn, mul_assoc] using (integrableOn_inverseQuarterSum_density N).const_mul (32 / 3 : ℝ)
    · intro y hy
      exact pointwiseArchIntegral_upper hN hy

end

 
noncomputable section
open scoped BigOperators

 
def bandRank (v : Triangle) : ℤ := if v.2.2 then 2 * v.1 else 2 * v.1 + 1

def bandVertex (k : ℤ) : Triangle :=
  if k % 2 = 0 then up (k / 2) 0 else down (k / 2) 0

@[simp] theorem bandVertex_band (k : ℤ) : (bandVertex k).2.1 = 0 := by
  simp only [bandVertex]; split <;> rfl

@[simp] theorem bandRank_bandVertex (k : ℤ) : bandRank (bandVertex k) = k := by
  simp only [bandVertex]
  split <;> simp only [bandRank, up, down, Bool.false_eq_true, reduceIte, ite_true]
  all_goals omega

theorem bandVertex_bandRank (v : Triangle) (hv : v.2.1 = 0) : bandVertex (bandRank v) = v := by
  rcases v with ⟨i, j, b⟩
  change j = 0 at hv
  subst j
  cases b <;> simp [bandRank, bandVertex, up, down, Int.add_ediv]

@[simp] theorem bandRank_up (k : ℤ) : bandRank (up k 0) = 2 * k := rfl
@[simp] theorem bandRank_down (k : ℤ) : bandRank (down k 0) = 2 * k + 1 := rfl

 
theorem band_adjacent_iff {v w : Triangle} (hv : v.2.1 = 0) (hw : w.2.1 = 0) :
    adjacent v w ↔ bandRank w = bandRank v + 1 ∨ bandRank w = bandRank v - 1 := by
  rcases v with ⟨a, j, b⟩
  rcases w with ⟨a', j', b'⟩
  change j = 0 at hv
  change j' = 0 at hw
  subst j; subst j'
  cases b <;> cases b' <;> simp [adjacent, upDownAdjacent, bandRank] <;> omega

def unitAdjacent (a b : ℤ) : Prop := b = a + 1 ∨ b = a - 1

theorem int_chain_directed {l : List ℤ} {a b s : ℤ}
    (hs : s = 1 ∨ s = -1) (h : (a :: b :: l).IsChain unitAdjacent)
    (hn : (a :: b :: l).Nodup) (hab : b = a + s) :
    (a :: b :: l).IsChain (fun x y => y = x + s) := by
  induction l generalizing a b with
  | nil => simpa [unitAdjacent] using hab
  | cons c l ih =>
    have htl := (List.isChain_cons_cons.mp h).2
    have hbc := (List.isChain_cons_cons.mp htl).1
    have hac : c ≠ a := by
      intro heq
      exact (List.nodup_cons.mp hn).1 (by simp [← heq])
    have hbc' : c = b + s := by
      rcases hs with rfl | rfl <;> rcases hbc with hbc | hbc <;> omega
    exact List.isChain_cons_cons.mpr ⟨hab, ih htl hn.of_cons hbc'⟩

theorem int_chain_direction {l : List ℤ} (h : l.IsChain unitAdjacent) (hn : l.Nodup) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ l.IsChain (fun x y => y = x + s) := by
  rcases l with _ | ⟨a, l⟩
  · exact ⟨1, Or.inl rfl, List.isChain_nil⟩
  rcases l with _ | ⟨b, l⟩
  · exact ⟨1, Or.inl rfl, List.isChain_singleton _⟩
  rcases (List.isChain_cons_cons.mp h).1 with hab | hab
  · exact ⟨1, Or.inl rfl, int_chain_directed (Or.inl rfl) h hn hab⟩
  · exact ⟨-1, Or.inr rfl, int_chain_directed (Or.inr rfl) h hn (by omega)⟩

theorem directed_chain_eq_range {l : List ℤ} {a s : ℤ}
    (hh : l.head? = some a) (hc : l.IsChain (fun x y => y = x + s)) :
    l = (List.range l.length).map (fun n : ℕ => a + s * n) := by
  induction l generalizing a with
  | nil => simp at hh
  | cons b l ih =>
    have hba : b = a := by simpa using hh
    subst b
    cases l with
    | nil => simp
    | cons b l =>
      obtain ⟨hba, htl⟩ := List.isChain_cons_cons.mp hc
      have he := ih (a := b) rfl htl
      change a :: b :: l = (List.range ((b :: l).length + 1)).map (fun n : ℕ => a + s * n)
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [Nat.cast_zero, mul_zero, add_zero]
      congr 1
      apply he.trans
      apply List.map_congr_left
      intro n hn
      dsimp only [Function.comp_def]
      rw [Nat.cast_succ, hba]
      ring

 
def integerLinePath (k : ℤ) : List ℤ :=
  (List.range (k.natAbs + 1)).map (fun n : ℕ => if k < 0 then -(n : ℤ) else (n : ℤ))

@[simp] theorem integerLinePath_length (k : ℤ) : (integerLinePath k).length = k.natAbs + 1 := by
  simp [integerLinePath]

@[simp] theorem integerLinePath_head (k : ℤ) : (integerLinePath k).head? = some 0 := by
  simp [integerLinePath, List.head?_map, List.head?_range]

@[simp] theorem integerLinePath_last (k : ℤ) : (integerLinePath k).getLast? = some k := by
  simp only [integerLinePath, List.getLast?_map, List.getLast?_range, Nat.add_eq_zero_iff,
    Nat.one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel, Option.map_some]
  congr 1
  split
  · rw [Int.natCast_natAbs, abs_of_neg (by assumption)]; ring
  · rw [Int.natAbs_of_nonneg (by omega)]

theorem integerLinePath_nodup (k : ℤ) : (integerLinePath k).Nodup := by
  apply List.Nodup.map _ List.nodup_range
  intro a b hab
  by_cases hk : k < 0 <;> simpa [hk] using hab

theorem integerLinePath_chain (k : ℤ) : (integerLinePath k).IsChain unitAdjacent := by
  apply (List.isChain_map _).mpr
  apply (List.isChain_range_succ _ _).mpr
  intro m hm
  by_cases hk : k < 0
  · simp only [hk, ↓reduceIte, unitAdjacent]; right; push_cast; ring
  · simp only [hk, ↓reduceIte, unitAdjacent]; left; push_cast; ring

end
end CriticalStrip

end OAI
