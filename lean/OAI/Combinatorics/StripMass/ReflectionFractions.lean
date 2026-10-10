import Mathlib
import OAI.Combinatorics.StripMass.MomentGrowth

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators
open Set MeasureTheory
lemma reflection_partialFractions_distinct {n : ℕ} (hn : 0 < n) {y : Fin n → ℝ}
    (hy : ∀ i, 0 < y i) (hinj : Function.Injective y) {x : ℝ} (hx : 0 ≤ x) :
    reflectionProduct n x y = 1 - x * ∑ i, reflectionResidue n y i / (x+y i) := by
  classical
  let P : Polynomial ℝ := ∏ i, (Polynomial.C (y i) - Polynomial.X)
  let Q : Polynomial ℝ := ∏ i, (Polynomial.C (y i) + Polynomial.X)
  let R : Fin n → Polynomial ℝ := fun i => ∏ j ∈ Finset.univ.erase i, (Polynomial.C (y j)+Polynomial.X)
  let T : Polynomial ℝ := Q - Polynomial.X * ∑ i, Polynomial.C (reflectionResidue n y i) * R i
  have hlin (a : ℝ) : (Polynomial.C a + Polynomial.X).natDegree ≤ 1 := by
    exact (Polynomial.natDegree_add_le _ _).trans (by simp)
  have hR (i : Fin n) : (R i).natDegree ≤ n-1 := by
    apply (Polynomial.natDegree_prod_le (Finset.univ.erase i)
      (fun j => Polynomial.C (y j) + Polynomial.X)).trans
    calc
      ∑ j ∈ Finset.univ.erase i, (Polynomial.C (y j)+Polynomial.X).natDegree ≤
          ∑ _j ∈ Finset.univ.erase i, 1 := by
        apply Finset.sum_le_sum
        intro j _
        exact hlin (y j)
      _ = n-1 := by simp
  have hP : P.natDegree ≤ n := by
    apply (Polynomial.natDegree_prod_le Finset.univ
      (fun i => Polynomial.C (y i) - Polynomial.X)).trans
    calc
      ∑ i : Fin n, (Polynomial.C (y i)-Polynomial.X).natDegree ≤ ∑ _i : Fin n, 1 := by
        apply Finset.sum_le_sum
        intro i _
        exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
      _ = n := by simp
  have hQ : Q.natDegree ≤ n := by
    apply (Polynomial.natDegree_prod_le Finset.univ
      (fun i => Polynomial.C (y i) + Polynomial.X)).trans
    calc
      ∑ i : Fin n, (Polynomial.C (y i)+Polynomial.X).natDegree ≤ ∑ _i : Fin n, 1 :=
        by
          apply Finset.sum_le_sum
          intro i _
          exact hlin (y i)
      _ = n := by simp
  have hT : T.natDegree ≤ n := by
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le hQ
    apply (Polynomial.natDegree_mul_le).trans
    have hh : (∑ i, Polynomial.C (reflectionResidue n y i) * R i).natDegree ≤ n-1 := by
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro i _
      exact (Polynomial.natDegree_C_mul_le _ _).trans (hR i)
    simpa only [Polynomial.natDegree_X] using (add_le_add_right hh 1 |>.trans (by omega : 1+(n-1) ≤ n))
  have hnode : Function.Injective (Fin.cons (0:ℝ) (fun i => -y i)) := by
    rw [Fin.cons_injective_iff]
    refine ⟨?_, fun i j h => hinj (neg_injective h)⟩
    rintro ⟨i, hi⟩
    exact (hy i).ne' (neg_eq_zero.mp hi)
  have he : P = T := by
    apply Polynomial.eq_of_degrees_lt_of_eval_index_eq
      (s := Finset.univ) (v := Fin.cons (0:ℝ) (fun i => -y i))
      (hnode.injOn)
      ((Polynomial.degree_le_of_natDegree_le hP).trans_lt (by
        simp only [Finset.card_univ, Fintype.card_fin]
        exact_mod_cast Nat.lt_succ_self n))
      ((Polynomial.degree_le_of_natDegree_le hT).trans_lt (by
        simp only [Finset.card_univ, Fintype.card_fin]
        exact_mod_cast Nat.lt_succ_self n))
    intro i _
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [P, Q, T, Polynomial.eval_prod]
    · have hQ0 : Q.eval (-y i) = 0 := by
        simp only [Q, Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by ring)
      have hsum : (∑ j, Polynomial.C (reflectionResidue n y j) * R j).eval (-y i) =
          reflectionResidue n y i * ∏ j ∈ Finset.univ.erase i, (y j-y i) := by
        simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]
        rw [Finset.sum_eq_single i]
        · simp [R, Polynomial.eval_prod, sub_eq_add_neg]
        · intro j _ hji
          have hz : (R j).eval (-y i) = 0 := by
            simp only [R, Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
            exact Finset.prod_eq_zero (show i ∈ Finset.univ.erase j from by simp [hji.symm]) (by ring)
          rw [hz, mul_zero]
        · simp
      have hres : reflectionResidue n y i * ∏ j ∈ Finset.univ.erase i, (y j-y i) =
          2 * ∏ j ∈ Finset.univ.erase i, (y j+y i) := by
        rw [reflectionResidue, Finset.prod_div_distrib, mul_assoc, div_mul_cancel₀]
        exact Finset.prod_ne_zero_iff.mpr fun j hj => sub_ne_zero.mpr (hinj.ne (Finset.mem_erase.mp hj).1)
      have hPm : P.eval (-y i) = (2*y i) * ∏ j ∈ Finset.univ.erase i, (y j+y i) := by
        simp only [P, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X, sub_neg_eq_add]
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
        ring
      simp only [Fin.cons_succ, T, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X,
        hQ0, hsum, hres, hPm]
      ring
  have heval := congrArg (Polynomial.eval x) he
  simp only [P, Q, T, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_finsetSum, R] at heval
  have hden : (∏ i, (y i+x)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => (add_pos_of_pos_of_nonneg (hy i) hx).ne'
  have hi (i : Fin n) : (∏ j ∈ Finset.univ.erase i, (y j+x))/(∏ j, (y j+x)) = (x+y i)⁻¹ := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    rw [mul_comm (y i+x), div_mul_cancel_left₀]
    · rw [add_comm]
    · exact Finset.prod_ne_zero_iff.mpr fun j _ => (add_pos_of_pos_of_nonneg (hy j) hx).ne'
  rw [reflectionProduct, Finset.prod_div_distrib, heval, sub_div, div_self hden,
    mul_div_assoc, Finset.sum_div]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_div_assoc, hi, div_eq_mul_inv]

lemma integral_unitCube_cons (n : ℕ) (f : (Fin (n+1) → ℝ) → ℝ) :
    (∫ z, f z ∂unitCubeMeasure (n+1)) =
      ∫ p : ℝ × (Fin n → ℝ), f (Fin.cons p.1 p.2)
        ∂(volume.restrict (Ioo 0 1)).prod (unitCubeMeasure n) := by
  symm
  simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Fin.zero_succAbove, Equiv.coe_fn_mk, cast_eq] using
    ((measurePreserving_piFinSuccAbove
      (fun _ : Fin (n+1) => volume.restrict (Ioo (0:ℝ) 1)) 0).symm).integral_comp' f

lemma integrable_unitCube_cons {n : ℕ} {f : (Fin (n+1) → ℝ) → ℝ}
    (hf : Integrable f (unitCubeMeasure (n+1))) :
    Integrable (fun p : ℝ × (Fin n → ℝ) => f (Fin.cons p.1 p.2))
      ((volume.restrict (Ioo 0 1)).prod (unitCubeMeasure n)) := by
  simpa only [Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Fin.zero_succAbove, Equiv.coe_fn_mk, cast_eq] using
    ((measurePreserving_piFinSuccAbove
      (fun _ : Fin (n+1) => volume.restrict (Ioo (0:ℝ) 1)) 0).symm).integrable_comp_of_integrable hf

lemma integrable_unitCube_of_abs_le_weights {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : Measurable f) {b : ℝ}
    (hbd : ∀ z, (∀ i, z i ∈ Ioo (0:ℝ) 1) → |f z| ≤ b * ∏ i, omega (z i)) :
    Integrable f (unitCubeMeasure n) := by
  apply ((Integrable.fintype_prod (fun _ : Fin n => integrableOn_omega)).const_mul b).mono'
    hf.aestronglyMeasurable
  filter_upwards [ae_unitCube n] with z hz
  exact hbd z hz

lemma reflection_with_density_cons {n : ℕ} {x : ℝ} {y : Fin n → ℝ}
    (_hx : 0 < x) (_hy : ∀ i, 0 < y i) :
    omega x * reflectionProduct n x y * density n y =
      density (n+1) (Fin.cons x y) / ∏ j, (y j-x) := by
  rw [density_cons, mul_div_assoc, ← Finset.prod_div_distrib]
  have he : ∏ j, pairKernel x (y j) / (y j-x) = reflectionProduct n x y := by
    apply Finset.prod_congr rfl
    intro j _
    unfold pairKernel
    by_cases h : y j = x
    · simp [h]
    · field_simp [sub_ne_zero.mpr h]
  rw [he]
  ring

lemma lagrange_reverse_denominator_sum {n k : ℕ} (hk : k < n) {z : Fin (n+1) → ℝ}
    (hz : Function.Injective z) :
    ∑ i, z i ^ k / ∏ j ∈ Finset.univ.erase i, (z j-z i) = 0 := by
  classical
  have hd : (Polynomial.X ^ k : Polynomial ℝ).degree <
      ((Finset.univ : Finset (Fin (n+1))).card : WithBot ℕ) := by
    simp only [Polynomial.degree_X_pow, Finset.card_univ, Fintype.card_fin]
    exact_mod_cast (by omega : k < n+1)
  have H := Lagrange.coeff_eq_sum hz.injOn hd
  simp only [Polynomial.coeff_X_pow, Finset.card_univ, Fintype.card_fin,
    Nat.add_sub_cancel, ite_eq_right (by omega : n ≠ k), Polynomial.eval_pow,
    Polynomial.eval_X] at H
  have he (i : Fin (n+1)) :
      (∏ j ∈ Finset.univ.erase i, (z j-z i)) =
        (-1:ℝ)^n * ∏ j ∈ Finset.univ.erase i, (z i-z j) := by
    simp_rw [show ∀ j, z j-z i = (-1:ℝ)*(z i-z j) from fun j => by ring]
    rw [Finset.prod_mul_distrib]
    simp
  simp_rw [he, mul_comm ((-1:ℝ)^n), div_mul_eq_div_mul_one_div]
  rw [← Finset.sum_mul, ← H, zero_mul]

 

def reflectionMomentKernel (n k : ℕ) (z : Fin (n+1) → ℝ) : ℝ :=
  (z 0)^k * omega (z 0) * reflectionProduct n (z 0) (Fin.tail z) * density n (Fin.tail z)

lemma measurable_reflectionMomentKernel (n k : ℕ) : Measurable (reflectionMomentKernel n k) := by
  have ht : Measurable (fun z : Fin (n+1) → ℝ => Fin.tail z) :=
    Measurable.of_eval (fun i => measurable_pi_apply i.succ)
  exact ((((measurable_pi_apply 0).pow_const k).mul (measurable_omega.comp (measurable_pi_apply 0))).mul
    ((measurable_reflectionProduct n).comp ((measurable_pi_apply 0).prodMk ht))).mul
    ((measurable_density n).comp ht)

lemma abs_reflectionMomentKernel_le_weights {n k : ℕ} {z : Fin (n+1) → ℝ}
    (hz : ∀ i, z i ∈ Ioo (0:ℝ) 1) :
    |reflectionMomentKernel n k z| ≤ ∏ i, omega (z i) := by
  have ht : ∀ i, Fin.tail z i ∈ Ioo (0:ℝ) 1 := fun i => hz i.succ
  have hpow : (z 0)^k ≤ 1 := pow_le_one₀ (hz 0).1.le (hz 0).2.le
  have hrefl : |reflectionProduct n (z 0) (Fin.tail z)| ≤ 1 := by
    rw [reflectionProduct, Finset.abs_prod]
    exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _)
      (fun i _ => abs_reflectionFactor_le_one (hz 0).1.le (ht i).1)
  rw [reflectionMomentKernel, abs_mul, abs_mul, abs_mul,
    abs_of_nonneg (pow_nonneg (hz 0).1.le _), abs_of_nonneg (omega_nonneg _),
    abs_of_nonneg (density_nonneg_of_nonneg (fun i => (ht i).1.le)), Fin.prod_univ_succ]
  calc
    _ ≤ 1 * omega (z 0) * 1 * (∏ i, omega (Fin.tail z i)) := by
      apply mul_le_mul
      · exact mul_le_mul (mul_le_mul_of_nonneg_right hpow (omega_nonneg _)) hrefl
          (abs_nonneg _) (by positivity [omega_nonneg (z 0)])
      · exact density_cube_le_product ht
      · exact density_nonneg_of_nonneg (fun i => (ht i).1.le)
      · positivity [omega_nonneg (z 0)]
    _ = _ := by simp [Fin.tail_def]

lemma integrable_reflectionMomentKernel (n k : ℕ) :
    Integrable (reflectionMomentKernel n k) (unitCubeMeasure (n+1)) := by
  apply integrable_unitCube_of_abs_le_weights (measurable_reflectionMomentKernel n k) (b := 1)
  intro z hz
  simpa only [one_mul] using abs_reflectionMomentKernel_le_weights (k := k) hz

lemma reflectionMomentKernel_sum_swaps {n k : ℕ} (hk : k < n)
    {z : Fin (n+1) → ℝ} (hz : ∀ i, 0 < z i) :
    ∑ i : Fin (n+1), reflectionMomentKernel n k (z ∘ Equiv.swap 0 i) = 0 := by
  classical
  have he (i : Fin (n+1)) : reflectionMomentKernel n k (z ∘ Equiv.swap 0 i) =
      density (n+1) z * (z i ^ k / ∏ j ∈ Finset.univ.erase i, (z j-z i)) := by
    have hx : 0 < (z ∘ Equiv.swap 0 i) 0 := hz _
    have hy : ∀ j, 0 < Fin.tail (z ∘ Equiv.swap 0 i) j := fun j => hz _
    unfold reflectionMomentKernel
    rw [mul_assoc ((z ∘ Equiv.swap 0 i) 0 ^ k), mul_assoc,
      reflection_with_density_cons hx hy, Fin.cons_self_tail,
      density_perm_of_nonneg (fun i => (hz i).le)]
    have hp : (∏ j, (Fin.tail (z ∘ Equiv.swap 0 i) j - (z ∘ Equiv.swap 0 i) 0)) =
        ∏ j ∈ Finset.univ.erase i, (z j-z i) := by
      have he0 : (∏ j, (Fin.tail (z ∘ Equiv.swap 0 i) j - (z ∘ Equiv.swap 0 i) 0)) =
          ∏ j ∈ Finset.univ.erase (0 : Fin (n+1)), ((z ∘ Equiv.swap 0 i) j - z i) := by
        have he0 : (Finset.univ.erase (0 : Fin (n+1))) =
            Finset.univ.filter (fun j => j ≠ 0) := by ext; simp
        rw [he0, Finset.prod_filter, Fin.prod_univ_succ]
        simp [Fin.tail_def]
      have hs : ∏ j ∈ Finset.univ.erase (0 : Fin (n+1)), ((z ∘ Equiv.swap 0 i) j - z i) =
          ∏ j ∈ Finset.univ.erase i, (z j-z i) := by
        apply Finset.prod_equiv (Equiv.swap 0 i)
        · intro j
          simp [Equiv.swap_apply_eq_iff]
        · intro j hj
          rfl
      exact he0.trans hs
    rw [hp]
    simp only [Function.comp_apply, Equiv.swap_apply_left]
    ring
  simp_rw [he, ← Finset.mul_sum]
  by_cases hi : Function.Injective z
  · rw [lagrange_reverse_denominator_sum hk hi, mul_zero]
  · rw [density_zero_of_not_injective hi, zero_mul]

lemma integral_reflectionMomentKernel_zero {n k : ℕ} (hk : k < n) :
    (∫ z, reflectionMomentKernel n k z ∂unitCubeMeasure (n+1)) = 0 := by
  classical
  have his (i : Fin (n+1)) : Integrable
      (fun z => reflectionMomentKernel n k (z ∘ Equiv.swap 0 i)) (unitCubeMeasure (n+1)) := by
    simpa only [Function.comp_def, StripPfaffian.piCongrLeft_const_apply, Equiv.symm_symm] using
      (measurePreserving_piCongrLeft (fun _ : Fin (n+1) => volume.restrict (Ioo (0:ℝ) 1))
        (Equiv.swap 0 i).symm).integrable_comp_of_integrable (integrable_reflectionMomentKernel n k)
  have he (i : Fin (n+1)) :
      (∫ z, reflectionMomentKernel n k (z ∘ Equiv.swap 0 i) ∂unitCubeMeasure (n+1)) =
        ∫ z, reflectionMomentKernel n k z ∂unitCubeMeasure (n+1) := by
    simpa only [StripPfaffian.piCongrLeft_const_apply, Equiv.symm_symm] using
      (measurePreserving_piCongrLeft (fun _ : Fin (n+1) => volume.restrict (Ioo (0:ℝ) 1))
        (Equiv.swap 0 i).symm).integral_comp' (reflectionMomentKernel n k)
  have hsum : ((n:ℝ)+1) * (∫ z, reflectionMomentKernel n k z ∂unitCubeMeasure (n+1)) = 0 := by
    calc
      _ = ∑ i : Fin (n+1), ∫ z, reflectionMomentKernel n k (z ∘ Equiv.swap 0 i) ∂unitCubeMeasure (n+1) := by
        simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      _ = ∫ z, ∑ i : Fin (n+1), reflectionMomentKernel n k (z ∘ Equiv.swap 0 i) ∂unitCubeMeasure (n+1) :=
        (integral_finsetSum _ (fun i _ => his i)).symm
      _ = ∫ _z, (0 : ℝ) ∂unitCubeMeasure (n+1) := by
        apply integral_congr_ae
        filter_upwards [ae_unitCube (n+1)] with z hz
        exact reflectionMomentKernel_sum_swaps hk (fun i => (hz i).1)
      _ = 0 := integral_zero _ _
  exact (mul_eq_zero.mp hsum).resolve_left (by positivity)

 

theorem reflection_expectation_moments {n k : ℕ} (hk : k < n) :
    (∫ x in Ioo (0:ℝ) 1, momentBasis k x * expectation n (reflectionProduct n x)) = 0 := by
  have hF := integral_reflectionMomentKernel_zero hk
  rw [integral_unitCube_cons, integral_prod _ (integrable_unitCube_cons (integrable_reflectionMomentKernel n k))] at hF
  have he (x : ℝ) : (∫ y, reflectionMomentKernel n k (Fin.cons x y) ∂unitCubeMeasure n) =
      momentBasis k x * (∫ y, reflectionProduct n x y * density n y ∂unitCubeMeasure n) := by
    simp only [reflectionMomentKernel, Fin.cons_zero, Fin.tail_cons, momentBasis,
      mul_assoc, integral_const_mul]
  simp_rw [he] at hF
  calc
    _ = ∫ x in Ioo (0:ℝ) 1,
        (momentBasis k x * (∫ y, reflectionProduct n x y * density n y ∂unitCubeMeasure n)) /
          (∫ y, density n y ∂unitCubeMeasure n) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro x hx
      dsimp only
      rw [expectation_reflection_unitCube n hx.1.le, mul_div_assoc]
    _ = 0 := by rw [integral_div, hF, zero_div]

 

def meanCharacteristic (n : ℕ) : Polynomial ℝ :=
  ∑ s ∈ (Finset.univ : Finset (Fin n)).powerset,
    Polynomial.C ((-1 : ℝ)^s.card *
      ∫ y, (∏ j ∈ Finset.univ \ s, y j) * density n y ∂unitCubeMeasure n) * Polynomial.X^s.card

lemma integrable_coordinateProduct_density {n : ℕ} (s : Finset (Fin n)) :
    Integrable (fun y => (∏ j ∈ s, y j) * density n y) (unitCubeMeasure n) := by
  apply integrable_cube_mul_density (by fun_prop) (b := 1)
  intro y hy
  rw [Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun j _ => by rw [abs_of_pos (hy j).1]; exact (hy j).2.le)

lemma meanCharacteristic_eval (n : ℕ) (x : ℝ) :
    (meanCharacteristic n).eval x = ∫ y, (∏ j, (y j-x)) * density n y ∂unitCubeMeasure n := by
  classical
  have he (y : Fin n → ℝ) : (∏ j, (y j-x)) * density n y =
      ∑ s ∈ (Finset.univ : Finset (Fin n)).powerset,
        ((-1 : ℝ)^s.card * x^s.card) * ((∏ j ∈ Finset.univ \ s, y j) * density n y) := by
    rw [Finset.prod_sub, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s _
    simp only [Finset.prod_const]
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun s _ => (integrable_coordinateProduct_density _).const_mul _)]
  simp only [meanCharacteristic, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, integral_const_mul]
  apply Finset.sum_congr rfl
  intro s _
  ring

lemma meanCharacteristic_natDegree (n : ℕ) : (meanCharacteristic n).natDegree ≤ n := by
  classical
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro s hs
  apply (Polynomial.natDegree_mul_le).trans
  simpa only [Polynomial.natDegree_C, Polynomial.natDegree_X_pow, zero_add, Finset.card_univ,
    Fintype.card_fin] using (Finset.card_le_card (Finset.mem_powerset.mp hs))

lemma polynomial_transformedBasis (n : ℕ) (p : Polynomial ℝ) (hp : p.natDegree < n)
    {x : ℝ} (hx : 0 < x) :
    x * (∫ y in Ioo (0:ℝ) 1, p.eval y * omega y / (x+y)) =
      ∑ k : Fin n, p.coeff k.val * transformedBasis k.val x := by
  have hev (y : ℝ) : p.eval y = ∑ k : Fin n, p.coeff k.val * y^k.val := by
    rw [Polynomial.eval_eq_sum_range' hp, ← Fin.sum_univ_eq_sum_range]
  have heq : (fun y => x * (p.eval y * omega y / (x+y))) =
      fun y => ∑ k : Fin n, p.coeff k.val * (boundedCauchy x y * momentBasis k.val y) := by
    funext y
    rw [hev]
    simp only [Finset.sum_mul, Finset.sum_div, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    unfold boundedCauchy momentBasis
    ring
  rw [← integral_const_mul, heq,
    integral_finsetSum _ (fun k _ => (integrableOn_boundedCauchy_basis k.val hx).const_mul _)]
  simp only [integral_const_mul, transformedBasis]

 
def reflectionResidueKernel (n : ℕ) (x : ℝ) (i : Fin n) (y : Fin n → ℝ) : ℝ :=
  reflectionResidue n y i * density n y / (x+y i)

lemma measurable_reflectionResidueKernel (n : ℕ) (x : ℝ) (i : Fin n) :
    Measurable (reflectionResidueKernel n x i) := by
  unfold reflectionResidueKernel reflectionResidue
  apply Measurable.div
  · apply Measurable.mul _ (measurable_density n)
    fun_prop
  · fun_prop

lemma reflectionResidueKernel_perm {n : ℕ} (x : ℝ) {y : Fin n → ℝ}
    (hy : ∀ i, 0 ≤ y i) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    reflectionResidueKernel n x i (y ∘ σ) = reflectionResidueKernel n x (σ i) y := by
  unfold reflectionResidueKernel
  rw [reflectionResidue_perm, density_perm_of_nonneg hy]
  rfl

lemma reflectionResidueKernel_cons {n : ℕ} (x : ℝ) {u : ℝ} {y : Fin n → ℝ}
    (hu : 0 < u) (hy : ∀ i, 0 < y i) :
    reflectionResidueKernel (n+1) x 0 (Fin.cons u y) =
      2 * omega u / (x+u) * ((∏ j, (y j-u)) * density n y) := by
  rw [reflectionResidueKernel, reflectionResidue_density_cons hu hy, Fin.cons_zero]
  ring

lemma abs_reflectionResidueKernel_zero_le {n : ℕ} {x : ℝ} (hx : 0 < x)
    {z : Fin (n+1) → ℝ} (hz : ∀ i, z i ∈ Ioo (0:ℝ) 1) :
    |reflectionResidueKernel (n+1) x 0 z| ≤ (2/x) * ∏ i, omega (z i) := by
  have hprod : |∏ j : Fin n, (Fin.tail z j-z 0)| ≤ 1 := by
    rw [Finset.abs_prod]
    exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun j _ => by
      rw [abs_le]; constructor <;> dsimp [Fin.tail_def] <;> linarith [(hz j.succ).1, (hz j.succ).2, (hz 0).1, (hz 0).2])
  have hd : 0 ≤ density n (Fin.tail z) := density_nonneg_of_nonneg fun j => (hz j.succ).1.le
  have hω := omega_nonneg (z 0)
  have hz0 : 0 < z 0 := (hz 0).1
  have he := reflectionResidueKernel_cons (y := Fin.tail z) x (hz 0).1 (fun j => (hz j.succ).1)
  change reflectionResidueKernel (n+1) x 0 (Fin.cons (z 0) (Fin.tail z)) = _ at he
  rw [Fin.cons_self_tail] at he
  rw [he, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2*omega (z 0)/(x+z 0)), abs_mul, abs_of_nonneg hd]
  calc
    _ ≤ (2*omega (z 0)/(x+z 0)) * (1 * density n (Fin.tail z)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hprod hd) (by positivity [ (hz 0).1 ])
    _ ≤ (2*omega (z 0)/x) * density n (Fin.tail z) := by
      rw [one_mul]
      apply mul_le_mul_of_nonneg_right _ hd
      exact div_le_div_of_nonneg_left (by positivity) hx (le_add_of_nonneg_right (hz 0).1.le)
    _ ≤ (2*omega (z 0)/x) * ∏ j : Fin n, omega (Fin.tail z j) :=
      mul_le_mul_of_nonneg_left (density_cube_le_product (fun j => hz j.succ)) (by positivity)
    _ = _ := by rw [Fin.prod_univ_succ]; simp only [Fin.tail_def]; ring

lemma abs_reflectionResidueKernel_le {n : ℕ} {x : ℝ} (hx : 0 < x)
    (i : Fin (n+1)) {z : Fin (n+1) → ℝ} (hz : ∀ i, z i ∈ Ioo (0:ℝ) 1) :
    |reflectionResidueKernel (n+1) x i z| ≤ (2/x) * ∏ j, omega (z j) := by
  have he : reflectionResidueKernel (n+1) x 0 (z ∘ Equiv.swap 0 i) =
      reflectionResidueKernel (n+1) x i z := by
    rw [reflectionResidueKernel_perm _ (fun i => (hz i).1.le), Equiv.swap_apply_left]
  have h := abs_reflectionResidueKernel_zero_le (z := z ∘ Equiv.swap 0 i) hx (fun j => hz (Equiv.swap 0 i j))
  rw [he] at h
  apply h.trans_eq
  congr 1
  exact Fintype.prod_equiv (Equiv.swap 0 i) _ _ (fun _ => rfl)

lemma integrable_reflectionResidueKernel {n : ℕ} {x : ℝ} (hx : 0 < x) (i : Fin (n+1)) :
    Integrable (reflectionResidueKernel (n+1) x i) (unitCubeMeasure (n+1)) := by
  exact integrable_unitCube_of_abs_le_weights (measurable_reflectionResidueKernel _ _ _)
    (fun _ hz => abs_reflectionResidueKernel_le hx i hz)

end
end CriticalStrip

end OAI
