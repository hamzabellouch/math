import Mathlib
import OAI.Combinatorics.StripMass.ReflectionIntegrals
import OAI.Combinatorics.StripMass.CollisionSubstitutions

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open Set MeasureTheory Filter
open scoped Topology

lemma transformed_omega_extended {s t : ℝ} (hs : -1 < s) (ht : 0 < t) :
    |(-8 * t * (t ^ 2 + 1) / uniformDen t ^ 2)| •
        (s * omega (uniformizer t) / (1 + s * uniformizer t)) =
      quarticWeighted (Real.sqrt ((1 + s) / 2)) t -
        quarticWeighted (Real.sqrt (1 / 2)) t := by
  rw [omega_uniformizer ht, abs_of_neg (by
    exact div_neg_of_neg_of_pos (by nlinarith [sq_nonneg t])
      (sq_pos_of_pos (uniformDen_pos t))), smul_eq_mul]
  unfold quarticWeighted quarticDen
  rw [Real.sq_sqrt (by linarith : (0 : ℝ) ≤ (1 + s) / 2),
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  unfold uniformizer uniformDen
  have hd : 1 + t^2*4 + t^4*2 + s ≠ 0 := by nlinarith [sq_nonneg t,sq_nonneg (t^2)]
  field_simp
  ring_nf
  field_simp [hd]
  ring

lemma omega_resolvent_extended {s : ℝ} (hs : -1 < s) :
    IntegrableOn (fun x => s * omega x / (1 + s * x)) (Ioo 0 1) ∧
      (∫ x in Ioo 0 1, s * omega x / (1 + s * x)) =
        Real.pi * (minusBranch s - minusBranch 0) := by
  have hr : 0 < Real.sqrt ((1 + s) / 2) := Real.sqrt_pos.mpr (by linarith)
  have hr0 : 0 < Real.sqrt ((1 : ℝ) / 2) := by positivity
  have hint := (quartic_weighted_integral hr).1.sub (quartic_weighted_integral hr0).1
  have hi := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun t _ => (uniformizer_deriv t).hasDerivWithinAt) uniformizer_inj
    (fun x => s * omega x / (1 + s * x))
  rw [uniformizer_image] at hi
  constructor
  · apply hi.2
    exact IntegrableOn.congr_fun hint (fun t ht => (transformed_omega_extended hs ht).symm)
      measurableSet_Ioi
  · have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      (fun t _ => (uniformizer_deriv t).hasDerivWithinAt) uniformizer_inj
      (fun x => s * omega x / (1 + s * x))
    rw [uniformizer_image] at h
    rw [h, setIntegral_congr_fun measurableSet_Ioi (fun t ht => transformed_omega_extended hs ht),
      integral_sub (quartic_weighted_integral hr).1 (quartic_weighted_integral hr0).1,
      quartic_weighted_integral_sqrt hr, quartic_weighted_integral_sqrt hr0]
    simp only [minusBranch, add_zero]
    ring

 
lemma stieltjes_omega_right {z : ℝ} (hz : 1 < z) :
    fBranch z = C + (1 / Real.pi) *
        ∫ x in Ioo (0 : ℝ) 1, omega x / (x - z) := by
  have hz0 : 0 < z := by linarith
  have hs : -1 < -1 / z := by rw [lt_div_iff₀ hz0]; linarith
  have heq : EqOn (fun x => (-1 / z) * omega x / (1 + (-1 / z) * x))
      (fun x => omega x / (x - z)) (Ioo 0 1) := by
    intro x hx
    dsimp only
    have ha : 1 + (-1 / z) * x ≠ 0 := by
      have he : 1 + (-1 / z) * x = (z-x)/z := by field_simp; ring
      rw [he]; exact div_ne_zero (by linarith [hx.2]) hz0.ne'
    have hb : x - z ≠ 0 := by linarith [hx.2]
    apply (div_eq_div_iff ha hb).2
    field_simp
    ring
  have h := (omega_resolvent_extended hs).2
  rw [setIntegral_congr_fun measurableSet_Ioo heq, minusBranch_zero] at h
  have he : minusBranch (-1 / z) = fBranch z := by
    unfold minusBranch fBranch
    congr 4
    ring
  rw [he] at h
  change fBranch z = C + (1 / Real.pi) * _
  change _ = Real.pi * (fBranch z - C) at h
  rw [h]
  field_simp
  ring

lemma transformed_squareWeight_extended {s t : ℝ} (hs : -1 < s) (ht : 0 < t) :
    |(-2 * t / (1 + t ^ 2) ^ 2)| •
        (s * squareWeight (squareUniformizer t) / (1 + s * squareUniformizer t)) =
      (1 / Real.sqrt 2) * ((1 + s) * ((1 + s) + t ^ 2)⁻¹ - (1 + t ^ 2)⁻¹) := by
  rw [squareWeight_uniformizer ht, abs_of_neg (by
    exact div_neg_of_neg_of_pos (by linarith) (by positivity)), smul_eq_mul]
  unfold squareUniformizer
  have hd : 1 + t^2 + s ≠ 0 := by nlinarith [sq_nonneg t]
  field_simp
  ring_nf
  field_simp [hd]
  ring

lemma squareWeight_resolvent_extended {s : ℝ} (hs : -1 < s) :
    IntegrableOn (fun x => s * squareWeight x / (1 + s * x)) (Ioo 0 1) ∧
      (∫ x in Ioo 0 1, s * squareWeight x / (1 + s * x)) =
        (Real.pi / (2 * Real.sqrt 2)) * (Real.sqrt (1 + s) - 1) := by
  let a := Real.sqrt (1 + s)
  have ha : 0 < a := Real.sqrt_pos.mpr (by linarith)
  have ha2 : a ^ 2 = 1 + s := Real.sq_sqrt (by linarith)
  have hint1 : IntegrableOn (fun t : ℝ => ((1 + s) + t ^ 2)⁻¹) (Ioi 0) := by
    rw [← ha2]
    exact (scaled_cauchy ha).1.integrableOn
  have hint0 : IntegrableOn (fun t : ℝ => (1 + t ^ 2)⁻¹) (Ioi 0) :=
    integrable_inv_one_add_sq.integrableOn
  have hint := ((hint1.const_mul (1 + s)).sub hint0).const_mul (1 / Real.sqrt 2)
  have hi := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun t _ => (squareUniformizer_deriv t).hasDerivWithinAt) squareUniformizer_inj
    (fun x => s * squareWeight x / (1 + s * x))
  rw [squareUniformizer_image] at hi
  constructor
  · apply hi.2
    exact IntegrableOn.congr_fun hint (fun t ht => (transformed_squareWeight_extended hs ht).symm)
      measurableSet_Ioi
  · have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      (fun t _ => (squareUniformizer_deriv t).hasDerivWithinAt) squareUniformizer_inj
      (fun x => s * squareWeight x / (1 + s * x))
    rw [squareUniformizer_image] at h
    rw [h, setIntegral_congr_fun measurableSet_Ioi (fun t ht => transformed_squareWeight_extended hs ht),
      integral_const_mul, integral_sub (hint1.const_mul (1 + s)) hint0,
      integral_const_mul, ← ha2, scaled_cauchy_Ioi ha, integral_Ioi_inv_one_add_sq,
      Real.arctan_zero, sub_zero]
    rw [Real.sqrt_sq ha.le]
    field_simp

lemma stieltjes_omega_square_right {z : ℝ} (hz : 1 < z) :
    fBranch z ^ 2 = C ^ 2 + (1 / Real.pi) *
        ∫ x in Ioo (0 : ℝ) 1, lBranch x * omega x / (x - z) := by
  have hz0 : 0 < z := by linarith
  have hs : -1 < -1 / z := by rw [lt_div_iff₀ hz0]; linarith
  have heq : EqOn (fun x => (-1 / z) * squareWeight x / (1 + (-1 / z) * x))
      (fun x => lBranch x * omega x / (x - z)) (Ioo 0 1) := by
    intro x hx
    dsimp only
    rw [lBranch_mul_omega hx]
    have ha : 1 + (-1 / z) * x ≠ 0 := by
      have he : 1 + (-1 / z) * x = (z-x)/z := by field_simp; ring
      rw [he]; exact div_ne_zero (by linarith [hx.2]) hz0.ne'
    have hb : x - z ≠ 0 := by linarith [hx.2]
    apply (div_eq_div_iff ha hb).2
    field_simp
    ring
  have h := (squareWeight_resolvent_extended hs).2
  rw [setIntegral_congr_fun measurableSet_Ioo heq] at h
  have hC : C ^ 2 = (1 + Real.sqrt (1 / 2)) / 2 := by
    change (Real.cos (Real.pi/8))^2 = _
    rw [← minusBranch_zero]
    unfold minusBranch
    simp only [add_zero]
    exact Real.sq_sqrt (by positivity)
  rw [h, hC, fBranch, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (1 + Real.sqrt ((1 - 1 / z) / 2)) / 2)]
  have heq' : 1 - 1 / z = 1 + -1 / z := by ring
  rw [heq', Real.sqrt_div (by linarith : (0 : ℝ) ≤ 1 + -1 / z),
    Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one]
  field_simp
  ring



lemma offCut_of_outside {z : ℝ} (hz : z < 0 ∨ 1 < z) : offCut 1 z := by
  intro x hx
  simp only [one_mul]
  rcases hz with hz | hz <;> linarith [hx.1,hx.2]

lemma fBranch_transform_outside {z : ℝ} (hz : z < 0 ∨ 1 < z) :
    fBranch z = C - (1 / Real.pi) * realStieltjes 1 omega z := by
  have h : fBranch z = C + (1 / Real.pi) * ∫ x in Ioo (0:ℝ) 1, omega x/(x-z) := by
    rcases hz with hz | hz
    · exact stieltjes_omega hz
    · exact stieltjes_omega_right hz
  have heq : (∫ x in Ioo (0 : ℝ) 1, omega x / (x - z)) = -realStieltjes 1 omega z := by
    rw [realStieltjes, ← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro x _
    simp only [one_mul]
    rw [show x - z = -(z - x) by ring, div_neg]
  simpa only [heq, mul_neg, ← sub_eq_add_neg] using h

lemma fBranch_square_transform_outside {z : ℝ} (hz : z < 0 ∨ 1 < z) :
    fBranch z ^ 2 = C ^ 2 -
      (1 / Real.pi) * realStieltjes 1 (fun x => lBranch x * omega x) z := by
  have h : fBranch z ^ 2 = C ^ 2 + (1 / Real.pi) *
      ∫ x in Ioo (0:ℝ) 1, lBranch x * omega x/(x-z) := by
    rcases hz with hz | hz
    · exact stieltjes_omega_square hz
    · exact stieltjes_omega_square_right hz
  have heq : (∫ x in Ioo (0 : ℝ) 1, lBranch x * omega x / (x - z)) =
      -realStieltjes 1 (fun x => lBranch x * omega x) z := by
    rw [realStieltjes, ← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro x _
    simp only [one_mul]
    rw [show x - z = -(z - x) by ring, div_neg]
  simpa only [heq, mul_neg, ← sub_eq_add_neg] using h

 
lemma projectionF_polynomial_outside (P J E : Polynomial ℝ) :
    ∃ R : Polynomial ℝ, ∀ z : ℝ, z < 0 ∨ 1 < z →
      projectionF P J E z = R.eval z - (1 / Real.pi) *
        realStieltjes 1 (fun x => projectionD J E x * omega x) z := by
  obtain ⟨Rj, hRj⟩ := polynomial_mul_realStieltjes (a := (1 : ℝ)) integrableOn_omega J
  obtain ⟨Re, hRe⟩ := polynomial_mul_realStieltjes (a := (1 : ℝ)) integrableOn_lBranch_omega E
  refine ⟨P + Polynomial.C C * J + Polynomial.C (C ^ 2) * E -
    Polynomial.C (1 / Real.pi) * (Rj + Re), ?_⟩
  intro z hz
  have hj := hRj z (offCut_of_outside hz)
  have he := hRe z (offCut_of_outside hz)
  have hsum := realStieltjes_add
    (integrableOn_polynomial_weight (a := (1 : ℝ)) integrableOn_omega J)
    (integrableOn_polynomial_weight (a := (1 : ℝ)) integrableOn_lBranch_omega E)
    (offCut_of_outside hz)
  have hw : (fun x => J.eval (1 * x) * omega x + E.eval (1 * x) * (lBranch x * omega x)) =
      fun x => projectionD J E x * omega x := by
    funext x
    simp only [one_mul, projectionD]
    ring
  rw [hw] at hsum
  simp only [one_mul] at hj he hsum
  rw [projectionF, fBranch_square_transform_outside hz, fBranch_transform_outside hz, hsum]
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
  linear_combination -(1 / Real.pi) * hj - (1 / Real.pi) * he

 
lemma projectionF_cauchy_outside (P J E : Polynomial ℝ)
    (hF : Tendsto (fun t : ℝ => projectionF P J E (-t)) atTop (𝓝 0)) :
    ∀ z : ℝ, z < 0 ∨ 1 < z → projectionF P J E z = -(1 / Real.pi) *
      realStieltjes 1 (fun x => projectionD J E x * omega x) z := by
  obtain ⟨R, hR⟩ := projectionF_polynomial_outside P J E
  have hz : Tendsto (fun t : ℝ => ‖-t‖) atTop atTop := by
    simpa only [norm_neg] using (tendsto_norm_atTop_atTop : Tendsto (fun t : ℝ => ‖t‖) atTop atTop)
  have hlim := hF.add ((tendsto_realStieltjes_zero (integrableOn_projection_weight J E)
    (by norm_num : |(1 : ℝ)| ≤ 1) hz).const_mul (1 / Real.pi))
  have hRlim : Tendsto (fun t : ℝ => R.eval (-t)) atTop (𝓝 0) := by
    have hlim' : Tendsto (fun t : ℝ => projectionF P J E (-t) + (1 / Real.pi) *
        realStieltjes 1 (fun x => projectionD J E x * omega x) (-t)) atTop (𝓝 0) := by
      simpa only [mul_zero, add_zero] using hlim
    apply hlim'.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have h := hR (-t) (Or.inl (neg_neg_of_pos ht))
    linarith
  have hR0 := polynomial_constant_of_limit hz R hRlim
  intro z hz
  simpa only [hR0, Polynomial.eval_C, zero_sub, neg_mul] using hR z hz

end

 

 

noncomputable section
open Set MeasureTheory Filter Polynomial
open scoped Topology BigOperators Classical

 

lemma lagrange_reverse_cauchy_sum {n : ℕ} {y : Fin (n+1) → ℝ}
    (hy : Function.Injective y) {z : ℝ} (hz : ∀ i, z ≠ y i) :
    ∑ i, 1 / ((z-y i) * ∏ j ∈ Finset.univ.erase i, (y j-y i)) =
      (-1:ℝ)^n / ∏ i, (z-y i) := by
  have H := congrArg (Polynomial.eval z) (Lagrange.sum_basis hy.injOn
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin (n+1))).Nonempty))
  simp only [eval_finsetSum, eval_one] at H
  have hb (i : Fin (n+1)) := Lagrange.eval_basis_not_at_node (Finset.mem_univ i) (hz i)
  simp only [Lagrange.eval_nodal, Lagrange.nodalWeight, Finset.prod_inv_distrib] at hb
  have he (i : Fin (n+1)) :
      (∏ j ∈ Finset.univ.erase i, (y j-y i)) =
        (-1:ℝ)^n * ∏ j ∈ Finset.univ.erase i, (y i-y j) := by
    simp_rw [show ∀ j, y j-y i = (-1:ℝ)*(y i-y j) from fun j => by ring]
    rw [Finset.prod_mul_distrib]
    simp
  have he' (i : Fin (n+1)) :
      1 / ((z-y i) * ∏ j ∈ Finset.univ.erase i, (y j-y i)) =
        (-1:ℝ)^n * (∏ j ∈ Finset.univ.erase i, (y i-y j))⁻¹ * (z-y i)⁻¹ := by
    rw [he, one_div, mul_inv, mul_inv]
    ring_nf
    simp only [inv_neg, inv_one]
    ring
  simp_rw [he']
  have hh : (∏ i, (z-y i)) *
      (∑ i, (∏ j ∈ Finset.univ.erase i, (y i-y j))⁻¹ * (z-y i)⁻¹) = 1 := by
    simpa only [hb, ← Finset.mul_sum] using H
  have hd : (∏ i, (z-y i)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => sub_ne_zero.mpr (hz i)
  have hh' : (∑ i, (∏ j ∈ Finset.univ.erase i, (y i-y j))⁻¹ * (z-y i)⁻¹) =
      1/(∏ i, (z-y i)) := (eq_div_iff hd).mpr (by simpa only [mul_comm] using hh)
  calc
    _ = (-1:ℝ)^n * (∑ i, (∏ j ∈ Finset.univ.erase i, (y i-y j))⁻¹ * (z-y i)⁻¹) := by
      simp_rw [mul_assoc]; rw [Finset.mul_sum]
    _ = _ := by rw [hh']; ring

def reflectionCauchyKernel (n : ℕ) (z : ℝ) (y : Fin (n+1) → ℝ) : ℝ :=
  reflectionMomentKernel n 0 y / (z-y 0)

lemma measurable_reflectionCauchyKernel (n : ℕ) (z : ℝ) :
    Measurable (reflectionCauchyKernel n z) :=
  (measurable_reflectionMomentKernel n 0).div (measurable_const.sub (measurable_pi_apply 0))

lemma integrable_reflectionCauchyKernel (n : ℕ) {z : ℝ} (hz : 1 < z) :
    Integrable (reflectionCauchyKernel n z) (unitCubeMeasure (n+1)) := by
  apply integrable_unitCube_of_abs_le_weights (measurable_reflectionCauchyKernel n z)
    (b := (z-1)⁻¹)
  intro y hy
  rw [reflectionCauchyKernel, abs_div, abs_of_pos (by linarith [(hy 0).2] : 0 < z-y 0)]
  calc
    _ ≤ (∏ i, omega (y i))/(z-1) := div_le_div₀
      (Finset.prod_nonneg fun i _ => omega_nonneg _) (abs_reflectionMomentKernel_le_weights hy)
      (by linarith) (by linarith [(hy 0).2])
    _ = _ := by ring

lemma reflectionCauchyKernel_sum_swaps (n : ℕ) {z : ℝ} {y : Fin (n+1) → ℝ}
    (hy : ∀ i, 0 < y i) (hz : ∀ i, z ≠ y i) :
    ∑ i, reflectionCauchyKernel n z (y ∘ Equiv.swap 0 i) =
      (-1:ℝ)^n * (density (n+1) y / ∏ i, (z-y i)) := by
  have he (i : Fin (n+1)) : reflectionCauchyKernel n z (y ∘ Equiv.swap 0 i) =
      density (n+1) y * (1 / ((z-y i) * ∏ j ∈ Finset.univ.erase i, (y j-y i))) := by
    have hx : 0 < (y ∘ Equiv.swap 0 i) 0 := hy _
    have ht : ∀ j, 0 < Fin.tail (y ∘ Equiv.swap 0 i) j := fun j => hy _
    unfold reflectionCauchyKernel reflectionMomentKernel
    rw [pow_zero, one_mul, reflection_with_density_cons hx ht,
      Fin.cons_self_tail, density_perm_of_nonneg (fun i => (hy i).le)]
    have hp : (∏ j, (Fin.tail (y ∘ Equiv.swap 0 i) j - (y ∘ Equiv.swap 0 i) 0)) =
        ∏ j ∈ Finset.univ.erase i, (y j-y i) := by
      have he0 : (∏ j, (Fin.tail (y ∘ Equiv.swap 0 i) j - (y ∘ Equiv.swap 0 i) 0)) =
          ∏ j ∈ Finset.univ.erase (0 : Fin (n+1)), ((y ∘ Equiv.swap 0 i) j - y i) := by
        have he0 : (Finset.univ.erase (0 : Fin (n+1))) =
            Finset.univ.filter (fun j => j ≠ 0) := by ext; simp
        rw [he0, Finset.prod_filter, Fin.prod_univ_succ]
        simp [Fin.tail_def]
      have hs : ∏ j ∈ Finset.univ.erase (0 : Fin (n+1)), ((y ∘ Equiv.swap 0 i) j - y i) =
          ∏ j ∈ Finset.univ.erase i, (y j-y i) := by
        apply Finset.prod_equiv (Equiv.swap 0 i)
        · intro j
          simp [Equiv.swap_apply_eq_iff]
        · intro j hj
          rfl
      exact he0.trans hs
    rw [hp]
    simp only [Function.comp_apply, Equiv.swap_apply_left]
    rw [one_div, mul_inv]
    ring
  simp_rw [he, ← Finset.mul_sum]
  by_cases hi : Function.Injective y
  · rw [lagrange_reverse_cauchy_sum hi hz]
    ring
  · rw [density_zero_of_not_injective hi, zero_mul, zero_div, mul_zero]

 
def cauchyDensity (n : ℕ) (z : ℝ) (y : Fin n → ℝ) : ℝ :=
  density n y / ∏ i, (z-y i)

lemma integrable_cauchyDensity (n : ℕ) {z : ℝ} (hz : 1 < z) :
    Integrable (cauchyDensity n z) (unitCubeMeasure n) := by
  have hi : Integrable (fun y : Fin n → ℝ => (∏ i, (z-y i))⁻¹ * density n y)
      (unitCubeMeasure n) := by
    apply integrable_cube_mul_density (by fun_prop) (b := ((z-1)⁻¹)^n)
    intro y hy
    rw [abs_inv, Finset.abs_prod, ← Finset.prod_inv_distrib]
    have hh (i : Fin n) : |z-y i|⁻¹ ≤ (z-1)⁻¹ := by
      rw [abs_of_pos (by linarith [(hy i).2] : 0 < z-y i)]
      exact inv_anti₀ (by linarith) (by linarith [(hy i).2])
    calc
      _ ≤ ∏ _ : Fin n, (z-1)⁻¹ := Finset.prod_le_prod₀
        (fun i _ => inv_nonneg.mpr (abs_nonneg _)) (fun i _ => hh i)
      _ = _ := by simp
  exact hi.congr (Filter.Eventually.of_forall fun y => by dsimp [cauchyDensity]; ring)

lemma integral_cauchyDensity_pos (n : ℕ) {z : ℝ} (hz : 1 < z) :
    0 < ∫ y, cauchyDensity n z y ∂unitCubeMeasure n := by
  apply integral_pos_on_cube (integrable_cauchyDensity n hz)
  · intro y hy
    exact div_nonneg (density_nonneg_of_nonneg fun i => (hy i).1.le)
      (Finset.prod_nonneg fun i _ => by linarith [(hy i).2])
  · intro y hy
    exact div_pos (density_pos hy) (Finset.prod_pos fun i _ => by linarith [(hy.2 i).2])

lemma integral_reflectionCauchyKernel (n : ℕ) {z : ℝ} (hz : 1 < z) :
    ((n:ℝ)+1) * (∫ y, reflectionCauchyKernel n z y ∂unitCubeMeasure (n+1)) =
      (-1:ℝ)^n * ∫ y, cauchyDensity (n+1) z y ∂unitCubeMeasure (n+1) := by
  have his (i : Fin (n+1)) : Integrable
      (fun y => reflectionCauchyKernel n z (y ∘ Equiv.swap 0 i)) (unitCubeMeasure (n+1)) := by
    simpa only [Function.comp_def, StripPfaffian.piCongrLeft_const_apply, Equiv.symm_symm] using
      (measurePreserving_piCongrLeft (fun _ : Fin (n+1) => volume.restrict (Ioo (0:ℝ) 1))
        (Equiv.swap 0 i).symm).integrable_comp_of_integrable (integrable_reflectionCauchyKernel n hz)
  have he (i : Fin (n+1)) :
      (∫ y, reflectionCauchyKernel n z (y ∘ Equiv.swap 0 i) ∂unitCubeMeasure (n+1)) =
        ∫ y, reflectionCauchyKernel n z y ∂unitCubeMeasure (n+1) := by
    simpa only [StripPfaffian.piCongrLeft_const_apply, Equiv.symm_symm] using
      (measurePreserving_piCongrLeft (fun _ : Fin (n+1) => volume.restrict (Ioo (0:ℝ) 1))
        (Equiv.swap 0 i).symm).integral_comp' (reflectionCauchyKernel n z)
  calc
    _ = ∑ i : Fin (n+1), ∫ y, reflectionCauchyKernel n z (y ∘ Equiv.swap 0 i) ∂unitCubeMeasure (n+1) := by
      simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    _ = ∫ y, ∑ i : Fin (n+1), reflectionCauchyKernel n z (y ∘ Equiv.swap 0 i) ∂unitCubeMeasure (n+1) :=
      (integral_finsetSum _ (fun i _ => his i)).symm
    _ = ∫ y, (-1:ℝ)^n * cauchyDensity (n+1) z y ∂unitCubeMeasure (n+1) := by
      apply integral_congr_ae
      filter_upwards [ae_unitCube (n+1)] with y hy
      exact reflectionCauchyKernel_sum_swaps n (fun i => (hy i).1) (fun i => by linarith [(hy i).2])
    _ = _ := integral_const_mul _ _

lemma integral_density_unitCube_positive (n : ℕ) :
    0 < ∫ y, density n y ∂unitCubeMeasure n := by
  rw [integral_density_unitCube]
  exact mul_pos (by exact_mod_cast Nat.factorial_pos n) (normalizer_pos n)

lemma reflection_expectation_cauchy (n : ℕ) {z : ℝ} (hz : 1 < z) :
    realStieltjes 1 (fun x => expectation n (reflectionProduct n x) * omega x) z =
      ((-1:ℝ)^n * ∫ y, cauchyDensity (n+1) z y ∂unitCubeMeasure (n+1)) /
        (((n:ℝ)+1) * ∫ y, density n y ∂unitCubeMeasure n) := by
  have hF := integral_reflectionCauchyKernel n hz
  rw [integral_unitCube_cons,
    integral_prod _ (integrable_unitCube_cons (integrable_reflectionCauchyKernel n hz))] at hF
  have he (x : ℝ) : (∫ y, reflectionCauchyKernel n z (Fin.cons x y) ∂unitCubeMeasure n) =
      (omega x / (z-x)) * (∫ y, reflectionProduct n x y * density n y ∂unitCubeMeasure n) := by
    simp only [reflectionCauchyKernel, reflectionMomentKernel, pow_zero, one_mul,
      Fin.cons_zero, Fin.tail_cons]
    simp_rw [show ∀ y : Fin n → ℝ, omega x * reflectionProduct n x y * density n y / (z-x) =
      (omega x/(z-x)) * (reflectionProduct n x y * density n y) from fun y => by ring]
    rw [integral_const_mul]
  simp_rw [he] at hF
  have hh : (∫ x in Ioo (0:ℝ) 1, (omega x / (z-x)) *
      (∫ y, reflectionProduct n x y * density n y ∂unitCubeMeasure n)) =
      (∫ y, density n y ∂unitCubeMeasure n) *
        realStieltjes 1 (fun x => expectation n (reflectionProduct n x) * omega x) z := by
    rw [realStieltjes, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro x hx
    dsimp only
    rw [expectation_reflection_unitCube n hx.1.le, one_mul]
    field_simp [integral_density_unitCube_positive n |>.ne']
  rw [hh] at hF
  exact (eq_div_iff (mul_ne_zero (by positivity) (integral_density_unitCube_positive n).ne')).mpr
    (by nlinarith [hF])


 

 


lemma projection_initial_monic {n : ℕ} (hn : 1 ≤ n) {g P J E : Polynomial ℝ}
    (hg : g.Monic) (hd : g.natDegree = n)
    (hP : P.natDegree ≤ n) (hJ : J.natDegree ≤ n) (hE : E.degree < (n : WithBot ℕ))
    (hQ : homogeneousQ n g = P.comp harmonicCoordinate + X * J.comp harmonicCoordinate +
      X^2 * E.comp harmonicCoordinate) :
    (tildePoly n J).eval 0 = ((-8:ℝ)^n)⁻¹ := by
  have ht := (projection_top_coefficients n hn P J E hP hJ hE).1
  rw [← hQ, ← homogeneousQ_natDegree hg hd, (homogeneousQ_monic hg).coeff_natDegree] at ht
  apply (mul_left_cancel₀ (pow_ne_zero n (by norm_num : (-8:ℝ) ≠ 0)))
  rw [mul_inv_cancel₀ (pow_ne_zero n (by norm_num : (-8:ℝ) ≠ 0))]
  exact ht.symm

lemma projectionF_positive_cauchy {n : ℕ} (hn : 1 ≤ n) {g P J E : Polynomial ℝ}
    (hg : g.Monic) (hd : g.natDegree = n)
    (hP : P.natDegree ≤ n) (hJ : J.natDegree ≤ n) (hE : E.degree < (n : WithBot ℕ))
    (hQ : homogeneousQ n g = P.comp harmonicCoordinate + X * J.comp harmonicCoordinate +
      X^2 * E.comp harmonicCoordinate) {z : ℝ} (hz : 1 < z) :
    projectionF (tildePoly n P) (tildePoly n J) (tildePoly n E) z =
      - (∫ y, cauchyDensity (n+1) z y ∂unitCubeMeasure (n+1)) /
        (Real.pi * (8:ℝ)^n * ((n:ℝ)+1) * ∫ y, density n y ∂unitCubeMeasure n) := by
  have hD := projectionD_expectation n hn g P J E hP hJ hE hQ
  have hF : Tendsto (fun t : ℝ => projectionF (tildePoly n P) (tildePoly n J) (tildePoly n E) (-t))
      atTop (𝓝 0) := by
    simpa only [pow_zero,one_mul, projectionF, fBranch, highBranch] using tilde_F_decay n g P J E hP hJ
      (degree_lt_implies_natDegree_lt (by omega) hE).le hQ 0 (Nat.zero_le n)
  rw [projectionF_cauchy_outside _ _ _ hF z (Or.inr hz)]
  have he : realStieltjes 1 (fun x => projectionD (tildePoly n J) (tildePoly n E) x * omega x) z =
      (tildePoly n J).eval 0 * realStieltjes 1 (fun x => expectation n (reflectionProduct n x) * omega x) z := by
    rw [realStieltjes, realStieltjes, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro x hx
    dsimp only
    rw [hD x hx.1]
    ring
  rw [he, projection_initial_monic hn hg hd hP hJ hE hQ, reflection_expectation_cauchy n hz]
  have hs : (-8:ℝ)^n * (-1:ℝ)^n = (8:ℝ)^n := by rw [← mul_pow]; norm_num
  have hs' : ((-8:ℝ)^n)⁻¹ * (-1:ℝ)^n = ((8:ℝ)^n)⁻¹ := by
    have hp : (-1:ℝ)^n * (-1:ℝ)^n=1 := by rw [←mul_pow]; norm_num
    apply (mul_left_cancel₀ (by positivity : (8:ℝ)^n≠0))
    rw [mul_inv_cancel₀ (by positivity : (8:ℝ)^n≠0),←hs]
    calc
      _ = ((-8:ℝ)^n * ((-8:ℝ)^n)⁻¹) * ((-1:ℝ)^n * (-1:ℝ)^n) := by ring
      _ = 1 := by rw [mul_inv_cancel₀ (pow_ne_zero n (by norm_num : (-8:ℝ)≠0)),hp,one_mul]
  calc
    _ = -(1/Real.pi) * (((-8:ℝ)^n)⁻¹ * (-1:ℝ)^n) *
        (∫ y, cauchyDensity (n+1) z y ∂unitCubeMeasure (n+1)) /
        (((n:ℝ)+1) * ∫ y, density n y ∂unitCubeMeasure n) := by ring
    _ = _ := by rw [hs']; simp only [div_eq_mul_inv, mul_inv]; ring

lemma projectionF_neg {n : ℕ} (hn : 1 ≤ n) {g P J E : Polynomial ℝ}
    (hg : g.Monic) (hd : g.natDegree = n)
    (hP : P.natDegree ≤ n) (hJ : J.natDegree ≤ n) (hE : E.degree < (n : WithBot ℕ))
    (hQ : homogeneousQ n g = P.comp harmonicCoordinate + X * J.comp harmonicCoordinate +
      X^2 * E.comp harmonicCoordinate) {z : ℝ} (hz : 1 < z) :
    projectionF (tildePoly n P) (tildePoly n J) (tildePoly n E) z < 0 := by
  rw [projectionF_positive_cauchy hn hg hd hP hJ hE hQ hz]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (integral_cauchyDensity_pos _ hz))
    (by have hp := Real.pi_pos; have hi := integral_density_unitCube_positive n; positivity)


 

 


lemma scaled_cauchyDensity (n : ℕ) {z : ℝ} (hz : z ≠ 0) (y : Fin n → ℝ) :
    z^n * cauchyDensity n z y = (∏ i, (1-y i/z)⁻¹) * density n y := by
  have he (i : Fin n) : (1-y i/z)⁻¹ = z / (z-y i) := by
    rw [show 1-y i/z = (z-y i)/z by field_simp, inv_div]
  simp_rw [he]
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,cauchyDensity]
  ring

lemma scaled_cauchyDensity_bound {n : ℕ} {z : ℝ} (hz : 2 ≤ z) {y : Fin n → ℝ}
    (hy : ∀ i, y i ∈ Ioo (0:ℝ) 1) :
    ‖(∏ i, (1-y i/z)⁻¹) * density n y‖ ≤ (2:ℝ)^n * density n y := by
  have hd i : 1/2 ≤ 1-y i/z := by
    have hdiv : y i/z ≤ 1/2 := (div_le_iff₀ (by linarith : 0<z)).mpr (by linarith [(hy i).2])
    linarith
  have hn i : 0 ≤ (1-y i/z)⁻¹ := inv_nonneg.mpr (by linarith [hd i])
  rw [Real.norm_eq_abs,abs_of_nonneg
    (mul_nonneg (Finset.prod_nonneg fun i _ => hn i)
      (density_nonneg_of_nonneg fun i => (hy i).1.le))]
  apply mul_le_mul_of_nonneg_right _ (density_nonneg_of_nonneg fun i => (hy i).1.le)
  calc
    _ ≤ ∏ _ : Fin n, (2:ℝ) := Finset.prod_le_prod₀ (fun i _ => hn i) (fun i _ => by
      have hh := inv_anti₀ (by norm_num : (0:ℝ)<1/2) (hd i)
      norm_num at hh
      exact hh)
    _ = _ := by simp

lemma cauchyDensity_limit (n : ℕ) :
    Tendsto (fun z : ℝ => z^n * ∫ y, cauchyDensity n z y ∂unitCubeMeasure n)
      atTop (𝓝 (∫ y, density n y ∂unitCubeMeasure n)) := by
  have hi : Tendsto (fun z : ℝ => ∫ y, (∏ i, (1-y i/z)⁻¹) * density n y ∂unitCubeMeasure n)
      atTop (𝓝 (∫ y, density n y ∂unitCubeMeasure n)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun y => (2:ℝ)^n * density n y)
    · exact Filter.Eventually.of_forall fun z => ((by fun_prop : Measurable
        (fun y : Fin n → ℝ => (∏ i, (1-y i/z)⁻¹))).mul (measurable_density n)).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop (2:ℝ)] with z hz
      filter_upwards [ae_unitCube n] with y hy
      exact scaled_cauchyDensity_bound hz hy
    · exact (integrable_density_unitCube n).const_mul _
    · exact Filter.Eventually.of_forall fun y => by
        have ht (i : Fin n) : Tendsto (fun z : ℝ => (1-y i/z)⁻¹) atTop (𝓝 1) := by
          have hh : Tendsto (fun z : ℝ => 1-y i/z) atTop (𝓝 1) := by
            simpa only [mul_zero,sub_zero,div_eq_mul_inv] using
              ((tendsto_inv_atTop_zero : Tendsto (fun z : ℝ => z⁻¹) atTop (𝓝 0)).const_mul (y i)).const_sub 1
          simpa only [inv_one] using hh.inv₀ (by norm_num : (1:ℝ)≠0)
        simpa using (tendsto_finsetProd Finset.univ (fun i _ => ht i)).mul_const (density n y)
  apply hi.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with z hz
  rw [←integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => (scaled_cauchyDensity n hz.ne' y).symm

end
end CriticalStrip

end OAI
