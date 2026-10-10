import OAI.Probability.RadialTransition.RangeBounds

namespace OAI

universe uI

noncomputable section


open Function MeasureTheory Set Filter

open scoped BigOperators ENNReal NNReal ContDiff

namespace RadialTransition

lemma macroKernelError_row {I : Type uI} [Fintype I] (e : I → Cell) (he : Function.Injective e)
    {q : ℕ} (hq : 0 < q) {R : ℝ} (hR : (q:ℝ)/4 ≤ R) (i : Cell) :
    ((q:ℝ)/4)^3*∑ j, macroKernelError q R i (e j) ≤ 5000*(bumpLip:ℝ)*q/R := by
  classical
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hR
  let T := R/(q:ℝ)+1
  have hT : 1 ≤ T := by dsimp [T]; linarith [div_nonneg hR0.le hq0.le]
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hh := cellMajorant_row e he hT (show 0 ≤ T^3*((bumpLip:ℝ)/R^4*q) by positivity) i
  have heq (j : I) : cellMajorant T (T^3*((bumpLip:ℝ)/R^4*q)) i (e j) = macroKernelError q R i (e j) := by
    unfold cellMajorant macroKernelError
    split_ifs <;> simp_all [T, hT0.ne']
  simp_rw [heq] at hh
  have hTq : (q:ℝ)*T ≤ 5*R := by dsimp [T]; field_simp; nlinarith
  have hc : ((q:ℝ)*T)^3 ≤ (5*R)^3 := pow_le_pow_left₀ (by positivity) hTq 3
  calc
    _ ≤ ((q:ℝ)/4)^3*(2197*(T^3*((bumpLip:ℝ)/R^4*q))) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = (2197/64:ℝ)*((q:ℝ)*T)^3*((bumpLip:ℝ)*q/R^4) := by ring
    _ ≤ (2197/64:ℝ)*(5*R)^3*((bumpLip:ℝ)*q/R^4) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by norm_num)) (by positivity)
    _ ≤ _ := by field_simp; nlinarith [show (0:ℝ) ≤ bumpLip from NNReal.coe_nonneg _]

lemma macroRegions_disjoint (q m : ℕ) : Pairwise (Function.onFun Disjoint (fun i : GridIndex m => macroRegion q (gridEmbed i))) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact hij (gridEmbed_injective m (hx.symm.trans hy))

lemma macroRegions_integral {q m : ℕ} (hq : 0 < q) {f : Position → ℝ} (hf : Integrable f) :
    ∫ x in halfCube ((m:ℝ)*q/4), f x =
      ∑ j : GridIndex m, ∫ x in macroRegion q (gridEmbed j), f x := by
  rw [← halfCube_macro_union hq]
  exact integral_iUnion_fintype (fun _ => measurableSet_macroRegion _ _) (macroRegions_disjoint _ _) (fun _ => hf.integrableOn)

lemma macroKernel_center_error {q : ℕ} (hq : 0 < q) {R : ℝ} (hR : 0 < R)
    (i j : Cell) {y : Position} (hy : y ∈ macroRegion q j) :
    |scaledBump R (macroOrigin q i-y)-macroKernel q R i j| ≤ macroKernelError q R i j := by
  by_cases h : CellReach (R/q+1) i j
  · rw [macroKernelError, ite_eq_left h]
    exact (scaledBump_oscillation hR _ _).trans
      (mul_le_mul_of_nonneg_left (macro_difference_dist hq (macroOrigin_mem hq i) hy) (by positivity))
  · have hd : R < dist (macroOrigin q i) y := lt_of_not_ge (fun hh => h (macroReach_of_dist hq (macroOrigin_mem hq i) hy hh))
    have hd' : R < dist (macroOrigin q i) (macroOrigin q j) :=
      lt_of_not_ge (fun hh => h (macroReach_of_dist hq (macroOrigin_mem hq i) (macroOrigin_mem hq j) hh))
    rw [macroKernel, scaledBump_zero hR (by simpa only [dist_eq_norm] using hd.le),
      scaledBump_zero hR (by simpa only [dist_eq_norm] using hd'.le), sub_self, abs_zero,
      macroKernelError, ite_eq_right h]

lemma macroKernel_upper_integral {q : ℕ} (hq : 0 < q) {R : ℝ} (hR : 0 < R) (i j : Cell) :
    ((q:ℝ)/4)^3*(macroKernelUpper q R i j-2*macroKernelError q R i j) ≤
      ∫ y in macroRegion q j, scaledBump R (macroOrigin q i-y) := by
  have hh := setIntegral_mono_on
    (integrableOn_const (by rw [volume_macroRegion hq]; finiteness) :
      IntegrableOn (fun _ : Position => macroKernelUpper q R i j-2*macroKernelError q R i j) (macroRegion q j))
    ((integrable_scaledBump hR).comp_sub_left (macroOrigin q i)).integrableOn
    (measurableSet_macroRegion _ _) (fun y hy => ?_)
  · simpa only [setIntegral_const, Measure.real, volume_macroRegion hq,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity : 0 ≤ (q:ℝ)/4), smul_eq_mul] using hh
  · have hb := (abs_le.mp (macroKernel_center_error hq hR i j hy)).1
    unfold macroKernelUpper
    linarith

lemma macroKernel_lower_integral {q : ℕ} (hq : 0 < q) {R : ℝ} (hR : 0 < R) (i j : Cell) :
    (∫ y in macroRegion q j, scaledBump R (macroOrigin q i-y)) ≤
      ((q:ℝ)/4)^3*(macroKernelLower q R i j+2*macroKernelError q R i j) := by
  have hh := setIntegral_mono_on ((integrable_scaledBump hR).comp_sub_left (macroOrigin q i)).integrableOn
    (integrableOn_const (by rw [volume_macroRegion hq]; finiteness) :
      IntegrableOn (fun _ : Position => macroKernelLower q R i j+2*macroKernelError q R i j) (macroRegion q j))
    (measurableSet_macroRegion _ _) (fun y hy => ?_)
  · simpa only [setIntegral_const, Measure.real, volume_macroRegion hq,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity : 0 ≤ (q:ℝ)/4), smul_eq_mul] using hh
  · have hb := (abs_le.mp (macroKernel_center_error hq hR i j hy)).2
    have hm := le_max_right 0 (macroKernel q R i j-macroKernelError q R i j)
    change _ ≤ macroKernelLower q R i j at hm
    linarith

lemma macroKernelUpper_row {q m : ℕ} (hq : 0 < q) {R : ℝ} (hR : (q:ℝ)/4 ≤ R) (i : Cell) :
    ((q:ℝ)/4)^3*∑ j : GridIndex m, macroKernelUpper q R i (gridEmbed j) ≤
      1+10000*(bumpLip:ℝ)*q/R := by
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hR
  have hi := (integrable_scaledBump hR0).comp_sub_left (macroOrigin q i)
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun (j : GridIndex m) _ => macroKernel_upper_integral hq hR0 i (gridEmbed j))
  rw [← macroRegions_integral hq hi] at hh
  have hle : (∫ y in halfCube ((m:ℝ)*q/4), scaledBump R (macroOrigin q i-y)) ≤ 1 := by
    have ht := setIntegral_le_integral hi (Eventually.of_forall (fun y => scaledBump_nonneg hR0 _)) (s := halfCube ((m:ℝ)*q/4))
    simpa only [integral_sub_left_eq_self, integral_scaledBump hR0] using ht
  have hb := macroKernelError_row (@gridEmbed m) (gridEmbed_injective m) hq hR i
  simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum] at hh
  linear_combination hh + hle + 2*hb

lemma macroKernelLower_row_all {q m : ℕ} (hq : 0 < q) {R : ℝ} (hR : (q:ℝ)/4 ≤ R) (i : Cell)
    (hs : ∀ y ∉ halfCube ((m:ℝ)*q/4), scaledBump R (macroOrigin q i-y) = 0) :
    1-10000*(bumpLip:ℝ)*q/R ≤
      ((q:ℝ)/4)^3*∑ j : GridIndex m, macroKernelLower q R i (gridEmbed j) := by
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hR
  have hi := (integrable_scaledBump hR0).comp_sub_left (macroOrigin q i)
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun (j : GridIndex m) _ => macroKernel_lower_integral hq hR0 i (gridEmbed j))
  rw [← macroRegions_integral hq hi, setIntegral_eq_integral_of_forall_compl_eq_zero hs,
    integral_sub_left_eq_self, integral_scaledBump hR0] at hh
  have hb := macroKernelError_row (@gridEmbed m) (gridEmbed_injective m) hq hR i
  simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum] at hh
  linear_combination hh + 2*hb

end RadialTransition

end

end OAI
