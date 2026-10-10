import OAI.Dynamics.TriangleBilliards.FlightUniqueness

namespace OAI

universe uIota

open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
namespace TriangularBilliards

/-! Finite unfolding and the actual null vertex-aiming exception. -/

/-- Oriented angular momentum about the origin against a fixed velocity. -/
def crossMap (v : ℂ) : ℂ →ₗ[ℝ] ℝ where
  toFun x := (x * star v).im
  map_add' x y := by simp only [add_mul, Complex.add_im]
  map_smul' r x := by
    rw [smul_mul_assoc]
    exact Complex.imLm.map_smul r (x * star v)

lemma crossMap_unit (v : Circle) : crossMap v (Complex.I * (v : ℂ)) = 1 := by
  change (Complex.I * (v : ℂ) * star (v : ℂ)).im = 1
  rw [mul_assoc, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    Circle.norm_coe]
  norm_num

lemma crossMap_ker_ne_top (v : Circle) : LinearMap.ker (crossMap v) ≠ ⊤ := by
  intro h
  have hx : Complex.I * (v : ℂ) ∈ LinearMap.ker (crossMap v) := by rw [h]; trivial
  have hh := LinearMap.mem_ker.mp hx
  rw [crossMap_unit] at hh
  norm_num at hh

/-- States whose straight starting line passes through p, in either direction. -/
def aimingAt (p : ℂ) : Set Phase := {z | crossMap z.2 (z.1 - p) = 0}

lemma isClosed_aimingAt (p : ℂ) : IsClosed (aimingAt p) := by
  change IsClosed {z : Phase | ((z.1 - p) * star (z.2 : ℂ)).im = 0}
  apply isClosed_eq _ continuous_const
  fun_prop

lemma volume_aimingAt_slice (p : ℂ) (v : Circle) :
    volume ((fun x : ℂ => (x, v)) ⁻¹' aimingAt p) = 0 := by
  have hs : ((fun x : ℂ => (x, v)) ⁻¹' aimingAt p) =
      (fun x : ℂ => x + -p) ⁻¹' (LinearMap.ker (crossMap v) : Set ℂ) := by
    ext x
    change crossMap (v : ℂ) (x - p) = 0 ↔ crossMap (v : ℂ) (x + -p) = 0
    rw [sub_eq_add_neg]
  rw [hs, measure_preimage_add_right]
  exact Measure.addHaar_submodule volume _ (crossMap_ker_ne_top v)

lemma phaseMeasure_aimingAt (Q : Triangle) (p : ℂ) : phaseMeasure Q (aimingAt p) = 0 := by
  rw [phaseMeasure, Measure.prod_apply_symm (isClosed_aimingAt p).measurableSet]
  have hz (v : Circle) : ((volume Q.table)⁻¹ • volume.restrict Q.table)
      ((fun x : ℂ => (x, v)) ⁻¹' aimingAt p) = 0 := by
    rw [Measure.smul_apply]
    have hzero : (volume.restrict Q.table) ((fun x : ℂ => (x, v)) ⁻¹' aimingAt p) = 0 := by
      apply le_antisymm _ zero_le
      exact (Measure.le_iff'.mp Measure.restrict_le_self _).trans_eq (volume_aimingAt_slice p v)
    rw [hzero, smul_zero]
  simp only [hz, lintegral_zero]

/-- Reflection of a point in the supporting line of a side. -/
def wallReflection (Q : Triangle) (i : Fin 3) (x : ℂ) : ℂ :=
  Q.vertex i + reflect (Q.tangent i) (x - Q.vertex i)

/-- Finite unfolding places every vertex in the countable reflection orbit. -/
def unfoldedVertex (Q : Triangle) (w : List (Fin 3)) (i : Fin 3) : ℂ :=
  w.foldr (wallReflection Q) (Q.vertex i)

def vertexExceptional (Q : Triangle) : Set Phase :=
  ⋃ w : List (Fin 3), ⋃ i : Fin 3, aimingAt (unfoldedVertex Q w i)

lemma measurableSet_vertexExceptional (Q : Triangle) : MeasurableSet (vertexExceptional Q) := by
  exact MeasurableSet.iUnion fun w => MeasurableSet.iUnion fun i =>
    (isClosed_aimingAt (unfoldedVertex Q w i)).measurableSet

/-- A concrete, unconditional null exceptional set for all finite
unfolding vertex hits, in both time directions and for this exact measure. -/
lemma phaseMeasure_vertexExceptional (Q : Triangle) :
    phaseMeasure Q (vertexExceptional Q) = 0 := by
  apply measure_iUnion_null
  intro w
  apply measure_iUnion_null
  intro i
  exact phaseMeasure_aimingAt Q (unfoldedVertex Q w i)

namespace Triangle

def slope (Q : Triangle) (i : Fin 3) (v : ℂ) : ℝ := (Q.basis.coord i).linear v

lemma coord_shift (Q : Triangle) (i : Fin 3) (x v : ℂ) (t : ℝ) :
    Q.basis.coord i (x + t • v) = Q.basis.coord i x + t * Q.slope i v := by
  have h := (Q.basis.coord i).map_vadd x (t • v)
  simpa only [vadd_eq_add, map_smul, smul_eq_mul, add_comm, slope] using h

lemma sum_slope (Q : Triangle) (v : ℂ) : ∑ i, Q.slope i v = 0 := by
  have h := Q.basis.sum_coord_apply_eq_one v
  have h0 := Q.basis.sum_coord_apply_eq_one (0 : ℂ)
  have he (i : Fin 3) : Q.basis.coord i v = Q.slope i v + Q.basis.coord i 0 := by
    simpa only [vadd_eq_add, add_zero, slope] using (Q.basis.coord i).map_vadd 0 v
  simp only [he, Finset.sum_add_distrib] at h
  linarith

lemma slope_joint_injective (Q : Triangle) {v : ℂ}
    (hv : ∀ i, Q.slope i v = 0) : v = 0 := by
  apply Q.basis.ext_elem
  intro i
  have h := Q.coord_shift i 0 v 1
  simpa only [one_smul, zero_add, hv i, mul_zero, add_zero] using h

lemma exists_slope_neg (Q : Triangle) {v : ℂ} (hv : v ≠ 0) :
    ∃ i, Q.slope i v < 0 := by
  by_contra hn
  push Not at hn
  have hs := (Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ Finset.univ) => hn i)).mp
    (Q.sum_slope v)
  exact hv (Q.slope_joint_injective fun i => hs i (Finset.mem_univ i))

end Triangle

/-- Earliest exit for finitely many affine half-planes, including a starting
point on an open side with an inward velocity. This is finite real geometry,
not an assumed exit-time oracle. -/
lemma affine_first_exit {ι : Type uIota} [Fintype ι] (a b : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hin : ∀ i, a i = 0 → 0 < b i)
    (hb : ∃ i, b i < 0) :
    ∃ T : ℝ, 0 < T ∧ (∀ t, 0 < t → t < T → ∀ i, 0 < a i + t * b i) ∧
      (∀ i, 0 ≤ a i + T * b i) ∧ (∃ i, a i + T * b i = 0 ∧ b i < 0) := by
  classical
  let S := Finset.univ.filter fun i => b i < 0
  have hS : S.Nonempty := by
    obtain ⟨i, hi⟩ := hb
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  obtain ⟨i, hi, hmin⟩ := S.exists_min_image (fun i => a i / (-b i)) hS
  have hbi : b i < 0 := (Finset.mem_filter.mp hi).2
  have hai : 0 < a i := by
    by_contra h
    have hz : a i = 0 := le_antisymm (not_lt.mp h) (ha i)
    linarith [hin i hz]
  have hT : 0 < a i / (-b i) := div_pos hai (neg_pos.mpr hbi)
  refine ⟨a i / (-b i), hT, ?_, ?_, i, ?_, hbi⟩
  · intro t ht htT j
    by_cases hbj : b j < 0
    · have htj : t < a j / (-b j) := lt_of_lt_of_le htT
        (hmin j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hbj⟩))
      have hmul := (lt_div_iff₀ (neg_pos.mpr hbj)).mp htj
      nlinarith
    · have hbj' : 0 ≤ b j := le_of_not_gt hbj
      rcases lt_or_eq_of_le (ha j) with haj | haj
      · exact add_pos_of_pos_of_nonneg haj (mul_nonneg ht.le hbj')
      · have hp := hin j haj.symm
        simpa only [← haj, zero_add] using mul_pos ht hp
  · intro j
    by_cases hbj : b j < 0
    · have htj := hmin j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hbj⟩)
      have hmul := (le_div_iff₀ (neg_pos.mpr hbj)).mp htj
      nlinarith
    · exact add_nonneg (ha j) (mul_nonneg hT.le (le_of_not_gt hbj))
  · field_simp [ne_of_lt hbi]
    ring

namespace Triangle

/-- An admissible velocity is strictly inward at every active half-plane. -/
def Inward (Q : Triangle) (x v : ℂ) : Prop :=
  (∀ i, 0 ≤ Q.basis.coord i x) ∧
  (∀ i, Q.basis.coord i x = 0 → 0 < Q.slope i v)

lemma inward_of_table (Q : Triangle) {x v : ℂ} (hx : x ∈ Q.table) : Q.Inward x v := by
  have hp := (Q.table_iff_coords x).mp hx
  exact ⟨fun i => (hp i).le, fun i hi => False.elim ((ne_of_gt (hp i)) hi)⟩

lemma exists_exit (Q : Triangle) {x v : ℂ} (hv : v ≠ 0) (hx : Q.Inward x v) :
    ∃ T : ℝ, 0 < T ∧ (∀ t, 0 < t → t < T → x + t • v ∈ Q.table) ∧
      (∀ i, 0 ≤ Q.basis.coord i (x + T • v)) ∧
      (∃ i, Q.basis.coord i (x + T • v) = 0 ∧ Q.slope i v < 0) := by
  obtain ⟨T, hT, hint, hclosed, i, hi, hs⟩ := affine_first_exit
    (fun i => Q.basis.coord i x) (fun i => Q.slope i v) hx.1 hx.2 (Q.exists_slope_neg hv)
  refine ⟨T, hT, ?_, ?_, i, ?_, hs⟩
  · intro t ht htT
    rw [Q.table_iff_coords]
    intro j
    rw [Q.coord_shift]
    exact hint t ht htT j
  · intro j
    rw [Q.coord_shift]
    exact hclosed j
  · rw [Q.coord_shift]
    exact hi

end Triangle

lemma crossMap_self (v : ℂ) : crossMap v v = 0 := by
  change (v * star v).im = 0
  rw [Complex.star_def, Complex.mul_conj]
  exact Complex.ofReal_im _

lemma crossMap_reflect {e : ℂ} (he : e ≠ 0) (v x : ℂ) :
    crossMap (reflect e v) (reflect e x) = -crossMap v x := by
  have he' : star e ≠ 0 := star_ne_zero.mpr he
  have h : reflect e x * star (reflect e v) = star (x * star v) := by
    simp only [reflect, star_mul', star_div₀, star_star]
    field_simp
  change (reflect e x * star (reflect e v)).im = -(x * star v).im
  rw [h, Complex.star_def, Complex.conj_im]

lemma aimingAt_flight_iff (p x : ℂ) (v : Circle) (t : ℝ) :
    (x + t • (v : ℂ), v) ∈ aimingAt p ↔ (x, v) ∈ aimingAt p := by
  change crossMap (v : ℂ) (x + t • (v : ℂ) - p) = 0 ↔ crossMap (v : ℂ) (x - p) = 0
  rw [show x + t • (v : ℂ) - p = (x - p) + t • (v : ℂ) by abel,
    map_add, map_smul, crossMap_self, smul_zero, add_zero]

lemma vertexExceptional_flight_iff (Q : Triangle) (x : ℂ) (v : Circle) (t : ℝ) :
    (x + t • (v : ℂ), v) ∈ vertexExceptional Q ↔ (x, v) ∈ vertexExceptional Q := by
  simp only [vertexExceptional, mem_iUnion, aimingAt_flight_iff]

/-- Unit outgoing velocity, with exactly the specular law. -/
def reflectedDirection (Q : Triangle) (i : Fin 3) (v : Circle) : Circle :=
  ⟨reflect (Q.tangent i) v, mem_sphere_zero_iff_norm.mpr
    (by rw [reflect_norm (Q.tangent_ne_zero i), Circle.norm_coe])⟩

lemma wallReflection_involutive (Q : Triangle) (i : Fin 3) (x : ℂ) :
    wallReflection Q i (wallReflection Q i x) = x := by
  simp only [wallReflection, add_sub_cancel_left, reflect_involutive (Q.tangent_ne_zero i)]
  abel

lemma wallReflection_sub (Q : Triangle) (i : Fin 3) (x p : ℂ) :
    wallReflection Q i x - wallReflection Q i p = reflect (Q.tangent i) (x - p) := by
  change Q.vertex i + (reflectIsometry (Q.tangent i) (Q.tangent_ne_zero i)) (x - Q.vertex i) -
    (Q.vertex i + (reflectIsometry (Q.tangent i) (Q.tangent_ne_zero i)) (p - Q.vertex i)) = _
  rw [add_sub_add_left_eq_sub, ← map_sub, sub_sub_sub_cancel_right]
  rfl

lemma wallReflection_fixed_side (Q : Triangle) {i : Fin 3} {x : ℂ}
    (hx : x ∈ Q.side i) : wallReflection Q i x = x := by
  rw [Triangle.side, openSegment_eq_image_lineMap] at hx
  obtain ⟨t, _, rfl⟩ := hx
  rw [AffineMap.lineMap_apply_module']
  change Q.vertex i + reflect (Q.tangent i) (t • Q.tangent i + Q.vertex i - Q.vertex i) =
    t • Q.tangent i + Q.vertex i
  rw [add_sub_cancel_right, reflect_real_smul, reflect_tangent (Q.tangent_ne_zero i)]
  exact add_comm _ _

lemma aimingAt_reflection_iff (Q : Triangle) (i : Fin 3) (x p : ℂ) (v : Circle) :
    (wallReflection Q i x, reflectedDirection Q i v) ∈ aimingAt (wallReflection Q i p) ↔
      (x, v) ∈ aimingAt p := by
  change crossMap (reflect (Q.tangent i) v)
    (wallReflection Q i x - wallReflection Q i p) = 0 ↔ crossMap (v : ℂ) (x - p) = 0
  rw [wallReflection_sub, crossMap_reflect (Q.tangent_ne_zero i), neg_eq_zero]

lemma vertexExceptional_reflection_iff (Q : Triangle) (i : Fin 3) (x : ℂ) (v : Circle) :
    (wallReflection Q i x, reflectedDirection Q i v) ∈ vertexExceptional Q ↔
      (x, v) ∈ vertexExceptional Q := by
  constructor
  · intro h
    simp only [vertexExceptional, mem_iUnion] at h ⊢
    obtain ⟨w, k, hk⟩ := h
    refine ⟨i :: w, k, ?_⟩
    have hpi : wallReflection Q i (unfoldedVertex Q (i :: w) k) = unfoldedVertex Q w k := by
      exact wallReflection_involutive Q i _
    apply (aimingAt_reflection_iff Q i x (unfoldedVertex Q (i :: w) k) v).mp
    rwa [hpi]
  · intro h
    simp only [vertexExceptional, mem_iUnion] at h ⊢
    obtain ⟨w, k, hk⟩ := h
    exact ⟨i :: w, k, (aimingAt_reflection_iff Q i x (unfoldedVertex Q w k) v).mpr hk⟩

lemma not_vertex_of_not_exceptional (Q : Triangle) {x : ℂ} {v : Circle}
    (hx : (x, v) ∉ vertexExceptional Q) : ∀ i, x ≠ Q.vertex i := by
  intro i he
  apply hx
  simp only [vertexExceptional, mem_iUnion]
  refine ⟨[], i, ?_⟩
  change crossMap (v : ℂ) (x - Q.vertex i) = 0
  rw [he, sub_self, map_zero]

namespace Triangle

lemma sum_coord_cyclic (Q : Triangle) (x : ℂ) (i : Fin 3) :
    Q.basis.coord i x + Q.basis.coord (i + 1) x + Q.basis.coord (i + 2) x = 1 := by
  have h := Q.basis.sum_coord_apply_eq_one x
  simp only [Fin.sum_univ_three] at h
  fin_cases i
  · exact h
  · change Q.basis.coord 1 x + Q.basis.coord 2 x + Q.basis.coord 0 x = 1
    linarith
  · change Q.basis.coord 2 x + Q.basis.coord 0 x + Q.basis.coord 1 x = 1
    linarith

lemma side_of_coords (Q : Triangle) {x : ℂ} (i : Fin 3)
    (h0 : 0 < Q.basis.coord i x) (h1 : 0 < Q.basis.coord (i + 1) x)
    (h2 : Q.basis.coord (i + 2) x = 0) : x ∈ Q.side i := by
  have hs := Q.sum_coord_cyclic x i
  have ht : Q.basis.coord (i + 1) x < 1 := by linarith
  rw [side, openSegment_eq_image_lineMap]
  refine ⟨Q.basis.coord (i + 1) x, ⟨h1, ht⟩, ?_⟩
  apply Q.basis.ext_elem
  intro k
  change Q.basis.coord k (AffineMap.lineMap (Q.basis i) (Q.basis (i + 1)) _) = _
  rw [AffineMap.apply_lineMap, Q.basis.coord_apply, Q.basis.coord_apply,
    AffineMap.lineMap_apply_module]
  have h01 : i ≠ i + 1 := by fin_cases i <;> decide
  have h20 : i + 2 ≠ i := by fin_cases i <;> decide
  have h21 : i + 2 ≠ i + 1 := by fin_cases i <;> decide
  have hk : k = i ∨ k = i + 1 ∨ k = i + 2 := by fin_cases i <;> fin_cases k <;> decide
  rcases hk with rfl | rfl | rfl
  · simp only [ite_true, ite_eq_right h01, smul_eq_mul, mul_one, mul_zero, add_zero]
    linarith
  · simp only [ite_eq_right h01.symm, ite_true, smul_eq_mul, mul_zero, zero_add, mul_one]
  · simp only [ite_eq_right h20, ite_eq_right h21, smul_eq_mul, mul_zero, add_zero, h2]

lemma eq_vertex_of_two_coords_zero (Q : Triangle) {x : ℂ} (i : Fin 3)
    (h1 : Q.basis.coord (i + 1) x = 0) (h2 : Q.basis.coord (i + 2) x = 0) :
    x = Q.vertex i := by
  have hs := Q.sum_coord_cyclic x i
  apply Q.basis.ext_elem
  intro k
  change Q.basis.coord k x = Q.basis.coord k (Q.basis i)
  rw [Q.basis.coord_apply]
  have h01 : i ≠ i + 1 := by fin_cases i <;> decide
  have h20 : i + 2 ≠ i := by fin_cases i <;> decide
  have hk : k = i ∨ k = i + 1 ∨ k = i + 2 := by fin_cases i <;> fin_cases k <;> decide
  rcases hk with rfl | rfl | rfl
  · simp only [ite_true]
    linarith
  · simpa only [ite_eq_right h01.symm] using h1
  · simpa only [ite_eq_right h20] using h2

lemma boundary_open_side (Q : Triangle) {x : ℂ}
    (hx : ∀ i, 0 ≤ Q.basis.coord i x) (hz : ∃ i, Q.basis.coord i x = 0)
    (hv : ∀ i, x ≠ Q.vertex i) : ∃ i, x ∈ Q.side i := by
  obtain ⟨i, hi⟩ := hz
  have h1 : 0 < Q.basis.coord (i + 1) x := by
    apply lt_of_le_of_ne (hx (i + 1))
    intro he
    apply hv (i + 2)
    apply Q.eq_vertex_of_two_coords_zero
    · convert hi using 1; congr 2; fin_cases i <;> rfl
    · convert he.symm using 1; congr 2; fin_cases i <;> rfl
  have h2 : 0 < Q.basis.coord (i + 2) x := by
    apply lt_of_le_of_ne (hx (i + 2))
    intro he
    apply hv (i + 1)
    apply Q.eq_vertex_of_two_coords_zero
    · convert he.symm using 1; congr 2; fin_cases i <;> rfl
    · convert hi using 1; congr 2; fin_cases i <;> rfl
  refine ⟨i + 1, Q.side_of_coords (i + 1) h1 ?_ ?_⟩
  · convert h2 using 1; congr 2; fin_cases i <;> rfl
  · convert hi using 1; congr 2; fin_cases i <;> rfl

end Triangle

lemma complex_decompose_tangent {e : ℂ} (he : e ≠ 0) (v : ℂ) :
    ∃ a b : ℝ, v = a • e + b • (Complex.I * e) := by
  refine ⟨(v / e).re, (v / e).im, ?_⟩
  rw [Complex.real_smul, Complex.real_smul]
  calc
    v = (v / e) * e := (div_mul_cancel₀ v he).symm
    _ = ((v / e).re + (v / e).im * Complex.I) * e := by rw [Complex.re_add_im]
    _ = _ := by ring

lemma linear_reflect_neg {e : ℂ} (he : e ≠ 0) (l : ℂ →ₗ[ℝ] ℝ) (hl : l e = 0) (v : ℂ) :
    l (reflect e v) = -l v := by
  obtain ⟨a, b, rfl⟩ := complex_decompose_tangent he v
  rw [reflect_add, reflect_real_smul, reflect_real_smul, reflect_tangent he, reflect_normal he]
  simp only [map_add, map_smul, smul_eq_mul, hl, mul_zero, zero_add, map_neg]
  ring

namespace Triangle

lemma slope_tangent_zero (Q : Triangle) (i : Fin 3) : Q.slope (i + 2) (Q.tangent i) = 0 := by
  have h20 : i + 2 ≠ i := by fin_cases i <;> decide
  have h21 : i + 2 ≠ i + 1 := by fin_cases i <;> decide
  have h := (Q.basis.coord (i + 2)).linearMap_vsub (Q.basis (i + 1)) (Q.basis i)
  simp only [vsub_eq_sub, Q.basis.coord_apply, ite_eq_right h20, ite_eq_right h21, sub_zero] at h
  exact h

lemma slope_reflect (Q : Triangle) (i : Fin 3) (v : ℂ) :
    Q.slope (i + 2) (reflect (Q.tangent i) v) = -Q.slope (i + 2) v :=
  linear_reflect_neg (Q.tangent_ne_zero i) (Q.basis.coord (i + 2)).linear
    (Q.slope_tangent_zero i) v

lemma inward_after_reflection (Q : Triangle) {x v : ℂ} {i : Fin 3}
    (hside : x ∈ Q.side i) (hclosed : ∀ j, 0 ≤ Q.basis.coord j x)
    (hneg : Q.slope (i + 2) v < 0) : Q.Inward x (reflect (Q.tangent i) v) := by
  refine ⟨hclosed, ?_⟩
  intro j hj
  have he := (Q.side_coord_zero_iff hside j).mp hj
  rw [he, Q.slope_reflect]
  exact neg_pos.mpr hneg

end Triangle

/-- A finite collision datum whose existence is proved from the actual
half-plane geometry and the countable unfolded-vertex exception. -/
structure NextCollision (Q : Triangle) (x : ℂ) (v : Circle) where
  delay : ℝ
  wall : Fin 3
  positive : 0 < delay
  on_side : x + delay • (v : ℂ) ∈ Q.side wall
  inside : ∀ t : ℝ, 0 < t → t < delay → x + t • (v : ℂ) ∈ Q.table
  inward : Q.Inward (x + delay • (v : ℂ)) (reflectedDirection Q wall v)
  regular : (x + delay • (v : ℂ), reflectedDirection Q wall v) ∉ vertexExceptional Q

lemma exists_next_collision (Q : Triangle) {x : ℂ} {v : Circle}
    (hx : Q.Inward x v) (hreg : (x, v) ∉ vertexExceptional Q) :
    Nonempty (NextCollision Q x v) := by
  obtain ⟨T, hT, hint, hclosed, k, hk, hneg⟩ := Q.exists_exit (Circle.coe_ne_zero v) hx
  have hreg' : (x + T • (v : ℂ), v) ∉ vertexExceptional Q := by
    rwa [vertexExceptional_flight_iff]
  obtain ⟨i, hi⟩ := Q.boundary_open_side hclosed ⟨k, hk⟩
    (not_vertex_of_not_exceptional Q hreg')
  have hki := (Q.side_coord_zero_iff hi k).mp hk
  refine ⟨⟨T, i, hT, hi, hint, ?_, ?_⟩⟩
  · exact Q.inward_after_reflection hi hclosed (hki ▸ hneg)
  · have hiff := vertexExceptional_reflection_iff Q i (x + T • (v : ℂ)) v
    rw [wallReflection_fixed_side Q hi] at hiff
    exact fun h => hreg' (hiff.mp h)

/-- Actual states on a regular recursively extendible ray. Boundary initial
states are allowed only with strict inward velocity. -/
structure Admissible (Q : Triangle) where
  pos : ℂ
  vel : Circle
  inward : Q.Inward pos vel
  regular : (pos, vel) ∉ vertexExceptional Q

namespace Admissible

noncomputable def collision {Q : Triangle} (z : Admissible Q) : NextCollision Q z.pos z.vel :=
  Classical.choice (exists_next_collision Q z.inward z.regular)

noncomputable def next {Q : Triangle} (z : Admissible Q) : Admissible Q where
  pos := z.pos + z.collision.delay • (z.vel : ℂ)
  vel := reflectedDirection Q z.collision.wall z.vel
  inward := z.collision.inward
  regular := z.collision.regular

noncomputable def iterate {Q : Triangle} (z : Admissible Q) : ℕ → Admissible Q
  | 0 => z
  | n + 1 => (z.iterate n).next

noncomputable def time {Q : Triangle} (z : Admissible Q) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, (z.iterate k).collision.delay

lemma time_zero {Q : Triangle} (z : Admissible Q) : z.time 0 = 0 := by
  simp [time]

lemma time_succ {Q : Triangle} (z : Admissible Q) (n : ℕ) :
    z.time (n + 1) = z.time n + (z.iterate n).collision.delay := by
  exact Finset.sum_range_succ _ n

lemma time_strictMono {Q : Triangle} (z : Admissible Q) : StrictMono z.time := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [z.time_succ]
  exact lt_add_of_pos_right _ (z.iterate n).collision.positive

lemma iterate_flight {Q : Triangle} (z : Admissible Q) (n : ℕ) :
    (z.iterate (n + 1)).pos = (z.iterate n).pos +
      (z.time (n + 1) - z.time n) • ((z.iterate n).vel : ℂ) := by
  rw [z.time_succ, add_sub_cancel_left]
  rfl

lemma iterate_inside {Q : Triangle} (z : Admissible Q) (n : ℕ) {t : ℝ}
    (h0 : z.time n < t) (h1 : t < z.time (n + 1)) :
    (z.iterate n).pos + (t - z.time n) • ((z.iterate n).vel : ℂ) ∈ Q.table := by
  apply (z.iterate n).collision.inside (t - z.time n) (sub_pos.mpr h0)
  rw [z.time_succ] at h1
  linarith

lemma iterate_on_side {Q : Triangle} (z : Admissible Q) (n : ℕ) :
    (z.iterate (n + 1)).pos ∈ Q.side (z.iterate n).collision.wall :=
  (z.iterate n).collision.on_side

lemma dist_iterate_succ {Q : Triangle} (z : Admissible Q) (n : ℕ) :
    dist (z.iterate n).pos (z.iterate (n + 1)).pos = z.time (n + 1) - z.time n := by
  rw [dist_comm, dist_eq_norm, z.iterate_flight, add_sub_cancel_left, norm_smul,
    Circle.norm_coe, mul_one, Real.norm_eq_abs, abs_of_pos]
  exact sub_pos.mpr (z.time_strictMono (Nat.lt_succ_self n))

lemma dist_iterate_le_time {Q : Triangle} (z : Admissible Q) {m n : ℕ} (hmn : m ≤ n) :
    dist (z.iterate m).pos (z.iterate n).pos ≤ z.time n - z.time m := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    calc
      dist (z.iterate m).pos (z.iterate (n + 1)).pos ≤
          dist (z.iterate m).pos (z.iterate n).pos +
          dist (z.iterate n).pos (z.iterate (n + 1)).pos := dist_triangle _ _ _
      _ ≤ (z.time n - z.time m) + (z.time (n + 1) - z.time n) :=
        add_le_add ih (z.dist_iterate_succ n).le
      _ = z.time (n + 1) - z.time m := by ring

end Admissible

end TriangularBilliards
end

end OAI
