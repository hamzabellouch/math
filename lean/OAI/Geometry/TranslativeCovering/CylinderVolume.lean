import OAI.Geometry.TranslativeCovering.ResidualCaps

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CylinderVolume
open Set MeasureTheory Metric Finset ConeStretch
open scoped ENNReal
noncomputable def scale {n : ℕ} (i : Fin n) (a b : ℝ) : Space n →ₗ[ℝ] Space n :=
  Matrix.toEuclideanLin (Matrix.diagonal (fun j => if j = i then a else b))
lemma scale_apply {n : ℕ} (i : Fin n) (a b : ℝ) (x : Space n) (j : Fin n) :
    scale i a b x j = (if j = i then a else b)*x j := by
  simp [scale,Matrix.toLpLin_apply,Matrix.mulVec_diagonal]
lemma scale_det {n : ℕ} (i : Fin n) (a b : ℝ) :
    LinearMap.det (scale i a b) = a*b^(n-1) := by
  classical
  rw [scale,Matrix.toEuclideanLin_eq_toLin_orthonormal,LinearMap.det_toLin,
    Matrix.det_diagonal,← mul_prod_erase _ _ (mem_univ i)]
  simp only [ite_true]
  congr 1
  calc
    _ = ∏ _j ∈ (univ : Finset (Fin n)).erase i,b := by
      apply prod_congr rfl
      intro j hj
      rw [ite_eq_right (mem_erase.mp hj).1]
    _ = _ := by simp
lemma scale_norm_sq {n : ℕ} (i : Fin n) (a b : ℝ) (x : Space n) :
    ‖scale i a b x‖^2 = a^2*(x i)^2+b^2*(‖x‖^2-(x i)^2) := by
  classical
  rw [norm_sq,norm_sq]
  simp only [scale_apply]
  have he : ∀ j : Fin n,((if j = i then a else b)*x j)^2 =
      b^2*(x j)^2+if j = i then (a^2-b^2)*(x i)^2 else 0 := by
    intro j
    by_cases hj : j = i
    · subst j; simp; ring
    · simp [hj]; ring
  simp_rw [he]
  rw [sum_add_distrib,← mul_sum]
  simp
  ring
lemma scale_inverse {n : ℕ} (i : Fin n) {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (x : Space n) : scale i a b (scale i a⁻¹ b⁻¹ x) = x := by
  ext j
  simp only [scale_apply]
  split_ifs <;> field_simp

def cylinder {n : ℕ} (i : Fin n) (D r : ℝ) : Set (Space n) :=
  {x | |x i| ≤ D ∧ ‖x‖^2-(x i)^2 ≤ r^2}

lemma cylinder_closed {n : ℕ} (i : Fin n) (D r : ℝ) : IsClosed (cylinder i D r) := by
  apply IsClosed.inter
  · exact isClosed_le ((EuclideanSpace.proj i).continuous.abs) continuous_const
  · exact isClosed_le (continuous_norm.pow 2 |>.sub ((EuclideanSpace.proj i).continuous.pow 2)) continuous_const

lemma cylinder_subset_image {n : ℕ} (i : Fin n) {D r a b : ℝ}
    (hD : 0 < D) (_hr : 0 < r) (ha : 0 < a) (hb : 0 < b)
    (hscale : D^2/a^2+r^2/b^2 ≤ D^2) :
    cylinder i D r ⊆ scale i a b '' closedBall (0 : Space n) D := by
  intro x hx
  refine ⟨scale i a⁻¹ b⁻¹ x,?_,scale_inverse i ha.ne' hb.ne' x⟩
  rw [mem_closedBall_zero_iff]
  have h1 : (x i)^2 ≤ D^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hD.le).mpr hx.1
  have hs := scale_norm_sq i a⁻¹ b⁻¹ x
  have hsq : ‖scale i a⁻¹ b⁻¹ x‖^2 ≤ D^2 := by
    calc
      _ ≤ a⁻¹^2*D^2+b⁻¹^2*r^2 := by
        rw [hs]
        exact add_le_add (mul_le_mul_of_nonneg_left h1 (sq_nonneg _))
          (mul_le_mul_of_nonneg_left hx.2 (sq_nonneg _))
      _ = D^2/a^2+r^2/b^2 := by ring
      _ ≤ _ := hscale
  nlinarith [norm_nonneg (scale i a⁻¹ b⁻¹ x)]

lemma cylinder_volume {n : ℕ} [NeZero n] (i : Fin n) {D r : ℝ}
    (hD : 0 < D) (hr : 0 < r) :
    volume (cylinder i D r) ≤ ENNReal.ofReal (3*((n:ℝ)+1)*(r/D)^(n-1))*
      volume (closedBall (0 : Space n) D) := by
  let a : ℝ := n+1
  let b : ℝ := ((n:ℝ)+1)/(n:ℝ)*(r/D)
  have hn : 0 < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hscale : D^2/a^2+r^2/b^2 ≤ D^2 := by
    dsimp [a,b]
    field_simp
    nlinarith [sq_nonneg D]
  have hsub := cylinder_subset_image i hD hr ha hb hscale
  have hm := measure_mono (μ := volume) hsub
  rw [Measure.addHaar_image_linearMap,scale_det,abs_of_pos (mul_pos ha (pow_pos hb _))] at hm
  apply hm.trans
  apply mul_le_mul_left
  apply ENNReal.ofReal_le_ofReal
  have hpow : (1+(n:ℝ)⁻¹)^(n-1) ≤ 3 :=
    (pow_le_pow_right₀ (show 1 ≤ 1+(n:ℝ)⁻¹ by linarith [inv_nonneg.mpr hn.le]) (Nat.sub_le n 1)).trans
      (Real.one_add_inv_pow_le_exp.trans Real.exp_one_lt_three.le)
  have he : ((n:ℝ)+1)/(n:ℝ) = 1+(n:ℝ)⁻¹ := by field_simp
  dsimp [a,b]
  rw [mul_pow,he]
  nlinarith [mul_nonneg (show 0 ≤ (n:ℝ)+1 by positivity)
    (mul_nonneg (pow_nonneg (div_nonneg hr.le hD.le) (n-1)) (sub_nonneg.mpr hpow))]

lemma perp_sq {n : ℕ} (i : Fin n) (x : Space n) :
    ‖x‖^2-(x i)^2 = ∑ j ∈ (univ : Finset (Fin n)).erase i,(x j)^2 := by
  rw [norm_sq,← sum_erase_add _ _ (mem_univ i)]
  ring

lemma cylinder_translated_volume {n : ℕ} [NeZero n] (i : Fin n) (q : Space n)
    {D r : ℝ} (hD : 0 < D) (hr : 0 < r) :
    volume {x : Space n | |x i| ≤ D ∧ ‖x-q‖^2-((x-q) i)^2 ≤ r^2} ≤
      ENNReal.ofReal (3*((n:ℝ)+1)*(r/D)^(n-1))*volume (closedBall (0 : Space n) D) := by
  let v := q-EuclideanSpace.single i (q i)
  have he : {x : Space n | |x i| ≤ D ∧ ‖x-q‖^2-((x-q) i)^2 ≤ r^2} =
      (fun x => x-v) ⁻¹' cylinder i D r := by
    ext x
    have hi : (x-v) i = x i := by simp [v]
    have hp : ‖x-v‖^2-((x-v) i)^2 = ‖x-q‖^2-((x-q) i)^2 := by
      rw [perp_sq,perp_sq]
      apply sum_congr rfl
      intro j hj
      simp [v,(mem_erase.mp hj).1]
    change (|x i| ≤ D ∧ ‖x-q‖^2-((x-q) i)^2 ≤ r^2) ↔
      (|(x-v) i| ≤ D ∧ ‖x-v‖^2-((x-v) i)^2 ≤ r^2)
    rw [hp,hi]
  rw [he,(measurePreserving_sub_right volume v).measure_preimage (cylinder_closed i D r).measurableSet.nullMeasurableSet]
  exact cylinder_volume i hD hr

lemma affine_cylinder_volume {n : ℕ} [NeZero n] (u : Space n) (hu : ‖u‖ = 1)
    (q : Space n) {D r : ℝ} (hD : 0 < D) (hr : 0 < r) :
    volume {x : Space n | ‖x‖ ≤ D ∧ ‖x-q‖^2-(inner ℝ u (x-q))^2 ≤ r^2} ≤
      ENNReal.ofReal (3*((n:ℝ)+1)*(r/D)^(n-1))*volume (closedBall (0 : Space n) D) := by
  let i : Fin n := ⟨0,Nat.pos_of_ne_zero (NeZero.ne n)⟩
  let v : Space n := EuclideanSpace.single i 1
  have hv : ‖v‖ = 1 := by simp [v]
  let e := (Submodule.span ℝ ({u-v} : Set (Space n)))ᗮ.reflection
  have he : e u = v := Submodule.reflection_sub (hu.trans hv.symm)
  let C := {x : Space n | |x i| ≤ D ∧ ‖x-e q‖^2-((x-e q) i)^2 ≤ r^2}
  have hC : MeasurableSet C := by
    apply MeasurableSet.inter
    · exact measurableSet_le (EuclideanSpace.proj i).continuous.abs.measurable measurable_const
    · exact measurableSet_le ((continuous_id.sub continuous_const).norm.pow 2 |>.sub
        (((EuclideanSpace.proj i).continuous.comp (continuous_id.sub continuous_const)).pow 2)).measurable measurable_const
  have hsub : {x : Space n | ‖x‖ ≤ D ∧ ‖x-q‖^2-(inner ℝ u (x-q))^2 ≤ r^2} ⊆ e ⁻¹' C := by
    intro x hx
    have hc : |e x i| ≤ ‖e x‖ := by
      have hh := coordinate_sq_le i (e x)
      nlinarith [sq_abs (e x i),abs_nonneg (e x i),norm_nonneg (e x)]
    have hip : inner ℝ u (x-q) = (e x-e q) i := by
      rw [← e.inner_map_map,he,e.map_sub]
      simp [v,EuclideanSpace.inner_single_left]
    refine ⟨hc.trans (by rw [e.norm_map]; exact hx.1),?_⟩
    rw [← hip,← e.map_sub,e.norm_map]
    exact hx.2
  have hm := measure_mono (μ := volume) hsub
  rw [e.measurePreserving.measure_preimage hC.nullMeasurableSet] at hm
  exact hm.trans (cylinder_translated_volume i (e q) hD hr)

end CylinderVolume

end OAI
