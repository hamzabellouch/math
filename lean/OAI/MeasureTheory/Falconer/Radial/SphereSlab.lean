import OAI.MeasureTheory.Falconer.Angular.SphereCapBox
import OAI.MeasureTheory.Falconer.Angular.NorthRotation

namespace OAI

/-! Linear slab bounds for the surface measure, obtained from cone volume. -/

namespace Falconer
open Set MeasureTheory Metric
open scoped ENNReal Pointwise

noncomputable def northSlabBox (n : ℕ) (r : ℝ) : Set (Space (n+1)) :=
  WithLp.ofLp ⁻¹' Icc (Fin.cons (-r) (fun _ : Fin n => -1))
    (Fin.cons r (fun _ : Fin n => 1))

theorem mem_northSlabBox {n : ℕ} {r : ℝ} {z : Space (n+1)} :
    z ∈ northSlabBox n r ↔ |z 0| ≤ r ∧ ∀ i : Fin n, |z i.succ| ≤ 1 := by
  simp only [northSlabBox, mem_preimage, mem_Icc, Pi.le_def, Fin.forall_fin_succ,
    Fin.cons_zero, Fin.cons_succ, abs_le]
  aesop

theorem northSlabBox_volume (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (volume : Measure (Space (n+1))) (northSlabBox n r) = ENNReal.ofReal ((2*r)*2^n) := by
  unfold northSlabBox
  rw [← Measure.map_apply (PiLp.volume_preserving_ofLp (Fin (n+1))).measurable measurableSet_Icc,
    (PiLp.volume_preserving_ofLp (Fin (n+1))).map_eq, Real.volume_Icc_pi, Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, sub_neg_eq_add, ← two_mul,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_one]
  rw [← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2),
    ← ENNReal.ofReal_mul (mul_nonneg (by norm_num) hr)]

theorem north_slab_cone_subset {n : ℕ} {r : ℝ} :
    Ioo (0 : ℝ) 1 • ((↑) '' {w : Sphere (n+1) | |(w : Space (n+1)) 0| ≤ r}) ⊆
      northSlabBox n r := by
  rintro z ⟨t, ht, y, ⟨w, hw, rfl⟩, rfl⟩
  rw [mem_northSlabBox]
  constructor
  · change |t*(w : Space (n+1)) 0| ≤ r
    rw [abs_mul, abs_of_pos ht.1]
    exact (mul_le_of_le_one_left (abs_nonneg _) ht.2.le).trans hw
  · intro i
    have hi : |(w : Space (n+1)) i.succ| ≤ 1 := by
      simpa only [sphere_norm, Real.norm_eq_abs] using PiLp.norm_apply_le (w : Space (n+1)) i.succ
    change |t*(w : Space (n+1)) i.succ| ≤ 1
    rw [abs_mul, abs_of_pos ht.1]
    exact (mul_le_of_le_one_left (abs_nonneg _) ht.2.le).trans hi

theorem north_sphere_slab_bound (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    sphereMeasure (n+1) {w : Sphere (n+1) | |(w : Space (n+1)) 0| ≤ r} ≤
      ENNReal.ofReal (((n+1 : ℕ) : ℝ)*2^(n+1)*r) := by
  rw [sphereMeasure, Measure.toSphere_apply' _ (measurableSet_le (by fun_prop) measurable_const)]
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  apply (mul_le_mul_right (measure_mono north_slab_cone_subset) _).trans_eq
  rw [northSlabBox_volume n hr, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  congr 1
  rw [pow_succ]
  ring

theorem unit_sphere_slab_bound (n : ℕ) (u : Sphere (n+1)) {r : ℝ} (hr : 0 ≤ r) :
    sphereMeasure (n+1) {w : Sphere (n+1) | |inner ℝ (w : Space (n+1)) u| ≤ r} ≤
      ENNReal.ofReal (((n+1 : ℕ) : ℝ)*2^(n+1)*r) := by
  let e := northRotation u
  have hi (w : Sphere (n+1)) : (e (w : Space (n+1))) 0 = inner ℝ (w : Space (n+1)) u := by
    rw [← inner_northLift_zero, ← gnomonicChart_zero_coe, ← northRotation_apply u]
    exact e.inner_map_map _ _
  have hm : MeasurableSet {w : Sphere (n+1) | |(w : Space (n+1)) 0| ≤ r} :=
    measurableSet_le (by fun_prop) measurable_const
  have he := (sphereMap_measurePreserving e).map_eq
  have hpre : sphereMap e ⁻¹' {w : Sphere (n+1) | |(w : Space (n+1)) 0| ≤ r} =
      {w : Sphere (n+1) | |inner ℝ (w : Space (n+1)) u| ≤ r} := by
    ext w
    simp only [mem_preimage, mem_ofPred_eq, sphereMap, hi]
  rw [← hpre, ← Measure.map_apply (continuous_sphereMap e).measurable hm, he]
  exact north_sphere_slab_bound n hr

theorem sphere_slab_bound (n : ℕ) {v : Space (n+1)} (hv : v ≠ 0)
    {r : ℝ} (hr : 0 ≤ r) :
    sphereMeasure (n+1) {w : Sphere (n+1) | |inner ℝ (w : Space (n+1)) v| ≤ r} ≤
      ENNReal.ofReal ((((n+1 : ℕ) : ℝ)*2^(n+1))*r/‖v‖) := by
  have hvp : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let u : Sphere (n+1) := ⟨‖v‖⁻¹ • v, by
    rw [mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hvp), inv_mul_cancel₀ hvp.ne']⟩
  have he (w : Sphere (n+1)) : |inner ℝ (w : Space (n+1)) u| =
      |inner ℝ (w : Space (n+1)) v| / ‖v‖ := by
    change |inner ℝ (w : Space (n+1)) (‖v‖⁻¹ • v)| = _
    rw [inner_smul_right, abs_mul, abs_of_pos (inv_pos.mpr hvp)]
    ring
  have hset : {w : Sphere (n+1) | |inner ℝ (w : Space (n+1)) v| ≤ r} =
      {w : Sphere (n+1) | |inner ℝ (w : Space (n+1)) u| ≤ r/‖v‖} := by
    ext w
    rw [mem_ofPred_eq, mem_ofPred_eq, he, div_le_div_iff_of_pos_right hvp]
  rw [hset]
  exact (unit_sphere_slab_bound n u (div_nonneg hr hvp.le)).trans_eq
    (by congr 1; ring)

end Falconer

end OAI
