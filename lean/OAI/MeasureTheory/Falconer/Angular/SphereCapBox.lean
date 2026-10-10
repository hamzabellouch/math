import OAI.MeasureTheory.Falconer.Angular.GnomonicCap
import OAI.MeasureTheory.Falconer.Angular.SphereRotations
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

namespace OAI

/-! # A rectangular bound for the cone under a spherical cap -/

namespace Falconer
open Set MeasureTheory Metric
open scoped ENNReal Pointwise

noncomputable def northCapBox (n : ℕ) (r : ℝ) : Set (Space (n+1)) :=
  WithLp.ofLp ⁻¹' Icc (Fin.cons (-1) (fun _ : Fin n => -r))
    (Fin.cons 1 (fun _ : Fin n => r))

theorem mem_northCapBox {n : ℕ} {r : ℝ} {z : Space (n+1)} :
    z ∈ northCapBox n r ↔ |z 0| ≤ 1 ∧ ∀ i : Fin n, |z i.succ| ≤ r := by
  simp only [northCapBox,mem_preimage,mem_Icc,Pi.le_def,Fin.forall_fin_succ,
    Fin.cons_zero,Fin.cons_succ,abs_le]
  aesop

theorem northCapBox_volume (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (volume : Measure (Space (n+1))) (northCapBox n r) =
      ENNReal.ofReal (2*(2*r)^n) := by
  unfold northCapBox
  rw [← Measure.map_apply (PiLp.volume_preserving_ofLp (Fin (n+1))).measurable measurableSet_Icc,
    (PiLp.volume_preserving_ofLp (Fin (n+1))).map_eq,Real.volume_Icc_pi,Fin.prod_univ_succ]
  simp only [Fin.cons_zero,Fin.cons_succ,sub_neg_eq_add,← two_mul,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (mul_nonneg (by norm_num) hr),
    ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

theorem north_cap_cone_subset {n : ℕ} {r : ℝ} :
    Ioo (0:ℝ) 1 • ((↑) '' (ball (gnomonicChart (0 : Space n)) r)) ⊆ northCapBox n r := by
  rintro z ⟨t,ht,y,⟨w,hw,rfl⟩,rfl⟩
  rw [mem_northCapBox]
  have hw0 : |(w:Space (n+1)) 0| ≤ 1 := by
    simpa only [sphere_norm,Real.norm_eq_abs] using PiLp.norm_apply_le (w:Space (n+1)) 0
  constructor
  · change |t*(w:Space (n+1)) 0| ≤ 1
    rw [abs_mul,abs_of_pos ht.1]
    exact (mul_le_mul_of_nonneg_left hw0 ht.1.le).trans (by simpa only [mul_one] using ht.2.le)
  · intro i
    have hd : ‖(w:Space (n+1))-northLift (0:Space n)‖ < r := by
      simpa only [mem_ball,Subtype.dist_eq,gnomonicChart_zero_coe,dist_eq_norm] using hw
    have hi : |(w:Space (n+1)) i.succ| < r := by
      have hh := (PiLp.norm_apply_le ((w:Space (n+1))-northLift (0:Space n)) i.succ).trans_lt hd
      simpa [northLift] using hh
    change |t*(w:Space (n+1)) i.succ| ≤ r
    rw [abs_mul,abs_of_pos ht.1]
    exact (mul_le_of_le_one_left (abs_nonneg _) ht.2.le).trans hi.le

theorem north_sphere_cap_bound (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    sphereMeasure (n+1) (ball (gnomonicChart (0:Space n)) r) ≤
      ENNReal.ofReal (((n+1:ℕ):ℝ)*2*(2*r)^n) := by
  rw [sphereMeasure,Measure.toSphere_apply' _ measurableSet_ball]
  simp only [finrank_euclideanSpace,Fintype.card_fin]
  apply (mul_le_mul_right (measure_mono north_cap_cone_subset) _).trans_eq
  rw [northCapBox_volume n hr,← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  congr 1
  ring

end Falconer

end OAI
