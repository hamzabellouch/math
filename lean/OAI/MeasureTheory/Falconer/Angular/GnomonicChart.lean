import OAI.MeasureTheory.Falconer.Angular.SphereRotations
import OAI.MeasureTheory.Falconer.Fourier.ChartDerivatives

namespace OAI

/-!
# The north-hemisphere gnomonic chart

This is the explicit inverse gnomonic map, in Euclidean coordinates.
The measure identity used with this map is kept separate as a published
input; all the coordinate identities below are proved.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

noncomputable def northLift {n : ℕ} (x : Space n) : Space (n+1) :=
  WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))

@[simp] theorem northLift_zero {n : ℕ} (x : Space n) : northLift x 0 = 1 := rfl

@[simp] theorem northLift_succ {n : ℕ} (x : Space n) (i : Fin n) :
    northLift x i.succ = x i := by simp [northLift]

theorem northLift_ne_zero {n : ℕ} (x : Space n) : northLift x ≠ 0 := by
  intro h
  have hh := congrArg (fun z : Space (n+1) => z 0) h
  simp at hh

theorem northLift_norm_sq {n : ℕ} (x : Space n) : ‖northLift x‖^2 = 1+‖x‖^2 := by
  rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_succ]
  simp

theorem northLift_continuous (n : ℕ) : Continuous (@northLift n) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin (n+1) => ℝ)).comp
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact continuous_const
  · simpa only [Fin.cons_succ] using (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j)

noncomputable def gnomonicChart {n : ℕ} (x : Space n) : Sphere (n+1) :=
  ⟨‖northLift x‖⁻¹ • northLift x, by
    rw [Metric.mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr (northLift_ne_zero x))),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr (northLift_ne_zero x))]⟩

theorem gnomonicChart_continuous (n : ℕ) : Continuous (@gnomonicChart n) := by
  apply Continuous.subtype_mk
  exact ((northLift_continuous n).norm.inv₀ (fun x =>
    norm_ne_zero_iff.mpr (northLift_ne_zero x))).smul (northLift_continuous n)

@[simp] theorem gnomonicChart_zero {n : ℕ} (x : Space n) :
    (gnomonicChart x : Space (n+1)) 0 = ‖northLift x‖⁻¹ := by
  simp [gnomonicChart]

@[simp] theorem gnomonicChart_succ {n : ℕ} (x : Space n) (i : Fin n) :
    (gnomonicChart x : Space (n+1)) i.succ = ‖northLift x‖⁻¹ * x i := by
  simp [gnomonicChart]

def northHemisphere (n : ℕ) : Set (Sphere (n+1)) :=
  {w | 0 < (w : Space (n+1)) 0}

theorem gnomonicChart_mem_hemisphere {n : ℕ} (x : Space n) :
    gnomonicChart x ∈ northHemisphere n := by
  change 0 < (gnomonicChart x : Space (n+1)) 0
  rw [gnomonicChart_zero]
  exact inv_pos.mpr (norm_pos_iff.mpr (northLift_ne_zero x))

theorem gnomonicChart_coordinate_ratio {n : ℕ} (x : Space n) (i : Fin n) :
    (gnomonicChart x : Space (n+1)) i.succ / (gnomonicChart x : Space (n+1)) 0 = x i := by
  rw [gnomonicChart_succ,gnomonicChart_zero]
  have h := norm_ne_zero_iff.mpr (northLift_ne_zero x)
  field_simp

theorem gnomonicChart_injective (n : ℕ) : Function.Injective (@gnomonicChart n) := by
  intro x y h
  apply PiLp.ext
  intro i
  rw [← gnomonicChart_coordinate_ratio x i,← gnomonicChart_coordinate_ratio y i,h]

noncomputable def gnomonicDensity {n : ℕ} (x : Space n) : ℝ :=
  (1+‖x‖^2)^(-((n+1 : ℕ) : ℝ)/2)

theorem gnomonicDensity_pos {n : ℕ} (x : Space n) : 0 < gnomonicDensity x :=
  Real.rpow_pos_of_pos (by positivity) _

theorem gnomonicDensity_continuous (n : ℕ) : Continuous (@gnomonicDensity n) := by
  change Continuous (fun x : Space n => (1+‖x‖^2)^(-((n+1 : ℕ) : ℝ)/2))
  have h : Continuous (fun x : Space n => 1+‖x‖^2) :=
    continuous_const.add (continuous_norm.pow 2)
  exact h.rpow_const (fun x => Or.inl (ne_of_gt (by positivity)))

end Falconer

end OAI
