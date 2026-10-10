import OAI.Geometry.Immersion.ClosedSurface.PhaseMean

namespace OAI

/-! A numerical operator norm bound for covariant two-tensor pullback. -/
noncomputable section
namespace ClosedSurfaceR4.PhaseMean
open SmallModes

lemma norm_evaluate_le (A : Tensor) (v w : Base) :
    ‖evaluate A v w‖ ≤ 4*‖A‖*‖v‖*‖w‖ := by
  have hA (i : Fin 3) : ‖A i‖ ≤ ‖A‖ := norm_le_pi_norm A i
  have hv1 := norm_fst_le v
  have hv2 := norm_snd_le v
  have hw1 := norm_fst_le w
  have hw2 := norm_snd_le w
  have hmid : ‖v.1*w.2+v.2*w.1‖ ≤ ‖v‖*‖w‖+‖v‖*‖w‖ := by
    calc
      _ ≤ ‖v.1*w.2‖+‖v.2*w.1‖ := norm_add_le _ _
      _ ≤ _ := by simp only [norm_mul]; gcongr
  have h0 : ‖A 0*v.1*w.1‖ ≤ ‖A‖*‖v‖*‖w‖ := by
    simp only [norm_mul]
    gcongr
    exact hA 0
  have h1 : ‖A 1*(v.1*w.2+v.2*w.1)‖ ≤ ‖A‖*(‖v‖*‖w‖+‖v‖*‖w‖) := by
    rw [norm_mul]
    exact mul_le_mul (hA 1) hmid (norm_nonneg _) (norm_nonneg _)
  have h2 : ‖A 2*v.2*w.2‖ ≤ ‖A‖*‖v‖*‖w‖ := by
    simp only [norm_mul]
    gcongr
    exact hA 2
  calc
    _ ≤ ‖A 0*v.1*w.1‖ + ‖A 1*(v.1*w.2+v.2*w.1)‖ + ‖A 2*v.2*w.2‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ‖A‖*‖v‖*‖w‖ + ‖A‖*(‖v‖*‖w‖+‖v‖*‖w‖) + ‖A‖*‖v‖*‖w‖ :=
      add_le_add (add_le_add h0 h1) h2
    _ = _ := by ring

lemma norm_pullback_le (L : Base →L[ℝ] Base) : ‖pullback L‖ ≤ 4*‖L‖^2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro A
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  change ‖evaluate A (L (firstDirection i)) (L (secondDirection i))‖ ≤ _
  have hv : ‖L (firstDirection i)‖ ≤ ‖L‖ :=
    (L.le_opNorm _).trans (by simpa using mul_le_mul_of_nonneg_left (firstDirection_norm i) (norm_nonneg L))
  have hw : ‖L (secondDirection i)‖ ≤ ‖L‖ :=
    (L.le_opNorm _).trans (by simpa using mul_le_mul_of_nonneg_left (secondDirection_norm i) (norm_nonneg L))
  calc
    _ ≤ 4*‖A‖*‖L (firstDirection i)‖*‖L (secondDirection i)‖ := norm_evaluate_le _ _ _
    _ ≤ 4*‖A‖*‖L‖*‖L‖ := by gcongr
    _ = _ := by ring

end ClosedSurfaceR4.PhaseMean

end

end OAI
