import OAI.Geometry.RCD.Transport.ReflectedMidpointMass
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

namespace OAI

/-! # Dilating a local diameter bound to arbitrary compact sets -/

open Set Metric MeasureTheory
open scoped Pointwise
noncomputable section
namespace RegularPointCoordinates

theorem compact_isodiametric_of_local {n : ℕ} {a : ℝ} (ha : 0 < a)
    (hlocal : ∀ A : Set (Euclidean n), IsCompact A → A ⊆ closedBall 0 a →
      volume.real A ≤ volume.real (closedBall (0 : Euclidean n) (diam A/2))) :
    ∀ A : Set (Euclidean n), IsCompact A →
      volume.real A ≤ volume.real (closedBall (0 : Euclidean n) (diam A/2)) := by
  intro A hA
  obtain ⟨R,hR,hAR⟩ := hA.isBounded.exists_pos_norm_le
  let t := a/R
  have ht : 0 < t := div_pos ha hR
  have hscale : t*R=a := div_mul_cancel₀ a hR.ne'
  have hAt : IsCompact (t • A) :=
    hA.image (show Continuous (fun x : Euclidean n => t • x) by fun_prop)
  have hAtub : t • A ⊆ closedBall 0 a := by
    rintro x ⟨y,hy,rfl⟩
    rw [mem_closedBall,dist_zero_right,norm_smul,Real.norm_of_nonneg ht.le]
    exact (mul_le_mul_of_nonneg_left (hAR y hy) ht.le).trans_eq hscale
  have h := hlocal (t • A) hAt hAtub
  have hv : volume.real (t • A) = t^n*volume.real A := by
    simp only [Measure.real,Measure.addHaar_smul_of_nonneg volume ht.le,
      ENNReal.toReal_mul,finrank_euclideanSpace_fin,ENNReal.toReal_ofReal (pow_nonneg ht.le _)]
  have hd : diam (t • A)/2=t*(diam A/2) := by
    rw [diam_smul₀,Real.norm_of_nonneg ht.le]
    ring
  have hb : volume.real (closedBall (0 : Euclidean n) (t*(diam A/2))) =
      t^n*volume.real (closedBall (0 : Euclidean n) (diam A/2)) := by
    rw [Measure.real,Measure.addHaar_closedBall_mul_of_pos volume (0 : Euclidean n) ht]
    simp only [ENNReal.toReal_mul,finrank_euclideanSpace_fin,
      ENNReal.toReal_ofReal (pow_nonneg ht.le _),Measure.real]
  rw [hv,hd,hb] at h
  exact le_of_mul_le_mul_left h (pow_pos ht n)

end RegularPointCoordinates

end

end OAI
