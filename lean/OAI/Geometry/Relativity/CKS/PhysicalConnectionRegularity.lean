import OAI.Geometry.Relativity.CKS.PhysicalFrameConnection

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma matrix_det_contDiffAt {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hg : ContDiffAt ℝ ∞ G x) : ContDiffAt ℝ ∞ (fun y => (G y).det) x := by
  have hc (i j) : ContDiffAt ℝ ∞ (fun y => G y i j) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hg i) j
  simp only [Matrix.det_fin_three]
  fun_prop

lemma matrix_inv_component_contDiffAt {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hg : ContDiffAt ℝ ∞ G x) (h0 : (G x).det ≠ 0) (i j : Fin 3) :
    ContDiffAt ℝ ∞ (fun y => (G y)⁻¹ i j) x := by
  have hc (i j) : ContDiffAt ℝ ∞ (fun y => G y i j) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hg i) j
  have hd := (matrix_det_contDiffAt hg).inv h0
  simp only [Matrix.inv_def,Ring.inverse_eq_inv',Matrix.smul_apply,smul_eq_mul,
    Matrix.adjugate_fin_three]
  fin_cases i <;> fin_cases j
  · change ContDiffAt ℝ ∞ (fun y => ((G y).det)⁻¹ * (G y 1 1 * G y 2 2 - G y 1 2 * G y 2 1)) x
    exact hd.mul (by fun_prop)
  · change ContDiffAt ℝ ∞ (fun y => ((G y).det)⁻¹ * (-(G y 0 1 * G y 2 2) + G y 0 2 * G y 2 1)) x
    exact hd.mul (by fun_prop)
  · change ContDiffAt ℝ ∞ (fun y => ((G y).det)⁻¹ * (G y 0 1 * G y 1 2 - G y 0 2 * G y 1 1)) x
    exact hd.mul (by fun_prop)
  · change ContDiffAt ℝ ∞ (fun y => ((G y).det)⁻¹ * (-(G y 1 0 * G y 2 2) + G y 1 2 * G y 2 0)) x
    exact hd.mul (by fun_prop)
  · change ContDiffAt ℝ ∞ (fun y => ((G y).det)⁻¹ * (G y 0 0 * G y 2 2 - G y 0 2 * G y 2 0)) x
    exact hd.mul (by fun_prop)
  · change ContDiffAt ℝ ∞ (fun y => ((G y).det)⁻¹ * (-(G y 0 0 * G y 1 2) + G y 0 2 * G y 1 0)) x
    exact hd.mul (by fun_prop)
  · change ContDiffAt ℝ ∞ (fun y => ((G y).det)⁻¹ * (G y 1 0 * G y 2 1 - G y 1 1 * G y 2 0)) x
    exact hd.mul (by fun_prop)
  · change ContDiffAt ℝ ∞ (fun y => ((G y).det)⁻¹ * (-(G y 0 0 * G y 2 1) + G y 0 1 * G y 2 0)) x
    exact hd.mul (by fun_prop)
  · change ContDiffAt ℝ ∞ (fun y => ((G y).det)⁻¹ * (G y 0 0 * G y 1 1 - G y 0 1 * G y 1 0)) x
    exact hd.mul (by fun_prop)

lemma coordinateChristoffel_contDiffAt {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hg : ContDiffAt ℝ ∞ G x) (h0 : (G x).det ≠ 0) (i j k : Fin 3) :
    ContDiffAt ℝ ∞ (fun y => coordinateChristoffel G y i j k) x := by
  have hc (i j) : ContDiffAt ℝ ∞ (fun y => G y i j) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hg i) j
  have hdc (a i j) : ContDiffAt ℝ ∞
      (fun y => D (CKSRealizedRound.basis a) (fun z => G z i j) y) x :=
    contDiffAt_D (hc i j) (by simp) _
  have hi (i j) := matrix_inv_component_contDiffAt hg h0 i j
  unfold coordinateChristoffel
  apply ContDiffAt.sum
  intro l _
  apply ContDiffAt.mul _ (hi l k)
  change ContDiffAt ℝ ∞ (fun y =>
    (D (CKSRealizedRound.basis i) (fun z => G z j l) y +
     D (CKSRealizedRound.basis j) (fun z => G z i l) y -
     D (CKSRealizedRound.basis l) (fun z => G z i j) y)/2) x
  exact (((hdc i j l).add (hdc j i l)).sub (hdc l i j)).div_const 2

lemma variable_direction_smooth {V : PhysicalPoint → PhysicalPoint}
    {f : PhysicalPoint → ℝ} {x : PhysicalPoint}
    (hv : ContDiffAt ℝ ∞ V x) (hf : ContDiffAt ℝ ∞ f x) :
    ContDiffAt ℝ ∞ (fun y => D (V y) f y) x := by
  exact (hf.fderiv_right (by simp)).clm_apply hv

lemma covariantVector_contDiffAt {G : PhysicalPoint → AmbientMat}
    {V W : PhysicalPoint → PhysicalPoint} {x : PhysicalPoint}
    (hg : ContDiffAt ℝ ∞ G x) (h0 : (G x).det ≠ 0)
    (hv : ContDiffAt ℝ ∞ V x) (hw : ContDiffAt ℝ ∞ W x) :
    ContDiffAt ℝ ∞ (fun y => covariantVector G (V y) W y) x := by
  have hvc i := contDiffAt_pi.mp hv i
  have hwc i := contDiffAt_pi.mp hw i
  apply contDiffAt_pi.mpr
  intro k
  have hd := variable_direction_smooth hv (hwc k)
  have hc (i j) := coordinateChristoffel_contDiffAt hg h0 i j k
  unfold covariantVector
  exact hd.add (ContDiffAt.sum (fun i _ => ContDiffAt.sum
    (fun j _ => ((hvc i).mul (hwc j)).mul (hc i j))))

lemma metricPair_contDiffAt {G : PhysicalPoint → AmbientMat}
    {V W : PhysicalPoint → PhysicalPoint} {x : PhysicalPoint}
    (hg : ContDiffAt ℝ ∞ G x) (hv : ContDiffAt ℝ ∞ V x)
    (hw : ContDiffAt ℝ ∞ W x) :
    ContDiffAt ℝ ∞ (fun y => metricPair (G y) (V y) (W y)) x := by
  have hgc (i j) : ContDiffAt ℝ ∞ (fun y => G y i j) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hg i) j
  have hvc i := contDiffAt_pi.mp hv i
  have hwc i := contDiffAt_pi.mp hw i
  exact ContDiffAt.sum (fun i _ => ContDiffAt.sum
    (fun j _ => ((hgc i j).mul (hvc i)).mul (hwc j)))

lemma frameCoefficient_contDiffAt {G : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (hg : ContDiffAt ℝ ∞ G x) (h0 : (G x).det ≠ 0)
    (he : ∀ i, ContDiffAt ℝ ∞ (E i) x) (i j k : Fin 3) :
    ContDiffAt ℝ ∞ (fun y => frameCoefficient G E y i j k) x :=
  metricPair_contDiffAt hg (covariantVector_contDiffAt hg h0 (he i) (he j)) (he k)

end
end CKSAngularGeometry

end

end OAI
