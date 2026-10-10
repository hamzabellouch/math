import OAI.Geometry.IsometricImmersion.Coordinates.ActualShearHyperbolicity
import OAI.Geometry.IsometricImmersion.Immersions.BoundedHeightClasses

namespace OAI

noncomputable section
open Set
open scoped ContDiff Matrix

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation

theorem boundedClassSpeed_sq {kappa : ℝ} (hkappa : 0 < kappa)
    {M : ℕ} (hM : 0 < M) :
    (boundedClassSpeed kappa M) ^ 2 = kappa / (2 * (M : ℝ) ^ 3) := by
  have hMp : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
  have he : ((M : ℝ) ^ (-(3 : ℝ) / 2)) ^ (2 : ℕ) = ((M : ℝ) ^ (3 : ℕ))⁻¹ := by
    rw [← Real.rpow_mul_natCast hMp.le]
    norm_num [Real.rpow_neg, Real.rpow_natCast]
  unfold boundedClassSpeed
  rw [mul_pow, Real.sq_sqrt (by positivity), he]
  ring

theorem boundedClassSpeed_sq_energy {kappa : ℝ} (hkappa : 0 < kappa)
    {M : ℕ} (hM : 0 < M) :
    (boundedClassSpeed kappa M) ^ 2 =
      kappa * (1 / (M : ℝ)) / (2 * (M : ℝ) ^ 2) := by
  rw [boundedClassSpeed_sq hkappa hM]
  field_simp

theorem bounded_class_shear_estimates {g : MetricField} {z : Coord → ℝ}
    {M : ℕ} (h : BoundedAdmissibleHeight g M z) {kappa q0 : ℝ}
    (hkappa : 0 < kappa) {p : Coord}
    (hp : inverseShearCoordinates q0 p ∈ modelSquare)
    (hK : gaussianCurvature g (inverseShearCoordinates q0 p) ≤ -kappa / 2)
    (hq : |hessianQuotient g z (inverseShearCoordinates q0 p) - q0| ≤
      1 / (10 * boundedClassWidth kappa M)) :
    (boundedClassSpeed kappa M) ^ 2 / 2 ≤ -shearTimeFactor g z q0 p ∧
    (boundedClassSpeed kappa M) ^ 2 / (2 * (M : ℝ)) ≤
      |covHessian (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) p 0 0| ∧
    0 < qFirstCoefficient (metricInShearCoordinates g q0) 5
      (qSolutionJet (heightInShearCoordinates z q0) p) ∧
    |qFirstCoefficient (metricInShearCoordinates g q0) 4
      (qSolutionJet (heightInShearCoordinates z q0) p)| +
        Real.sqrt (qFirstCoefficient (metricInShearCoordinates g q0) 5
          (qSolutionJet (heightInShearCoordinates z q0) p)) < boundedClassWidth kappa M / 4 := by
  obtain ⟨hM, hadm, hjet, hHb, hEb⟩ := h
  obtain ⟨U, hU, hSU, hg, hz, hD, hE, hyy, hsmall⟩ := hadm
  have hMp : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
  have hv := boundedClassSpeed_pos hkappa hM
  obtain ⟨hd, hxx, hS, hchar⟩ := actual_shear_hyperbolicity hg hz hU (hSU hp)
    hkappa (one_div_pos.mpr hMp) hv (boundedClassSpeed_sq_energy hkappa hM).le
    (hyy _ hp) (hHb _ hp).2 (hEb _ hp) hK hq (hD _ hp)
  have hdneg : shearTimeFactor g z q0 p < 0 := by
    have hv2 : 0 < (boundedClassSpeed kappa M) ^ 2 / 2 := half_pos (sq_pos_of_pos hv)
    linarith
  have hfac : covHessian (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) p 0 0 =
      shearTimeFactor g z q0 p * covHessian g z (inverseShearCoordinates q0 p) 1 1 :=
    sheared_Hxx_factor hg hz hU q0 (hSU hp) (hyy _ hp) (hD _ hp)
  refine ⟨hd, ?_, hS, hchar⟩
  calc
    _ = ((boundedClassSpeed kappa M) ^ 2 / 2) * (1 / (M : ℝ)) := by ring
    _ ≤ (-shearTimeFactor g z q0 p) * |covHessian g z (inverseShearCoordinates q0 p) 1 1| :=
      mul_le_mul hd (hHb _ hp).1 (one_div_nonneg.mpr hMp.le) (neg_pos.mpr hdneg).le
    _ = _ := by rw [hfac, abs_mul, abs_of_neg hdneg]

theorem boundedClassShearHxxFloor_pos {kappa : ℝ} (hkappa : 0 < kappa)
    {M : ℕ} (hM : 0 < M) :
    0 < (boundedClassSpeed kappa M) ^ 2 / (2 * (M : ℝ)) :=
  div_pos (sq_pos_of_pos (boundedClassSpeed_pos hkappa hM))
    (mul_pos (by norm_num) (Nat.cast_pos.mpr hM))

end SmoothLocal.Perturbation

end

end OAI
