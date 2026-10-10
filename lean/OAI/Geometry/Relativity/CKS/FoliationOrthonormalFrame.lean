import OAI.Geometry.Relativity.CKS.PhysicalFrameCalculus

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix Filter CKSCalculus
open scoped BigOperators Topology ContDiff

 def adaptedFrame (U : ℝ) (γ : Mat) (s : Point) : Fin 3 → PhysicalPoint :=
  ![foliationNormal U s,
    ![0,(Real.sqrt (γ 0 0))⁻¹,0],
    ![0,-γ 0 1/(Real.sqrt (γ 0 0)*Real.sqrt γ.det),Real.sqrt (γ 0 0)/Real.sqrt γ.det]]

lemma metricPair_foliationNormal {U : ℝ} (hU : U ≠ 0) {γ : Mat} (hγ : γ.IsHermitian)
    (s : Point) : metricPair (foliationMetric U γ s) (foliationNormal U s) (foliationNormal U s)=1 := by
  have h := foliationNormal_unit hU hγ s
  simpa only [metricPair,dotProduct,mulVec,star_apply,star_trivial,Finset.mul_sum,mul_comm,mul_left_comm,mul_assoc] using h

lemma metricPair_normal_tangent {U : ℝ} (hU : U ≠ 0) {γ : Mat} (hγ : γ.IsHermitian)
    (s : Point) (v : PhysicalPoint) (hv : v 0=0) :
    metricPair (foliationMetric U γ s) v (foliationNormal U s)=0 := by
  unfold metricPair
  apply Finset.sum_eq_zero
  intro i _
  refine Fin.cases ?_ (fun a => ?_) i
  · simp [hv]
  · calc
      _ = v a.succ * ∑ j, foliationMetric U γ s a.succ j * foliationNormal U s j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = 0 := by rw [foliationNormal_orthogonal hU hγ s a]; ring

lemma adaptedFrame_radial (U : ℝ) (γ : Mat) (s : Point) (a : Fin 2) :
    adaptedFrame U γ s a.succ 0=0 := by fin_cases a <;> rfl

lemma adaptedFrame_first (U : ℝ) (γ : Mat) (s : Point) :
    adaptedFrame U γ s 0=foliationNormal U s := rfl

lemma metricPair_tangent_expanded (U : ℝ) (γ : Mat) (s : Point)
    (v w : PhysicalPoint) (hv : v 0=0) (hw : w 0=0) :
    metricPair (foliationMetric U γ s) v w =
      γ 0 0*v 1*w 1+γ 0 1*v 1*w 2+(γ 1 0*v 2*w 1+γ 1 1*v 2*w 2) := by
  simp only [metricPair, Fin.sum_univ_three, hv, hw, mul_zero, zero_mul, zero_add, add_zero]
  rfl

lemma adaptedFrame_orthonormal {U : ℝ} (hU : U ≠ 0) {γ : Mat} (hγ : γ.PosDef)
    (s : Point) (i j : Fin 3) :
    metricPair (foliationMetric U γ s) (adaptedFrame U γ s i) (adaptedFrame U γ s j)=
      if i=j then 1 else 0 := by
  have h00 : 0 < γ 0 0 := hγ.diag_pos
  have hd : 0 < γ.det := hγ.det_pos
  have ha : 0 < Real.sqrt (γ 0 0) := Real.sqrt_pos.mpr h00
  have hb : 0 < Real.sqrt γ.det := Real.sqrt_pos.mpr hd
  have ha2 := Real.sq_sqrt h00.le
  have hb2 := Real.sq_sqrt hd.le
  have hdet : γ.det=γ 0 0*γ 1 1-(γ 0 1)^2 := by
    rw [Matrix.det_fin_two,hermitian_real_symmetry hγ.isHermitian 0 1]
    ring
  have hn (a : Fin 2) := metricPair_normal_tangent hU hγ.isHermitian s
    (adaptedFrame U γ s a.succ) (adaptedFrame_radial U γ s a)
  have hgs : (foliationMetric U γ s).IsHermitian := metricBlock_hermitian _ _ hγ.isHermitian
  have hnt (a : Fin 2) : metricPair (foliationMetric U γ s) (adaptedFrame U γ s 0)
      (adaptedFrame U γ s a.succ)=0 := by
    rw [metricPair_symm hgs]
    exact hn a
  fin_cases i <;> fin_cases j
  · exact metricPair_foliationNormal hU hγ.isHermitian s
  · exact hnt 0
  · exact hnt 1
  · exact hn 0
  · rw [metricPair_tangent_expanded U γ s _ _ rfl rfl]
    change γ 0 0 * (Real.sqrt (γ 0 0))⁻¹ * (Real.sqrt (γ 0 0))⁻¹ +
      γ 0 1 * (Real.sqrt (γ 0 0))⁻¹ * 0 +
      (γ 1 0 * 0 * (Real.sqrt (γ 0 0))⁻¹ + γ 1 1 * 0 * 0) = 1
    simp only [mul_zero,zero_mul,add_zero]
    field_simp
    rw [ha2]
  · rw [metricPair_tangent_expanded U γ s _ _ rfl rfl]
    change γ 0 0 * (Real.sqrt (γ 0 0))⁻¹ * (-γ 0 1/(Real.sqrt (γ 0 0)*Real.sqrt γ.det)) +
      γ 0 1 * (Real.sqrt (γ 0 0))⁻¹ * (Real.sqrt (γ 0 0)/Real.sqrt γ.det) +
      (γ 1 0 * 0 * (-γ 0 1/(Real.sqrt (γ 0 0)*Real.sqrt γ.det)) +
       γ 1 1 * 0 * (Real.sqrt (γ 0 0)/Real.sqrt γ.det)) = 0
    simp only [zero_mul,mul_zero,add_zero]
    field_simp
    rw [ha2]
    ring
  · exact hn 1
  · rw [metricPair_tangent_expanded U γ s _ _ rfl rfl]
    change γ 0 0 * (-γ 0 1/(Real.sqrt (γ 0 0)*Real.sqrt γ.det)) * (Real.sqrt (γ 0 0))⁻¹ +
      γ 0 1 * (-γ 0 1/(Real.sqrt (γ 0 0)*Real.sqrt γ.det)) * 0 +
      (γ 1 0 * (Real.sqrt (γ 0 0)/Real.sqrt γ.det) * (Real.sqrt (γ 0 0))⁻¹ +
       γ 1 1 * (Real.sqrt (γ 0 0)/Real.sqrt γ.det) * 0) = 0
    rw [hermitian_real_symmetry hγ.isHermitian 0 1]
    simp only [mul_zero,add_zero]
    field_simp
    rw [ha2]
    ring
  · rw [metricPair_tangent_expanded U γ s _ _ rfl rfl]
    change γ 0 0 * (-γ 0 1/(Real.sqrt (γ 0 0)*Real.sqrt γ.det)) * (-γ 0 1/(Real.sqrt (γ 0 0)*Real.sqrt γ.det)) +
      γ 0 1 * (-γ 0 1/(Real.sqrt (γ 0 0)*Real.sqrt γ.det)) * (Real.sqrt (γ 0 0)/Real.sqrt γ.det) +
      (γ 1 0 * (Real.sqrt (γ 0 0)/Real.sqrt γ.det) * (-γ 0 1/(Real.sqrt (γ 0 0)*Real.sqrt γ.det)) +
       γ 1 1 * (Real.sqrt (γ 0 0)/Real.sqrt γ.det) * (Real.sqrt (γ 0 0)/Real.sqrt γ.det)) = 1
    rw [hermitian_real_symmetry hγ.isHermitian 0 1]
    field_simp
    rw [ha2,hb2,hdet]
    ring

end
end CKSAngularGeometry

end

end OAI
