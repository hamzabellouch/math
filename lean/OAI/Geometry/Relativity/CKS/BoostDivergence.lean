import OAI.Geometry.Relativity.CKS.BoostFlow

namespace OAI

noncomputable section
namespace CKSSphericalHarmonics
noncomputable section
open scoped RealInnerProductSpace ContDiff
open Finset

def boostField (p x : Ambient) : Ambient := p - inner ℝ p x • x

def coordinateCM (i : Fin 3) : C(Sphere,ℝ) :=
  smoothRestriction (fun x : Ambient => x i) (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffOn

lemma smoothRotation_coordinate (i j k : Fin 3) (x : Ambient) :
    smoothRotation i j (fun x : Ambient => x k) x =
      (if k=j then x i else 0) - (if k=i then x j else 0) := by
  change fderiv ℝ (EuclideanSpace.proj (𝕜 := ℝ) k) x _ = _
  rw [(EuclideanSpace.proj (𝕜 := ℝ) k).fderiv]
  exact rotationGenerator_apply i j k x

lemma sphereIntegral_coordinate_rotation {F : Ambient → ℝ}
    (hF : ContDiffOn ℝ ∞ F puncturedSpace) (i j : Fin 3) :
    sphereIntegral (coordinateCM i *
      smoothRestriction (smoothRotation i j F) (smoothRotation_smooth hF i j)) =
      if i=j then 0 else sphereIntegral (coordinateCM j * smoothRestriction F hF) := by
  by_cases hij : i=j
  · subst j
    have hzero : smoothRestriction (smoothRotation i i F) (smoothRotation_smooth hF i i) = 0 := by
      ext n
      change fderiv ℝ F n (rotationGenerator i i n) = 0
      have hgen : rotationGenerator i i (n:Ambient) = 0 := by ext k; simp [rotationGenerator_apply]
      rw [hgen, map_zero]
    simp [hzero]
  have h := smoothRotation_skew_adjoint (F := fun x : Ambient => x i) (G := F)
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffOn hF i j hij
  rw [inner_toL2, inner_toL2] at h
  have he : smoothRestriction (smoothRotation i j (fun x : Ambient => x i))
      (smoothRotation_smooth (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffOn i j) = -coordinateCM j := by
    ext n
    change smoothRotation i j (fun x : Ambient => x i) n = -(n:Ambient) j
    simp [smoothRotation_coordinate, hij]
  rw [he] at h
  simp only [neg_mul, map_neg] at h
  simpa [hij, coordinateCM] using neg_injective h.symm

lemma boostField_decomposition (p : Ambient) (n : Sphere) :
    boostField p n = ∑ i : Fin 3, ∑ j : Fin 3,
      ((n:Ambient) i * p j) • rotationGenerator i j n := by
  have h := rotationGenerator_decomposition (n:Ambient) p
  have hn : ‖(n:Ambient)‖ = 1 := by simp
  rw [hn, one_pow, one_smul] at h
  have hi : inner ℝ p (n:Ambient) = ∑ i : Fin 3, (n:Ambient) i * p i := by
    rw [PiLp.inner_apply]
    simp [mul_comm]
  unfold boostField
  rw [hi]
  exact sub_eq_iff_eq_add.mpr h

theorem sphereIntegral_boostField {F : Ambient → ℝ}
    (hF : ContDiffOn ℝ ∞ F puncturedSpace) (p : Ambient) :
    ∫ n : Sphere, fderiv ℝ F n (boostField p n) ∂surfaceMeasure =
      2 * ∫ n : Sphere, inner ℝ p (n:Ambient) * F n ∂surfaceMeasure := by
  let L : C(Sphere,ℝ) := ∑ i : Fin 3, ∑ j : Fin 3,
    p j • (coordinateCM i * smoothRestriction (smoothRotation i j F) (smoothRotation_smooth hF i j))
  have hL : ∀ n : Sphere, L n = fderiv ℝ F n (boostField p n) := by
    intro n
    rw [boostField_decomposition]
    simp only [map_sum, map_smul, L, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
      ContinuousMap.mul_apply, smul_eq_mul, coordinateCM, smoothRestriction, smoothRotation, ContinuousMap.coe_mk]
    apply sum_congr rfl; intro i hi
    apply sum_congr rfl; intro j hj
    ring
  have hi : ∫ n : Sphere, fderiv ℝ F n (boostField p n) ∂surfaceMeasure = sphereIntegral L := by
    rw [sphereIntegral_apply]
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall fun n => (hL n).symm
  rw [hi]
  have hsig : sphereIntegral L =
      2 * sphereIntegral ((∑ j : Fin 3, p j • coordinateCM j) * smoothRestriction F hF) := by
    simp only [L, map_sum, map_smul, smul_eq_mul, sphereIntegral_coordinate_rotation hF]
    simp only [Fin.sum_univ_three]
    simp only [Fin.reduceEq, ite_true, ite_false, mul_zero, zero_add, add_zero]
    rw [add_mul, add_mul, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc]
    simp only [map_add, map_smul, smul_eq_mul]
    ring
  rw [hsig, sphereIntegral_apply]
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with n
  simp only [ContinuousMap.mul_apply, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    smul_eq_mul, coordinateCM, smoothRestriction, ContinuousMap.coe_mk]
  congr 1
  rw [PiLp.inner_apply]
  simp [mul_comm]

end
end CKSSphericalHarmonics

end

end OAI
