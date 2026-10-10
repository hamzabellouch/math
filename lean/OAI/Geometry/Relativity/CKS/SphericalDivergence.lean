import OAI.Geometry.Relativity.CKS.SphericalTensor

namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter Finset CKSCalculus CKSRealizedRound
open CKSInducedSphere (E Ix Mat e grad hess pd proj roundLaplacian sphereGradient tensorDivergence U)
open scoped Topology ContDiff

lemma projected_test (x : Point) (z : E)
    (hz : ∑ i : Ix, sphereParam x i * z i = 0) (l : Ix) :
    (∑ j : Ix, z j * proj (fun i => sphereParam x i) j l) = z l := by
  simp only [proj,mul_sub,sum_sub_distrib,mul_ite,mul_one,mul_zero,sum_ite_eq']
  have he : (∑ j : Ix, z j * (sphereParam x j * sphereParam x l)) =
      (∑ j : Ix, sphereParam x j * z j) * sphereParam x l := by
    rw [sum_mul]
    apply sum_congr rfl
    intro j hj
    ring
  rw [he,hz,zero_mul,sub_zero]
  simp

lemma dPair_expansion (T : E → Mat) (n d v w : E) :
    dPair T n d v w = ∑ k : Ix, ∑ i : Ix, ∑ j : Ix,
      d k * v i * w j * pd k (fun y => T y i j) n := by
  simp only [dPair,pair,CKSInducedSphere.fderiv_expand,grad,mul_sum]
  rw [CKSInducedSphere.sum3_rotate,CKSInducedSphere.sum3_rotate]
  apply sum_congr rfl
  intro k hk
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  ring

lemma divergence_test (T : E → Mat) (x : Point) (z : E)
    (hz : ∑ i : Ix, sphereParam x i * z i = 0) :
    (∑ j : Ix, z j * tensorDivergence T (sphereParam x) j) =
      ∑ k : Ix, ∑ i : Ix, ∑ l : Ix,
        proj (fun a => sphereParam x a) k i * z l * pd k (fun y => T y i l) (sphereParam x) := by
  simp only [tensorDivergence,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro k hk
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  rw [sum_comm]
  apply sum_congr rfl
  intro l hl
  calc
    _ = proj (fun a => sphereParam x a) k i *
      (∑ j : Ix, z j * proj (fun a => sphereParam x a) j l) *
      pd k (fun y => T y i l) (sphereParam x) := by
        simp only [mul_sum,sum_mul]
        apply sum_congr rfl
        intro j hj
        ring
    _ = _ := by rw [projected_test x z hz l]

lemma divergence_frame (T : E → Mat) (x : Point) (z : E)
    (hz : ∑ i : Ix, sphereParam x i * z i = 0) :
    (∑ j : Ix, z j * tensorDivergence T (sphereParam x) j) =
      dPair T (sphereParam x) (thetaFrame x) (thetaFrame x) z +
      dPair T (sphereParam x) (phiUnit x) (phiUnit x) z := by
  rw [divergence_test T x z hz,dPair_expansion,dPair_expansion]
  simp only [projected_frame,add_mul,sum_add_distrib]

lemma gradient_test (F : E → ℝ) (x : Point) (z : E)
    (hz : ∑ i : Ix, sphereParam x i * z i = 0) :
    (∑ j : Ix, z j * sphereGradient F (sphereParam x) j) = fderiv ℝ F (sphereParam x) z := by
  rw [CKSInducedSphere.fderiv_expand]
  simp only [sphereGradient,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  calc
    _ = (∑ j : Ix, z j * proj (fun a => sphereParam x a) j i) * grad F (sphereParam x) i := by
      simp only [sum_mul]
      apply sum_congr rfl
      intro j hj
      ring
    _ = _ := by rw [projected_test x z hz i]

end
end CKSSphericalChart

end

end OAI
