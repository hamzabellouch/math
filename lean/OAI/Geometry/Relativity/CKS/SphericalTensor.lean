import OAI.Geometry.Relativity.CKS.HeatGenerated
import OAI.Geometry.Relativity.CKS.SphericalLaplacian

namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter Finset CKSCalculus CKSRealizedRound
open CKSInducedSphere (E Ix Mat e grad hess pd proj roundLaplacian sphereGradient tensorDivergence U)
open scoped Topology ContDiff

def pair (M : Mat) (v w : E) : ℝ := ∑ i : Ix, ∑ j : Ix, v i * w j * M i j

def dPair (T : E → Mat) (n d v w : E) : ℝ :=
  pair (fun i j => fderiv ℝ (fun y => T y i j) n d) v w

lemma pair_symm (M : Mat) (hM : ∀ i j, M i j = M j i) (v w : E) :
    pair M v w = pair M w v := by
  unfold pair
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  rw [hM j i]
  ring

@[simp] lemma pair_zero_left (M : Mat) (v : E) : pair M 0 v = 0 := by simp [pair]
@[simp] lemma pair_zero_right (M : Mat) (v : E) : pair M v 0 = 0 := by simp [pair]
@[simp] lemma pair_smul_left (M : Mat) (c : ℝ) (v w : E) :
    pair M (c • v) w = c * pair M v w := by simp [pair, mul_assoc, mul_sum]
@[simp] lemma pair_smul_right (M : Mat) (c : ℝ) (v w : E) :
    pair M v (c • w) = c * pair M v w := by
  simp only [pair, PiLp.smul_apply, smul_eq_mul, mul_sum]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  ring
@[simp] lemma pair_neg_left (M : Mat) (v w : E) : pair M (-v) w = -pair M v w := by
  simpa only [neg_one_smul, neg_one_mul] using pair_smul_left M (-1) v w
@[simp] lemma pair_neg_right (M : Mat) (v w : E) : pair M v (-w) = -pair M v w := by
  simpa only [neg_one_smul, neg_one_mul] using pair_smul_right M (-1) v w
@[simp] lemma pair_add_left (M : Mat) (u v w : E) :
    pair M (u+v) w = pair M u w + pair M v w := by
  simp [pair, add_mul, sum_add_distrib]
@[simp] lemma pair_add_right (M : Mat) (u v w : E) :
    pair M u (v+w) = pair M u v + pair M u w := by
  simp [pair, mul_add, add_mul, sum_add_distrib]
@[simp] lemma dPair_smul_dir (T : E → Mat) (n d v w : E) (c : ℝ) :
    dPair T n (c • d) v w = c * dPair T n d v w := by
  simp only [dPair,pair,map_smul,smul_eq_mul,mul_sum]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  ring

lemma pair_normal (M : Mat) (n v : E) (hn : ∀ j : Ix, ∑ i : Ix, n i * M i j = 0) :
    pair M n v = 0 := by
  unfold pair
  rw [sum_comm]
  have he (j : Ix) : (∑ i : Ix, n i * v j * M i j) = v j * ∑ i : Ix, n i * M i j := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    ring
  simp only [he,hn,mul_zero,sum_const_zero]

lemma pair_trace (M : Mat) (x : Point)
    (hn : ∀ j : Ix, ∑ i : Ix, sphereParam x i * M i j = 0) :
    pair M (thetaFrame x) (thetaFrame x) + pair M (phiUnit x) (phiUnit x) = ∑ i : Ix, M i i := by
  have he : pair M (thetaFrame x) (thetaFrame x) + pair M (phiUnit x) (phiUnit x) =
      ∑ i : Ix, ∑ j : Ix, proj (fun k => sphereParam x k) i j * M i j := by
    simp [pair,projected_frame,add_mul,sum_add_distrib]
  rw [he]
  simp only [proj,sub_mul,sum_sub_distrib,ite_mul,one_mul,zero_mul,sum_ite_eq]
  change (∑ i : Ix, M i i) - pair M (sphereParam x) (sphereParam x) = _
  rw [pair_normal M _ _ hn,sub_zero]

lemma dPair_symm {T : E → Mat} (_hT : ∀ i j, ContDiffOn ℝ ∞ (fun y => T y i j) U)
    (hS : ∀ y ∈ U, ∀ i j, T y i j = T y j i) {n : E} (hn : n ∈ U) (d v w : E) :
    dPair T n d v w = dPair T n d w v := by
  apply pair_symm
  intro i j
  have he : (fun y => T y i j) =ᶠ[𝓝 n] (fun y => T y j i) :=
    Filter.eventually_of_mem (CKSInducedSphere.U_open.mem_nhds hn) (fun y hy => hS y hy i j)
  rw [he.fderiv_eq]

lemma pair_smooth {T : E → Mat} (hT : ∀ i j, ContDiffOn ℝ ∞ (fun y => T y i j) U)
    {v w : Point → E} (hv : ContDiff ℝ ∞ v) (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (fun x => pair (T (sphereParam x)) (v x) (w x)) := by
  apply ContDiff.sum
  intro i hi
  apply ContDiff.sum
  intro j hj
  exact (((EuclideanSpace.proj i).contDiff.comp hv).mul
    ((EuclideanSpace.proj j).contDiff.comp hw)).mul (angular_smooth (hT i j))

lemma D_sum {J : Type*} (s : Finset J) {f : J → Point → ℝ} {x : Point}
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) x) (v : Point) :
    D v (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, D v (f i) x := by
  simp only [D, fderiv_fun_sum hf, _root_.sum_apply]

lemma pair_derivative {T : E → Mat} (hT : ∀ i j, ContDiffOn ℝ ∞ (fun y => T y i j) U)
    {v w : Point → E} (hv : ContDiff ℝ ∞ v) (hw : ContDiff ℝ ∞ w) (x : Point) (k : Ix) :
    D (basis k) (fun y => pair (T (sphereParam y)) (v y) (w y)) x =
      pair (T (sphereParam x)) (fderiv ℝ v x (basis k)) (w x) +
      pair (T (sphereParam x)) (v x) (fderiv ℝ w x (basis k)) +
      dPair T (sphereParam x) (chartVector k x) (v x) (w x) := by
  have hvd (i : Ix) : DifferentiableAt ℝ (fun y => v y i) x :=
    (contDiff_euclidean.mp hv i).differentiable (by simp) x
  have hwd (i : Ix) : DifferentiableAt ℝ (fun y => w y i) x :=
    (contDiff_euclidean.mp hw i).differentiable (by simp) x
  have htd (i j : Ix) := (angular_smooth (hT i j)).differentiable (by simp) x
  have hterm (i j : Ix) : DifferentiableAt ℝ
      (fun y => v y i * w y j * T (sphereParam y) i j) x := ((hvd i).mul (hwd j)).mul (htd i j)
  change D (basis k) (fun y => ∑ i : Ix, ∑ j : Ix, v y i * w y j * T (sphereParam y) i j) x = _
  rw [D_sum univ (f := fun i y => ∑ j : Ix, v y i * w y j * T (sphereParam y) i j)
    (fun i _ => by
      convert! (DifferentiableAt.sum (u := univ) (fun j _ => hterm i j)) using 1)]
  have he (i : Ix) := D_sum univ (f := fun j y => v y i * w y j * T (sphereParam y) i j)
    (fun j _ => hterm i j) (basis k)
  simp only [he, pair, dPair]
  simp only [← sum_add_distrib]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  erw [D_mul _ ((hvd i).mul (hwd j)) (htd i j), D_mul _ (hvd i) (hwd j)]
  rw [angular_first (hT i j)]
  rw [component_fderiv (hv.differentiable (by simp) x), component_fderiv (hw.differentiable (by simp) x)]
  dsimp only [Pi.mul_apply]
  ring

end
end CKSSphericalChart

end

end OAI
