import OAI.Geometry.Relativity.CKS.CoordinateLeviCivita

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology

 def metricPair (g : AmbientMat) (v w : PhysicalPoint) : ℝ :=
  ∑ i, ∑ j, g i j*v i*w j

lemma D_sum3 (e : PhysicalPoint) {x : PhysicalPoint} (f : Fin 3 → PhysicalPoint → ℝ)
    (hf : ∀ i, DifferentiableAt ℝ (f i) x) :
    D e (fun y => ∑ i, f i y) x = ∑ i, D e (f i) x := by
  simp only [D, fderiv_fun_sum (fun i _ => hf i), _root_.sum_apply]

lemma direction_expansion (v : PhysicalPoint) :
    v = ∑ i, v i • CKSRealizedRound.basis i := by
  ext j
  simp [CKSRealizedRound.basis, Pi.single_apply]

lemma D_direction_expansion (e x : PhysicalPoint) (f : PhysicalPoint → ℝ) :
    D e f x = ∑ i, e i*D (CKSRealizedRound.basis i) f x := by
  unfold D
  conv_lhs => rw [direction_expansion e]
  simp

lemma D_metricPair (e : PhysicalPoint) {G : PhysicalPoint → AmbientMat}
    {V W : PhysicalPoint → PhysicalPoint} {x : PhysicalPoint}
    (hg : DifferentiableAt ℝ G x) (hv : DifferentiableAt ℝ V x)
    (hw : DifferentiableAt ℝ W x) :
    D e (fun y => metricPair (G y) (V y) (W y)) x =
      ∑ i, ∑ j, (D e (fun y => G y i j) x*V x i*W x j +
        G x i j*D e (fun y => V y i) x*W x j+
        G x i j*V x i*D e (fun y => W y j) x) := by
  have hgc (i j) : DifferentiableAt ℝ (fun y => G y i j) x :=
    differentiableAt_pi.mp (differentiableAt_pi.mp hg i) j
  have hvc (i) : DifferentiableAt ℝ (fun y => V y i) x := differentiableAt_pi.mp hv i
  have hwc (i) : DifferentiableAt ℝ (fun y => W y i) x := differentiableAt_pi.mp hw i
  have ht (i j) : DifferentiableAt ℝ (fun y => G y i j*V y i*W y j) x :=
    ((hgc i j).fun_mul (hvc i)).fun_mul (hwc j)
  have hsum (i) : DifferentiableAt ℝ (fun y => ∑ j, G y i j*V y i*W y j) x :=
    DifferentiableAt.fun_sum (fun j _ => ht i j)
  unfold metricPair
  rw [D_sum3 e _ hsum]
  apply Finset.sum_congr rfl
  intro i _
  rw [D_sum3 e _ (ht i)]
  apply Finset.sum_congr rfl
  intro j _
  rw [D_mul e ((hgc i j).fun_mul (hvc i)) (hwc j), D_mul e (hgc i j) (hvc i)]
  ring

 def covariantVector (G : PhysicalPoint → AmbientMat) (e : PhysicalPoint)
    (W : PhysicalPoint → PhysicalPoint) (x : PhysicalPoint) (k : Fin 3) : ℝ :=
  D e (fun y => W y k) x + ∑ i, ∑ j, e i * W x j * coordinateChristoffel G x i j k

lemma covariantVector_lowered {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hg : (G x).PosDef) (e : PhysicalPoint) (W : PhysicalPoint → PhysicalPoint) (k : Fin 3) :
    (∑ l, covariantVector G e W x l * G x l k) =
      (∑ l, D e (fun y => W y l) x * G x l k) +
      ∑ i, ∑ j, e i * W x j * lowerKoszul (actualMetricFirstJet G x) i j k := by
  simp only [covariantVector, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [christoffel_lowered hg]

lemma metricPair_symm {g : AmbientMat} (hg : g.IsHermitian) (v w : PhysicalPoint) :
    metricPair g v w=metricPair g w v := by
  unfold metricPair
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hermitian_real_symmetry hg i j]
  ring

lemma metricPair_covariant {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hg : (G x).PosDef) (e w : PhysicalPoint) (V : PhysicalPoint → PhysicalPoint) :
    metricPair (G x) (covariantVector G e V x) w =
      (∑ k, (∑ l, D e (fun y => V y l) x * G x l k) * w k) +
      ∑ k, (∑ i, ∑ j, e i * V x j * lowerKoszul (actualMetricFirstJet G x) i j k) * w k := by
  unfold metricPair
  rw [Finset.sum_comm]
  simp_rw [mul_comm (G x _ _) (covariantVector G e V x _), ← Finset.sum_mul,
    covariantVector_lowered hg]
  simp [add_mul, Finset.sum_add_distrib]

end
end CKSAngularGeometry

end

end OAI
