import OAI.Geometry.Relativity.CKS.FoliationKoszul

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix Filter CKSCalculus
open scoped BigOperators Topology

 def actualMetricFirstJet (G : PhysicalPoint → AmbientMat) (x : PhysicalPoint) :
    Fin 3 → AmbientMat := fun i j k => D (CKSRealizedRound.basis i) (fun y => G y j k) x

 def coordinateNormalCovariant (G : PhysicalPoint → AmbientMat) (N : PhysicalPoint → PhysicalPoint)
    (x : PhysicalPoint) (i k : Fin 3) : ℝ :=
  ∑ j, (G x j k * D (CKSRealizedRound.basis i) (fun y => N y j) x +
    N x j * lowerKoszul (actualMetricFirstJet G x) i j k)

lemma normalCovariant_realization {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : DifferentiableAt ℝ U x) (hγ : DifferentiableAt ℝ γ x)
    (hs : DifferentiableAt ℝ s x) (h0 : U x ≠ 0) (i k : Fin 3) :
    coordinateNormalCovariant (fun y => foliationMetric (U y) (γ y) (s y))
      (fun y => foliationNormal (U y) (s y)) x i k =
    normalCovariantFirstJet (U x) (γ x) (s x)
      (fun p => D (CKSRealizedRound.basis p) U x)
      (fun p a b => D (CKSRealizedRound.basis p) (fun y => γ y a b) x)
      (fun p a => D (CKSRealizedRound.basis p) (fun y => s y a) x) i k := by
  have hg : actualMetricFirstJet (fun y => foliationMetric (U y) (γ y) (s y)) x =
      fun p => foliationMetricDerivative (U x) (γ x) (s x)
        (D (CKSRealizedRound.basis p) U x)
        (fun a b => D (CKSRealizedRound.basis p) (fun y => γ y a b) x)
        (fun a => D (CKSRealizedRound.basis p) (fun y => s y a) x) := by
    funext p
    exact foliationMetric_derivative _ hU hγ hs h0
  have hn (p j) := congrFun (foliationNormal_derivative (CKSRealizedRound.basis p) hU hs) j
  unfold coordinateNormalCovariant normalCovariantFirstJet
  rw [hg]
  simp_rw [← hn]

lemma derivative_matrix_hermitian {γ : PhysicalPoint → Mat} {x : PhysicalPoint}
    (hγ : ∀ᶠ y in 𝓝 x, (γ y).IsHermitian) (e : PhysicalPoint) :
    Matrix.IsHermitian (fun a b : Fin 2 => D e (fun y => γ y a b) x) := by
  ext a b
  change D e (fun y => γ y b a) x = D e (fun y => γ y a b) x
  apply D_congr
  filter_upwards [hγ] with y hy
  exact hermitian_real_symmetry hy a b

theorem physical_foliation_leaf_geometry {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : DifferentiableAt ℝ U x) (hγ : DifferentiableAt ℝ γ x)
    (hs : DifferentiableAt ℝ s x) (h0 : 0 < U x)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) :
    (∀ a b : Fin 2,
      coordinateNormalCovariant (fun y => foliationMetric (U y) (γ y) (s y))
        (fun y => foliationNormal (U y) (s y)) x a.succ b.succ =
      U x/2 * (D (CKSRealizedRound.basis 0) (fun y => γ y a b) x -
        ∑ c, (s x c*D (CKSRealizedRound.basis c.succ) (fun y => γ y a b) x +
          γ x c b*D (CKSRealizedRound.basis a.succ) (fun y => s y c) x +
          γ x a c*D (CKSRealizedRound.basis b.succ) (fun y => s y c) x))) ∧
    (∀ a : Fin 2,
      (∑ i, foliationNormal (U x) (s x) i *
        coordinateNormalCovariant (fun y => foliationMetric (U y) (γ y) (s y))
          (fun y => foliationNormal (U y) (s y)) x i a.succ) =
        D (CKSRealizedRound.basis a.succ) U x / U x) := by
  have hsym : ∀ᶠ y in 𝓝 x, (γ y).IsHermitian := hp.mono (fun _ h => h.isHermitian)
  have hsym0 : (γ x).IsHermitian := hsym.self_of_nhds
  constructor
  · intro a b
    rw [normalCovariant_realization hU hγ hs h0.ne']
    exact foliation_chi_koszul h0.ne' hsym0 _ _ _ _
      (fun p => derivative_matrix_hermitian hsym (CKSRealizedRound.basis p)) a b
  · intro a
    simp_rw [normalCovariant_realization hU hγ hs h0.ne']
    exact foliation_acceleration_koszul h0.ne' hsym0 _ _ _ _
      (fun p => derivative_matrix_hermitian hsym (CKSRealizedRound.basis p)) a

end
end CKSAngularGeometry

end

end OAI
