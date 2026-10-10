import OAI.Geometry.Relativity.CKS.AdaptedKoszul
import OAI.Geometry.Relativity.CKS.PhysicalFrameCalculus

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology

lemma covariantVector_metric {G : PhysicalPoint → AmbientMat}
    {V W : PhysicalPoint → PhysicalPoint} {x : PhysicalPoint}
    (hg : DifferentiableAt ℝ G x) (hv : DifferentiableAt ℝ V x)
    (hw : DifferentiableAt ℝ W x) (hp : (G x).PosDef)
    (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian) (e : PhysicalPoint) :
    D e (fun y => metricPair (G y) (V y) (W y)) x =
      metricPair (G x) (covariantVector G e V x) (W x) +
      metricPair (G x) (V x) (covariantVector G e W x) := by
  rw [D_metricPair e hg hv hw,
    metricPair_symm hp.isHermitian (V x) (covariantVector G e W x),
    metricPair_covariant hp, metricPair_covariant hp]
  have hd (i j) : D e (fun y => G y i j) x =
      ∑ a, e a * actualMetricFirstJet G x a i j := D_direction_expansion e x _
  simp_rw [hd]
  simp only [Fin.sum_univ_three, lowerKoszul]
  simp only [hermitian_real_symmetry hp.isHermitian 0 1,
    hermitian_real_symmetry hp.isHermitian 0 2,
    hermitian_real_symmetry hp.isHermitian 1 2,
    actualMetricFirstJet_symmetric hs 0 1 0,
    actualMetricFirstJet_symmetric hs 0 2 0,
    actualMetricFirstJet_symmetric hs 0 2 1,
    actualMetricFirstJet_symmetric hs 1 1 0,
    actualMetricFirstJet_symmetric hs 1 2 0,
    actualMetricFirstJet_symmetric hs 1 2 1,
    actualMetricFirstJet_symmetric hs 2 1 0,
    actualMetricFirstJet_symmetric hs 2 2 0,
    actualMetricFirstJet_symmetric hs 2 2 1]
  ring

abbrev LocalFrame := Fin 3 → PhysicalPoint → PhysicalPoint

 def frameCoefficient (G : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (x : PhysicalPoint) (i j k : Fin 3) : ℝ :=
  metricPair (G x) (covariantVector G (E i x) (E j) x) (E k x)

 def actualFrameBracket (E : LocalFrame) (x : PhysicalPoint) (i j : Fin 3) : PhysicalPoint :=
  fun k => D (E i x) (fun y => E j y k) x - D (E j x) (fun y => E i y k) x

 def frameBracketCoefficient (G : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (x : PhysicalPoint) (i j k : Fin 3) : ℝ :=
  metricPair (G x) (actualFrameBracket E x i j) (E k x)

lemma frameCoefficient_metric {G : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (hg : DifferentiableAt ℝ G x)
    (he : ∀ i, DifferentiableAt ℝ (E i) x) (hp : (G x).PosDef)
    (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian)
    (ho : ∀ᶠ y in 𝓝 x, ∀ i j, metricPair (G y) (E i y) (E j y) = if i=j then 1 else 0)
    (i j k : Fin 3) : frameCoefficient G E x i j k = -frameCoefficient G E x i k j := by
  have h := covariantVector_metric hg (he j) (he k) hp hs (E i x)
  have hd : D (E i x) (fun y => metricPair (G y) (E j y) (E k y)) x=0 := by
    rw [D_congr (ho.mono (fun _ hy => hy j k)) (E i x)]
    exact D_const _ _ _
  rw [hd, metricPair_symm hp.isHermitian (E j x)] at h
  change 0=frameCoefficient G E x i j k+frameCoefficient G E x i k j at h
  linarith

lemma covariantVector_torsion {G : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian)
    (i j : Fin 3) :
    (fun k => covariantVector G (E i x) (E j) x k - covariantVector G (E j x) (E i) x k) =
      actualFrameBracket E x i j := by
  ext k
  have hsum : (∑ a, ∑ b, E i x a * E j x b * coordinateChristoffel G x a b k) =
      ∑ a, ∑ b, E j x a * E i x b * coordinateChristoffel G x a b k := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [coordinateChristoffel_torsion hs b a]
    ring
  dsimp [covariantVector,actualFrameBracket]
  rw [hsum]
  ring

lemma frameCoefficient_torsion {G : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian)
    (i j k : Fin 3) :
    frameCoefficient G E x i j k-frameCoefficient G E x j i k=frameBracketCoefficient G E x i j k := by
  unfold frameBracketCoefficient
  rw [← covariantVector_torsion hs i j]
  simp only [frameCoefficient,metricPair,mul_sub,sub_mul,Finset.sum_sub_distrib]

theorem physical_frame_koszul {G : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (hg : DifferentiableAt ℝ G x)
    (he : ∀ i, DifferentiableAt ℝ (E i) x) (hp : (G x).PosDef)
    (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian)
    (ho : ∀ᶠ y in 𝓝 x, ∀ i j, metricPair (G y) (E i y) (E j y) = if i=j then 1 else 0) :
    frameCoefficient G E x = CKSFrame.koszul (frameBracketCoefficient G E x) := by
  funext i j k
  have h1 := frameCoefficient_torsion (E := E) hs i j k
  have h2 := frameCoefficient_torsion (E := E) hs j k i
  have h3 := frameCoefficient_torsion (E := E) hs k i j
  have hm1 := frameCoefficient_metric hg he hp hs ho i k j
  have hm2 := frameCoefficient_metric hg he hp hs ho j i k
  have hm3 := frameCoefficient_metric hg he hp hs ho k j i
  unfold CKSFrame.koszul
  linarith

end
end CKSAngularGeometry

end

end OAI
