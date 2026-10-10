import OAI.Geometry.Relativity.CKS.FoliationPhysicalLeaf

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology

 def coordinateChristoffel (G : PhysicalPoint → AmbientMat) (x : PhysicalPoint)
    (i j k : Fin 3) : ℝ :=
  ∑ l, lowerKoszul (actualMetricFirstJet G x) i j l * (G x)⁻¹ l k

 def coordinateCovariantNormal (G : PhysicalPoint → AmbientMat)
    (N : PhysicalPoint → PhysicalPoint) (x : PhysicalPoint) (i k : Fin 3) : ℝ :=
  D (CKSRealizedRound.basis i) (fun y => N y k) x +
    ∑ j, coordinateChristoffel G x i j k * N x j

lemma christoffel_lowered {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hG : (G x).PosDef) (i j k : Fin 3) :
    (∑ l, coordinateChristoffel G x i j l * G x l k) =
      lowerKoszul (actualMetricFirstJet G x) i j k := by
  simp only [coordinateChristoffel, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  have hi := Matrix.nonsing_inv_mul (G x) (isUnit_iff_ne_zero.mpr hG.det_pos.ne')
  change (∑ l, lowerKoszul (actualMetricFirstJet G x) i j l * ((G x)⁻¹ * G x) l k) = _
  rw [hi]
  change (∑ l, lowerKoszul (actualMetricFirstJet G x) i j l * (if l=k then 1 else 0)) = _
  simp

lemma actualMetricFirstJet_symmetric {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hG : ∀ᶠ y in 𝓝 x, (G y).IsHermitian) (i j k : Fin 3) :
    actualMetricFirstJet G x i j k = actualMetricFirstJet G x i k j := by
  apply D_congr
  filter_upwards [hG] with y hy
  exact (hermitian_real_symmetry hy j k).symm

lemma coordinateChristoffel_torsion {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hG : ∀ᶠ y in 𝓝 x, (G y).IsHermitian) (i j k : Fin 3) :
    coordinateChristoffel G x i j k = coordinateChristoffel G x j i k := by
  apply Finset.sum_congr rfl
  intro l _
  congr 1
  unfold lowerKoszul
  rw [actualMetricFirstJet_symmetric hG l j i]
  ring

lemma coordinateChristoffel_metric {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hG : (G x).PosDef) (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian) (i j k : Fin 3) :
    actualMetricFirstJet G x i j k =
      (∑ l, coordinateChristoffel G x i j l * G x l k) +
      (∑ l, coordinateChristoffel G x i k l * G x j l) := by
  have hsecond : (∑ l, coordinateChristoffel G x i k l * G x j l) =
      lowerKoszul (actualMetricFirstJet G x) i k j := by
    simpa only [hermitian_real_symmetry hG.isHermitian] using christoffel_lowered hG i k j
  rw [christoffel_lowered hG, hsecond]
  unfold lowerKoszul
  rw [actualMetricFirstJet_symmetric hs i k j]
  ring

theorem coordinateNormalCovariant_is_LeviCivita {G : PhysicalPoint → AmbientMat}
    {N : PhysicalPoint → PhysicalPoint} {x : PhysicalPoint} (hG : (G x).PosDef)
    (i k : Fin 3) :
    (∑ l, coordinateCovariantNormal G N x i l * G x l k) =
      coordinateNormalCovariant G N x i k := by
  simp only [coordinateCovariantNormal, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hs : (∑ j, ∑ l, coordinateChristoffel G x i j l * N x j * G x l k) =
      ∑ j, N x j * lowerKoszul (actualMetricFirstJet G x) i j k := by
    apply Finset.sum_congr rfl
    intro j _
    calc
      _ = N x j * ∑ l, coordinateChristoffel G x i j l * G x l k := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        ring
      _ = _ := by rw [christoffel_lowered hG]
  rw [hs]
  simp only [coordinateNormalCovariant, Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  ring

end
end CKSAngularGeometry

end

end OAI
