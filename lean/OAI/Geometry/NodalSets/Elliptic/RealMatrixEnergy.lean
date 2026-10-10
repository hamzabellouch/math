import OAI.Geometry.NodalSets.Elliptic.CompactWeightedWeakEquation
import OAI.Geometry.NodalSets.Elliptic.CoordinateMatrixEllipticity

namespace OAI

namespace Yau.Geometry
open Yau.Jets Matrix MeasureTheory
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

def realCoordGradient (w : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) : Yau.Jets.Coord := fun i ↦ Yau.coordPartial w x i

def realMatrixEnergy (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ) (u v : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) : ℝ :=
  coordMatrixForm (B x) (realCoordGradient u x) (realCoordGradient v x)

lemma realMatrixEnergy_apply (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (u v : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) :
    realMatrixEnergy B u v x = ∑ i, ∑ j, Yau.coordPartial u x i*B x i j*Yau.coordPartial v x j :=
  coordMatrixForm_apply _ _ _

lemma realMatrixEnergy_smooth (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j))
    (u v : Yau.Jets.Coord → ℝ) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (realMatrixEnergy B u v) := by
  simp only [show realMatrixEnergy B u v = fun x ↦ ∑ i, ∑ j,
    Yau.coordPartial u x i*B x i j*Yau.coordPartial v x j from funext (realMatrixEnergy_apply B u v)]
  exact ContDiff.sum (fun i _ ↦ ContDiff.sum (fun j _ ↦
    ((real_coordPartial_smooth u hu i).mul (hB i j)).mul (real_coordPartial_smooth v hv j)))

lemma realMatrixEnergy_compact_left (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (u v : Yau.Jets.Coord → ℝ) (hc : HasCompactSupport u) : HasCompactSupport (realMatrixEnergy B u v) := by
  have hh := HasCompactSupport.finset_sum (s := Finset.univ) (fun i _ ↦
    HasCompactSupport.finset_sum (s := Finset.univ) (fun j _ ↦
      ((hc.fderiv_apply ℝ (Pi.single i 1)).mul_right (f' := fun x ↦ B x i j)).mul_right
        (f' := fun x ↦ Yau.coordPartial v x j)))
  convert hh using 1
  first | rfl | (ext x; simp [realMatrixEnergy_apply,Yau.coordPartial])

lemma coordMatrixForm_symmetric (B : Matrix (Fin 4) (Fin 4) ℝ) (hs : ∀ i j, B i j = B j i)
    (v w : Yau.Jets.Coord) : coordMatrixForm B v w = coordMatrixForm B w v := by
  rw [coordMatrixForm_apply,coordMatrixForm_apply,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hs j i]
  ring

lemma coordMatrixForm_nonneg (B : Matrix (Fin 4) (Fin 4) ℝ) (hp : B.PosDef) (v : Yau.Jets.Coord) :
    0 ≤ coordMatrixForm B v v := by
  by_cases hv : v = 0
  · simp [hv]
  · exact (coordMatrixForm_positive B hp v hv).le

lemma realCoordGradient_cutoff (eta w : Yau.Jets.Coord → ℝ)
    (heta : ContDiff ℝ ∞ eta) (hw : ContDiff ℝ ∞ w) (x : Yau.Jets.Coord) :
    realCoordGradient (fun y ↦ eta y^2*w y) x =
      (eta x^2) • realCoordGradient w x + (2*eta x*w x) • realCoordGradient eta x := by
  ext i
  have he : (fun y ↦ eta y^2*w y) = fun y ↦ (eta y*eta y)*w y := by
    funext y; ring
  simp only [realCoordGradient,he,Yau.real_coordPartial_mul _ _ (heta.mul heta) hw,
    Yau.real_coordPartial_mul _ _ heta heta,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  ring

lemma realMatrixEnergy_cutoff (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (eta w : Yau.Jets.Coord → ℝ) (heta : ContDiff ℝ ∞ eta) (hw : ContDiff ℝ ∞ w) (x : Yau.Jets.Coord) :
    realMatrixEnergy B (fun y ↦ eta y^2*w y) w x =
      eta x^2*realMatrixEnergy B w w x + 2*eta x*w x*realMatrixEnergy B eta w x := by
  unfold realMatrixEnergy
  rw [realCoordGradient_cutoff eta w heta hw x]
  simp [map_add,map_smul,smul_eq_mul]

lemma realMatrixEnergy_cutoff_square (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (hs : ∀ x i j, B x i j = B x j i) (hp : ∀ x, (B x).PosDef)
    (eta w : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) :
    0 ≤ eta x^2*realMatrixEnergy B w w x +
      4*(eta x*w x*realMatrixEnergy B eta w x) + 4*w x^2*realMatrixEnergy B eta eta x := by
  have h := coordMatrixForm_nonneg (B x) (hp x)
    (eta x • realCoordGradient w x + (2*w x) • realCoordGradient eta x)
  simp only [map_add,map_smul,_root_.add_apply,_root_.smul_apply,smul_eq_mul] at h
  rw [coordMatrixForm_symmetric (B x) (hs x) (realCoordGradient w x) (realCoordGradient eta x)] at h
  change 0 ≤ _ at h
  unfold realMatrixEnergy
  nlinarith only [h]

end
end Yau.Geometry

end OAI
