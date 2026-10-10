import Mathlib
import OAI.Analysis.Conductivity.Variational.PhysicalFaceSum
import OAI.Analysis.Conductivity.Sources.FacePasting
import OAI.Analysis.Conductivity.Sources.NonzeroJacobianAE

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix

lemma flatEndCoordinates_ae {a : ℝ} (ha : a≠0) (b : ℝ)
    {P : Coord3 → Prop} (hP : ∀ᵐ y ∂volume,P y) :
    ∀ᵐ x ∂volume,P (flatEndCoordinates a b x) := by
  apply ae_comp_of_nonzero_jacobian (endAxialAffine_hasFDeriv a b) _ _ _ hP
  · intro x y h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp only [endAxialAffine,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val] at h0 h1 h2
    have h0' : x 0=y 0 := by linarith [mul_left_cancel₀ ha h0]
    ext k
    fin_cases k <;> assumption
  · exact measurable_const
  · intro x
    change (Matrix.toLin' (endAxialMatrix a)).det≠0
    simpa [LinearMap.det_toLin',endAxialMatrix,Matrix.det_diagonal,Fin.prod_univ_succ] using ha

lemma ae_image_of_differentiable {f : Coord3 → Coord3} {S : Set Coord3}
    (hS : MeasurableSet S) (hI : MeasurableSet (f '' S)) (hf : DifferentiableOn ℝ f S) {P : Coord3 → Prop}
    (hP : ∀ᵐ x ∂volume.restrict S,P (f x)) :
    ∀ᵐ y ∂volume.restrict (f '' S),P y := by
  have hn : volume {x | x∈S ∧ ¬ P (f x)}=0 := by
    rw [ae_restrict_iff' hS,ae_iff] at hP
    simpa using hP
  have hn' := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    (hf.mono (show {x | x∈S ∧ ¬ P (f x)}⊆S from fun x hx => hx.1)) hn
  rw [ae_iff,Measure.restrict_apply' hI]
  apply le_antisymm _ bot_le
  have he : {y | ¬P y} ∩ f '' S ⊆ f '' {x | x∈S ∧ ¬P (f x)} := by
    rintro y ⟨hy,x,hx,rfl⟩
    exact ⟨x,⟨hx,hy⟩,rfl⟩
  exact (measure_mono he).trans hn'.le

lemma sourceClosedCollarBand_ae_faces {l r : ℝ}
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) {P : Coord3 → Prop}
    (hP : ∀ i j : Fin 4,∀ᵐ x ∂volume.restrict (sourceExtendedBox l r),
      P (sourceCollarPiece i j x)) :
    ∀ᵐ y ∂volume.restrict (sourceClosedCollarBand l r),P y := by
  rw [sourceClosedCollarBand_measure_faces hl hr]
  simp only [ae_finsetSum_measure_iff,Finset.mem_univ,true_implies]
  intro i j
  exact ae_image_of_differentiable measurableSet_Icc (sourceCollarClosedPiece_measurable l r i j)
    (fun x _ => (sourceCollarPiece_hasFDeriv i j x).differentiableAt.differentiableWithinAt)
    (hP i j)

end ScalarConductivity

end

end OAI
