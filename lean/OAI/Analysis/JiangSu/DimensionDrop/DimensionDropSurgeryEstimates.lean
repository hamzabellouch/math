import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.DimensionDrop.DimensionDropSquareDensity
import OAI.Analysis.JiangSu.MatrixAlgebras.MatrixFiberCommutants
import OAI.Analysis.JiangSu.CStarAlgebras.FourEdgeConjugationEstimates

namespace OAI


noncomputable section
namespace JiangSuConstruction
open MatrixTensor FourEdgeSurgery
open scoped CStarAlgebra ComplexOrder

variable {p q : ℕ}

lemma rightUnitary_conjugation (w : unitary (TensorMat p q)) (x : (TensorMat p q)) :
    unitaryConjugation (rightUnitary w) (MatrixTensor.right (I := Fin p×Fin q) x)=
      MatrixTensor.right (unitaryConjugation w x) := by
  change MatrixTensor.right (I := Fin p×Fin q) (w:(TensorMat p q))*MatrixTensor.right x*star (MatrixTensor.right (w:(TensorMat p q)))=
    MatrixTensor.right ((w:(TensorMat p q))*x*star (w:(TensorMat p q)))
  simp only [map_mul,map_star]

lemma pFlow_commute_drop_one (f : DimensionDrop p q) (r : ℝ) :
    Commute ((pFlow (I := Fin p) (J := Fin q)) r:(MatrixTensor.Mat (MatrixTensor.Four (Fin p) (Fin q)))) (MatrixTensor.left (f.val rightEndpoint)) ∧
    Commute ((pFlow (I := Fin p) (J := Fin q)) r:(MatrixTensor.Mat (MatrixTensor.Four (Fin p) (Fin q)))) (MatrixTensor.right (f.val rightEndpoint)) := by
  obtain ⟨x,hx⟩ := f.property.2
  change rightAmplification p q x=f.val rightEndpoint at hx
  rw [←hx,rightAmplification_eq]
  exact ⟨pFlow_commute_left_right r x,pFlow_commute_right_right r x⟩
lemma qFlow_commute_drop_zero (f : DimensionDrop p q) (r : ℝ) :
    Commute ((qFlow (I := Fin p) (J := Fin q)) r:(MatrixTensor.Mat (MatrixTensor.Four (Fin p) (Fin q)))) (MatrixTensor.left (f.val leftEndpoint)) ∧
    Commute ((qFlow (I := Fin p) (J := Fin q)) r:(MatrixTensor.Mat (MatrixTensor.Four (Fin p) (Fin q)))) (MatrixTensor.right (f.val leftEndpoint)) := by
  obtain ⟨x,hx⟩ := f.property.1
  change leftAmplification p q x=f.val leftEndpoint at hx
  rw [←hx,leftAmplification_eq]
  exact ⟨qFlow_commute_left_left r x,qFlow_commute_right_left r x⟩

lemma surgerySection_control (W : C(Interval×Interval,unitary (TensorMat p q)))
    (a b : C(Interval,ℝ)) (f : DimensionDrop p q) {δ η : ℝ} (hδ : 0≤δ) (hη : 0≤η)
    (ha : ∀ s,a s≠0 → ‖f.val s-f.val leftEndpoint‖≤δ)
    (hb : ∀ s,b s≠0 → ‖f.val s-f.val rightEndpoint‖≤δ)
    (hW : ∀ s t,‖unitaryConjugation (W (s,t)) (f.val s)-f.val t‖≤η)
    (s t : Interval) :
    ‖unitaryConjugation (surgerySection W a b (s,t)) (MatrixTensor.left (f.val s))-
      MatrixTensor.right (f.val t)‖≤16*δ+5*η := by
  have hl (x y : (TensorMat p q)) : ‖MatrixTensor.left (J := Fin p×Fin q) x-MatrixTensor.left y‖≤‖x-y‖ := by
    rw [←map_sub]
    exact NonUnitalStarAlgHom.norm_apply_le _ _
  have hr (x y : (TensorMat p q)) : ‖MatrixTensor.right (I := Fin p×Fin q) x-MatrixTensor.right y‖≤‖x-y‖ := by
    rw [←map_sub]
    exact NonUnitalStarAlgHom.norm_apply_le _ _
  have hv (u v : Interval) :
      ‖unitaryConjugation (rightUnitary (W (u,v))) (MatrixTensor.right (f.val u))-
        MatrixTensor.right (f.val v)‖≤η := by
    rw [rightUnitary_conjugation]
    exact (hr _ _).trans (hW u v)
  exact surgery_control (pFlow (I := Fin p) (J := Fin q)) (qFlow (I := Fin p) (J := Fin q)) (rightUnitary (W (s,leftEndpoint)))
    (rightUnitary (W (s,rightEndpoint))) (rightUnitary (W (s,t)))
    (a s) (b s) (a t) (b t)
    (MatrixTensor.left (f.val s)) (MatrixTensor.left (f.val leftEndpoint))
    (MatrixTensor.left (f.val rightEndpoint)) (MatrixTensor.right (f.val s))
    (MatrixTensor.right (f.val leftEndpoint)) (MatrixTensor.right (f.val rightEndpoint))
    (MatrixTensor.right (f.val t)) hδ hη
    (fun r => (pFlow_commute_drop_one f r).1) (fun r => (qFlow_commute_drop_zero f r).1)
    (fun r => (pFlow_commute_drop_one f r).2) (fun r => (qFlow_commute_drop_zero f r).2)
    (fun h => (hl _ _).trans (ha s h)) (fun h => (hl _ _).trans (hb s h))
    (fun h => (hr _ _).trans (ha s h)) (fun h => (hr _ _).trans (hb s h))
    (fun h => (hr _ _).trans (ha t h)) (fun h => (hr _ _).trans (hb t h))
    (by simpa only [pFlow_one,qFlow_one] using partial_flip (f.val s))
    (hv s leftEndpoint) (hv s rightEndpoint) (hv s t)

end JiangSuConstruction

end

end OAI
