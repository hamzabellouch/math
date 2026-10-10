import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.MatrixAlgebras.MatrixPartialFlips

namespace OAI


noncomputable section

namespace MatrixTensor
open scoped CStarAlgebra ComplexOrder

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

lemma fiber_commute_left (S : StarSubalgebra ℂ (Mat I)) (T : StarSubalgebra ℂ (Mat J))
    (x : Mat I) (hx : ∀ a∈S,Commute a x) {y : Mat (I×J)} (hy : y∈fiberAlgebra S T) :
    Commute y (left x) := by
  obtain ⟨n,a,b,rfl⟩ := fiber_finite_sum S T hy
  apply Commute.sum_left
  intro i _
  have h1 : Commute (left (J := J) (a i).val) (left (J := J) x) :=
    (hx (a i).val (a i).property).map (left (I := I) (J := J))
  have h2 : Commute (right (I := I) (b i).val) (left (J := J) x) :=
    (MatrixTensor.commute x (b i).val).symm
  exact h1.mul_left h2
lemma fiber_commute_right (S : StarSubalgebra ℂ (Mat I)) (T : StarSubalgebra ℂ (Mat J))
    (x : Mat J) (hx : ∀ b∈T,Commute b x) {y : Mat (I×J)} (hy : y∈fiberAlgebra S T) :
    Commute y (right x) := by
  obtain ⟨n,a,b,rfl⟩ := fiber_finite_sum S T hy
  apply Commute.sum_left
  intro i _
  have h1 : Commute (left (J := J) (a i).val) (right (I := I) x) :=
    MatrixTensor.commute (a i).val x
  have h2 : Commute (right (I := I) (b i).val) (right (I := I) x) :=
    (hx (b i).val (b i).property).map (right (I := I) (J := J))
  exact h1.mul_left h2

lemma qFlow_commute_left_left (r : ℝ) (x : Mat I) :
    Commute (qFlow (I := I) (J := J) r : Mat (Four I J)) (left (left (J := J) x)) := by
  apply fiber_commute_left _ _ _ _ (qFlow_mem r)
  rintro a ⟨b,rfl⟩
  exact (MatrixTensor.commute x b).symm
lemma qFlow_commute_right_left (r : ℝ) (x : Mat I) :
    Commute (qFlow (I := I) (J := J) r : Mat (Four I J)) (right (left (J := J) x)) := by
  apply fiber_commute_right _ _ _ _ (qFlow_mem r)
  rintro a ⟨b,rfl⟩
  exact (MatrixTensor.commute x b).symm
lemma pFlow_commute_left_right (r : ℝ) (x : Mat J) :
    Commute (pFlow (I := I) (J := J) r : Mat (Four I J)) (left (right (I := I) x)) := by
  apply fiber_commute_left _ _ _ _ (pFlow_mem r)
  rintro a ⟨b,rfl⟩
  exact MatrixTensor.commute b x
lemma pFlow_commute_right_right (r : ℝ) (x : Mat J) :
    Commute (pFlow (I := I) (J := J) r : Mat (Four I J)) (right (right (I := I) x)) := by
  apply fiber_commute_right _ _ _ _ (pFlow_mem r)
  rintro a ⟨b,rfl⟩
  exact MatrixTensor.commute b x

end MatrixTensor

end

end OAI
