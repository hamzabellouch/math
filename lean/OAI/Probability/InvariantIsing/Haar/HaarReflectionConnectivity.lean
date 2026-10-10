import OAI.Probability.InvariantIsing.Haar.ReflectionPairPath
import OAI.Probability.InvariantIsing.Haar.ReflectionParity

namespace OAI

/-! Differentiable connection of every special orthogonal matrix to the identity. -/
noncomputable section
open Matrix
namespace InvariantIsing

lemma evenReflectionList_exists_curve {N : ℕ} (l : List (EuclideanSpace ℝ (Fin N)))
    (hl : ∀ v ∈ l, v ≠ 0) (heven : Even l.length) :
    ∃ γ : HaarDifferentiableCurve N,
      (γ.value 0 : Matrix (Fin N) (Fin N) ℝ) =
        rotationMatrix ((l.map hyperplaneReflection).prod) ∧ γ.value 1 = 1 := by
  induction l using List.twoStepInduction with
  | nil =>
    refine ⟨HaarDifferentiableCurve.constant 1,?_,rfl⟩
    simp [HaarDifferentiableCurve.constant]
  | singleton v => simp at heven
  | cons_cons v w l ih _ =>
    have hv := hl v (by simp)
    have hw := hl w (by simp)
    have hl' : ∀ x ∈ l, x ≠ 0 := fun x hx => hl x (by simp [hx])
    have heven' : Even l.length := by
      simpa only [List.length_cons,Nat.even_add_one,Nat.odd_add_one,not_not] using heven
    obtain ⟨γ,hγ0,hγ1⟩ := ih hl' heven'
    obtain ⟨η,hη0,hη1⟩ := reflectionPair_exists_path v w hv hw
    refine ⟨η.mul γ,?_,?_⟩
    · change (η.value 0 : Matrix (Fin N) (Fin N) ℝ)*
        (γ.value 0 : Matrix (Fin N) (Fin N) ℝ) = _
      rw [hη0,hγ0]
      simp only [List.map_cons,List.prod_cons,rotationMatrix_mul,reflectionPair]
      exact mul_assoc _ _ _
    · change η.value 1*γ.value 1 = 1
      rw [hη1,hγ1,mul_one]

theorem specialOrthogonal_exists_differentiableCurve {N : ℕ} (U : SpecialOrthogonal N) :
    ∃ γ : HaarDifferentiableCurve N, γ.value 0 = U ∧ γ.value 1 = 1 := by
  obtain ⟨l,hl,heven,heq⟩ := specialRotation_even_reflections U
  obtain ⟨γ,hγ0,hγ1⟩ := evenReflectionList_exists_curve l hl heven
  refine ⟨γ,?_,hγ1⟩
  apply Subtype.ext
  rw [hγ0,← heq,rotationMatrix_specialRotation]

theorem haarPolynomial_global_oscillation_bound {N : ℕ} (U : SpecialOrthogonal N) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (p : MatrixPolynomial N) (δ : ℝ), 0 ≤ δ →
      (∀ V : SpecialOrthogonal N, haarPolynomialValue (haarPolynomialGamma p p) V ≤ δ^2) →
      |haarPolynomialValue p U-haarPolynomialValue p 1| ≤ K*δ := by
  obtain ⟨γ,hγ0,hγ1⟩ := specialOrthogonal_exists_differentiableCurve U
  obtain ⟨K,hK,hbound⟩ := γ.polynomial_bound
  refine ⟨K,hK,?_⟩
  intro p δ hδ hp
  simpa only [hγ0,hγ1,abs_sub_comm] using hbound p δ hδ hp

end InvariantIsing

end

end OAI
