import OAI.Analysis.KadisonKastler.VectorStateTracialRepresentation

namespace OAI

/-! # The faithful vector trace on a centralizing matrix closure

Finite strong approximation transfers the centralizer identity from the
matrix stages to their generated algebra. No trace on the ambient algebra
is used.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

/-- Centrality of the vector functional passes to the generated matrix algebra. -/
theorem matrixClosure_vector_centralizes
    (A : ℕ → FiniteMatrixStage M)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra)) (Ω : H)
    (hcentral : ∀ n a, a ∈ (A n).units.concreteAlgebra → ∀ x : Algebra M,
      inner ℂ Ω ((a * x.val) Ω) = inner ℂ Ω ((x.val * a) Ω))
    (r : Algebra (FiniteMatrixStage.generatedVonNeumann A)) (x : Algebra M) :
    inner ℂ Ω ((r.val * x.val) Ω) = inner ℂ Ω ((x.val * r.val) Ω) := by
  classical
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  let C : ℝ := ‖Ω‖ + ‖star x.val Ω‖
  have hC : 0 ≤ C := add_nonneg (norm_nonneg _) (norm_nonneg _)
  let δ : ℝ := ε / (C + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨n,a,ha⟩ := FiniteMatrixStage.exists_stage_strong_approximation A hA r
    {Ω, x.val Ω} δ hδ
  have hΩ := ha Ω (Finset.mem_insert_self _ _)
  have hx := ha (x.val Ω) (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hc := hcentral n a.val a.property x
  have he : inner ℂ Ω ((r.val * x.val) Ω) - inner ℂ Ω ((x.val * r.val) Ω) =
      inner ℂ Ω (r.val (x.val Ω) - a.val (x.val Ω)) -
        inner ℂ (star x.val Ω) (r.val Ω - a.val Ω) := by
    simp only [inner_sub_right, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left, mul_apply_eq_comp] at hc ⊢
    rw [hc]
    ring
  rw [he, zero_add]
  calc
    _ ≤ ‖inner ℂ Ω (r.val (x.val Ω) - a.val (x.val Ω))‖ +
        ‖inner ℂ (star x.val Ω) (r.val Ω - a.val Ω)‖ := norm_sub_le _ _
    _ ≤ ‖Ω‖ * ‖r.val (x.val Ω) - a.val (x.val Ω)‖ +
        ‖star x.val Ω‖ * ‖r.val Ω - a.val Ω‖ :=
      add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ ‖Ω‖ * δ + ‖star x.val Ω‖ * δ :=
      add_le_add (mul_le_mul_of_nonneg_left hx.le (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hΩ.le (norm_nonneg _))
    _ = C * δ := by dsimp [C]; ring
    _ ≤ ε := by
      have hd : (C + 1) * δ = ε := by
        dsimp [δ]
        exact mul_div_cancel₀ _ (by positivity)
      nlinarith

/-- A faithful unit vector which is tracial on an algebra gives its faithful trace. -/
def faithfulVectorTrace (N : VonNeumannAlgebra H) (Ω : H) (hΩ : ‖Ω‖ = 1)
    (hsep : ∀ a : Algebra N, a.val Ω = 0 → a = 0)
    (htr : ∀ a b : Algebra N,
      inner ℂ Ω ((a * b).val Ω) = inner ℂ Ω ((b * a).val Ω)) :
    FaithfulTracialState (Algebra N) where
  toLinearMap := {
    toFun := fun a => inner ℂ Ω (a.val Ω)
    map_add' := fun a b => inner_add_right _ _ _
    map_smul' := fun c a => inner_smul_right _ _ _ }
  map_one := by
    change inner ℂ Ω Ω = 1
    exact inner_self_eq_one_of_norm_eq_one hΩ
  positive a := by
    change 0 ≤ (inner ℂ Ω (star a.val (a.val Ω))).re
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
    exact inner_self_nonneg (𝕜 := ℂ) (x := a.val Ω)
  positive_im a := by
    change (inner ℂ Ω (star a.val (a.val Ω))).im = 0
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
    exact inner_self_im (𝕜 := ℂ) (a.val Ω)
  faithful a ha := by
    change inner ℂ Ω (star a.val (a.val Ω)) = 0 at ha
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right] at ha
    exact hsep a (inner_self_eq_zero.mp ha)
  tracial := htr

/-- The trace on the closure is the restriction of the given faithful vector state. -/
def matrixClosureVectorTrace
    (A : ℕ → FiniteMatrixStage M)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra)) (Ω : H) (hΩ : ‖Ω‖ = 1)
    (hsep : ∀ a : Algebra M, a.val Ω = 0 → a = 0)
    (hcentral : ∀ n a, a ∈ (A n).units.concreteAlgebra → ∀ x : Algebra M,
      inner ℂ Ω ((a * x.val) Ω) = inner ℂ Ω ((x.val * a) Ω)) :
    FaithfulTracialState (Algebra (FiniteMatrixStage.generatedVonNeumann A)) :=
  faithfulVectorTrace _ Ω hΩ
    (fun a ha => Subtype.ext (show a.val = (0 : H →L[ℂ] H) from
      congrArg (fun b : Algebra M => b.val)
        (hsep (coordinateInclusion (FiniteMatrixStage.generatedVonNeumann_le A) a) ha)))
    (fun a b => matrixClosure_vector_centralizes A hA Ω hcentral a
      (coordinateInclusion (FiniteMatrixStage.generatedVonNeumann_le A) b))

@[simp] theorem matrixClosureVectorTrace_apply
    (A : ℕ → FiniteMatrixStage M)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra)) (Ω : H) (hΩ : ‖Ω‖ = 1)
    (hsep : ∀ a : Algebra M, a.val Ω = 0 → a = 0)
    (hcentral : ∀ n a, a ∈ (A n).units.concreteAlgebra → ∀ x : Algebra M,
      inner ℂ Ω ((a * x.val) Ω) = inner ℂ Ω ((x.val * a) Ω))
    (a : Algebra (FiniteMatrixStage.generatedVonNeumann A)) :
    (matrixClosureVectorTrace A hA Ω hΩ hsep hcentral).toLinearMap a =
      inner ℂ Ω (a.val Ω) := rfl

end

end KadisonKastler

end OAI
