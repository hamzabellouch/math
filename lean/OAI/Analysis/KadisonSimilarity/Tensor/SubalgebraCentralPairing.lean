import OAI.Analysis.KadisonSimilarity.Tracial.TracialMatrixCenter
import OAI.Analysis.KadisonSimilarity.Tracial.TracialBaseGeometry

namespace OAI

/-! A dense matrix tower determines the pairing of an ambient central
element against the whole subalgebra. The central element need not belong
to that subalgebra. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (D : StarSubalgebra ℂ P)
  [IsClosed (D : Set P)]
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) (G.baseGeometry D).trace (G.baseGeometry D).vector)

include M in
private theorem ambient_central_stage_pairing (c : P)
    (hc : ∀ a : P, a * c = c * a) (j : ℕ) (a : Matrix (I j) (I j) ℂ) :
    G.trace (c * (M.embedding j a : P)) =
      G.trace c * G.trace (M.embedding j a : P) := by
  let F : Matrix (I j) (I j) ℂ →ₗ[ℂ] ℂ :=
    G.trace.comp ((LinearMap.mulLeft ℂ c).comp
      (D.subtype.toLinearMap.comp (M.embedding j).toLinearMap))
  have ht (x y : Matrix (I j) (I j) ℂ) : F (x * y) = F (y * x) := by
    change G.trace (c * (M.embedding j (x * y) : P)) =
      G.trace (c * (M.embedding j (y * x) : P))
    rw [map_mul (M.embedding j) x y, map_mul (M.embedding j) y x]
    change G.trace (c * ((M.embedding j x : P) * (M.embedding j y : P))) =
      G.trace (c * ((M.embedding j y : P) * (M.embedding j x : P)))
    calc
      _ = G.trace ((c * (M.embedding j x : P)) * (M.embedding j y : P)) := by rw [mul_assoc]
      _ = G.trace ((M.embedding j y : P) * (c * (M.embedding j x : P))) := G.tracial _ _
      _ = _ := by rw [← mul_assoc, hc, mul_assoc]
  have h := matrix_tracial_functional F ht a
  have hF1 : F 1 = G.trace c := by
    change G.trace (c * (M.embedding j 1 : P)) = _
    rw [map_one]
    simp only [OneMemClass.coe_one, mul_one]
  rw [hF1] at h
  have hτ := M.trace_embedding j a
  change G.trace (M.embedding j a : P) = _ at hτ
  change G.trace (c * (M.embedding j a : P)) = _ at h
  rw [h, hτ]
  ring

include M in
/-- Central trace pairings factor against the entire matrix-generated
subalgebra, by density of its trace vectors. -/
theorem ambient_central_pairing_of_matrix_tower (c : P)
    (hc : ∀ a : P, a * c = c * a) (d : D) :
    G.trace (c * (d : P)) = G.trace c * G.trace (d : P) := by
  have hs : closure (⋃ j, Set.range (fun a => (G.baseGeometry D).vector (M.embedding j a))) ⊆
      {x : G.baseSpace D |
        inner ℂ (G.vector (star c)) (G.baseInclusion D x) =
          G.trace c * inner ℂ (G.vector 1) (G.baseInclusion D x)} := by
    apply closure_minimal ?_ (isClosed_eq (by fun_prop) (by fun_prop))
    intro x hx
    obtain ⟨j, a, rfl⟩ := Set.mem_iUnion.mp hx
    change inner ℂ (G.vector (star c)) (G.vector (M.embedding j a : P)) =
      G.trace c * inner ℂ (G.vector 1) (G.vector (M.embedding j a : P))
    rw [G.inner_vector, G.inner_vector, star_star, star_one, one_mul]
    exact G.ambient_central_stage_pairing D M c hc j a
  have h := hs (M.dense (G.baseVector D d))
  change inner ℂ (G.vector (star c)) (G.vector (d : P)) =
    G.trace c * inner ℂ (G.vector 1) (G.vector (d : P)) at h
  simpa only [G.inner_vector, star_star, star_one, one_mul] using h

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
