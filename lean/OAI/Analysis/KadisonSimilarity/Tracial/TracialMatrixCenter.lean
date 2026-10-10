import OAI.Analysis.KadisonSimilarity.Tracial.MatrixTraceUniqueness
import OAI.Analysis.KadisonSimilarity.Derivation.TracialCornerCyclicity
import OAI.Analysis.KadisonSimilarity.Tracial.TracialMatrixTower

namespace OAI

/-! Density of full matrix stages forces the center of the original
faithful tracial algebra to be scalar. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H)
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) G.trace G.vector)

include M in
private theorem central_stage_pairing (c : P)
    (hc : ∀ a : P, a * c = c * a) (j : ℕ) (a : Matrix (I j) (I j) ℂ) :
    G.trace (c * M.embedding j a) = G.trace c * G.trace (M.embedding j a) := by
  let F : Matrix (I j) (I j) ℂ →ₗ[ℂ] ℂ :=
    G.trace.comp ((LinearMap.mulLeft ℂ c).comp (M.embedding j).toLinearMap)
  have ht (x y : Matrix (I j) (I j) ℂ) : F (x * y) = F (y * x) := by
    change G.trace (c * M.embedding j (x * y)) = G.trace (c * M.embedding j (y * x))
    rw [map_mul (M.embedding j) x y, map_mul (M.embedding j) y x]
    calc
      _ = G.trace ((c * M.embedding j x) * M.embedding j y) := by rw [mul_assoc]
      _ = G.trace (M.embedding j y * (c * M.embedding j x)) := G.tracial _ _
      _ = _ := by rw [← mul_assoc, hc, mul_assoc]
  have h := matrix_tracial_functional F ht a
  change G.trace (c * M.embedding j a) =
    (Fintype.card (I j) : ℂ)⁻¹ * G.trace (c * M.embedding j 1) * Matrix.trace a at h
  rw [map_one, mul_one] at h
  rw [h, M.trace_embedding]
  ring

include M in
/-- No nonscalar central element survives density of the full matrix stages. -/
theorem central_eq_trace_smul_one (hf : Function.Injective G.vector)
    (c : P) (hc : ∀ a : P, a * c = c * a) : c = G.trace c • (1 : P) := by
  apply hf
  rw [map_smul]
  apply ext_inner_left ℂ
  intro ξ
  have hs : closure (⋃ j, Set.range (fun a => G.vector (M.embedding j a))) ⊆
      {η | inner ℂ η (G.vector c) = inner ℂ η (G.trace c • G.vector 1)} := by
    apply closure_minimal ?_ (isClosed_eq (by fun_prop) (by fun_prop))
    intro η hη
    obtain ⟨j, a, rfl⟩ := Set.mem_iUnion.mp hη
    change inner ℂ (G.vector (M.embedding j a)) (G.vector c) = _
    rw [inner_smul_right, G.inner_vector, G.inner_vector, mul_one, G.tracial]
    simpa only [map_star] using G.central_stage_pairing M c hc j (star a)
  exact hs (M.dense ξ)

include M in
theorem scalar_center_of_matrix_tower (hf : Function.Injective G.vector) :
    ∀ c : P, (∀ a : P, a * c = c * a) → ∃ z : ℂ, c = z • (1 : P) := by
  intro c hc
  exact ⟨G.trace c, G.central_eq_trace_smul_one M hf c hc⟩

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
