import OAI.Analysis.KadisonKastler.UnitaryBounds
import OAI.Analysis.KadisonKastler.Algebra
import OAI.Analysis.KadisonKastler.BoundaryImprovement

namespace OAI

/-! # The linear map determined by unitary trace vectors

Once every unitary vector has a unitary image, the four-unitary
decomposition constructs a map on the whole algebra. A separating
embedding proves linearity and the quantitative operator-norm bound.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {A B E : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [AddCommGroup E] [Module ℂ E]

/-- A linear map on trace vectors extends to an actual algebra-valued
linear map if it sends every unitary vector to a unitary vector. -/
theorem exists_linear_map_of_unitary_vectors
    (J : A →ₗ[ℂ] E) (K : B →ₗ[ℂ] E) (hK : Function.Injective K)
    (S : E →ₗ[ℂ] E)
    (hU : ∀ u : unitary A, ∃ v : unitary B, K v = S (J u)) :
    ∃ θ : A →ₗ[ℂ] B,
      (∀ a, K (θ a) = S (J a)) ∧ (∀ u : unitary A, θ u ∈ unitary B) := by
  classical
  have hmem (a : A) : ∃ b : B, K b = S (J a) := by
    obtain ⟨u, c, ha, _⟩ := CStarAlgebra.exists_sum_four_unitary a
    choose v hv using fun i => hU (u i)
    refine ⟨∑ i, c i • (v i : B), ?_⟩
    rw [ha]
    simp only [map_sum, map_smul, hv]
  choose T hT using hmem
  let θ : A →ₗ[ℂ] B :=
    { toFun := T
      map_add' := by
        intro a b
        apply hK
        simp only [hT, map_add]
      map_smul' := by
        intro c a
        apply hK
        simp only [hT, map_smul, RingHom.id_apply] }
  refine ⟨θ, hT, ?_⟩
  intro u
  obtain ⟨v, hv⟩ := hU u
  have he : θ u = (v : B) := hK ((hT u).trans hv.symm)
  rw [he]
  exact v.property

/-- A linear map preserving unitaries is automatically bounded. -/
def continuousLinearMapOfUnitaryImages
    (θ : A →ₗ[ℂ] B) (hθ : ∀ u : unitary A, θ u ∈ unitary B) : A →L[ℂ] B :=
  θ.mkContinuous 2 (fun a => by
    have h := norm_le_twice_unitary_bound θ
      (fun u => norm_unitary_le_one (⟨θ u, hθ u⟩ : unitary B)) a
    simpa only [mul_one] using h)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M N : VonNeumannAlgebra H}

/-- The unitary approximation bound extends to all algebra elements,
with the factor two from the four-unitary decomposition. -/
theorem linear_transfer_norm_sub_le
    (θ : Algebra M →ₗ[ℂ] Algebra N) {C : ℝ}
    (hθ : ∀ u : unitary (Algebra M),
      ‖(θ u : H →L[ℂ] H) - (u : Algebra M)‖ ≤ C) (a : Algebra M) :
    ‖(θ a : H →L[ℂ] H) - (a : H →L[ℂ] H)‖ ≤ 2 * C * ‖a‖ := by
  let F : Algebra M →ₗ[ℂ] (H →L[ℂ] H) :=
    N.toStarSubalgebra.subtype.toLinearMap.comp θ - M.toStarSubalgebra.subtype.toLinearMap
  exact norm_le_twice_unitary_bound F hθ a

/-- The transferred algebra map is bounded as soon as its unitary
images are uniformly close to the original unitaries. -/
def continuousLinearTransfer
    (θ : Algebra M →ₗ[ℂ] Algebra N) {C : ℝ}
    (hθ : ∀ u : unitary (Algebra M),
      ‖(θ u : H →L[ℂ] H) - (u : Algebra M)‖ ≤ C) :
    Algebra M →L[ℂ] Algebra N :=
  θ.mkContinuous (1 + 2 * C) (fun a => by
    have h := linear_transfer_norm_sub_le θ hθ a
    have ht := norm_add_le ((θ a : H →L[ℂ] H) - a) (a : H →L[ℂ] H)
    rw [sub_add_cancel] at ht
    change ‖(θ a : H →L[ℂ] H)‖ ≤ _
    calc
      _ ≤ ‖(θ a : H →L[ℂ] H) - a‖ + ‖a‖ := ht
      _ ≤ 2 * C * ‖a‖ + ‖a‖ := add_le_add h le_rfl
      _ = _ := by ring)

end

end KadisonKastler

end OAI
