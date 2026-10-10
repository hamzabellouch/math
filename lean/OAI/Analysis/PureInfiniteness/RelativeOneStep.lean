import OAI.Analysis.PureInfiniteness.OneStepAbelianRange

namespace OAI

/-! The relative-domain form of KR02 Proposition 7.14 needed for the nuclear
subalgebra of the ultrapower. The witnesses lie in the ambient algebra. -/

noncomputable section
open scoped BigOperators

namespace WeakPureInfiniteness

variable {B D : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra D]

/-- Finite inner approximation relative to the specified inclusion. -/
def ApproximatelyInnerAlong (φ : B →⋆ₙₐ[ℂ] D) (T : B → D) : Prop :=
  ∀ (F : Finset B) (ε : ℝ), 0 < ε →
    ∃ n : ℕ, ∃ v : Fin n → D, ∀ b ∈ F,
      ‖T b - ∑ j, star (v j) * φ b * v j‖ < ε

/-- One-coefficient approximation relative to the specified inclusion. -/
def ApproximatelyOneStepAlong (φ : B →⋆ₙₐ[ℂ] D) (T : B → D) : Prop :=
  ∀ (F : Finset B) (ε : ℝ), 0 < ε →
    ∃ d : D, ∀ b ∈ F, ‖T b - star d * φ b * d‖ < ε

lemma ApproximatelyOneStepAlong.of_pointNorm_approximation
    (φ : B →⋆ₙₐ[ℂ] D) (T : B → D)
    (hT : ∀ (F : Finset B) (ε : ℝ), 0 < ε →
      ∃ S : B → D, ApproximatelyOneStepAlong φ S ∧ ∀ b ∈ F, ‖T b - S b‖ < ε) :
    ApproximatelyOneStepAlong φ T := by
  intro F ε hε
  obtain ⟨S, hS, hTS⟩ := hT F (ε / 2) (by positivity)
  obtain ⟨d, hd⟩ := hS F (ε / 2) (by positivity)
  refine ⟨d, fun b hb => ?_⟩
  calc
    _ ≤ ‖T b - S b‖ + ‖S b - star d * φ b * d‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hTS b hb) (hd b hb)
    _ = ε := by ring

variable [PartialOrder B] [StarOrderedRing B]
  {A : Type*} [NonUnitalCStarAlgebra A]
  (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ) ≤ Filter.atTop)]

local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U

/-- The finite one-step reduction applies to any subalgebra inclusion, without
requiring the whole ambient ultrapower to be nuclear or separable. -/
theorem approximately_oneStepAlong_of_abelian_range (hP : MainGap.PropertyP A)
    (φ : B →⋆ₙₐ[ℂ] N) (T : B →L[ℂ] N) (hT : ApproximatelyInnerAlong φ T)
    (hpos : ∀ b, 0 ≤ b → 0 ≤ T b) (hcomm : ∀ b c, Commute (T b) (T c)) :
    ApproximatelyOneStepAlong φ T := by
  classical
  intro F ε hε
  let I := F × Fin 4
  let b (i : I) := fourPositiveParts i.1.val i.2
  let G := Finset.univ.image b
  obtain ⟨m, d, hd⟩ := hT G (ε / 5) (by positivity)
  obtain ⟨f, hf⟩ := finite_oneStep_reduction U hP
    (fun i => T (b i)) (fun i => φ (b i))
    (fun i => hpos _ (fourPositiveParts_nonneg _ _)) (fun i j => hcomm _ _) m d
  let R := innerHomCompression φ f
  have herr (x : F) (j : Fin 4) : ‖(T - R) (fourPositiveParts x.val j)‖ < ε / 5 := by
    have hb : b (x, j) ∈ G := Finset.mem_image.mpr ⟨(x, j), Finset.mem_univ _, rfl⟩
    have he := (hf (x, j)).trans_lt (by simpa only [norm_sub_rev] using hd _ hb)
    change ‖T (b (x, j)) - star f * φ (b (x, j)) * f‖ < ε / 5
    rw [norm_sub_rev]
    exact he
  refine ⟨f, ?_⟩
  intro x hx
  change ‖(T - R) x‖ < ε
  calc
    _ ≤ (‖(T - R) (fourPositiveParts x 0)‖ + ‖(T - R) (fourPositiveParts x 1)‖) +
        (‖(T - R) (fourPositiveParts x 2)‖ + ‖(T - R) (fourPositiveParts x 3)‖) :=
      norm_apply_le_fourPositiveParts (T - R) x
    _ < (ε / 5 + ε / 5) + (ε / 5 + ε / 5) :=
      add_lt_add (add_lt_add (herr ⟨x, hx⟩ 0) (herr ⟨x, hx⟩ 1))
        (add_lt_add (herr ⟨x, hx⟩ 2) (herr ⟨x, hx⟩ 3))
    _ < ε := by linarith

end WeakPureInfiniteness

end

end OAI
