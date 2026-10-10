import OAI.Analysis.PureInfiniteness.FiniteOneStepReduction
import OAI.Analysis.PureInfiniteness.DoubledCorner

namespace OAI

/-! The finite approximation consequence of KR02 Proposition 7.14. Positive
commuting targets and finite inner approximation suffice; the proof constructs
the single coefficient rather than assuming one-step innerness. -/

noncomputable section
open scoped BigOperators

namespace WeakPureInfiniteness

variable {D E : Type*} [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

omit [PartialOrder D] [StarOrderedRing D] in
lemma norm_apply_le_fourPositiveParts (f : D →L[ℂ] E) (x : D) :
    ‖f x‖ ≤ (‖f (fourPositiveParts x 0)‖ + ‖f (fourPositiveParts x 1)‖) +
      (‖f (fourPositiveParts x 2)‖ + ‖f (fourPositiveParts x 3)‖) := by
  conv_lhs => rw [fourPositiveParts_decomposition x, map_add, map_sub, map_smul, map_sub]
  calc
    _ ≤ ‖f (fourPositiveParts x 0) - f (fourPositiveParts x 1)‖ +
        ‖Complex.I • (f (fourPositiveParts x 2) - f (fourPositiveParts x 3))‖ := norm_add_le _ _
    _ = ‖f (fourPositiveParts x 0) - f (fourPositiveParts x 1)‖ +
        ‖f (fourPositiveParts x 2) - f (fourPositiveParts x 3)‖ := by
      rw [norm_smul, Complex.norm_I, one_mul]
    _ ≤ _ := add_le_add (norm_sub_le _ _) (norm_sub_le _ _)

variable {A : Type*} [NonUnitalCStarAlgebra A]
  (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ) ≤ Filter.atTop)]

local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U

theorem approximately_oneStep_of_abelian_range (hP : MainGap.PropertyP A)
    (T : N →L[ℂ] N) (hT : ApproximatelyInner T)
    (hpos : ∀ x, 0 ≤ x → 0 ≤ T x) (hcomm : ∀ x y, Commute (T x) (T y)) :
    ApproximatelyOneStepInner T := by
  classical
  intro F ε hε
  let I := F × Fin 4
  let b (i : I) := fourPositiveParts i.1.val i.2
  let G := Finset.univ.image b
  obtain ⟨m, d, hd⟩ := hT G (ε / 5) (by positivity)
  obtain ⟨f, hf⟩ := finite_oneStep_reduction U hP (fun i => T (b i)) b
    (fun i => hpos _ (fourPositiveParts_nonneg _ _)) (fun i j => hcomm _ _) m d
  let R : N →L[ℂ] N := ContinuousLinearMap.mulLeftRight ℂ N (star f) f
  have herr (x : F) (j : Fin 4) : ‖(T - R) (fourPositiveParts x.val j)‖ < ε / 5 := by
    have hb : b (x, j) ∈ G := Finset.mem_image.mpr ⟨(x, j), Finset.mem_univ _, rfl⟩
    have he := (hf (x, j)).trans_lt (by
      simpa only [finiteCompression, norm_sub_rev] using hd _ hb)
    change ‖T (b (x, j)) - star f * b (x, j) * f‖ < ε / 5
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
