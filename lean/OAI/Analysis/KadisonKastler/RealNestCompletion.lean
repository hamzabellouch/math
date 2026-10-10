import OAI.Analysis.KadisonKastler.FiniteNestCompletion
import OAI.Analysis.FactorGeneration.OperatorLimits
import Mathlib.Data.Finset.Sort

namespace OAI

/-! # Simultaneous contractive completion along a real-indexed nest

Finite chains are completed explicitly. A bounded weak operator limit over
finite subsets imposes all the prescribed lower corners at once.
-/

namespace KadisonKastler

open Filter Generator.Tracial
open scoped Topology InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem finite_real_nest_completion
    (P : ℝ → H →L[ℂ] H) (hP : ∀ a, IsStarProjection (P a))
    (hmono : ∀ a b, a ≤ b → P a * P b = P a)
    (T : H →L[ℂ] H) (hT : ∀ a, ‖(1 - P a) * T * P a‖ ≤ 1)
    (s : Finset ℝ) :
    ∃ X : H →L[ℂ] H, ‖X‖ ≤ 1 ∧
      ∀ a ∈ s, (1 - P a) * X * P a = (1 - P a) * T * P a := by
  classical
  let L := (s.sort (· ≤ ·)).map P
  have hchain : L.Pairwise (fun Q R => Q * R = Q) :=
    List.pairwise_map.mpr ((s.pairwise_sort (· ≤ ·)).imp (fun hab => hmono _ _ hab))
  have hdata : ∀ R ∈ L, IsStarProjection R ∧ ‖(1 - R) * T * R‖ ≤ 1 := by
    rintro R hR
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hR
    exact ⟨hP a, hT a⟩
  obtain ⟨X, hX, hfix⟩ := finite_projection_chain_completion T L hchain hdata
  refine ⟨X, hX, ?_⟩
  intro a ha
  exact hfix (P a) (List.mem_map.mpr ⟨a, (s.mem_sort (· ≤ ·)).mpr ha, rfl⟩)

theorem real_nest_contractive_completion
    (P : ℝ → H →L[ℂ] H) (hP : ∀ a, IsStarProjection (P a))
    (hmono : ∀ a b, a ≤ b → P a * P b = P a)
    (T : H →L[ℂ] H) (hT : ∀ a, ‖(1 - P a) * T * P a‖ ≤ 1) :
    ∃ X : H →L[ℂ] H, ‖X‖ ≤ 1 ∧
      ∀ a, (1 - P a) * X * P a = (1 - P a) * T * P a := by
  classical
  choose X hX hfix using finite_real_nest_completion P hP hmono T hT
  let ω := Ultrafilter.of (atTop : Filter (Finset ℝ))
  obtain ⟨Y, hY, ht⟩ := exists_weak_operator_ultralimit ω X 1 zero_le_one hX
  refine ⟨Y, hY, ?_⟩
  intro a
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  let Q := 1 - P a
  change inner ℂ y (Q (Y (P a x))) = inner ℂ y (Q (T (P a x)))
  rw [← Q.adjoint_inner_left, ← Q.adjoint_inner_left]
  have he : ∀ᶠ s : Finset ℝ in (ω : Filter (Finset ℝ)),
      (1 - P a) * X s * P a = (1 - P a) * T * P a := by
    apply (show (ω : Filter (Finset ℝ)) ≤ atTop from Ultrafilter.of_le atTop)
    exact Filter.eventually_atTop.mpr ⟨{a}, fun s hs => hfix s a (hs (by simp))⟩
  have heq : ∀ᶠ s : Finset ℝ in (ω : Filter (Finset ℝ)),
      inner ℂ (Q.adjoint y) (X s (P a x)) = inner ℂ (Q.adjoint y) (T (P a x)) := by
    filter_upwards [he] with s hs
    rw [Q.adjoint_inner_left, Q.adjoint_inner_left]
    exact congrArg (fun S : H →L[ℂ] H => inner ℂ y (S x)) hs
  exact tendsto_nhds_unique (ht (P a x) (Q.adjoint y))
    (tendsto_const_nhds.congr' (Filter.EventuallyEq.symm heq))

end

end KadisonKastler

end OAI
