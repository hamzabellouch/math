import OAI.GroupTheory.PolycyclicRecognition.Algebra.RayHalfspace
import OAI.GroupTheory.PolycyclicRecognition.Analysis.MixedWordBoxModel

namespace OAI

/-!
# Strictly positive mixed-word widths in a negative ray halfspace

Inside-ray supports can be negative. A sufficiently large positive
outside support dominates all inside contributions in each word of the
fixed bounded length. This constructs the switch template required for
the ideal-fiber trajectories in `boundary.tex`.
-/

noncomputable section

namespace PolycyclicRecognition

open Set
open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem bracketWordExponent_ge_length_lower
    (s : I → ℝ) (A : ℝ) (hs : ∀ i, -A ≤ s i) (w : FreeMagma I) :
    -(bracketWordLength w : ℝ) * A ≤ bracketWordExponent s w := by
  induction w using FreeMagma.rec with
  | of i => simpa only [bracketWordLength, Nat.cast_one, neg_one_mul, bracketWordExponent_of] using hs i
  | mul u v hu hv =>
    change -((bracketWordLength u + bracketWordLength v : ℕ) : ℝ) * A ≤
      bracketWordExponent s (u * v)
    rw [bracketWordExponent_mul, Nat.cast_add]
    nlinarith

theorem bracketWordExponent_ge_mixed_lower
    (s : I → ℝ) (outside : I → Prop) (A R : ℝ)
    (hs : ∀ i, -A ≤ s i) (hout : ∀ i, outside i → R ≤ s i)
    (w : FreeMagma I) (hw : IsMixedWord outside w) :
    R - ((bracketWordLength w : ℝ) - 1) * A ≤ bracketWordExponent s w := by
  induction w using FreeMagma.rec with
  | of i => simpa only [bracketWordLength, Nat.cast_one, sub_self, zero_mul,
      sub_zero, bracketWordExponent_of] using hout i hw
  | mul u v hu hv =>
    change R - (((bracketWordLength u + bracketWordLength v : ℕ) : ℝ) - 1) * A ≤
      bracketWordExponent s (u * v)
    rw [bracketWordExponent_mul, Nat.cast_add]
    rcases hw with hw | hw
    · have h₁ := hu hw
      have h₂ := bracketWordExponent_ge_length_lower s A hs v
      nlinarith
    · have h₁ := bracketWordExponent_ge_length_lower s A hs u
      have h₂ := hv hw
      nlinarith

/-- A compact negative-height template can have strictly positive width
for every mixed word in the bounded alphabet used for the cone ideal. -/
theorem exists_negative_halfspace_positive_mixed_widths
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (α : V →L[ℝ] ℝ) (β : I → V →L[ℝ] ℝ)
    (v₀ : V) (hα : α v₀ < 0) (hβ : ∀ i, β i ≠ 0) (N : ℕ) :
    ∃ E : Set V, IsCompact E ∧ Convex ℝ E ∧ v₀ ∈ E ∧
      (∀ v ∈ E, α v ≤ α v₀) ∧
      ∀ w : FreeMagma I,
        IsMixedWord (fun i => (β i).toLinearMap ∉ positiveWeightRay α.toLinearMap) w →
        bracketWordLength w ≤ N →
        0 < bracketWordExponent (fun i => sSup (β i '' E)) w := by
  let A := ∑ i, |β i v₀|
  have hA : 0 ≤ A := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hlower (i : I) : -A ≤ β i v₀ := by
    have hh : |β i v₀| ≤ A := Finset.single_le_sum (fun i _ => abs_nonneg (β i v₀)) (Finset.mem_univ i)
    exact (neg_le_neg hh).trans (neg_abs_le _)
  have hβ' (i : I) : (β i).toLinearMap ≠ 0 := by
    intro hi
    apply hβ i
    apply ContinuousLinearMap.ext
    intro v
    exact DFunLike.congr_fun hi v
  obtain ⟨E, hE, hconv, hv₀, hheight, hlarge⟩ := exists_compact_negative_halfspace_template
    α.toLinearMap (fun i => (β i).toLinearMap) v₀ hα hβ' ((N : ℝ) * A + 1)
  refine ⟨E, hE, hconv, hv₀, hheight, ?_⟩
  let s := fun i => sSup (β i '' E)
  have hbdd (i : I) : BddAbove (β i '' E) := (hE.image (β i).continuous).bddAbove
  have hs (i : I) : -A ≤ s i :=
    (hlower i).trans (le_csSup (hbdd i) ⟨v₀, hv₀, rfl⟩)
  have hout (i : I) (hi : (β i).toLinearMap ∉ positiveWeightRay α.toLinearMap) :
      (N : ℝ) * A + 1 ≤ s i := by
    obtain ⟨v, hv, hR⟩ := hlarge i hi
    exact hR.trans (le_csSup (hbdd i) ⟨v, hv, rfl⟩)
  intro w hw hlen
  have hh := bracketWordExponent_ge_mixed_lower s
    (fun i => (β i).toLinearMap ∉ positiveWeightRay α.toLinearMap)
    A ((N : ℝ) * A + 1) hs hout w hw
  have hlen' : (bracketWordLength w : ℝ) ≤ N := Nat.cast_le.mpr hlen
  have hmul := mul_le_mul_of_nonneg_right hlen' hA
  change 0 < bracketWordExponent s w
  nlinarith

end PolycyclicRecognition

end

end OAI
