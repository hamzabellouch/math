import Mathlib
import OAI.Probability.UnimodularPercolation.Main
import OAI.Probability.UnimodularPercolation.Cayley.Geometry

namespace OAI

/-! The group Følner criterion and nonamenable Cayley graphs. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u
section GroupGeometry
variable {Λ : Type u} [Group Λ]
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def rightTranslate (A : Finset Λ) (g : Λ) : Finset Λ :=
  A.image (fun x => x * g)

@[simp] lemma card_rightTranslate (A : Finset Λ) (g : Λ) :
    (rightTranslate A g).card = A.card :=
  Finset.card_image_of_injective _ (Equiv.mulRight g).injective

@[simp] lemma rightTranslate_one (A : Finset Λ) : rightTranslate A 1 = A := by
  simp [rightTranslate]

lemma rightTranslate_mul (A : Finset Λ) (g h : Λ) :
    rightTranslate (rightTranslate A g) h = rightTranslate A (g * h) := by
  simp only [rightTranslate, Finset.image_image, Function.comp_def, mul_assoc]

lemma rightTranslate_sdiff (A B : Finset Λ) (g : Λ) :
    rightTranslate (A \ B) g = rightTranslate A g \ rightTranslate B g :=
  Finset.image_sdiff _ _ (Equiv.mulRight g).injective

noncomputable def rightDefect (A : Finset Λ) (g : Λ) : ℕ :=
  (rightTranslate A g \ A).card

omit [Group Λ] in
lemma card_sdiff_triangle (A B C : Finset Λ) :
    (A \ C).card ≤ (A \ B).card + (B \ C).card := by
  apply (Finset.card_le_card (show A \ C ⊆ (A \ B) ∪ (B \ C) from ?_)).trans
    (Finset.card_union_le _ _)
  intro x hx
  simp only [Finset.mem_sdiff, Finset.mem_union] at hx ⊢
  by_cases hb : x ∈ B <;> tauto

lemma rightDefect_mul_le (A : Finset Λ) (g h : Λ) :
    rightDefect A (g * h) ≤ rightDefect A g + rightDefect A h := by
  calc
    rightDefect A (g * h) ≤
        (rightTranslate A (g * h) \ rightTranslate A h).card + rightDefect A h :=
      card_sdiff_triangle _ _ _
    _ = rightDefect A g + rightDefect A h := by
      rw [← rightTranslate_mul, ← rightTranslate_sdiff, card_rightTranslate]
      rfl

@[simp] lemma rightDefect_inv (A : Finset Λ) (g : Λ) :
    rightDefect A g⁻¹ = rightDefect A g := by
  calc
    rightDefect A g⁻¹ = (rightTranslate (rightTranslate A g⁻¹ \ A) g).card :=
      (card_rightTranslate _ _).symm
    _ = (A \ rightTranslate A g).card := by
      rw [rightTranslate_sdiff, rightTranslate_mul, inv_mul_cancel, rightTranslate_one]
    _ = rightDefect A g := Finset.card_sdiff_comm (card_rightTranslate A g).symm

lemma rightDefect_le_boundary (S : Finset Λ)
    (hgen : Subgroup.closure (S : Set Λ) = ⊤) (g : Λ) :
    ∃ n : ℕ, ∀ A : Finset Λ,
      rightDefect A g ≤ n * (vertexBoundary (cayleyGraph S) A).ncard := by
  have hg : g ∈ Subgroup.closure (S : Set Λ) := by rw [hgen]; trivial
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    refine ⟨1, ?_⟩
    intro A
    rw [one_mul]
    change (rightTranslate A g \ A).card ≤ _
    rw [← Set.ncard_coe_finset]
    apply Set.ncard_le_ncard ?_ (finite_vertexBoundary _ (cayley_locallyFinite S) A)
    intro y hy
    obtain ⟨hy, hnot⟩ := Finset.mem_sdiff.mp hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact ⟨hnot, x, hx, cayley_adj_of_mem S x g hg⟩
  | one =>
    exact ⟨0, fun A => by simp [rightDefect]⟩
  | mul g h hg hh ig ih =>
    obtain ⟨n, hn⟩ := ig
    obtain ⟨m, hm⟩ := ih
    refine ⟨n + m, fun A => ?_⟩
    exact (rightDefect_mul_le A g h).trans (by simpa [add_mul] using Nat.add_le_add (hn A) (hm A))
  | inv g hg ig =>
    obtain ⟨n, hn⟩ := ig
    exact ⟨n, fun A => by simpa only [rightDefect_inv] using hn A⟩

lemma cayley_hV_pos (S : Finset Λ) (hgen : Subgroup.closure (S : Set Λ) = ⊤)
    (hna : ¬ AmenableGroup Λ) : 0 < hV (cayleyGraph S) := by
  by_contra hh
  apply hna
  intro K ε hε
  choose n hn using rightDefect_le_boundary S hgen
  let N : ℕ := (∑ g ∈ K, n g) + 1
  have hN : (0 : ℝ) < N := by dsimp [N]; positivity
  have hng (g : Λ) (hg : g ∈ K) : n g ≤ N :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hg).trans (Nat.le_add_right _ _)
  let B : Set ℝ := {r | ∃ A : Finset Λ, A.Nonempty ∧
    r = (vertexBoundary (cayleyGraph S) A).ncard / (A.card : ℝ)}
  have hb : BddBelow B := by
    refine ⟨0, ?_⟩
    rintro r ⟨A, hA, rfl⟩
    positivity
  have hB : B.Nonempty :=
    ⟨_, {1}, Finset.singleton_nonempty 1, rfl⟩
  have hlt : sInf B < ε / N :=
    (le_of_not_gt hh).trans_lt (div_pos hε hN)
  obtain ⟨r, ⟨A, hA, rfl⟩, hr⟩ := (csInf_lt_iff hb hB).mp hlt
  have hAc : (0 : ℝ) < A.card := Nat.cast_pos.mpr hA.card_pos
  have hbound : (N : ℝ) * (vertexBoundary (cayleyGraph S) A).ncard < ε * A.card := by
    have hh := (div_lt_iff₀ hAc).mp hr
    have hh' := mul_lt_mul_of_pos_left hh hN
    have heq : (N : ℝ) * (ε / N * A.card) = ε * A.card := by
      field_simp
    rwa [heq] at hh'
  refine ⟨A, hA, ?_⟩
  intro g hg
  have hd : (rightDefect A g : ℝ) ≤ (N : ℝ) *
      (vertexBoundary (cayleyGraph S) A).ncard := by
    exact_mod_cast (hn g A).trans (Nat.mul_le_mul_right _ (hng g hg))
  exact hd.trans_lt hbound

end GroupGeometry
end Percolation

end OAI
