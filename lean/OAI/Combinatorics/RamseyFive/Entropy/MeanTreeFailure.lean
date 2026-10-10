import Mathlib
import OAI.Combinatorics.RamseyFive.Trees.ReachedFailure

namespace OAI

namespace SharpRamseyFive.TreeCodec
open FiniteEntropy BinaryTree
open scoped Classical BigOperators
noncomputable section
local instance (priority := high) meanTreePropDecidable (P : Prop) : Decidable P := Classical.propDecidable P
universe u v w z s
variable {I : Type u} {C : Type v} [Fintype C]
  (Ω : I → C → Type w) [∀ i c, Fintype (Ω i c)]
  (M : ∀ i c, Ω i c → Type z) (left right : ∀ i c t, M i c t → C)
  {Z : Type s} [Fintype Z] (μ : Law Z)
  (enc : Z → ∀ i c t, Option (M i c t))

lemma mean_reached_abort (p : ∀ i c, Law (Ω i c)) (ready : Z → I → C → Prop)
    (ε : I → ℝ) (hε : ∀ i, 0≤ε i)
    (hlocal : ∀ z i c, ready z i c →
      eventMass (p i c) (Finset.univ.filter (fun t => enc z i c t = none)) ≤ ε i)
    (b : BinaryTree I) (c : C) (j : Address b) :
    (∑ z, μ z * eventMass (tapeLaw Ω p b) (Finset.univ.filter (fun ω =>
      abortAt Ω M left right (enc z) b ω c j = some true))) ≤
    (∑ z, μ z * eventMass (tapeLaw Ω p b) (Finset.univ.filter (fun ω => ∃ c',
      contextAt Ω M left right (enc z) b ω c j = some c' ∧ ¬ready z (label b j) c'))) + ε (label b j) := by
  have h := Finset.sum_le_sum (fun z (_ : z∈(Finset.univ : Finset Z)) =>
    mul_le_mul_of_nonneg_left (reached_abort_bound Ω M left right (enc z) p (ready z) ε hε (hlocal z) b c j) (μ.nonneg z))
  simpa only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, μ.sum_one, one_mul] using h

lemma mean_missing_mass (b : BinaryTree I) (p : Law (Tape Ω b)) (c : C) (j : Address b) :
    (∑ z, μ z * eventMass p (Finset.univ.filter (fun ω =>
      successAt Ω M left right (enc z) b ω c j = none))) =
    pathSum b (fun k => ∑ z, μ z * eventMass p (Finset.univ.filter (fun ω =>
      abortAt Ω M left right (enc z) b ω c k = some true))) j := by
  have h (z : Z) := missing_mass_path Ω M left right (enc z) b p c j
  have hh := mean_pathSum μ b (fun z k => eventMass p (Finset.univ.filter (fun ω =>
    abortAt Ω M left right (enc z) b ω c k = some true))) j
  calc
    _ = ∑ z, μ z * pathSum b (fun k => eventMass p (Finset.univ.filter (fun ω =>
        abortAt Ω M left right (enc z) b ω c k = some true))) j := by
      apply Finset.sum_congr rfl
      intro z _
      convert congrArg (fun a : ℝ => μ z*a) (h z) using 1 <;> congr
      funext k
      congr 1
      ext ω
      simp only [Finset.mem_filter]
    _ = _ := hh

lemma mean_missing_mass_le (b : BinaryTree I) (p : Law (Tape Ω b)) (c : C)
    (B : Address b → ℝ)
    (h : ∀ k, (∑ z, μ z*eventMass p (Finset.univ.filter (fun ω =>
      abortAt Ω M left right (enc z) b ω c k = some true))) ≤ B k)
    (j : Address b) :
    (∑ z, μ z*eventMass p (Finset.univ.filter (fun ω =>
      successAt Ω M left right (enc z) b ω c j = none))) ≤ pathSum b B j := by
  rw [mean_missing_mass]
  exact pathSum_mono b _ _ h j
end
end SharpRamseyFive.TreeCodec

end OAI
