import OAI.GroupTheory.PolycyclicRecognition.Algebra.HomogeneousWordProjection

namespace OAI

/-! # Finite right-nested coefficients of homogeneous primitive words -/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators

variable {n d : ℕ}

def wordOfFn (w : Fin d → Fin n) : FreeMonoid (Fin n) :=
  FreeMonoid.ofList (List.ofFn w)

theorem wordOfFn_injective : Function.Injective (wordOfFn : (Fin d → Fin n) → _) := by
  intro f g h
  apply List.ofFn_injective
  exact congrArg FreeMonoid.toList h

theorem exists_wordOfFn_of_length (w : FreeMonoid (Fin n)) (h : w.length = d) :
    ∃ f : Fin d → Fin n, wordOfFn f = w := by
  change w.toList.length = d at h
  subst d
  exact ⟨w.toList.get, congrArg FreeMonoid.ofList (List.ofFn_get _)⟩

theorem wordLieProjection_homogeneous {A : Type*} [Ring A] [Algebra ℚ A]
    (X : Fin n → A) (p : RationalWords n) (hp : IsHomogeneousRationalWord p d) :
    wordLieProjection X p = ∑ w : Fin d → Fin n,
      p.coeff (wordOfFn w) • wordRightLie X (List.ofFn w) := by
  classical
  let s : Finset (FreeMonoid (Fin n)) := Finset.univ.image (wordOfFn (d := d))
  have hs : p.coeff ∈ Finsupp.supported ℚ ℚ (↑s : Set (FreeMonoid (Fin n))) := by
    rw [Finsupp.mem_supported]
    intro w hw
    obtain ⟨f, rfl⟩ := exists_wordOfFn_of_length w (hp w (Finsupp.mem_support_iff.mp hw))
    exact Finset.mem_image.mpr ⟨f, Finset.mem_univ _, rfl⟩
  change Finsupp.linearCombination ℚ (fun w => wordRightLie X w.toList) p.coeff = _
  rw [Finsupp.linearCombination_apply_of_mem_supported ℚ hs]
  dsimp [s]
  rw [Finset.sum_image]
  · rfl
  · intro f _ g _ h
    exact wordOfFn_injective h

attribute [local instance 100] LieRing.ofAssociativeRing

theorem wordRightLie_ofFn {A : Type*} [Ring A] [Algebra ℚ A]
    (X : Fin n → A) (d : ℕ) (w : Fin (d + 1) → Fin n) :
    wordRightLie X (List.ofFn w) = evalBracketWord X (rightNestedWord d w) := by
  induction d with
  | zero => simp [List.ofFn_succ, wordRightLie, rightNestedWord]
  | succ d ih =>
    rw [List.ofFn_succ]
    have htail : List.ofFn (fun i => w i.succ) ≠ [] := by
      intro h
      have := congrArg List.length h
      simp at this
    cases h : List.ofFn (fun i => w i.succ) with
    | nil => exact (htail h).elim
    | cons i l =>
      change X (w 0) * wordRightLie X (i :: l) -
        wordRightLie X (i :: l) * X (w 0) = _
      rw [← h, ih]
      rfl

theorem primitive_word_finite_expansion {A : Type*} [Ring A] [Algebra ℚ A]
    (X : Fin n → A) (p : RationalWords n) (hp : IsPrimitiveRationalWord p)
    (hd : IsHomogeneousRationalWord p (d + 1)) :
    rationalWordEvaluation X p = ∑ w : Fin (d + 1) → Fin n,
      ((d + 1 : ℚ)⁻¹ * p.coeff (wordOfFn w)) •
        evalBracketWord X (rightNestedWord d w) := by
  have hc : (d + 1 : ℚ) ≠ 0 := by positivity
  calc
    rationalWordEvaluation X p = (d + 1 : ℚ)⁻¹ • wordLieProjection X p := by
      rw [primitive_homogeneous_word_projection X hp hd, smul_smul]
      simp [hc]
    _ = _ := by
      rw [wordLieProjection_homogeneous X p hd, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro w _
      rw [smul_smul, wordRightLie_ofFn]

end PolycyclicRecognition

end

end OAI
