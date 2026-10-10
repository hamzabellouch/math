import OAI.Analysis.KadisonSimilarity.FreeProduct.EvenAlternatingWords
import OAI.Analysis.KadisonSimilarity.Tracial.TracialMomentContinuity
import Mathlib.Algebra.Star.UnitaryStarAlgAut

namespace OAI

/-! Integer mixed moments imply freeness of a conjugated subalgebra. -/

noncomputable section
namespace KadisonSimilarity
open HochschildPatching

variable {B C : Type*} [CStarAlgebra B] [CStarAlgebra C]

private def conjugateMomentTail : List (B × B) → List (IntAtom B)
  | [] => [(-1, none)]
  | (a, b) :: v => (-1, some a) :: (1, some b) :: conjugateMomentTail v

omit [CStarAlgebra B] in
private lemma conjugateMomentTail_admissible (v : List (B × B)) :
    admissibleIntTail (conjugateMomentTail v) := by
  induction v with
  | nil => exact ⟨by simp [conjugateMomentTail], by simp [conjugateMomentTail]⟩
  | cons p v ih => exact intTail_cons (intTail_cons ih 1 p.2) (-1) p.1

omit [CStarAlgebra B] in
private lemma conjugateMomentTail_nonzero (v : List (B × B)) :
    ∀ b ∈ conjugateMomentTail v, b.1 ≠ 0 := by
  induction v with
  | nil => simp [conjugateMomentTail]
  | cons p v ih =>
    intro b hb
    simp only [conjugateMomentTail, List.mem_cons] at hb
    rcases hb with rfl | rfl | hb
    · norm_num
    · norm_num
    · exact ih b hb

private def conjugateMomentBlock (F : B → C) (u : unitary C) (p : B × B) : C :=
  F p.1 * (u : C) * F p.2 * star (u : C)

omit [CStarAlgebra B] in
private lemma conjugateMomentTail_eval (F : B → C) (u : unitary C) (v : List (B × B)) :
    ((conjugateMomentTail v).map (fun b => ((u ^ b.1 : unitary C) : C) * wordCoeff F b.2)).prod =
      star (u : C) * (v.map (conjugateMomentBlock F u)).prod := by
  induction v with
  | nil => simp [conjugateMomentTail, wordCoeff, ← Unitary.star_eq_inv]
  | cons p v ih =>
    simp only [conjugateMomentTail, List.map_cons, List.prod_cons, wordCoeff_some,
      zpow_neg_one, zpow_one, ← Unitary.star_eq_inv, Unitary.coe_star, ih,
      conjugateMomentBlock, mul_assoc]

omit [CStarAlgebra B] in
private lemma conjugate_blocks_zero (σ : C →ₗ[ℂ] ℂ) (F : B → C) (u : unitary C)
    (hm : ∀ a : Option B, ∀ l : List (IntAtom B), admissibleIntTail l →
      (∀ b ∈ l, b.1 ≠ 0) → σ (integerEval F u a l) = 0)
    (p : B × B) (v : List (B × B)) :
    σ (((p :: v).map (conjugateMomentBlock F u)).prod) = 0 := by
  have hz := hm (some p.1) ((1, some p.2) :: conjugateMomentTail v)
    (intTail_cons (conjugateMomentTail_admissible v) 1 p.2) (by
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · norm_num
      · exact conjugateMomentTail_nonzero v b hb)
  simpa only [integerEval, List.map_cons, List.prod_cons, wordCoeff_some, zpow_one,
    conjugateMomentTail_eval, conjugateMomentBlock, mul_assoc] using hz

variable (σ : C →ₗ[ℂ] ℂ) (h1 : σ 1 = 1)
  (tr : ∀ a b, σ (a * b) = σ (b * a)) (φ : B →⋆ₐ[ℂ] C) (u : unitary C)

include tr in
private lemma trace_conjugation (b : C) :
    σ ((u : C) * b * star (u : C)) = σ b := by
  rw [tr, ← mul_assoc, Unitary.coe_star_mul_self, one_mul]

include tr in
private lemma even_conjugate_blocks (xs : List C)
    (hw : AlternatingCenteredWord σ φ.range
      (((Unitary.conjStarAlgAut ℂ C u).toStarAlgHom).comp φ).range true xs)
    (he : xs.length % 2 = 0) :
    ∃ v : List (B × B), xs.prod =
      (v.map (conjugateMomentBlock (fun b => φ b - σ (φ b) • 1) u)).prod ∧
      xs.length = 2 * v.length := by
  induction xs using List.twoStepInduction with
  | nil => exact ⟨[], rfl, rfl⟩
  | singleton x => simp at he
  | cons_cons x y xs ih _ =>
    cases hw with
    | cons hx hx0 ht =>
      cases ht with
      | cons hy hy0 ht =>
        obtain ⟨a, ha⟩ := hx
        obtain ⟨b, hb⟩ := hy
        have hb' : (u : C) * φ b * star (u : C) = y := hb
        have hta : σ (φ a) = 0 := ha ▸ hx0
        have htb : σ (φ b) = 0 := by
          rw [← trace_conjugation σ tr u, hb']
          exact hy0
        obtain ⟨v, hv, hn⟩ := ih (by simpa only [Bool.not_not] using ht) (by
          simp only [List.length_cons] at he
          omega)
        refine ⟨(a, b) :: v, ?_, ?_⟩
        · simp only [List.prod_cons, List.map_cons, conjugateMomentBlock, hta, htb,
            zero_smul, sub_zero, ← ha, ← hb', hv, mul_assoc]
          rfl
        · simp only [List.length_cons, hn]
          omega

include h1 tr in
/-- The only moments needed for conjugate freeness are words with nonzero
integer powers and centered coefficients in the original algebra. -/
theorem scalarFree_conjugate_of_integer_moments
    (hm : ∀ a : Option B, ∀ l : List (IntAtom B), admissibleIntTail l →
      (∀ b ∈ l, b.1 ≠ 0) →
      σ (integerEval (fun b => φ b - σ (φ b) • 1) u a l) = 0) :
    ScalarFree σ φ.range
      (((Unitary.conjStarAlgAut ℂ C u).toStarAlgHom).comp φ).range := by
  apply scalarFree_of_even_cyclic h1 tr
  intro x xs hw he
  obtain ⟨v, hv, hn⟩ := even_conjugate_blocks σ tr φ u (x :: xs) hw he
  have hvne : v ≠ [] := by
    intro h
    simp only [h, List.length_nil, mul_zero, List.length_cons] at hn
    omega
  obtain ⟨p, w, rfl⟩ := List.exists_cons_of_ne_nil hvne
  rw [hv]
  exact conjugate_blocks_zero σ _ u hm p w

end KadisonSimilarity

end

end OAI
