import OAI.Analysis.KadisonKastler.PointedMatrixProduct
import Mathlib.Data.List.Nodup

namespace OAI

/-! # Repeated words in commuting matrix sites

The reduction below is independent of the representation: it gathers each
site into one matrix entry and records incompatible matrix indices by zero.
-/

namespace KadisonKastler

open Generator

abbrev MatrixSiteLetter (I : Type*) := I × Fin 2 × Fin 2
abbrev MatrixSiteWord (I : Type*) := List (MatrixSiteLetter I)

namespace MatrixSiteWord

variable {I J A : Type*}

def reindex (e : I ≃ J) (w : MatrixSiteWord I) : MatrixSiteWord J :=
  w.map fun a => (e a.1, a.2.1, a.2.2)

def star (w : MatrixSiteWord I) : MatrixSiteWord I :=
  w.reverse.map fun a => (a.1, a.2.2, a.2.1)

def indices (w : MatrixSiteWord I) : List I := w.map Prod.fst

@[simp] theorem reindex_nil (e : I ≃ J) : reindex e [] = [] := rfl

@[simp] theorem reindex_cons (e : I ≃ J) (a : MatrixSiteLetter I) (w : MatrixSiteWord I) :
    reindex e (a :: w) = (e a.1, a.2.1, a.2.2) :: reindex e w := rfl

@[simp] theorem reindex_append (e : I ≃ J) (w v : MatrixSiteWord I) :
    reindex e (w ++ v) = reindex e w ++ reindex e v := by
  simp only [reindex, List.map_append]

@[simp] theorem reindex_star (e : I ≃ J) (w : MatrixSiteWord I) :
    reindex e (star w) = star (reindex e w) := by
  simp only [reindex, star, List.map_reverse, List.map_map, Function.comp_def]

variable [Ring A] [StarRing A] [_root_.Algebra ℂ A]

def eval (E : I → MatrixUnitSystem (Fin 2) A) (w : MatrixSiteWord I) : A :=
  (w.map fun a => (E a.1).entry a.2.1 a.2.2).prod

@[simp] theorem eval_nil (E : I → MatrixUnitSystem (Fin 2) A) : eval E [] = 1 := rfl

@[simp] theorem eval_cons (E : I → MatrixUnitSystem (Fin 2) A)
    (a : MatrixSiteLetter I) (w : MatrixSiteWord I) :
    eval E (a :: w) = (E a.1).entry a.2.1 a.2.2 * eval E w := rfl

@[simp] theorem eval_append (E : I → MatrixUnitSystem (Fin 2) A)
    (w v : MatrixSiteWord I) : eval E (w ++ v) = eval E w * eval E v := by
  simp only [eval, List.map_append, List.prod_append]

@[simp] theorem eval_reindex (E : J → MatrixUnitSystem (Fin 2) A)
    (e : I ≃ J) (w : MatrixSiteWord I) :
    eval E (reindex e w) = eval (E ∘ e) w := by
  simp only [eval, reindex, List.map_map, Function.comp_def]

@[simp] theorem eval_star (E : I → MatrixUnitSystem (Fin 2) A)
    (w : MatrixSiteWord I) : eval E (star w) = Star.star (eval E w) := by
  induction w with
  | nil => simp [star]
  | cons a w ih =>
    have he : star (a :: w) = star w ++ [(a.1, a.2.2, a.2.1)] := by
      simp [star, List.reverse_cons]
    rw [he, eval_append, ih]
    simp only [eval_cons, eval_nil, mul_one, star_mul, (E a.1).star_entry]

section Reduction

variable [DecidableEq I]

/-- Insert a matrix entry into a word with distinct sites. -/
def insert (a : MatrixSiteLetter I) : MatrixSiteWord I → Option (MatrixSiteWord I)
  | [] => some [a]
  | b :: w =>
    if a.1 = b.1 then
      if a.2.2 = b.2.1 then some ((a.1, a.2.1, b.2.2) :: w) else none
    else (insert a w).map (List.cons b)

/-- The canonical distinct-site reduction; `none` denotes zero. -/
def reduce : MatrixSiteWord I → Option (MatrixSiteWord I)
  | [] => some []
  | a :: w => (reduce w).bind (insert a)

def evalOption (E : I → MatrixUnitSystem (Fin 2) A)
    (w : Option (MatrixSiteWord I)) : A := w.elim 0 (eval E)

omit [DecidableEq I] in
private theorem evalOption_map_cons (E : I → MatrixUnitSystem (Fin 2) A)
    (a : MatrixSiteLetter I) (w : Option (MatrixSiteWord I)) :
    evalOption E (w.map (List.cons a)) =
      (E a.1).entry a.2.1 a.2.2 * evalOption E w := by
  cases w <;> simp [evalOption]

theorem evalOption_insert (E : I → MatrixUnitSystem (Fin 2) A)
    (hE : ∀ i j, i ≠ j → ∀ a b c d,
      Commute ((E i).entry a b) ((E j).entry c d))
    (a : MatrixSiteLetter I) (w : MatrixSiteWord I) :
    evalOption E (insert a w) = (E a.1).entry a.2.1 a.2.2 * eval E w := by
  induction w with
  | nil => simp [insert, evalOption]
  | cons b w ih =>
    by_cases hij : a.1 = b.1
    · by_cases hbc : a.2.2 = b.2.1
      · simp only [insert, hij, hbc, ite_true, evalOption, Option.elim_some, eval_cons]
        rw [← mul_assoc, ← hij, (E a.1).mul_entry]
        simp only [ite_true]
      · simp only [insert, hij, hbc, ite_true, ite_false, evalOption,
          Option.elim_none, eval_cons]
        rw [← mul_assoc, ← hij, (E a.1).mul_entry]
        simp only [hbc, ite_false, zero_mul]
    · simp only [insert, hij, ite_false]
      rw [evalOption_map_cons, ih, eval_cons, ← mul_assoc,
        ← (hE a.1 b.1 hij a.2.1 a.2.2 b.2.1 b.2.2).eq, mul_assoc]

theorem evalOption_reduce (E : I → MatrixUnitSystem (Fin 2) A)
    (hE : ∀ i j, i ≠ j → ∀ a b c d,
      Commute ((E i).entry a b) ((E j).entry c d))
    (w : MatrixSiteWord I) : evalOption E (reduce w) = eval E w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [reduce]
    cases h : reduce w with
    | none =>
      simp only [h, evalOption, Option.elim_none] at ih
      simp only [Option.bind_none, evalOption, Option.elim_none, eval_cons, ← ih, mul_zero]
    | some v =>
      simp only [h, evalOption, Option.elim_some] at ih
      simp only [Option.bind_some]
      rw [evalOption_insert E hE, ih, eval_cons]

theorem indices_insert_subset (a : MatrixSiteLetter I) (w v : MatrixSiteWord I)
    (h : insert a w = some v) : ∀ i ∈ indices v, i = a.1 ∨ i ∈ indices w := by
  induction w generalizing v with
  | nil =>
    simp only [insert, Option.some.injEq] at h
    subst v
    simp [indices]
  | cons b w ih =>
    by_cases hab : a.1 = b.1
    · by_cases hbc : a.2.2 = b.2.1
      · simp only [insert, hab, hbc, ite_true, Option.some.injEq] at h
        subst v
        intro i hi
        simp only [indices, List.map_cons, List.mem_cons] at hi ⊢
        exact hi.imp (fun h => h.trans hab.symm) (fun h => Or.inr h)
      · simp [insert, hab, hbc] at h
    · simp only [insert, hab, ite_false] at h
      cases hv : insert a w with
      | none => simp [hv] at h
      | some z =>
        simp only [hv, Option.map_some, Option.some.injEq] at h
        subst v
        intro i hi
        simp only [indices, List.map_cons, List.mem_cons] at hi ⊢
        rcases hi with hi | hi
        · exact Or.inr (Or.inl hi)
        · exact (ih z hv i hi).imp id Or.inr

theorem indices_insert_nodup (a : MatrixSiteLetter I) (w v : MatrixSiteWord I)
    (hw : (indices w).Nodup) (h : insert a w = some v) : (indices v).Nodup := by
  induction w generalizing v with
  | nil =>
    simp only [insert, Option.some.injEq] at h
    subst v
    simp [indices]
  | cons b w ih =>
    have hw' : b.1 ∉ indices w ∧ (indices w).Nodup := by
      simpa only [indices, List.map_cons, List.nodup_cons] using hw
    by_cases hab : a.1 = b.1
    · by_cases hbc : a.2.2 = b.2.1
      · simp only [insert, hab, hbc, ite_true, Option.some.injEq] at h
        subst v
        simpa only [indices, List.map_cons, List.nodup_cons, hab] using hw
      · simp [insert, hab, hbc] at h
    · simp only [insert, hab, ite_false] at h
      cases hv : insert a w with
      | none => simp [hv] at h
      | some z =>
        simp only [hv, Option.map_some, Option.some.injEq] at h
        subst v
        apply List.nodup_cons.mpr
        constructor
        · intro hb
          rcases indices_insert_subset a w z hv b.1 hb with hb | hb
          · exact hab hb.symm
          · exact hw'.1 hb
        · exact ih z hw'.2 hv

theorem indices_reduce_nodup (w v : MatrixSiteWord I) (h : reduce w = some v) :
    (indices v).Nodup := by
  induction w generalizing v with
  | nil =>
    simp only [reduce, Option.some.injEq] at h
    subst v
    exact List.nodup_nil
  | cons a w ih =>
    simp only [reduce] at h
    cases hw : reduce w with
    | none => simp [hw] at h
    | some z =>
      simp only [hw, Option.bind_some] at h
      exact indices_insert_nodup a z v (ih z hw) h

end Reduction

end MatrixSiteWord

namespace PointedMatrixSites

variable {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {Ω : H} {ν : I → ℝ}

noncomputable def wordOperator (S : PointedMatrixSites M Ω ν) (w : MatrixSiteWord I) : H →L[ℂ] H :=
  MatrixSiteWord.eval S.site w

noncomputable def wordVector (S : PointedMatrixSites M Ω ν) (w : MatrixSiteWord I) : H :=
  S.wordOperator w Ω

@[simp] theorem wordOperator_nil (S : PointedMatrixSites M Ω ν) : S.wordOperator [] = 1 := rfl
@[simp] theorem wordOperator_cons (S : PointedMatrixSites M Ω ν)
    (a : MatrixSiteLetter I) (w : MatrixSiteWord I) :
    S.wordOperator (a :: w) = (S.site a.1).entry a.2.1 a.2.2 * S.wordOperator w := rfl
@[simp] theorem wordOperator_append (S : PointedMatrixSites M Ω ν)
    (w v : MatrixSiteWord I) : S.wordOperator (w ++ v) = S.wordOperator w * S.wordOperator v :=
  MatrixSiteWord.eval_append S.site w v
@[simp] theorem wordOperator_star (S : PointedMatrixSites M Ω ν) (w : MatrixSiteWord I) :
    S.wordOperator (MatrixSiteWord.star w) = star (S.wordOperator w) :=
  MatrixSiteWord.eval_star S.site w
@[simp] theorem wordVector_nil (S : PointedMatrixSites M Ω ν) : S.wordVector [] = Ω := rfl
@[simp] theorem wordVector_cons (S : PointedMatrixSites M Ω ν)
    (a : MatrixSiteLetter I) (w : MatrixSiteWord I) :
    S.wordVector (a :: w) = (S.site a.1).entry a.2.1 a.2.2 (S.wordVector w) := rfl

end PointedMatrixSites

end KadisonKastler

end OAI
