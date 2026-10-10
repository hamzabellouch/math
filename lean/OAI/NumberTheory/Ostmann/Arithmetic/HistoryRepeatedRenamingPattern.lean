import OAI.NumberTheory.Ostmann.Arithmetic.HistoryRepeatedRenamingScope

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryRepeatedRenaming
open Construction Characters.RationalHistory HistoryOccurrenceVariables HistorySymbolicScope

def patternKey {l : ℕ} (h : History l) : Key h → Bool ⊕ (ℕ × ℤ)
  | .inl b => .inl b
  | .inr i => .inr (keyLevel h (.inr i), integerSample h (.inr i))

def patternLevel (l : ℕ) : Bool ⊕ (ℕ × ℤ) → ℕ
  | .inl _ => l+1
  | .inr i => i.1

def patternSample {l : ℕ} (h : History l) : Bool ⊕ (ℕ × ℤ) → ℤ
  | .inl false => h.root.giantPlus
  | .inl true => h.root.giantMinus
  | .inr i => i.2

@[simp] theorem patternKey_level {l : ℕ} (h : History l) (i : Key h) :
    patternLevel l (patternKey h i) = keyLevel h i := by
  rcases i with b | i <;> rfl

@[simp] theorem patternKey_sample {l : ℕ} (h : History l) (i : Key h) :
    patternSample h (patternKey h i) = integerSample h i := by
  rcases i with b | i
  · cases b <;> rfl
  · rfl

theorem patternKey_small_eq_iff {l : ℕ} (h : History l)
    (i j : Fin h.root.small.length ⊕ InternalKey h) :
    patternKey h (.inr i) = patternKey h (.inr j) ↔
      keyLevel h (.inr i) = keyLevel h (.inr j) ∧
      integerSample h (.inr i) = integerSample h (.inr j) := by
  simp only [patternKey, Sum.inr.injEq, Prod.mk.injEq]

@[simp] theorem patternKey_giant_ne_small {l : ℕ} (h : History l)
    (b : Bool) (i : Fin h.root.small.length ⊕ InternalKey h) :
    patternKey h (.inl b) ≠ patternKey h (.inr i) := by
  intro hbad
  cases hbad

def PatternKey {l : ℕ} (h : History l) :=
  {j : Bool ⊕ (ℕ × ℤ) // j ∈ Finset.univ.image (patternKey h)}

instance patternKeyDecidableEq {l : ℕ} (h : History l) : DecidableEq (PatternKey h) :=
  inferInstanceAs (DecidableEq {j : Bool ⊕ (ℕ × ℤ) //
    j ∈ Finset.univ.image (patternKey h)})

instance patternKeyFintype {l : ℕ} (h : History l) : Fintype (PatternKey h) :=
  inferInstanceAs (Fintype {j // j ∈ Finset.univ.image (patternKey h)})

def patternMap {l : ℕ} (h : History l) (i : Key h) : PatternKey h :=
  ⟨patternKey h i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩

theorem patternMap_surjective {l : ℕ} (h : History l) :
    Function.Surjective (patternMap h) := by
  intro j
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp j.property
  exact ⟨i, Subtype.ext hi⟩

@[simp] theorem patternMap_eq_iff {l : ℕ} (h : History l) (i j : Key h) :
    patternMap h i = patternMap h j ↔ patternKey h i = patternKey h j :=
  Subtype.ext_iff

@[simp] theorem patternMap_level {l : ℕ} (h : History l) (i : Key h) :
    patternLevel l (patternMap h i).val = keyLevel h i := patternKey_level h i

@[simp] theorem patternMap_sample {l : ℕ} (h : History l) (i : Key h) :
    patternSample h (patternMap h i).val = integerSample h i := patternKey_sample h i

theorem pattern_integerEval {l : ℕ} (h : History l) (e : Expr (Key h)) :
    (e.rename (patternMap h)).integerEval (fun j => patternSample h j.val) =
      e.integerEval (integerSample h) := by
  rw [Expr.integerEval_rename]
  congr 1
  funext i
  exact patternMap_sample h i

theorem pattern_fieldEval {l : ℕ} {K : Type*} [Field K]
    (h : History l) (e : Expr (Key h)) :
    (e.rename (patternMap h)).fieldEval (fun j => (patternSample h j.val : K)) =
      e.fieldEval (fun i => (integerSample h i : K)) := by
  rw [Expr.fieldEval_rename]
  congr 1
  funext i
  exact congrArg (fun z : ℤ => (z : K)) (patternMap_sample h i)

theorem pattern_rationalEval {l : ℕ} (h : History l) (e : Expr (Key h)) :
    (e.rename (patternMap h)).rationalEval (fun j => (patternSample h j.val : ℚ)) =
      e.rationalEval (rationalSample h) := by
  rw [Expr.rationalEval_rename]
  congr 1
  funext i
  exact congrArg (fun z : ℤ => (z : ℚ)) (patternMap_sample h i)

theorem pattern_type_excluded {l : ℕ} (h : History l)
    (e : Expr (Key h)) (t : ℕ) (he : Above (keyLevel h) t e)
    (j : PatternKey h) (hj : patternLevel l j.val ≤ t) :
    j ∉ (e.rename (patternMap h)).atoms ∧
    j ∉ (e.rename (patternMap h)).numerator.vars ∧
    j ∉ (e.rename (patternMap h)).denominator.vars := by
  classical
  exact type_excluded e (patternMap h) (keyLevel h) (fun j => patternLevel l j.val)
    (patternMap_level h) t he j hj

end Ostmann.Arithmetic.HistoryRepeatedRenaming
end

end OAI
