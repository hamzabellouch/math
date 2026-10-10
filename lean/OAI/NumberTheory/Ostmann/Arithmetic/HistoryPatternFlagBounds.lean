import OAI.NumberTheory.Ostmann.Arithmetic.HistoryIntegerFieldBridge
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPatternRows

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryPatternFlagBounds
open Construction Characters.RationalHistory HistoryOccurrenceVariables
open HistorySymbolicScope HistoryOccurrenceRows HistoryPatternRows HistoryRepeatedRenaming
open ClearedCoefficientFlags MvPolynomial

variable {ι κ : Type*}

theorem heightBudget_rename (e : Expr ι) (f : ι → κ) (B : ℝ) :
    (e.rename f).heightBudget B = e.heightBudget B := by
  induction e <;> simp_all only [Expr.rename,Expr.heightBudget]

theorem fraction_bound_on_atoms [DecidableEq ι] (e : Expr ι) (x : ι → ℝ)
    {B : ℝ} (hB : 1 ≤ B) (hx : ∀ i ∈ e.atoms, |x i| ≤ B) :
    |eval₂ (Int.castRingHom ℝ) x e.numerator| ≤ e.heightBudget B ∧
      |eval₂ (Int.castRingHom ℝ) x e.denominator| ≤ e.heightBudget B := by
  let y : ι → ℝ := fun i => if i ∈ e.atoms then x i else 0
  have hy : ∀ i, |y i| ≤ B := by
    intro i
    by_cases hi : i ∈ e.atoms
    · simpa only [y,ite_eq_left hi] using hx i hi
    · simp only [y,ite_eq_right hi,abs_zero]
      linarith
  have hn : eval₂ (Int.castRingHom ℝ) x e.numerator =
      eval₂ (Int.castRingHom ℝ) y e.numerator := by
    apply eval₂Hom_congr' rfl _ rfl
    intro i hi _
    simp only [y,ite_eq_left (e.fraction_vars_subset.1 hi)]
  have hd : eval₂ (Int.castRingHom ℝ) x e.denominator =
      eval₂ (Int.castRingHom ℝ) y e.denominator := by
    apply eval₂Hom_congr' rfl _ rfl
    intro i hi _
    simp only [y,ite_eq_left (e.fraction_vars_subset.2 hi)]
  rw [hn,hd]
  exact e.fraction_eval_abs_le y B hB hy

variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

def height (h : History l) (V : ℕ → ℕ) (B : ℝ) : ℝ :=
  (2*HistoryHeightBudgetFixed.frequencyBound V l)^
    (2^l*(2+h.root.small.length+2*h.internalOccurrences.length+7*l)+5)*
      B^(2^l*(h.root.small.length+2*h.internalOccurrences.length))

theorem row_atom_bound (h : History l) (hs : h.Supported V outside) (i : InternalKey h)
    (x : PatternKey h → ℝ) {B : ℝ}
    (hx : ∀ j : Fin h.root.small.length ⊕ InternalKey h,
      |x (patternMap h (Sum.inr j))| ≤ B) :
    (∀ j ∈ (row h hs i).1.atoms, |x j| ≤ B) ∧
      (∀ j ∈ (row h hs i).2.atoms, |x j| ≤ B) := by
  classical
  have hfree := rows_above h hs _ _ (HistoryCoefficientBounds.rootFreeLevel h)
    (HistoryCoefficientBounds.coefficientHistory_rootFreeAbove h hs false)
    (HistoryCoefficientBounds.coefficientHistory_rootFreeAbove h hs true) i
  have hunit : ∀ e : Expr (Key h),
      Above (HistoryCoefficientBounds.rootFreeLevel h) (internalLevel h i) e →
      ∀ j ∈ (e.rename (patternMap h)).atoms, |x j| ≤ B := by
    intro e he j hj
    rw [Expr.atoms_rename] at hj
    obtain ⟨k,hk,hkj⟩ := Finset.mem_image.mp hj
    subst j
    rcases k with b | k
    · exact False.elim (Nat.not_lt_zero _ (above_atoms e he (Sum.inl b) hk))
    · exact hx k
  exact ⟨hunit _ hfree.1,hunit _ hfree.2⟩

theorem row_fraction_bounds (h : History l) (hs : h.Supported V outside) (i : InternalKey h)
    (x : PatternKey h → ℝ) {B : ℝ} (hB : 1 ≤ B)
    (hx : ∀ j : Fin h.root.small.length ⊕ InternalKey h,
      |x (patternMap h (Sum.inr j))| ≤ B) :
    (|eval₂ (Int.castRingHom ℝ) x (row h hs i).1.numerator| ≤ height h V B ∧
      |eval₂ (Int.castRingHom ℝ) x (row h hs i).1.denominator| ≤ height h V B) ∧
    (|eval₂ (Int.castRingHom ℝ) x (row h hs i).2.numerator| ≤ height h V B ∧
      |eval₂ (Int.castRingHom ℝ) x (row h hs i).2.denominator| ≤ height h V B) := by
  have ha := row_atom_bound h hs i x hx
  have h1 := fraction_bound_on_atoms (row h hs i).1 x hB ha.1
  have h2 := fraction_bound_on_atoms (row h hs i).2 x hB ha.2
  have hh := canonical_heightBudget h hs i hB
  have hh1 : (row h hs i).1.heightBudget B ≤ height h V B := by
    simpa only [row,heightBudget_rename,height] using hh.1
  have hh2 : (row h hs i).2.heightBudget B ≤ height h V B := by
    simpa only [row,heightBudget_rename,height] using hh.2
  exact ⟨⟨h1.1.trans hh1,h1.2.trans hh1⟩,⟨h2.1.trans hh2,h2.2.trans hh2⟩⟩

theorem flags_eval_bound (h : History l) (hs : h.Supported V outside) (i : InternalKey h)
    (x : PatternKey h → ℝ) {B : ℝ} (hB : 1 ≤ B)
    (hx : ∀ j : Fin h.root.small.length ⊕ InternalKey h,
      |x (patternMap h (Sum.inr j))| ≤ B) :
    |eval₂ (Int.castRingHom ℝ) x (leftFlag h hs i)| ≤ (height h V B)^2 ∧
      |eval₂ (Int.castRingHom ℝ) x (rightFlag h hs i)| ≤ (height h V B)^2 := by
  have hf := row_fraction_bounds h hs i x hB hx
  have hH : 0 ≤ height h V B := (abs_nonneg _).trans hf.1.1
  constructor
  · change |eval₂ _ _ ((row h hs i).1.numerator*(row h hs i).2.denominator)| ≤ _
    rw [eval₂_mul,abs_mul,pow_two]
    exact mul_le_mul hf.1.1 hf.2.2 (abs_nonneg _) hH
  · change |eval₂ _ _ ((row h hs i).2.numerator*(row h hs i).1.denominator)| ≤ _
    rw [eval₂_mul,abs_mul,pow_two]
    exact mul_le_mul hf.2.1 hf.1.2 (abs_nonneg _) hH

theorem minor_eval_bound (h : History l) (hs : h.Supported V outside) (i j : InternalKey h)
    (x : PatternKey h → ℝ) {B : ℝ} (hB : 1 ≤ B)
    (hx : ∀ k : Fin h.root.small.length ⊕ InternalKey h,
      |x (patternMap h (Sum.inr k))| ≤ B) :
    |eval₂ (Int.castRingHom ℝ) x (minorFlag h hs i j)| ≤ 2*(height h V B)^4 := by
  have hi := flags_eval_bound h hs i x hB hx
  have hj := flags_eval_bound h hs j x hB hx
  change |eval₂ _ _ (leftFlag h hs i*rightFlag h hs j-rightFlag h hs i*leftFlag h hs j)| ≤ _
  rw [eval₂_sub,eval₂_mul,eval₂_mul]
  apply (abs_sub _ _).trans
  rw [abs_mul,abs_mul]
  have h1 := mul_le_mul hi.1 hj.2 (abs_nonneg _) (sq_nonneg (height h V B))
  have h2 := mul_le_mul hi.2 hj.1 (abs_nonneg _) (sq_nonneg (height h V B))
  calc
    _ ≤ (height h V B)^2*(height h V B)^2+(height h V B)^2*(height h V B)^2 :=
      add_le_add h1 h2
    _ = _ := by ring

theorem integer_flags_bound (h : History l) (hs : h.Supported V outside) (i : InternalKey h)
    {B : ℝ} (hB : 1 ≤ B)
    (hx : ∀ j : Fin h.root.small.length ⊕ InternalKey h,
      |(integerSample h (Sum.inr j):ℝ)| ≤ B) :
    |(eval (fun j => patternSample h j.val) (leftFlag h hs i):ℝ)| ≤ (height h V B)^2 ∧
      |(eval (fun j => patternSample h j.val) (rightFlag h hs i):ℝ)| ≤ (height h V B)^2 := by
  have he := flags_eval_bound h hs i (fun j => (patternSample h j.val:ℝ)) hB (fun j => by
    simpa only [patternMap_sample] using hx j)
  simpa only [Expr.eval₂_cast_int] using he

theorem integer_minor_bound (h : History l) (hs : h.Supported V outside) (i j : InternalKey h)
    {B : ℝ} (hB : 1 ≤ B)
    (hx : ∀ k : Fin h.root.small.length ⊕ InternalKey h,
      |(integerSample h (Sum.inr k):ℝ)| ≤ B) :
    |(eval (fun j => patternSample h j.val) (minorFlag h hs i j):ℝ)| ≤ 2*(height h V B)^4 := by
  have he := minor_eval_bound h hs i j (fun j => (patternSample h j.val:ℝ)) hB (fun k => by
    simpa only [patternMap_sample] using hx k)
  simpa only [Expr.eval₂_cast_int] using he

end Ostmann.Arithmetic.HistoryPatternFlagBounds

end

end OAI
