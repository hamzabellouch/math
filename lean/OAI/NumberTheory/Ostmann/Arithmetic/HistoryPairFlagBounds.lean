import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairRows
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPatternFlagBounds

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairFlagBounds
open Construction Characters.RationalHistory HistoryOccurrenceVariables
open HistorySymbolicScope HistoryOccurrenceRows HistoryPairPattern HistoryPairRows
open ClearedCoefficientFlags MvPolynomial

variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

def height (h k : History l) (V : ℕ → ℕ) (B : ℝ) : ℝ :=
  max (HistoryPatternFlagBounds.height h V B) (HistoryPatternFlagBounds.height k V B)

theorem canonical_fraction_bounds_rename {κ : Type*} [DecidableEq κ]
    (h : History l) (hs : h.Supported V outside) (i : InternalKey h)
    (f : Key h → κ) (x : κ → ℝ) {B : ℝ} (hB : 1 ≤ B)
    (hx : ∀ j : Fin h.root.small.length ⊕ InternalKey h, |x (f (Sum.inr j))| ≤ B) :
    (|eval₂ (Int.castRingHom ℝ) x ((canonical h hs i).1.rename f).numerator| ≤
        HistoryPatternFlagBounds.height h V B ∧
      |eval₂ (Int.castRingHom ℝ) x ((canonical h hs i).1.rename f).denominator| ≤
        HistoryPatternFlagBounds.height h V B) ∧
    (|eval₂ (Int.castRingHom ℝ) x ((canonical h hs i).2.rename f).numerator| ≤
        HistoryPatternFlagBounds.height h V B ∧
      |eval₂ (Int.castRingHom ℝ) x ((canonical h hs i).2.rename f).denominator| ≤
        HistoryPatternFlagBounds.height h V B) := by
  classical
  have hfree := rows_above h hs _ _ (HistoryCoefficientBounds.rootFreeLevel h)
    (HistoryCoefficientBounds.coefficientHistory_rootFreeAbove h hs false)
    (HistoryCoefficientBounds.coefficientHistory_rootFreeAbove h hs true) i
  have ha : ∀ e : Expr (Key h),
      Above (HistoryCoefficientBounds.rootFreeLevel h) (internalLevel h i) e →
      ∀ j ∈ (e.rename f).atoms, |x j| ≤ B := by
    intro e he j hj
    rw [Expr.atoms_rename] at hj
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hj
    rcases a with b | a
    · exact False.elim (Nat.not_lt_zero _ (above_atoms e he (Sum.inl b) ha))
    · exact hx a
  have h₁ := HistoryPatternFlagBounds.fraction_bound_on_atoms
    ((canonical h hs i).1.rename f) x hB (ha _ hfree.1)
  have h₂ := HistoryPatternFlagBounds.fraction_bound_on_atoms
    ((canonical h hs i).2.rename f) x hB (ha _ hfree.2)
  simp only [HistoryPatternFlagBounds.heightBudget_rename] at h₁ h₂
  have hh := canonical_heightBudget h hs i hB
  exact ⟨⟨h₁.1.trans hh.1,h₁.2.trans hh.1⟩,⟨h₂.1.trans hh.2,h₂.2.trans hh.2⟩⟩

theorem row_fraction_bounds (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (i : Occurrences h k)
    (x : PairKey h k → ℝ) {B : ℝ} (hB : 1 ≤ B)
    (hx : ∀ j : Fin h.root.small.length ⊕ InternalKey h, |x (leftMap h k (Sum.inr j))| ≤ B)
    (hy : ∀ j : Fin k.root.small.length ⊕ InternalKey k, |x (rightMap h k (Sum.inr j))| ≤ B) :
    (|eval₂ (Int.castRingHom ℝ) x (row h k hs ks i).1.numerator| ≤ height h k V B ∧
      |eval₂ (Int.castRingHom ℝ) x (row h k hs ks i).1.denominator| ≤ height h k V B) ∧
    (|eval₂ (Int.castRingHom ℝ) x (row h k hs ks i).2.numerator| ≤ height h k V B ∧
      |eval₂ (Int.castRingHom ℝ) x (row h k hs ks i).2.denominator| ≤ height h k V B) := by
  rcases i with i | i
  · have hh := canonical_fraction_bounds_rename h hs i (leftMap h k) x hB hx
    exact ⟨⟨hh.1.1.trans (le_max_left _ _),hh.1.2.trans (le_max_left _ _)⟩,
      ⟨hh.2.1.trans (le_max_left _ _),hh.2.2.trans (le_max_left _ _)⟩⟩
  · have hh := canonical_fraction_bounds_rename k ks i (rightMap h k) x hB hy
    exact ⟨⟨hh.1.1.trans (le_max_right _ _),hh.1.2.trans (le_max_right _ _)⟩,
      ⟨hh.2.1.trans (le_max_right _ _),hh.2.2.trans (le_max_right _ _)⟩⟩

theorem flags_eval_bound (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (i : Occurrences h k)
    (x : PairKey h k → ℝ) {B : ℝ} (hB : 1 ≤ B)
    (hx : ∀ j : Fin h.root.small.length ⊕ InternalKey h, |x (leftMap h k (Sum.inr j))| ≤ B)
    (hy : ∀ j : Fin k.root.small.length ⊕ InternalKey k, |x (rightMap h k (Sum.inr j))| ≤ B) :
    |eval₂ (Int.castRingHom ℝ) x (leftFlag h k hs ks i)| ≤ (height h k V B)^2 ∧
      |eval₂ (Int.castRingHom ℝ) x (rightFlag h k hs ks i)| ≤ (height h k V B)^2 := by
  have hf := row_fraction_bounds h k hs ks i x hB hx hy
  have hH : 0 ≤ height h k V B := (abs_nonneg _).trans hf.1.1
  constructor
  · change |eval₂ _ _ ((row h k hs ks i).1.numerator * (row h k hs ks i).2.denominator)| ≤ _
    rw [eval₂_mul,abs_mul,pow_two]
    exact mul_le_mul hf.1.1 hf.2.2 (abs_nonneg _) hH
  · change |eval₂ _ _ ((row h k hs ks i).2.numerator * (row h k hs ks i).1.denominator)| ≤ _
    rw [eval₂_mul,abs_mul,pow_two]
    exact mul_le_mul hf.2.1 hf.1.2 (abs_nonneg _) hH

theorem minor_eval_bound (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (i j : Occurrences h k)
    (x : PairKey h k → ℝ) {B : ℝ} (hB : 1 ≤ B)
    (hx : ∀ a : Fin h.root.small.length ⊕ InternalKey h, |x (leftMap h k (Sum.inr a))| ≤ B)
    (hy : ∀ a : Fin k.root.small.length ⊕ InternalKey k, |x (rightMap h k (Sum.inr a))| ≤ B) :
    |eval₂ (Int.castRingHom ℝ) x (minorFlag h k hs ks i j)| ≤ 2 * (height h k V B)^4 := by
  have hi := flags_eval_bound h k hs ks i x hB hx hy
  have hj := flags_eval_bound h k hs ks j x hB hx hy
  change |eval₂ _ _ (leftFlag h k hs ks i * rightFlag h k hs ks j -
    rightFlag h k hs ks i * leftFlag h k hs ks j)| ≤ _
  rw [eval₂_sub,eval₂_mul,eval₂_mul]
  apply (abs_sub _ _).trans
  rw [abs_mul,abs_mul]
  have h₁ := mul_le_mul hi.1 hj.2 (abs_nonneg _) (sq_nonneg (height h k V B))
  have h₂ := mul_le_mul hi.2 hj.1 (abs_nonneg _) (sq_nonneg (height h k V B))
  calc
    _ ≤ (height h k V B)^2 * (height h k V B)^2 +
        (height h k V B)^2 * (height h k V B)^2 := add_le_add h₁ h₂
    _ = _ := by ring

theorem integer_flags_bound (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (hroot : RootGiantsAgree h k)
    (i : Occurrences h k) {B : ℝ} (hB : 1 ≤ B)
    (hx : ∀ j : Fin h.root.small.length ⊕ InternalKey h, |(integerSample h (Sum.inr j) : ℝ)| ≤ B)
    (hy : ∀ j : Fin k.root.small.length ⊕ InternalKey k, |(integerSample k (Sum.inr j) : ℝ)| ≤ B) :
    |(eval (pairSample h k) (leftFlag h k hs ks i) : ℝ)| ≤ (height h k V B)^2 ∧
      |(eval (pairSample h k) (rightFlag h k hs ks i) : ℝ)| ≤ (height h k V B)^2 := by
  have he := flags_eval_bound h k hs ks i (fun a => (pairSample h k a : ℝ)) hB
    (fun j => by simpa only [leftMap_sample] using hx j)
    (fun j => by simpa only [rightMap_sample h k hroot] using hy j)
  simpa only [Expr.eval₂_cast_int] using he

theorem integer_minor_bound (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (hroot : RootGiantsAgree h k)
    (i j : Occurrences h k) {B : ℝ} (hB : 1 ≤ B)
    (hx : ∀ a : Fin h.root.small.length ⊕ InternalKey h, |(integerSample h (Sum.inr a) : ℝ)| ≤ B)
    (hy : ∀ a : Fin k.root.small.length ⊕ InternalKey k, |(integerSample k (Sum.inr a) : ℝ)| ≤ B) :
    |(eval (pairSample h k) (minorFlag h k hs ks i j) : ℝ)| ≤ 2 * (height h k V B)^4 := by
  have he := minor_eval_bound h k hs ks i j (fun a => (pairSample h k a : ℝ)) hB
    (fun a => by simpa only [leftMap_sample] using hx a)
    (fun a => by simpa only [rightMap_sample h k hroot] using hy a)
  simpa only [Expr.eval₂_cast_int] using he

end Ostmann.Arithmetic.HistoryPairFlagBounds

end

end OAI
