import OAI.RepresentationTheory.FoulkesHowe.FirstCounts
import OAI.RepresentationTheory.FoulkesHowe.FlattenedForm
import OAI.RepresentationTheory.FoulkesHowe.MultilinearPolynomial
import OAI.RepresentationTheory.FoulkesHowe.SlotDerivative

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem346

theorem multilinearPolynomial_eq_slotPolynomial
    {S K B V : Type*} [Fintype S] [DecidableEq S] [Fintype K]
    [AddCommGroup V] [Module ℂ V]
    (T : MultilinearMap ℂ (fun _ : S => V) ℂ) (e : K → V) (l : S → B) :
    multilinearPolynomial T e l =
      SlotPolynomial.polynomial (fun k => T (fun s => e (k s))) l := by
  classical
  unfold multilinearPolynomial SlotPolynomial.polynomial
  congr 1
  ext k
  simp

private theorem swap_pair_same_row {A B : Type*} [DecidableEq A] [DecidableEq B]
    (i : A) (j k : B) (p : A × B) :
    Equiv.swap (i, j) (i, k) p =
      (p.1, if p.1 = i then Equiv.swap j k p.2 else p.2) := by
  rcases p with ⟨q, t⟩
  by_cases hq : q = i
  · subst q
    by_cases htj : t = j
    · subst t
      simp
    · by_cases htk : t = k
      · subst t
        simp
      · simp [Equiv.swap_apply_of_ne_of_ne, htj, htk]
  · have h1 : (q,t) ≠ (i,j) := by intro h; exact hq (congrArg Prod.fst h)
    have h2 : (q,t) ≠ (i,k) := by intro h; exact hq (congrArg Prod.fst h)
    simp [Equiv.swap_apply_of_ne_of_ne h1 h2, hq]

/-- The flattened form is invariant under swapping two factors in a single row. -/
theorem flattenedForm_swap_row (a b : ℕ) (V : Type*)
    [AddCommGroup V] [Module ℂ V] (T : SymmetricMultilinearForm a b V)
    (i : Fin a) (j k : Fin b) (x : Fin a × Fin b → V) :
    flattenedForm T (x ∘ Equiv.swap (i,j) (i,k)) =
      flattenedForm T x := by
  classical
  have h := flattenedForm_factor_perm T
    (fun q => if q = i then Equiv.swap j k else Equiv.refl _) x
  convert h using 1
  congr 1
  funext p
  rw [Function.comp_apply, swap_pair_same_row]
  by_cases hp : p.1 = i <;> simp [hp]

/-- If the source label occurs only in one row, every occurrence gives the same
coordinate-polynomial derivative term, by symmetry of factors in that row. -/
theorem flattened_derivative_eq_card_smul
    (a b : ℕ) (V K B : Type*) [AddCommGroup V] [Module ℂ V]
    [Fintype K] [DecidableEq B]
    (T : SymmetricMultilinearForm a b V) (e : K → V)
    (l : Fin a × Fin b → B) (src dst : B) (i : Fin a) (j : Fin b)
    (hj : l (i,j) = src)
    (hrow : ∀ p, l p = src → p.1 = i)
    (D : Derivation ℂ (MvPolynomial (B × K) ℂ) (MvPolynomial (B × K) ℂ))
    (hD : ∀ q k, D (MvPolynomial.X (q,k)) =
      if q = src then MvPolynomial.X (dst,k) else 0) :
    D (multilinearPolynomial (flattenedForm T) e l) =
      (Finset.univ.filter (fun p => l p = src)).card •
        multilinearPolynomial (flattenedForm T) e
          (Function.update l (i,j) dst) := by
  classical
  let c : ((Fin a × Fin b) → K) → ℂ :=
    fun k => flattenedForm T (fun p => e (k p))
  have hc : ∀ p, l p = src → ∀ k, c (k ∘ Equiv.swap p (i,j)) = c k := by
    intro p hp k
    rcases p with ⟨q,t⟩
    have hq := hrow (q,t) hp
    dsimp at hq
    subst q
    exact flattenedForm_swap_row a b V T i t j (fun p => e (k p))
  have h := SlotPolynomial.derivation_polynomial_eq_card_smul
    c l src dst (i,j) hj D hD hc
  rw [multilinearPolynomial_eq_slotPolynomial, multilinearPolynomial_eq_slotPolynomial]
  exact h

/-- The concrete one-step identity in the first transfer. The source is the
`t` block; its remaining occurrences all lie in the distinguished row. -/
theorem firstLabel_derivative
    (r m k : ℕ) (hk : k < m) (V K : Type*)
    [AddCommGroup V] [Module ℂ V] [Fintype K]
    (T : SymmetricMultilinearForm (r+1) (r+m) V) (e : K → V)
    (D : Derivation ℂ (MvPolynomial (FirstBlock m × K) ℂ)
      (MvPolynomial (FirstBlock m × K) ℂ))
    (hD : ∀ q j, D (MvPolynomial.X (q,j)) =
      if q = some none then MvPolynomial.X (some (some ⟨k,hk⟩),j) else 0) :
    D (multilinearPolynomial (flattenedForm T) e
        (firstLabel r m k)) =
      ((r+m-k : ℕ) : ℂ) •
        multilinearPolynomial (flattenedForm T) e
          (firstLabel r m (k+1)) := by
  classical
  have hj : firstLabel r m k
      (0, ⟨k, Nat.lt_of_lt_of_le hk (Nat.le_add_left m r)⟩) = some none := by
    simp [firstLabel]
  have hrow : ∀ p, firstLabel r m k p = some none → p.1 = 0 := by
    intro p hp
    exact ((firstLabel_eq_t_iff r m k (Nat.le_of_lt hk) p).mp hp).1
  have h := flattened_derivative_eq_card_smul (r+1) (r+m) V K (FirstBlock m)
    T e (firstLabel r m k) (some none) (some (some ⟨k,hk⟩))
    0 ⟨k, Nat.lt_of_lt_of_le hk (Nat.le_add_left m r)⟩ hj hrow D hD
  rw [firstLabel_card_t r m k (Nat.le_of_lt hk), ← firstLabel_step r m k hk] at h
  simpa only [Nat.cast_smul_eq_nsmul] using h

end Problem346

end

end OAI
