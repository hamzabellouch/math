import OAI.NumberTheory.Ostmann.Arithmetic.MovingSamplePrior
import OAI.NumberTheory.Ostmann.Characters.TreeLeafIndex

namespace OAI

/-! # Fixed coordinates for the actual internal prime samples

The coordinates count each sample when it is made, not its later occurrences
in descendant lists. Their number is independent of the number of bulk slots.
-/

namespace Ostmann
open scoped Classical BigOperators

def MovingSampleIndex : ℕ → Type
  | 0 => Empty
  | n + 1 => (TreeLeafIndex n × Fin 4) ⊕ (Bool × MovingSampleIndex n)

instance movingSampleIndexFintype : (n : ℕ) → Fintype (MovingSampleIndex n)
  | 0 => inferInstanceAs (Fintype Empty)
  | n + 1 => @instFintypeSum _ _ inferInstance
      (@instFintypeProd _ _ inferInstance (movingSampleIndexFintype n))

def movingSampleTier : {n : ℕ} → MovingSampleIndex n → ℕ
  | n + 1, .inl _ => n
  | _ + 1, .inr (_, i) => movingSampleTier i

theorem movingSampleTier_lt {n : ℕ} (i : MovingSampleIndex n) : movingSampleTier i < n := by
  induction n with
  | zero => exact Empty.elim i
  | succ n ih =>
      rcases i with i | ⟨b, i⟩
      · exact Nat.lt_succ_self n
      · exact (ih i).trans (Nat.lt_succ_self n)

theorem card_movingSampleIndex (n : ℕ) : Fintype.card (MovingSampleIndex n) = 2 * n * 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change Fintype.card ((TreeLeafIndex n × Fin 4) ⊕ (Bool × MovingSampleIndex n)) = _
      rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_prod, Fintype.card_bool,
        Fintype.card_fin, card_treeLeafIndex, ih, pow_succ]
      ring

def movingSampleCoordinates (A : Type*) : (n : ℕ) →
    MovingSampleSlots A n ≃ (MovingSampleIndex n → A)
  | 0 =>
      { toFun := fun _ i => Empty.elim i
        invFun := fun _ => .leaf
        left_inv := fun a => by cases a; rfl
        right_inv := fun a => by funext i; exact Empty.elim i }
  | n + 1 =>
      { toFun := fun a => match a with
          | .node u l r => fun i => match i with
              | .inl (t, j) => treeLeafTupleEquiv (Fin 4 → A) n u t j
              | .inr (true, i) => movingSampleCoordinates A n l i
              | .inr (false, i) => movingSampleCoordinates A n r i
        invFun := fun a => .node
          ((treeLeafTupleEquiv (Fin 4 → A) n).symm (fun t j => a (.inl (t, j))))
          ((movingSampleCoordinates A n).symm (fun i => a (.inr (true, i))))
          ((movingSampleCoordinates A n).symm (fun i => a (.inr (false, i))))
        left_inv := by
          intro a
          cases a with
          | node u l r =>
              simp only [Equiv.symm_apply_apply]
        right_inv := by
          intro a
          funext i
          rcases i with ⟨t, j⟩ | ⟨b, i⟩
          · exact congrFun (congrFun ((treeLeafTupleEquiv (Fin 4 → A) n).apply_symm_apply
                (fun t j => a (.inl (t, j)))) t) j
          · cases b <;> exact congrFun ((movingSampleCoordinates A n).apply_symm_apply _) i }

theorem movingCompensationPrior_indexed {A : Type*} (μ : A → ℝ) (n : ℕ)
    (a : TreeLeafTuple (Fin 4 → A) n) :
    movingCompensationPrior μ n a =
      ∏ t : TreeLeafIndex n, ∏ j : Fin 4, μ (treeLeafTupleEquiv (Fin 4 → A) n a t j) := by
  induction n with
  | zero =>
      change (∏ j : Fin 4, μ (a j)) = ∏ _t : Unit, ∏ j : Fin 4, μ (a j)
      simp only [Fintype.prod_unique]
  | succ n ih =>
      change movingCompensationPrior μ n a.1 * movingCompensationPrior μ n a.2 =
        ∏ t : TreeLeafIndex n ⊕ TreeLeafIndex n,
          ∏ j : Fin 4, μ (treeLeafTupleEquiv (Fin 4 → A) (n + 1) a t j)
      rw [Fintype.prod_sum_type, ih, ih]
      rfl

/-- The tree law is precisely the product of the original coordinate priors.
This identity permits the proved equality-pattern comparison to be applied
without replacing the law by a conditioned or uniform distribution. -/
theorem movingSamplesPrior_coordinates {A : Type*} (μ : ℕ → A → ℝ) (n : ℕ)
    (a : MovingSampleSlots A n) :
    movingSamplesPrior μ a =
      ∏ i : MovingSampleIndex n, μ (movingSampleTier i) (movingSampleCoordinates A n a i) := by
  induction a with
  | leaf => rfl
  | @node n u l r hl hr =>
      change movingCompensationPrior (μ n) n u * movingSamplesPrior μ l * movingSamplesPrior μ r =
        ∏ i : (TreeLeafIndex n × Fin 4) ⊕ (Bool × MovingSampleIndex n), _
      rw [Fintype.prod_sum_type, Fintype.prod_prod_type, Fintype.prod_prod_type, Fintype.prod_bool,
        movingCompensationPrior_indexed, hl, hr]
      simp only [movingSampleTier, movingSampleCoordinates, Equiv.coe_fn_mk]
      ring

theorem movingSamplesPrior_reindex {A : Type*} [Fintype A] (μ : ℕ → A → ℝ)
    (n : ℕ) (F : MovingSampleSlots A n → ℂ) :
    (∑ a : MovingSampleSlots A n, (movingSamplesPrior μ a : ℂ) * F a) =
      ∑ x : MovingSampleIndex n → A,
        ((∏ i, μ (movingSampleTier i) (x i) : ℝ) : ℂ) *
          F ((movingSampleCoordinates A n).symm x) := by
  have h := (movingSampleCoordinates A n).symm.sum_comp
    (fun a => (movingSamplesPrior μ a : ℂ) * F a)
  rw [← h]
  apply Finset.sum_congr rfl
  intro x _
  rw [movingSamplesPrior_coordinates, Equiv.apply_symm_apply]

end Ostmann

end OAI
