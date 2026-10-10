import OAI.NumberTheory.Ostmann.Arithmetic.MovingPairedTransform
import OAI.NumberTheory.Ostmann.Characters.NormalizedResidueFamily
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSumFactors

namespace OAI

/-! # One surviving giant and its actual regular Fourier factors -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

local instance oneGiantSum_neZero {J I : Type*} (q : J → ℕ) (p : I → ℕ)
    [∀ j, NeZero (q j)] [∀ i, NeZero (p i)] (i : J ⊕ I) :
    NeZero (Sum.elim q p i) := by
  cases i <;> dsimp only [Sum.elim] <;> infer_instance

def movingOneGiantModuli {I : Type*} (X : ℕ) (p : I → ℕ) : Unit ⊕ I → ℕ :=
  Sum.elim (fun _ => X) p

instance movingOneGiantModuli_prime {I : Type*} (X : ℕ) (p : I → ℕ)
    [Fact X.Prime] [∀ i, Fact (p i).Prime] (i : Unit ⊕ I) :
    Fact (movingOneGiantModuli X p i).Prime := by
  cases i <;> dsimp only [movingOneGiantModuli, Sum.elim] <;> infer_instance

instance movingOneGiantModuli_neZero {I : Type*} (X : ℕ) (p : I → ℕ)
    [NeZero X] [∀ i, NeZero (p i)] (i : Unit ⊕ I) :
    NeZero (movingOneGiantModuli X p i) := by
  cases i <;> dsimp only [movingOneGiantModuli, Sum.elim] <;> infer_instance

noncomputable def movingOneGiantFactors {I : Type*} (X : ℕ) (p : I → ℕ)
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) :
    ∀ i, ZMod (movingOneGiantModuli X p i) → ℂ
  | .inl _ => fun t => if favorable X then complexUnitPhase (ggiant X t) else 0
  | .inr i => greg (p i)

theorem movingOneGiantModuli_product {I : Type*} [Fintype I] (X : ℕ) (p : I → ℕ) :
    (∏ i, movingOneGiantModuli X p i) = X * ∏ i, p i := by
  simp only [movingOneGiantModuli, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr,
    Fintype.prod_unique]

theorem movingOneGiantFactors_giant_norm {I : Type*} (X : ℕ) (p : I → ℕ)
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool)
    (x : ZMod X) :
    ‖movingOneGiantFactors X p greg ggiant favorable (.inl ()) x‖ ≤ 1 := by
  dsimp only [movingOneGiantFactors]
  split_ifs
  · exact complexUnitPhase_norm_le _
  · simp only [norm_zero, zero_le_one]

theorem movingOneGiantFactors_neg {I : Type*} (X : ℕ) (p : I → ℕ)
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool)
    (hgiant : ∀ x, ggiant X (-x) = conj (ggiant X x))
    (hregular : ∀ i x, greg (p i) (-x) = conj (greg (p i) x))
    (i : Unit ⊕ I) (x : ZMod (movingOneGiantModuli X p i)) :
    movingOneGiantFactors X p greg ggiant favorable i (-x) =
      conj (movingOneGiantFactors X p greg ggiant favorable i x) := by
  cases i with
  | inl _ =>
    dsimp only [movingOneGiantFactors]
    split_ifs
    · exact (congrArg complexUnitPhase (hgiant x)).trans (complexUnitPhase_conj _)
    · exact (map_zero _).symm
  | inr i => exact hregular i x

/-- The restored full factor is in the order required by giant transfer. -/
theorem movingOneGiant_restored {σ : Type*} (value : σ → ℕ)
    (n r m : ℕ) (u : TreeLeafIndex n × Fin 4 → σ)
    (y : MovingRegularSlot n r m → σ) (P X : ℕ)
    (hP : P ≠ 0) (hX : X ≠ 0) (hu : ∀ i, value (u i) ≠ 0) (hy : ∀ i, value (y i) ≠ 0)
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) (D : ℕ) (s : ℤ) :
    let _ : NeZero P := ⟨hP⟩
    let _ : NeZero X := ⟨hX⟩
    let _ : ∀ i, NeZero ((value ∘ u) i) := fun i => ⟨hu i⟩
    let _ : ∀ i, NeZero ((value ∘ y) i) := fun i => ⟨hy i⟩
    movingTaggedTransform
      (Sum.elim (fun b : Bool => if b then P else X)
        (value ∘ movingRestoreSample n r m u y))
      (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable D s =
    movingRegularTransform
      (Sum.elim (movingOneGiantModuli P (value ∘ u)) (movingOneGiantModuli X (value ∘ y)))
      (movingSumFactors (movingOneGiantModuli P (value ∘ u))
        (movingOneGiantModuli X (value ∘ y))
        (movingOneGiantFactors P (value ∘ u) greg ggiant favorable)
        (movingOneGiantFactors X (value ∘ y) greg ggiant favorable)) D s := by
  dsimp only
  rw [movingTaggedTransform_restored value n r m u y P X hP hX hu hy]
  unfold movingTaggedTransform movingRegularTransform
  apply Finset.prod_congr rfl
  intro i _
  rcases i with ((i | i) | (i | i)) <;> rfl

/-- The original compensation, giant, and surviving priors may be left
abstract while reindexing their common full Fourier factor. -/
theorem movingOneGiant_restored_average {σ A : Type} [Fintype σ] [Fintype A]
    (value : σ → ℕ) (hvalue : ∀ z, value z ≠ 0) (n r m : ℕ)
    (P : Finset ℕ) (hP : ∀ p : P, (p : ℕ) ≠ 0)
    (X : A → ℕ) (hX : ∀ a, X a ≠ 0) (y : A → MovingRegularSlot n r m → σ)
    (v : A → ℤ) (D : ℕ)
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool)
    (wU : (TreeLeafIndex n × Fin 4 → σ) → ℂ) (wP : P → ℂ)
    (W : (TreeLeafIndex n × Fin 4 → σ) → P → A → ℂ) :
    let _ : ∀ p : P, NeZero (p : ℕ) := fun p => ⟨hP p⟩
    let _ : ∀ a, NeZero (X a) := fun a => ⟨hX a⟩
    let _ : ∀ z, NeZero (value z) := fun z => ⟨hvalue z⟩
    let _ : ∀ (u : TreeLeafIndex n × Fin 4 → σ) i, NeZero ((value ∘ u) i) := fun u i => ⟨hvalue (u i)⟩
    let _ : ∀ a i, NeZero ((value ∘ y a) i) := fun a i => ⟨hvalue (y a i)⟩
    (∑ u : TreeLeafIndex n × Fin 4 → σ, wU u * ∑ p : P, wP p * ∑ a, W u p a *
      movingTaggedTransform
        (Sum.elim (fun b : Bool => if b then (p : ℕ) else X a)
          (value ∘ movingRestoreSample n r m u (y a)))
        (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable D (v a)) =
    ∑ u : TreeLeafIndex n × Fin 4 → σ, wU u * ∑ p : P, wP p * ∑ a, W u p a *
      movingRegularTransform
        (Sum.elim (movingOneGiantModuli (p : ℕ) (value ∘ u))
          (movingOneGiantModuli (X a) (value ∘ y a)))
        (movingSumFactors (movingOneGiantModuli (p : ℕ) (value ∘ u))
          (movingOneGiantModuli (X a) (value ∘ y a))
          (movingOneGiantFactors (p : ℕ) (value ∘ u) greg ggiant favorable)
          (movingOneGiantFactors (X a) (value ∘ y a) greg ggiant favorable)) D (v a) := by
  dsimp only
  apply Finset.sum_congr rfl
  intro u _
  apply congrArg (fun z : ℂ => wU u * z)
  apply Finset.sum_congr rfl
  intro p _
  apply congrArg (fun z : ℂ => wP p * z)
  apply Finset.sum_congr rfl
  intro a _
  exact congrArg (fun z : ℂ => W u p a * z)
    (movingOneGiant_restored value n r m u (y a) p (X a) (hP p) (hX a)
      (fun i => hvalue (u i)) (fun i => hvalue (y a i)) greg ggiant favorable D (v a))

end Ostmann

end OAI
