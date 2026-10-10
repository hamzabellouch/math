import OAI.NumberTheory.Ostmann.Arithmetic.MovingWeightedDiagonalMean
import OAI.NumberTheory.Ostmann.Arithmetic.MovingOriginalDiagonalPatterns

namespace OAI

/-! # Relabeling the retained exterior multiplier into arithmetic coordinates -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

noncomputable def movingPatternExternalMultiplier {J : Type*} [Fintype J] {N : ℕ}
    (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
    (reg : J → Fin (N + 1)) (active : J → Bool)
    (other : (Fin (N + 1) → primes) → J → ℤ)
    (greg : ∀ q : ℕ, ZMod q → ℂ) (sreg : ℤ) (φ : ℝ → ℝ)
    (Jleft Jright : ℝ) (diagonal : Bool) (x : Fin (N + 1) → primes) (z y : ℝ) : ℂ :=
  let q := fun j => (x (reg j) : ℕ)
  let _ : ∀ j, Fact (q j).Prime := fun j => ⟨hprimes _ (x (reg j)).property⟩
  (giantOuterWeight φ Jleft Jright diagonal ⌊Real.exp z⌋₊ ⌊Real.exp y⌋₊ : ℂ) *
    (naturalRegularMultiplier q active sreg (fun j => (other x j : ZMod (q j)))
      (fun j => greg (q j)) ⌊Real.exp z⌋₊ ⌊Real.exp y⌋₊ : ℝ)

theorem movingWeightedDiagonalKernel_fin {B C J : Type*} [Fintype J] {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (t : Bool → FrequencyTree ℤ n)
    (small : TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (pattern : Bool × MovingSampleIndex n → C)
    (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
    (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
    (g : ∀ i, ZMod (p i) → ℂ) (Dq : ∀ i, (ZMod (p i))ˣ)
    (reg : J → Fin (N + 1)) (active : J → Bool)
    (other : (Fin (N + 1) → primes) → J → ℤ)
    (greg : ∀ q : ℕ, ZMod q → ℂ) (sreg : ℤ)
    (f : ℤ → ℂ) (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (Jleft Jright : ℝ) (diagonal : Bool) (u v a b center : ℝ)
    (W : (B → primes) → ℝ → ℝ → ℂ)
    (x : Fin (N + 1) → primes)
    (hW : ∀ z y, W (fun j => x (e.symm (.inl j))) z y =
      movingPatternExternalMultiplier primes hprimes reg active other greg sreg φ
        Jleft Jright diagonal x z y) :
    movingWeightedDiagonalKernel p (fun q : primes => (q : ℕ)) outside
      childBound pivotBound f g Dq Finset.univ ψ X lo hi φ G t small
      (bulkSlotLeaves n m slot) W u v a b center
      (fun j => x (e.symm (.inl j)))
      ((movingSamplePairCoordinates primes n).symm
        (fun i => x (e.symm (.inr (pattern i))))) =
    movingOriginalPatternDiagonalObservable e t small slot pattern primes hprimes p g Dq
      reg active sreg other greg f outside childBound pivotBound
      ψ X lo hi φ G Jleft Jright diagonal u v a b center x := by
  have heval (side : Bool) :
      (movingPatternFinBulkData e n m t (fun _ => small) slot (Equiv.refl _) pattern side).map x =
      buildMovingSlotData n (t side)
        (treeLeafMap (List.map (fun j => x (e.symm (.inl j)))) n small)
        (treeLeafMap (List.map (fun j => x (e.symm (.inl j)))) n (bulkSlotLeaves n m slot))
        (movingPatternSamples primes n (fun i => x (e.symm (.inr (pattern i)))) side) := by
    have hbulk : movingPatternBulkLeaves n m slot (Equiv.refl _) =
        fun _ => bulkSlotLeaves n m slot := by
      funext b
      cases b <;> rfl
    rw [movingPatternFinBulkData, hbulk]
    exact movingPatternFinData_evaluate e t (fun _ => small)
      (fun _ => bulkSlotLeaves n m slot) pattern x side
  have hterm (side : Bool) (XL XR : ℕ) :
      let T := buildMovingSlotData n (t side)
        (treeLeafMap (List.map (fun j => x (e.symm (.inl j)))) n small)
        (treeLeafMap (List.map (fun j => x (e.symm (.inl j)))) n (bulkSlotLeaves n m slot))
        (movingPatternSamples primes n (fun i => x (e.symm (.inr (pattern i)))) side)
      movingSupportedWeight (fun q : primes => (q : ℕ)) outside T XL XR
        (movingOriginalGiantWeight p (fun q : primes => (q : ℕ)) childBound pivotBound
          (fun _ => f) (fun _ _ _ _ => 1) g Dq Finset.univ ψ X lo hi φ G T (t side) XL XR) =
      movingSupportedWeight (fun i => (x i : ℕ)) outside
        (movingPatternFinBulkData e n m t (fun _ => small) slot (Equiv.refl _) pattern side) XL XR
        (movingOriginalGiantWeight p (fun i => (x i : ℕ)) childBound pivotBound
          (fun _ => f) (fun _ _ _ _ => 1) g Dq Finset.univ ψ X lo hi φ G
          (movingPatternFinBulkData e n m t (fun _ => small) slot (Equiv.refl _) pattern side)
          (t side) XL XR) := by
    dsimp only
    rw [← heval side, movingOriginalGiantWeight_map, movingSupportedWeight_map]
    rfl
  unfold movingOriginalPatternDiagonalObservable
  unfold movingWeightedDiagonalKernel
  dsimp only
  rw [← movingPatternSamples_pair]
  dsimp only
  apply congrArg (complexPrimeInterval 1 0 a b)
  funext y
  apply congrArg (complexIntegerInterval 1 0 u v center)
  funext z
  simp only [Bool.false_eq_true, ite_false, ite_true]
  rw [hterm false, hterm true]
  rw [hW z y]
  unfold movingPatternExternalMultiplier movingOriginalSupportedOuterPair
  dsimp only
  exact (mul_assoc _ _ _).symm

end Ostmann

end OAI
