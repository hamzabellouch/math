import OAI.NumberTheory.Ostmann.Arithmetic.MovingOriginalMatchedMean
import OAI.NumberTheory.Ostmann.Arithmetic.MovingOriginalDiagonalPatterns

namespace OAI

/-! # Matched sampled histories in their original arithmetic pattern coordinates -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingOriginalMatchedKernel_fin {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (t : Bool → FrequencyTree ℤ n)
    (small : TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
    (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
    (g : ∀ i, ZMod (p i) → ℂ) (Dq : ∀ i, (ZMod (p i))ˣ)
    (greg : ∀ q : ℕ, ZMod q → ℂ) (sreg : ℤ)
    (f : ℤ → ℂ) (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (Jleft Jright : ℝ) (diagonal : Bool) (u v a b center : ℝ)
    (x : Fin (N + 1) → primes) :
    movingOriginalMatchedKernel p (fun q : primes => (q : ℕ)) outside
      childBound pivotBound f g Dq Finset.univ ψ X lo hi φ G t small
      (movingPatternBulkLeaves n m slot perm) greg sreg Jleft Jright diagonal u v a b center
      (fun j => x (e.symm (.inl j)))
      ((movingSamplePairCoordinates primes n).symm
        (fun i => x (e.symm (.inr (pattern i))))) =
    movingOriginalPatternMatchedObservable e t small slot perm pattern primes hprimes p g Dq
      (movingPatternRegularSlots e n m small slot).get (fun _ => true) sreg
      (fun x => movingRegularOther (fun i => (x i : ℕ)) outside
        (movingPatternRegularSlots e n m small slot)) greg f outside childBound pivotBound
      ψ X lo hi φ G Jleft Jright diagonal u v a b center x := by
  have heval (side : Bool) :
      (movingPatternFinBulkData e n m t (fun _ => small) slot perm pattern side).map x =
      buildMovingSlotData n (t side)
        (treeLeafMap (List.map (fun j => x (e.symm (.inl j)))) n small)
        (treeLeafMap (List.map (fun j => x (e.symm (.inl j)))) n
          (movingPatternBulkLeaves n m slot perm side))
        (movingPatternSamples primes n (fun i => x (e.symm (.inr (pattern i)))) side) := by
    exact movingPatternFinData_evaluate e t (fun _ => small)
      (movingPatternBulkLeaves n m slot perm) pattern x side
  have hterm (side : Bool) (XL XR : ℕ) :
      let T := buildMovingSlotData n (t side)
        (treeLeafMap (List.map (fun j => x (e.symm (.inl j)))) n small)
        (treeLeafMap (List.map (fun j => x (e.symm (.inl j)))) n
          (movingPatternBulkLeaves n m slot perm side))
        (movingPatternSamples primes n (fun i => x (e.symm (.inr (pattern i)))) side)
      movingSupportedWeight (fun q : primes => (q : ℕ)) outside T XL XR
        (movingOriginalGiantWeight p (fun q : primes => (q : ℕ)) childBound pivotBound
          (fun _ => f) (fun _ _ _ _ => 1) g Dq Finset.univ ψ X lo hi φ G T (t side) XL XR) =
      movingSupportedWeight (fun i => (x i : ℕ)) outside
        (movingPatternFinBulkData e n m t (fun _ => small) slot perm pattern side) XL XR
        (movingOriginalGiantWeight p (fun i => (x i : ℕ)) childBound pivotBound
          (fun _ => f) (fun _ _ _ _ => 1) g Dq Finset.univ ψ X lo hi φ G
          (movingPatternFinBulkData e n m t (fun _ => small) slot perm pattern side)
          (t side) XL XR) := by
    dsimp only
    rw [← heval side, movingOriginalGiantWeight_map, movingSupportedWeight_map]
    rfl
  have hprod : MovingSlotReversal.naturalProduct (fun i => (x i : ℕ))
      (movingPatternRegularSlots e n m small slot) =
      MovingSlotReversal.naturalProduct (fun j => (x (e.symm (.inl j)) : ℕ))
        (flattenMovingSlots n small ++ flattenMovingSlots n (bulkSlotLeaves n m slot)) := by
    rw [movingPatternRegularSlots_eq_map, MovingSlotReversal.naturalProduct_map]
    rfl
  rw [movingOriginalPatternMatchedObservable_primeProduct]
  unfold movingOriginalMatchedKernel
  dsimp only
  rw [← movingPatternSamples_pair]
  dsimp only
  apply congrArg (complexPrimeInterval 1 0 a b)
  funext y
  apply congrArg (complexIntegerInterval 1 0 u v center)
  funext z
  simp only [Bool.false_eq_true, ite_false, ite_true]
  rw [hterm false, hterm true]
  unfold movingExternalDiagonalWeight movingOriginalSupportedOuterPair
  dsimp only
  rw [hprod]
  exact (mul_assoc _ _ _).symm

theorem movingOriginalMatchedMean_finite_patterns {B : Type} [Fintype B]
    {n m : ℕ} (t : Bool → FrequencyTree ℤ n)
    (small : TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
    (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
    (μ : ℕ → primes → ℝ) (ν : B → primes → ℝ)
    (g : ∀ i, ZMod (p i) → ℂ) (Dq : ∀ i, (ZMod (p i))ˣ)
    (greg : ∀ q : ℕ, ZMod q → ℂ) (sreg : ℤ)
    (f : ℤ → ℂ) (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (Jleft Jright : ℝ) (diagonal : Bool) (u v a b center : ℝ)
    (N : Setoid (Bool × MovingSampleIndex n) → ℕ)
    (e : ∀ s : Setoid (Bool × MovingSampleIndex n), Fin (N s + 1) ≃ B ⊕ Quotient s) :
    let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
    movingOriginalMatchedMean p (fun q : primes => (q : ℕ)) outside μ ν childBound pivotBound
      f g Dq Finset.univ ψ X lo hi φ G n t small (movingPatternBulkLeaves n m slot perm) greg sreg
      Jleft Jright diagonal u v a b center =
      ∑ s : Setoid (Bool × MovingSampleIndex n), ∑ x : Fin (N s + 1) → primes,
        movingOriginalPatternWeight (e s) μ ν (fun q : primes => (q : ℕ)) n
          (fun i => Quotient.mk'' i)
          (movingOriginalPatternMatchedObservable (e s) t small slot perm (fun i => Quotient.mk'' i)
            primes hprimes p g Dq (movingPatternRegularSlots (e s) n m small slot).get
            (fun _ => true) sreg (fun x => movingRegularOther (fun i => (x i : ℕ)) outside
              (movingPatternRegularSlots (e s) n m small slot)) greg f outside childBound pivotBound
            ψ X lo hi φ G Jleft Jright diagonal u v a b center) x := by
  let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
  dsimp only
  rw [movingOriginalMatchedMean_patterns p (fun q : primes => (q : ℕ)) outside μ ν]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro x _
  unfold movingOriginalPatternWeight
  congr 1
  unfold movingPatternInjectionGuard
  split_ifs
  · exact movingOriginalMatchedKernel_fin (e s) t small slot perm _ primes hprimes p g Dq greg sreg
      f outside childBound pivotBound ψ X lo hi φ G Jleft Jright diagonal u v a b center x
  · rfl

end Ostmann

end OAI
