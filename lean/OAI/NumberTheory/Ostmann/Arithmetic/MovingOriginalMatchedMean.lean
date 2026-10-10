import OAI.NumberTheory.Ostmann.Arithmetic.MovingOriginalDiagonalMean
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternMatchedProduct

namespace OAI

/-! # The original matched-history mean and its exact equality patterns -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

noncomputable def movingOriginalMatchedKernel {σ I B : Type*} {n : ℕ}
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (childBound pivotBound : ℕ → ℕ) (f : ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (t : Bool → FrequencyTree ℤ n) (small : TreeLeafTuple (List B) n) (bulk : Bool → TreeLeafTuple (List B) n)
    (greg : ∀ q : ℕ, ZMod q → ℂ) (sreg : ℤ)
    (Jleft Jright : ℝ) (diagonal : Bool) (u v r w center : ℝ)
    (y : B → σ) (a : MovingSampleSlots σ n × MovingSampleSlots σ n) : ℂ :=
  let H := fun b XL XR =>
    let T := buildMovingSlotData n (t b) (treeLeafMap (List.map y) n small)
      (treeLeafMap (List.map y) n (bulk b)) (if b then a.2 else a.1)
    movingSupportedWeight value outside T XL XR
      (movingOriginalGiantWeight q value childBound pivotBound (fun _ => f)
        (fun _ _ _ _ => 1) g Dq S ψ X lo hi φ G T (t b) XL XR)
  complexPrimeInterval 1 0 r w (fun z => complexIntegerInterval 1 0 u v center (fun x =>
    (H false ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊ *
      star (H true ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊)) *
      movingExternalDiagonalWeight value outside small (bulk false) greg sreg φ Jleft Jright diagonal y x z))

/-- Both history averages and the external law are the original ones. -/
noncomputable def movingOriginalMatchedMean {σ I B : Type*}
    [Fintype σ] [Fintype B] (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ) (ν : B → σ → ℝ)
    (childBound pivotBound : ℕ → ℕ) (f : ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (t : Bool → FrequencyTree ℤ n) (small : TreeLeafTuple (List B) n) (bulk : Bool → TreeLeafTuple (List B) n)
    (greg : ∀ q : ℕ, ZMod q → ℂ) (sreg : ℤ)
    (Jleft Jright : ℝ) (diagonal : Bool) (u v r w center : ℝ) : ℂ :=
  ∑ y : B → σ, ((∏ b, ν b (y b) : ℝ) : ℂ) *
    complexPrimeInterval 1 0 r w (fun z => complexIntegerInterval 1 0 u v center (fun x =>
      (movingOriginalSampleAverage q value outside μ childBound pivotBound (fun _ => f)
        g Dq S ψ X lo hi φ G n (t false) (treeLeafMap (List.map y) n small)
        (treeLeafMap (List.map y) n (bulk false)) ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊ *
      star (movingOriginalSampleAverage q value outside μ childBound pivotBound (fun _ => f)
        g Dq S ψ X lo hi φ G n (t true) (treeLeafMap (List.map y) n small)
        (treeLeafMap (List.map y) n (bulk true)) ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊)) *
      movingExternalDiagonalWeight value outside small (bulk false) greg sreg φ Jleft Jright diagonal y x z))

theorem movingOriginalMatchedMean_patterns {σ I B : Type}
    [Fintype σ] [Fintype B] (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ) (ν : B → σ → ℝ)
    (childBound pivotBound : ℕ → ℕ) (f : ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (t : Bool → FrequencyTree ℤ n) (small : TreeLeafTuple (List B) n) (bulk : Bool → TreeLeafTuple (List B) n)
    (greg : ∀ q : ℕ, ZMod q → ℂ) (sreg : ℤ)
    (Jleft Jright : ℝ) (diagonal : Bool) (u v r w center : ℝ)
    (N : Setoid (Bool × MovingSampleIndex n) → ℕ)
    (e : ∀ s : Setoid (Bool × MovingSampleIndex n), Fin (N s + 1) ≃ B ⊕ Quotient s) :
    let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
    movingOriginalMatchedMean q value outside μ ν childBound pivotBound f g Dq S
      ψ X lo hi φ G n t small bulk greg sreg Jleft Jright diagonal u v r w center =
    ∑ s : Setoid (Bool × MovingSampleIndex n), ∑ x : Fin (N s + 1) → σ,
      movingOriginalPatternWeight (e s) μ ν value n (fun i => Quotient.mk'' i)
        (fun x => movingOriginalMatchedKernel q value outside childBound pivotBound f g Dq S
          ψ X lo hi φ G t small bulk greg sreg Jleft Jright diagonal u v r w center
          (fun b => x ((e s).symm (.inl b)))
          ((movingSamplePairCoordinates σ n).symm
            (fun i => x ((e s).symm (.inr (Quotient.mk'' i)))))) x := by
  let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
  dsimp only
  let H := movingOriginalMatchedKernel q value outside childBound pivotBound f g Dq S
    ψ X lo hi φ G t small bulk greg sreg Jleft Jright diagonal u v r w center
  have hpair (y : B → σ) :
      complexPrimeInterval 1 0 r w (fun z => complexIntegerInterval 1 0 u v center (fun x =>
        (movingOriginalSampleAverage q value outside μ childBound pivotBound (fun _ => f)
          g Dq S ψ X lo hi φ G n (t false) (treeLeafMap (List.map y) n small)
          (treeLeafMap (List.map y) n (bulk false)) ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊ *
        star (movingOriginalSampleAverage q value outside μ childBound pivotBound (fun _ => f)
          g Dq S ψ X lo hi φ G n (t true) (treeLeafMap (List.map y) n small)
          (treeLeafMap (List.map y) n (bulk true)) ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊)) *
        movingExternalDiagonalWeight value outside small (bulk false) greg sreg φ Jleft Jright diagonal y x z)) =
      ∑ s : Setoid (Bool × MovingSampleIndex n),
        ∑ a : {a : Quotient s → σ // Function.Injective a},
          (internalPatternWeight (fun i => Quotient.mk'' i)
            (fun i => μ (movingSampleTier i.2)) value a.val : ℂ) *
          H y ((movingSamplePairCoordinates σ n).symm (fun i => a.val (Quotient.mk'' i))) := by
    simp_rw [movingOriginalSampleAverage_compensated]
    exact movingCompensatedAverage_diagonal_patterns μ value n _ _ _ u v r w center
  unfold movingOriginalMatchedMean
  simp_rw [hpair]
  exact moving_external_pattern_mean μ ν value n H N e

end Ostmann

end OAI
