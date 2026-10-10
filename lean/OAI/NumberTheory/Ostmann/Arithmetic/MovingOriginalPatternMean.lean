import OAI.NumberTheory.Ostmann.Arithmetic.MovingPrimeSquareBudget
import OAI.NumberTheory.Ostmann.Arithmetic.MovingOriginalPatternSum
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternArithmeticComparison
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSampleMap

namespace OAI

/-! # Exact equality patterns under the original external prime law -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

/-- The fixed-sample prime integral before choosing any equality pattern. -/
noncomputable def movingOriginalPairPrimeKernel {σ I B : Type} {n : ℕ}
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (childBound pivotBound : ℕ → ℕ)
    (F : {d : ℕ} → MovingSlotData σ d → ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (t : Bool → FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List B) n)
    (u v r w : ℝ) (y : B → σ) (a : MovingSampleSlots σ n × MovingSampleSlots σ n) : ℂ :=
  let H := fun b XL XR =>
    let T := buildMovingSlotData n (t b) (treeLeafMap (List.map y) n small)
      (treeLeafMap (List.map y) n bulk) (if b then a.2 else a.1)
    movingSupportedWeight value outside T XL XR
      (movingOriginalGiantWeight q value childBound pivotBound F (fun _ _ _ _ => 1)
        g Dq S ψ X lo hi φ G T (t b) XL XR)
  complexPrimeInterval 1 0 r w (fun y => complexPrimeInterval 1 0 u v (fun x =>
    H false ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊ * star (H true ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊)))

/-- The same actual prime integral in the full finite pattern coordinates. -/
noncomputable def movingOriginalPatternPrimeObservable {σ I B C : Type}
    {N n : ℕ} (e : Fin (N + 1) ≃ B ⊕ C)
    (pattern : Bool × MovingSampleIndex n → C)
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (childBound pivotBound : ℕ → ℕ)
    (F : {d : ℕ} → MovingSlotData σ d → ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (t : Bool → FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List B) n)
    (u v r w : ℝ) (x : Fin (N + 1) → σ) : ℂ :=
  movingOriginalPairPrimeKernel q value outside childBound pivotBound F g Dq S
    ψ X lo hi φ G t small bulk u v r w (fun b => x (e.symm (.inl b)))
    ((movingSamplePairCoordinates σ n).symm (fun i => x (e.symm (.inr (pattern i)))))

/-- Finite reindexing is proved independently of the large prime integrand. -/
theorem moving_external_pattern_mean {σ B : Type} [Fintype σ] [Fintype B]
    (μ : ℕ → σ → ℝ) (ν : B → σ → ℝ) (value : σ → ℕ) (n : ℕ)
    (H : (B → σ) → (MovingSampleSlots σ n × MovingSampleSlots σ n) → ℂ) :
    let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
    ∀ (N : Setoid (Bool × MovingSampleIndex n) → ℕ)
      (e : ∀ s : Setoid (Bool × MovingSampleIndex n), Fin (N s + 1) ≃ B ⊕ Quotient s),
    (∑ y : B → σ, ((∏ b, ν b (y b) : ℝ) : ℂ) *
      ∑ s : Setoid (Bool × MovingSampleIndex n),
        ∑ z : {z : Quotient s → σ // Function.Injective z},
          (internalPatternWeight (fun i => Quotient.mk'' i)
            (fun i => μ (movingSampleTier i.2)) value z.val : ℂ) *
          H y ((movingSamplePairCoordinates σ n).symm (fun i => z.val (Quotient.mk'' i)))) =
    ∑ s : Setoid (Bool × MovingSampleIndex n), ∑ x : Fin (N s + 1) → σ,
      movingOriginalPatternWeight (e s) μ ν value n (fun i => Quotient.mk'' i)
        (fun x => H (fun b => x ((e s).symm (.inl b)))
          ((movingSamplePairCoordinates σ n).symm
            (fun i => x ((e s).symm (.inr (Quotient.mk'' i)))))) x := by
  dsimp only
  let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
  intro N e
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  let obs := fun x : Fin (N s + 1) → σ => H (fun b => x ((e s).symm (.inl b)))
    ((movingSamplePairCoordinates σ n).symm (fun i => x ((e s).symm (.inr (Quotient.mk'' i)))))
  have heq := movingOriginalPattern_sum_fin (e s) μ ν value n (fun i => Quotient.mk'' i) obs
  dsimp only [obs] at heq
  simp only [finite_univ_canonical] at heq ⊢
  unfold movingOriginalPatternWeight
  simp only [finite_univ_canonical] at heq ⊢
  refine Eq.trans ?_ heq
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  simp only [Equiv.apply_symm_apply, Sum.elim_inl, Sum.elim_inr, mul_assoc]

/-- Exact passage from the original two-history mean to the full coordinate
sum used by the arithmetic comparison. No independence of repeated internal
samples, deleted prime law, or new normalization is introduced. -/
theorem movingOriginalPrimePairMean_patterns {σ I B : Type}
    [Fintype σ] [Fintype B]
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (μ : ℕ → σ → ℝ) (ν : B → σ → ℝ) (childBound pivotBound : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (t : Bool → FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List B) n)
    (u v r w : ℝ) :
    let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
    ∀ (N : Setoid (Bool × MovingSampleIndex n) → ℕ)
      (e : ∀ s : Setoid (Bool × MovingSampleIndex n), Fin (N s + 1) ≃ B ⊕ Quotient s),
    movingOriginalPrimePairMean q value outside μ childBound pivotBound F g Dq S ψ X lo hi
      φ G n (fun y : B → σ => ∏ b, ν b (y b))
      (fun y => treeLeafMap (List.map y) n small)
      (fun y => treeLeafMap (List.map y) n bulk) u v r w (t false) (t true) =
    ∑ s : Setoid (Bool × MovingSampleIndex n), ∑ x : Fin (N s + 1) → σ,
      movingOriginalPatternWeight (e s) μ ν value n (fun i => Quotient.mk'' i)
        (movingOriginalPatternPrimeObservable (e s) (fun i => Quotient.mk'' i)
          q value outside childBound pivotBound F g Dq S ψ X lo hi φ G t small bulk u v r w) x := by
  dsimp only
  let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
  intro N e
  let H := movingOriginalPairPrimeKernel q value outside childBound pivotBound F g Dq S
    ψ X lo hi φ G t small bulk u v r w
  have hpair (y : B → σ) := movingOriginal_prime_pair_patterns q value outside μ
    childBound pivotBound (fun _ => F) g (fun _ => Dq) S ψ X lo hi φ G n t
    (fun _ => treeLeafMap (List.map y) n small)
    (fun _ => treeLeafMap (List.map y) n bulk) u v r w
  dsimp only at hpair
  have hexp : movingOriginalPrimePairMean q value outside μ childBound pivotBound F g Dq S
      ψ X lo hi φ G n (fun y : B → σ => ∏ b, ν b (y b))
      (fun y => treeLeafMap (List.map y) n small)
      (fun y => treeLeafMap (List.map y) n bulk) u v r w (t false) (t true) =
    ∑ y : B → σ, ((∏ b, ν b (y b) : ℝ) : ℂ) *
      ∑ s : Setoid (Bool × MovingSampleIndex n),
        ∑ z : {z : Quotient s → σ // Function.Injective z},
          (internalPatternWeight (fun i => Quotient.mk'' i)
            (fun i => μ (movingSampleTier i.2)) value z.val : ℂ) *
          H y ((movingSamplePairCoordinates σ n).symm (fun i => z.val (Quotient.mk'' i))) := by
    unfold movingOriginalPrimePairMean
    apply Finset.sum_congr rfl
    intro y _
    congr 1
    exact hpair y
  rw [hexp]
  exact moving_external_pattern_mean μ ν value n H N e

end Ostmann

end OAI
