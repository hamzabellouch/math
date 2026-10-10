import OAI.NumberTheory.Ostmann.Arithmetic.MovingPrimeFrequencyAverage
import OAI.NumberTheory.Ostmann.Arithmetic.FrozenSpectatorAbsolute

namespace OAI

/-! # The exact local factors in the final two-prime environment -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingInternalPrimeAverage {σ : Type*} {n : ℕ}
    (value : σ → ℕ) (T : Bool → MovingSlotData σ n) (p : ℕ) [Fact p.Prime] : ℂ :=
  (Fintype.card ((ZMod (p ^ 2))ˣ × (ZMod (p ^ 2))ˣ) : ℂ)⁻¹ *
    ∑ z : (ZMod (p ^ 2))ˣ × (ZMod (p ^ 2))ˣ,
      movingInternalPairFactor value T p z.1 z.2

noncomputable def movingSpectatorPrimeAverage {σ : Type*} (value : σ → ℕ)
    (p : ℕ) [Fact p.Prime] (g : ZMod p → ℂ) (D : Bool → (ZMod p)ˣ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) : ℂ :=
  (Fintype.card ((ZMod p)ˣ × (ZMod p)ˣ) : ℂ)⁻¹ *
    ∑ z : (ZMod p)ˣ × (ZMod p)ˣ, movingSpectatorPairFactor value p g D T z.1 z.2

noncomputable def frozenBulkSpectatorPrime {σ : Type*} {p : ℕ} [Fact p.Prime]
    (base : σ → ℕ) (n m : ℕ) (t : Bool → FrequencyTree ℤ n)
    (small : Bool → TreeLeafTuple (List σ) n) (samples : Bool → MovingSampleSlots σ n)
    (D : Bool → (ZMod p)ˣ) (e : Equiv.Perm (TreeLeafIndex n × Fin m)) (g : ZMod p → ℂ)
    (z : TreeLeafIndex n × Fin m → (ZMod p)ˣ) : ℂ :=
  (Fintype.card ((ZMod p)ˣ × (ZMod p)ˣ) : ℂ)⁻¹ *
    ∑ a, frozenBulkSpectatorPair base n m t small samples D e g a z

theorem movingArithmeticPrimePageFactor_averages {σ I : Type*}
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (D : Bool → ∀ i, (ZMod (q i))ˣ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode)
    (R : ℤ) (r : ℕ) [NeZero r] (P : Finset ℕ) (S : Finset I)
    [∀ p : P, Fact p.val.Prime] [∀ b, NeZero (movingArithmeticModuli r q P S b)]
    (input : PublishedProgressionInput) (Q : ℕ) (x y : ℝ) :
    (∏ b, (Fintype.card ((ZMod (movingArithmeticModuli r q P S b))ˣ ×
      (ZMod (movingArithmeticModuli r q P S b))ˣ) : ℂ)⁻¹ *
      ∑ z, movingArithmeticPrimePageFactor r q P S input Q x y
        (movingArithmeticLocalFactor q value outside F E g D T nodes R r P S) b z) =
      movingFrequencyPrimeAverage value outside F E T nodes R r input Q x y *
        (∏ p : P, movingInternalPrimeAverage value T p.val) *
        ∏ i : S, movingSpectatorPrimeAverage value (q i.val) (g i.val)
          (fun side => D side i.val) T := by
  simp only [Fintype.prod_sum_type, Fintype.prod_unique, movingArithmeticPrimePageFactor,
    movingArithmeticLocalFactor, movingArithmeticModuli, movingFrequencyPrimeAverage,
    correctedPrimePairAverage, movingInternalPrimeAverage, movingSpectatorPrimeAverage]
  rw [← mul_assoc]
  congr 4

/-- Both exceptional-character multipliers remain in the frequency factor.
All internal and spectator factors have the literal two-unit law. -/
theorem movingSeparatedPairResidueCoefficient_prime_page_factorization {σ I : Type*}
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (D : Bool → ∀ i, (ZMod (q i))ˣ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode)
    (R : ℤ) (r : ℕ) [NeZero r] (P : Finset ℕ) (S : Finset I)
    [∀ p : P, Fact p.val.Prime] [∀ b, NeZero (movingArithmeticModuli r q P S b)]
    [NeZero (∏ b, movingArithmeticModuli r q P S b)]
    (hf : ∀ side, (T side).Frequencies (· ≠ 0))
    (hR : ∀ side, (T side).frequencyProduct ∣ R)
    (hfrequency : R ^ (n + 1) ∣ (r : ℤ))
    (hcover : ∀ side, ∀ o ∈ (T side).occurrences,
      ∀ i ∈ o.current.compensationSlots, value i ∈ P)
    (hc : Pairwise (fun b c => (movingArithmeticModuli r q P S b).Coprime
      (movingArithmeticModuli r q P S c)))
    (input : PublishedProgressionInput) (Q : ℕ)
    (hpage : pageAtModulus (∏ b, movingArithmeticModuli r q P S b) (selectedPageZero input Q) =
      pageAtModulus r (selectedPageZero input Q)) (x y : ℝ) :
    correctedPrimePairAverage input Q (∏ b, movingArithmeticModuli r q P S b)
      (movingSeparatedPairResidueCoefficient q value outside F E g D S T nodes R) x y =
      movingFrequencyPrimeAverage value outside F E T nodes R r input Q x y *
        (∏ p : P, movingInternalPrimeAverage value T p.val) *
        ∏ i : S, movingSpectatorPrimeAverage value (q i.val) (g i.val)
          (fun side => D side i.val) T := by
  rw [movingSeparatedPairResidueCoefficient_prime_page_average q value outside F E g D T nodes
    R r P S hf hR hfrequency hcover hc input Q hpage]
  exact movingArithmeticPrimePageFactor_averages q value outside F E g D T nodes R r P S input Q x y

theorem frozenBulkSpectatorPrime_actual {σ : Type*} {q : ℕ} [Fact q.Prime]
    (base : σ → ℕ) (n m : ℕ) (t : Bool → FrequencyTree ℤ n)
    (small : Bool → TreeLeafTuple (List σ) n) (samples : Bool → MovingSampleSlots σ n)
    (D : Bool → (ZMod q)ˣ) (e : Equiv.Perm (TreeLeafIndex n × Fin m))
    (value : σ → ℕ)
    (hv : ∀ b, movingSlotValues value n (small b) = movingSlotValues base n (small b))
    (hs : ∀ b, (samples b).values value = (samples b).values base)
    (slot : TreeLeafIndex n × Fin m → σ) (g : ZMod q → ℂ)
    (z : TreeLeafIndex n × Fin m → (ZMod q)ˣ)
    (hz : ∀ j, (value (slot j) : ZMod q) = (z j : ZMod q)) :
    movingSpectatorPrimeAverage value q g D
      (fun b => buildMovingSlotData n (t b) (small b)
        (if b then bulkSlotLeaves n m (slot ∘ e.symm) else bulkSlotLeaves n m slot)
        (samples b)) = frozenBulkSpectatorPrime base n m t small samples D e g z := by
  unfold movingSpectatorPrimeAverage frozenBulkSpectatorPrime
  apply congrArg ((Fintype.card ((ZMod q)ˣ × (ZMod q)ˣ) : ℂ)⁻¹ * ·)
  apply Finset.sum_congr rfl
  intro a _
  exact frozenBulkSpectatorPair_actual base n m t small samples D e value hv hs slot g a z hz

/-- The original two-prime spectator average has the same absolute third
moment bound, without a density correction. -/
theorem frozenBulkSpectatorPrime_absolute_mean_le {σ : Type*} {q : ℕ} [Fact q.Prime]
    (hq : 3 ≤ q) (base : σ → ℕ) (n m : ℕ) (hm : 0 < m)
    (t : Bool → FrequencyTree ℤ n)
    (small : Bool → TreeLeafTuple (List σ) n) (samples : Bool → MovingSampleSlots σ n)
    (hfreq : ∀ b, movingGiantFrequencyUnits q n (t b))
    (hsmall : ∀ b, ((treeLeafProduct n (movingSlotValues base n (small b)) : ℕ) : ZMod q) ≠ 0)
    (hsamples : ∀ b, ((samples b).values base).UnitsAt q)
    (D : Bool → (ZMod q)ˣ) (e : Equiv.Perm (TreeLeafIndex n × Fin m))
    (g : ZMod q → ℂ) (hg : g 0 = 0) (henergy : ∑ x : ZMod q, ‖g x‖ ^ 2 ≤ (q : ℝ)) :
    (Fintype.card (TreeLeafIndex n × Fin m → (ZMod q)ˣ) : ℝ)⁻¹ *
      (∑ z : TreeLeafIndex n × Fin m → (ZMod q)ˣ,
        ‖frozenBulkSpectatorPrime base n m t small samples D e g z‖) ≤ (3 : ℝ) ^ (2 ^ n) := by
  have h := uniform_average_norm_average_mul_le
    (A := TreeLeafIndex n × Fin m → (ZMod q)ˣ)
    (B := (ZMod q)ˣ × (ZMod q)ˣ)
    (fun z a => frozenBulkSpectatorPair base n m t small samples D e g a z)
    (fun _ => 1) 1 ((3 : ℝ) ^ (2 ^ n)) (by norm_num) (fun _ => by simp)
    (fun a => frozenBulkSpectatorPair_absolute_mean_le hq base n m hm t small samples
      hfreq hsmall hsamples D e g hg henergy a)
  simpa only [mul_one, one_mul, frozenBulkSpectatorPrime] using h

end Ostmann

end OAI
