import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternPrimeIntegralBridge
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternArithmeticData
import OAI.NumberTheory.Ostmann.Arithmetic.MovingHarmonicSupport

namespace OAI

/-! # The original finite-pattern prime integral, with its actual CRT law -/

namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators SchwartzMap

/-- A direct application of the published progression input to the literal
pattern integral. Structural tree and compensation assumptions are derived
from the sampler and its prime ranges. The cutoff is uniform in all finite
pattern spaces, the sampled assignment, and the spectator list. -/
theorem PublishedProgressionInput.moving_original_pattern_prime_haar_rate
    (input : PublishedProgressionInput) (n : ℕ) (Cbudget : ℝ) (d : ℕ) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (B C I : Type) [Fintype C] [Fintype I] (N m : ℕ)
        (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
        (t : Bool → FrequencyTree ℤ n) (small : TreeLeafTuple (List B) n)
        (slot : (TreeLeafIndex n × Fin m) ↪ B) (pattern : Bool × MovingSampleIndex n → C)
        (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
        (x : Fin (N + 1) → primes)
        (p : I → ℕ) [∀ i, Fact (p i).Prime]
        (g : ∀ i, ZMod (p i) → ℂ) (Dq : ∀ i, (ZMod (p i))ˣ)
        (f : ℤ → ℂ) (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
        (R : ℤ) (r : ℕ) [NeZero r] (P : Finset ℕ) [∀ q : P, Fact q.val.Prime]
        [∀ b, NeZero (movingArithmeticModuli r p P Finset.univ b)]
        [NeZero (∏ b, movingArithmeticModuli r p P Finset.univ b)]
        (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
        (V : ℕ) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
        (φ : ℝ → ℝ) (G : ℕ → ℝ) (Bφ Dφ : ℝ),
      let value := fun i => (x i : ℕ)
      let T := movingPatternFinBulkData e n m t (fun _ => small) slot (Equiv.refl _) pattern
      let nodes := fun b => (T b).formulaNodes value
        (fun i => (hprimes _ (x i).property).ne_zero) childBound pivotBound
        (movingPatternFinBulkData_frequencies e t (fun _ => small) slot (Equiv.refl _)
          pattern (· ≠ 0) hfreq b) (.prime false) (.prime true)
      let M := ∏ b, movingArithmeticModuli r p P Finset.univ b
      let Reg := MovingSlotReversal.naturalProduct value
        (flattenMovingSlots n (movingPatternFiniteSmall e n small) ++
          flattenMovingSlots n (bulkSlotLeaves n m (movingPatternBulkEmbedding e slot)))
      (∀ b, n ≤ tierB b) → (∀ i, tierC (pattern i) = movingSampleTier i.2) →
      (∀ i j, (Sum.elim tierB tierC) (e i) ≠ (Sum.elim tierB tierC) (e j) → value i ≠ value j) →
      (∀ b, ∀ s ∈ allFrequencyList n (t b), s.natAbs ≤ V) → (∀ i, V < value i) →
      (∀ i, g i 0 = 0) → (∀ q ∈ outside, ∃ i, p i = q) →
      (∀ b, (T b).frequencyProduct ∣ R) → R ^ (n + 1) ∣ (r : ℤ) →
      (∀ i, IsCoprime (value i : ℤ) R) →
      (∀ i j, (value j : ZMod (p i)) ≠ 0) →
      (∀ i, V < p i) →
      P = Finset.univ.image (fun c : C => value (e.symm (.inr c))) →
      Function.Injective (fun c : C => value (e.symm (.inr c))) →
      Pairwise (fun a b => (movingArithmeticModuli r p P Finset.univ a).Coprime
        (movingArithmeticModuli r p P Finset.univ b)) →
      ∀ Q : ℕ, 2 ≤ Q → M ≤ Q →
      pageAtModulus M (selectedPageZero input Q) = pageAtModulus r (selectedPageZero input Q) →
      0 ≤ Bφ → 0 ≤ Dφ → (∀ z, |φ z| ≤ Bφ) →
      (∀ z w, |φ z - φ w| ≤ Dφ * |z - w|) → (∀ z, 1 ≤ |z| → φ z = 0) →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 1000 : ℝ) * L) →
      Real.log (M : ℝ) ≤ Real.exp ((12 / 1000 : ℝ) * L) →
      Real.log (Reg : ℝ) ≤ Real.exp ((12 / 1000 : ℝ) * L) →
      ∀ u v a b : ℝ,
      Real.exp ((49 / 1000 : ℝ) * L) ≤ u → u ≤ v → v ≤ u + 1 →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ a → a ≤ b → b ≤ a + 1 →
      ∀ A : ℝ, 0 ≤ A →
      (∀ z < M, ∀ w < M,
        ‖movingSeparatedPairResidueCoefficient p value outside (fun _ {_} _ => f)
          (fun _ {_} _ _ _ _ => 1) g (fun _ => Dq) Finset.univ T nodes R z w‖ ≤ A) →
      2 * A * (movingFourierVariationBudget ψ V lo hi n *
        (2 * Bφ + Dφ * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 ≤
          Real.exp (Cbudget * L ^ d + Cbudget * L * Real.exp ((12 / 1000 : ℝ) * L)) →
      ‖movingOriginalPatternPrimeObservable e pattern p (fun q : primes => (q : ℕ))
          outside childBound pivotBound (fun {_} _ => f) g Dq Finset.univ ψ X lo hi φ G
          t small (bulkSlotLeaves n m slot) u v a b x -
        (∫ z in Set.Ioc u v, ∫ y in Set.Ioc a b,
          movingPatternTwoPrimeObservable e t (fun _ => small) slot (Equiv.refl _) pattern
            primes hprimes childBound pivotBound hfreq (fun _ {_} _ => f)
            (fun _ {_} _ _ _ _ => 1) outside R r p g (fun i _ => Dq i) input Q z y
            ψ X lo hi hlo hhi φ G (Real.exp z) (Real.exp y) x / ((z : ℂ) * (y : ℂ))) *
          movingPatternPrimeHaarProduct e (fun q : primes => (q : ℕ))
            (fun q => hprimes _ q.property) n t (fun _ => small)
            (movingPatternBulkLeaves n m slot (Equiv.refl _)) pattern x‖ ≤
        Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) +
          Real.exp (-Real.exp ((1225 / 100000 : ℝ) * L)) := by
  filter_upwards [input.moving_original_supported_pair_haar_rate_uniform n Cbudget d] with L hL
  intro B C I _ _ N m e tierB tierC t small slot pattern primes hprimes x p _ g Dq f outside
    childBound pivotBound R r _ P _ _ _ hfreq V ψ X lo hi hlo hhi φ G Bφ Dφ
  dsimp only
  let value := fun i => (x i : ℕ)
  let T := movingPatternFinBulkData e n m t (fun _ => small) slot (Equiv.refl _) pattern
  let hf := movingPatternFinBulkData_frequencies e t (fun _ => small) slot (Equiv.refl _)
    pattern (· ≠ 0) hfreq
  let nodes := fun b => (T b).formulaNodes value (fun i => (hprimes _ (x i).property).ne_zero)
    childBound pivotBound (hf b) (.prime false) (.prime true)
  let M := ∏ b, movingArithmeticModuli r p P Finset.univ b
  let Reg := MovingSlotReversal.naturalProduct value
    (flattenMovingSlots n (movingPatternFiniteSmall e n small) ++
      flattenMovingSlots n (bulkSlotLeaves n m (movingPatternBulkEmbedding e slot)))
  intro hB htier hdisjoint hV hlarge hg hout hR hprecision hsmallR hres hspecLarge hP hinj hc
    Q hQ hMQ hpage hBφ hDφ hφ hlip hφout hQlog hMlog hReglog
    u v a b hu huv hv ha hab hb A hA hAbound hbudget
  have hprime (i) : (value i).Prime := hprimes _ (x i).property
  have hVN (side) : (T side).Frequencies (fun s => s.natAbs ≤ V) :=
    movingPatternFinBulkData_frequencies e t (fun _ => small) slot (Equiv.refl _) pattern _ hV side
  have hVR (side) : (T side).Frequencies (fun s => |(s : ℝ)| ≤ (V : ℝ)) :=
    (hVN side).mono (fun s hs => by
      simpa only [Nat.cast_natAbs, Int.cast_abs] using (show (s.natAbs : ℝ) ≤ V by exact_mod_cast hs))
  have hsmall (side) := (T side).small_frequency_units value hprime V hlarge (hf side) (hVN side)
  have hfmod (side) := (T side).small_frequency_residues value hprime V hlarge (hf side) (hVN side)
  have hden (side i) : (T side).ModularDenominators value (p i) := by
    apply (T side).modularDenominators_of_units value (p i) (hres i)
    exact movingPatternFinBulkData_frequencies e t (fun _ => small) slot (Equiv.refl _)
      pattern (fun s => (s : ZMod (p i)) ≠ 0)
      (fun b s hs => intCast_ne_zero_of_natAbs_lt (p i) s (hfreq b s hs)
        ((hV b s hs).trans_lt (hspecLarge i))) side
  have hcover := movingPatternFinBulkData_internal_cover e tierB tierC t (fun _ => small)
    slot (Equiv.refl _) pattern hB htier (fun q : primes => (q : ℕ)) x
  have hcoverP (side o) (ho : o ∈ (T side).occurrences) (j) (hj : j ∈ o.current.compensationSlots) :
      value j ∈ P := by
    rw [hP]
    exact hcover side o ho j hj
  have hperiod := movingArithmeticModuli_periods r p P Finset.univ R (n + 1) hprecision
  have hReg : 0 < Reg := by
    apply Nat.pos_of_ne_zero
    change (List.map value _).prod ≠ 0
    apply List.prod_ne_zero
    intro hz
    obtain ⟨i, _, hi⟩ := List.mem_map.mp hz
    exact (hprime i).ne_zero hi
  have h := hL (Fin (N + 1)) I p ((Sum.elim tierB tierC) ∘ e) value hprime hdisjoint
    outside childBound pivotBound T hf t
    (movingPatternFinBulkData_follows e t (fun _ => small) slot (Equiv.refl _) pattern)
    (movingPatternFinBulkData_levels e tierB tierC n m t (fun _ => small) slot (Equiv.refl _) pattern hB htier)
    (movingPatternFinBulkData_regular_coherent e t (fun _ => small) slot (Equiv.refl _) pattern)
    hsmall hfmod (fun _ {_} _ => f) (fun _ {_} _ _ _ _ => 1) g hg (fun _ => Dq) Finset.univ
    (fun q hq => by obtain ⟨i, hi⟩ := hout q hq; exact ⟨i, Finset.mem_univ _, hi⟩)
    R hR hsmallR (fun side i _ => hden side i) Reg
    (movingPatternFinBulkData_regular_product e t small slot pattern value)
    ψ X lo hi hlo hhi φ G Bφ Dφ hBφ hDφ hφ hlip hφout V hVR Q M hQ
    (Nat.one_le_iff_ne_zero.mpr (NeZero.ne M)) hMQ hperiod.1
    (fun side o ho j hj => hperiod.2.1 _ (hcoverP side o ho j hj))
    hperiod.2.2 hQlog u v a b hu huv hv ha hab hb hMlog hReg hReglog A hA hAbound hbudget
  rw [movingOriginalPatternPrimeObservable_pair_frequency]
  rw [movingPatternTwoPrimeObservable_integral_crt e t (fun _ => small) slot (Equiv.refl _)
    pattern primes hprimes childBound pivotBound hfreq (fun _ {_} _ => f)
    (fun _ {_} _ _ _ _ => 1) outside R r p g (fun i _ => Dq i) input Q ψ X lo hi hlo hhi φ G
    x P hP hinj hR hprecision hcoverP hc hpage]
  exact h

end Ostmann

end OAI
