import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternOriginalIntegralNorm
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternPrimeSupport
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSeparatedNorm
import OAI.NumberTheory.Ostmann.Arithmetic.MovingLeafAmplitude

namespace OAI

/-! # The published giant comparison under the unchanged original prior -/

namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators SchwartzMap

/-- Apply the published progression input before the signed arithmetic norm.
The internal modulus is the actual image of the sampled internal primes.
Its CRT coprimality and all compensation data are derived here. -/
theorem PublishedProgressionInput.movingPattern_original_prime_norm
    (input : PublishedProgressionInput) (n : ℕ) (Cbudget : ℝ) (d : ℕ) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (B C I : Type) [Fintype B] [Fintype C] [Fintype I] (N m : ℕ)
        (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
        (t : Bool → FrequencyTree ℤ n) (small : TreeLeafTuple (List B) n)
        (slot : (TreeLeafIndex n × Fin m) ↪ B) (pattern : Bool × MovingSampleIndex n → C)
        (_rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
        (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
        (μ : ℕ → primes → ℝ) (ν : B → primes → ℝ)
        (p : I → ℕ) [∀ i, Fact (p i).Prime] (_hinjp : Function.Injective p)
        (g : ∀ i, ZMod (p i) → ℂ) (Dq : ∀ i, (ZMod (p i))ˣ)
        (f : ℤ → ℂ) (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
        (R : ℤ) (r : ℕ) [NeZero r] (Q V : ℕ)
        (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
        (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
        (φ : ℝ → ℝ) (G : ℕ → ℝ) (Bφ Dφ E U u v a b : ℝ),
      let T := movingPatternFinBulkData e n m t (fun _ => small) slot (Equiv.refl _) pattern
      let coeff := movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) n pattern (fun _ => 1)
      let Pi := fun x => movingPatternInternalPrimes e (fun q : primes => (q : ℕ)) x
      let M := fun x => ∏ z, movingArithmeticModuli r p (Pi x) Finset.univ z
      let Reg := fun x => MovingSlotReversal.naturalProduct (fun i => (x i : ℕ))
        (flattenMovingSlots n (movingPatternFiniteSmall e n small) ++
          flattenMovingSlots n (bulkSlotLeaves n m (movingPatternBulkEmbedding e slot)))
      let A := (∏ i, (p i : ℝ) ^ (2 ^ n)) ^ 2
      (∀ j q, 0 ≤ μ j q) → (∀ j q, 0 ≤ ν j q) →
      (∀ j, ∑ q, μ j q = 1) → (∀ j, ∑ q, ν j q = 1) →
      0 ≤ E → 0 ≤ U → (∀ j (q : primes), (q : ℝ) * μ j q ≤ E) →
      (∀ q : primes, (q : ℝ) ≤ U) →
      (∀ b, n ≤ tierB b) → (∀ i, tierC (pattern i) = movingSampleTier i.2) →
      (∀ b, ∀ s ∈ allFrequencyList n (t b), s.natAbs ≤ V) →
      (∀ s, ‖f s‖ ≤ 1) → (∀ i, g i 0 = 0) → (∀ i z, ‖g i z‖ ≤ (p i : ℝ)) →
      (∀ q ∈ outside, ∃ i, p i = q) →
      (∀ b, (T b).frequencyProduct ∣ R) → R ^ (n + 1) ∣ (r : ℤ) →
      (∀ i, r.Coprime (p i)) → (∀ i, V < p i) →
      2 ≤ Q → 0 ≤ Bφ → 0 ≤ Dφ → (∀ z, |φ z| ≤ Bφ) →
      (∀ z w, |φ z - φ w| ≤ Dφ * |z - w|) → (∀ z, 1 ≤ |z| → φ z = 0) →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 1000 : ℝ) * L) →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ u → u ≤ v → v ≤ u + 1 →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ a → a ≤ b → b ≤ a + 1 →
      2 * A * (movingFourierVariationBudget ψ V lo hi n *
        (2 * Bφ + Dφ * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 ≤
          Real.exp (Cbudget * L ^ d + Cbudget * L * Real.exp ((12 / 1000 : ℝ) * L)) →
      (∀ x, coeff x ≠ 0 →
        (∀ i j, (Sum.elim tierB tierC) (e i) ≠ (Sum.elim tierB tierC) (e j) →
          (x i : ℕ) ≠ (x j : ℕ)) ∧
        (∀ i, V < (x i : ℕ)) ∧
        (∀ i, IsCoprime ((x i : ℕ) : ℤ) R) ∧
        (∀ i, r.Coprime (x i : ℕ)) ∧
        (∀ i j, ((x j : ℕ) : ZMod (p i)) ≠ 0) ∧
        M x ≤ Q ∧
        pageAtModulus (M x) (selectedPageZero input Q) =
          pageAtModulus r (selectedPageZero input Q) ∧
        Real.log (M x : ℝ) ≤ Real.exp ((12 / 1000 : ℝ) * L) ∧
        Real.log (Reg x : ℝ) ≤ Real.exp ((12 / 1000 : ℝ) * L)) →
      let actual := movingOriginalPatternPrimeObservable e pattern p
        (fun q : primes => (q : ℕ)) outside childBound pivotBound (fun {_} _ => f)
        g Dq Finset.univ ψ X lo hi φ G t small (bulkSlotLeaves n m slot) u v a b
      let integral := fun x => ∫ z in Set.Ioc u v, ∫ y in Set.Ioc a b,
        movingPatternTwoPrimeObservable e t (fun _ => small) slot (Equiv.refl _) pattern
          primes hprimes childBound pivotBound hfreq (fun _ {_} _ => f)
          (fun _ {_} _ _ _ _ => 1) outside R r p g (fun i _ => Dq i) input Q z y
          ψ X lo hi hlo hhi φ G (Real.exp z) (Real.exp y) x / ((z : ℂ) * (y : ℂ))
      ‖∑ x, movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) n pattern actual x‖ ≤
        (((2 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C)) * U ^ Fintype.card C) *
          (Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) +
            Real.exp (-Real.exp ((1225 / 100000 : ℝ) * L))) +
        ‖∑ x, movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) n pattern integral x *
          movingPatternPrimeHaarProduct e (fun q : primes => (q : ℕ))
            (fun q => hprimes _ q.property) n t (fun _ => small)
            (movingPatternBulkLeaves n m slot (Equiv.refl _)) pattern x‖ := by
  filter_upwards [input.moving_original_pattern_prime_haar_rate n Cbudget d] with L hL
  intro B C I _ _ _ N m e tierB tierC t small slot pattern rep primes hprimes μ ν
    p _ hinjp g Dq f outside childBound pivotBound R r _ Q V hfreq ψ X lo hi hlo hhi
    φ G Bφ Dφ E U u v a b
  dsimp only
  let T := movingPatternFinBulkData e n m t (fun _ => small) slot (Equiv.refl _) pattern
  let Pi := fun x => movingPatternInternalPrimes e (fun q : primes => (q : ℕ)) x
  let A := (∏ i, (p i : ℝ) ^ (2 ^ n)) ^ 2
  intro hμ hν hμmass hνmass hE hU hbound hsize hB htier hV hf hg hgnorm hout hR
    hprecision hrp hspecLarge hQ hBφ hDφ hφ hlip hφout hQlog hu huv hv ha hab hb
    hbudget hdata
  apply movingPattern_original_integral_norm e t small slot pattern rep primes hprimes μ ν
    childBound pivotBound hfreq f outside R r p g Dq input Q ψ X lo hi hlo hhi φ G u v a b
    E U _ hE hU (by positivity) hμ hν hμmass hνmass hbound hsize
  intro x hx
  obtain ⟨hdisjoint, hlarge, hsmallR, hrcop, hres, hMQ, hpage, hMlog, hReglog⟩ := hdata x hx
  have hprime (i) : (x i : ℕ).Prime := hprimes _ (x i).property
  have hPi := movingPatternInternalPrimes_prime e (fun q : primes => (q : ℕ))
    (fun q => hprimes _ q.property) x
  let : ∀ q : Pi x, Fact q.val.Prime := fun q => ⟨hPi _ q.property⟩
  have hnz (z) : movingArithmeticModuli r p (Pi x) Finset.univ z ≠ 0 :=
    movingArithmeticModuli_ne_zero r p (Pi x) Finset.univ (NeZero.ne r) hPi
      (fun i _ => (inferInstance : Fact (p i).Prime).out) z
  let : ∀ z, NeZero (movingArithmeticModuli r p (Pi x) Finset.univ z) := fun z => ⟨hnz z⟩
  let : NeZero (∏ z, movingArithmeticModuli r p (Pi x) Finset.univ z) :=
    ⟨Finset.prod_ne_zero_iff.mpr (fun z _ => hnz z)⟩
  have hsep (i : I) (j : Fin (N + 1)) : (x j : ℕ) ≠ p i := by
    intro heq
    apply hres i j
    rw [heq]
    exact ZMod.natCast_self (p i)
  have hc := movingPattern_prime_moduli_coprime e (fun q : primes => (q : ℕ))
    (fun q => hprimes _ q.property) x r p (fun i => (inferInstance : Fact (p i).Prime).out)
    hinjp hrcop hrp hsep
  have hinj := movingPattern_nonzero_internal_injective e μ ν (fun q : primes => (q : ℕ))
    Subtype.val_injective pattern (fun _ => 1) x hx
  have hweight (side) : ‖movingDataWeight (fun {_} _ => f) (fun {_} _ _ _ _ => 1) (T side)‖ ≤ 1 :=
    movingDataWeight_unit_norm_le_one (fun {_} _ => f) (fun s _ => hf s) (T side)
  have hnorm (z w : ℕ) :
      ‖movingSeparatedPairResidueCoefficient p (fun i => (x i : ℕ)) outside
        (fun _ {_} _ => f) (fun _ {_} _ _ _ _ => 1) g (fun _ => Dq) Finset.univ T
        (fun side => (T side).formulaNodes (fun i => (x i : ℕ)) (fun i => (hprime i).ne_zero)
          childBound pivotBound (movingPatternFinBulkData_frequencies e t (fun _ => small)
            slot (Equiv.refl _) pattern (· ≠ 0) hfreq side) (.prime false) (.prime true)) R z w‖ ≤ A := by
    apply (movingSeparatedPairResidueCoefficient_norm p (fun i => (x i : ℕ)) outside
      (fun _ {_} _ => f) (fun _ {_} _ _ _ _ => 1) g (fun _ => Dq) Finset.univ
      (fun i => (p i : ℝ)) (fun i _ => Nat.cast_nonneg _) (fun i _ => hgnorm i) T _ R z w).trans
    change (‖movingDataWeight (fun {_} _ => f) (fun {_} _ _ _ _ => 1) (T false)‖ * _ ) *
      (‖movingDataWeight (fun {_} _ => f) (fun {_} _ _ _ _ => 1) (T true)‖ * _) ≤ _
    have hprod : 0 ≤ ∏ i, (p i : ℝ) ^ (2 ^ n) := by positivity
    have hh := mul_le_mul (mul_le_mul_of_nonneg_right (hweight false) hprod)
      (mul_le_mul_of_nonneg_right (hweight true) hprod) (by positivity) (by positivity)
    simpa only [one_mul, pow_two, A] using hh
  exact hL B C I N m e tierB tierC t small slot pattern primes hprimes x p g Dq f
    outside childBound pivotBound R r (Pi x) hfreq V ψ X lo hi hlo hhi φ G Bφ Dφ
    hB htier hdisjoint hV hlarge hg hout hR hprecision hsmallR hres hspecLarge
    rfl hinj hc Q hQ hMQ hpage hBφ hDφ hφ hlip hφout hQlog hMlog
    hReglog u v a b hu huv hv ha hab hb A (by dsimp only [A]; positivity)
    (fun z _ w _ => hnorm z w) hbudget

end Ostmann

end OAI
