import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternMixedIntegralCRT
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternPermutedProduct
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSupportedSeparatedDiagonalRate
import OAI.NumberTheory.Ostmann.Arithmetic.MovingHarmonicSupport
import OAI.NumberTheory.Ostmann.Arithmetic.MovingLeafAmplitude

namespace OAI

/-! # The literal mixed comparison for arbitrarily matched sample trees -/

namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.moving_pattern_matched_haar_rate
    (input : PublishedProgressionInput) (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (Afreq Wwin Bφ Dφ : ℝ) (hAfreq : 0 ≤ Afreq) (hWwin : 0 ≤ Wwin)
    (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (B C J : Type) [Fintype C] [Fintype J] (N : ℕ)
        (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
        (t : Bool → FrequencyTree ℤ n) (small : TreeLeafTuple (List B) n)
        (slot : (TreeLeafIndex n × Fin m) ↪ B)
        (perm : Equiv.Perm (TreeLeafIndex n × Fin m)) (pattern : Bool × MovingSampleIndex n → C)
        (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime) (x : Fin (N + 1) → primes)
        (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (g : ∀ i, ZMod (p i) → ℂ) (Dq : ∀ i, (ZMod (p i))ˣ)
        (reg : J → ℕ) [∀ j, Fact (reg j).Prime]
        (active : J → Bool) (sreg : ℤ) (other : ∀ j, ZMod (reg j))
        (greg : ∀ j, ZMod (reg j) → ℂ)
        (f : ℤ → ℂ) (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
        (R : ℤ) (r : ℕ) [NeZero r] (P : Finset ℕ) [∀ q : P, Fact q.val.Prime]
        [∀ b, NeZero (movingArithmeticModuli r p P Finset.univ b)]
        [NeZero (∏ b, movingArithmeticModuli r p P Finset.univ b)]
        (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
        (V : ℕ) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
        (φ : ℝ → ℝ) (G : ℕ → ℝ) (Jleft Jright : ℝ) (diagonal : Bool),
      let value := fun i => (x i : ℕ)
      let T := movingPatternFinBulkData e n m t (fun _ => small) slot perm pattern
      let M := ∏ b, movingArithmeticModuli r p P Finset.univ b
      let Reg := MovingSlotReversal.naturalProduct value
        (flattenMovingSlots n (movingPatternFiniteSmall e n small) ++
          flattenMovingSlots n (bulkSlotLeaves n m (movingPatternBulkEmbedding e slot)))
      (∀ b, n ≤ tierB b) → (∀ i, tierC (pattern i) = movingSampleTier i.2) →
      (∀ i j, (Sum.elim tierB tierC) (e i) ≠ (Sum.elim tierB tierC) (e j) → value i ≠ value j) →
      (∀ b, ∀ s ∈ allFrequencyList n (t b), s.natAbs ≤ V) → (∀ i, V < value i) →
      (∀ s, ‖f s‖ ≤ 1) → (∀ i, g i 0 = 0) → (∀ i z, ‖g i z‖ ≤ (p i : ℝ)) →
      (∀ q ∈ outside, ∃ i, p i = q) →
      (∀ b, (T b).frequencyProduct ∣ R) → R ^ (n + 1) ∣ (r : ℤ) →
      (∀ i, IsCoprime (value i : ℤ) R) →
      (∀ i j, (value j : ZMod (p i)) ≠ 0) → (∀ i, V < p i) →
      P = Finset.univ.image (fun c : C => value (e.symm (.inr c))) →
      Function.Injective (fun c : C => value (e.symm (.inr c))) →
      Pairwise (fun a b => (movingArithmeticModuli r p P Finset.univ a).Coprime
        (movingArithmeticModuli r p P Finset.univ b)) →
      Reg = ∏ j, reg j → Reg.Coprime M → Reg * M ≤ giantProgressionCutoff L →
      pageAtModulus (Reg * M) (selectedPageZero input (giantProgressionCutoff L)) =
        pageAtModulus M (selectedPageZero input (giantProgressionCutoff L)) →
      pageAtModulus M (selectedPageZero input (giantProgressionCutoff L)) =
        pageAtModulus r (selectedPageZero input (giantProgressionCutoff L)) →
      (∀ b, movingRegularOutsidePairwise value outside (T b)) →
      Pairwise (fun i j => (reg i).Coprime (reg j)) →
      (∀ i, (∏ j, reg j).Coprime (p i)) →
      (∀ i, (sreg : ZMod (reg i)) ≠ 0) → (∀ i, other i ≠ 0) →
      (∀ i, greg i 0 = 0) → (∀ i, (∑ z : ZMod (reg i), ‖greg i z‖ ^ 2) = reg i) →
      (V : ℝ) ≤ Real.exp (Afreq * m) → hi - lo ≤ Real.exp (Wwin * m) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      (∀ z, |φ z| ≤ Bφ) → (∀ z w, |φ z - φ w| ≤ Dφ * |z - w|) →
      (∀ z, 1 ≤ |z| → φ z = 0) →
      ∀ u v a b center : ℝ,
      Real.exp ((49 / 1000 : ℝ) * L) ≤ center → u ≤ v → v ≤ u + 1 → v ≤ center + 1 →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ a → a ≤ b → b ≤ a + 1 →
      ‖complexPrimeInterval 1 0 a b (fun y => complexIntegerInterval 1 0 u v center (fun z =>
          movingOriginalSupportedOuterPair p value outside childBound pivotBound
            (fun _ {_} _ => f) (fun _ {_} _ _ _ _ => 1) g (fun _ => Dq) Finset.univ
            ψ X lo hi φ G Jleft Jright diagonal T t ⌊Real.exp z⌋₊ ⌊Real.exp y⌋₊ *
          (naturalRegularMultiplier reg active sreg other greg ⌊Real.exp z⌋₊ ⌊Real.exp y⌋₊ : ℂ))) -
        (∫ z in Set.Ioc u v, ∫ y in Set.Ioc a b,
          ((giantOuterWeight φ Jleft Jright diagonal (Real.exp z) (Real.exp y) *
            (((∏ j, if active j then (1 : ℝ) else 1 - (reg j : ℝ)⁻¹) : ℝ) : ℂ)) *
            movingPatternPrimeObservable e t (fun _ => small) slot perm pattern
              primes hprimes childBound pivotBound hfreq (fun _ {_} _ => f)
              (fun _ {_} _ _ _ _ => 1) outside R r p g (fun i _ => Dq i) input
              (giantProgressionCutoff L) y ψ X lo hi hlo hhi φ G (Real.exp z) (Real.exp y) x) *
            (Real.exp (z - center) : ℂ) / (y : ℂ)) *
          movingPatternHaarProduct e (fun q : primes => (q : ℕ)) (fun q => hprimes _ q.property)
            n t (fun _ => small) (movingPatternBulkLeaves n m slot perm) pattern x‖ ≤
        Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) +
          Real.exp (-Real.exp ((1225 / 100000 : ℝ) * L)) := by
  filter_upwards [input.moving_original_supported_separated_diagonal_prime_rate ψ n r₀ k
    Afreq Wwin Bφ Dφ hAfreq hWwin hBφ hDφ] with L hL
  dsimp only
  intro B C J _ _ N e tierB tierC t small slot perm pattern primes hprimes x p _ g Dq
    reg _ active sreg other greg f outside childBound pivotBound R r _ P _ _ _ hfreq V
    X lo hi hlo hhi φ G Jleft Jright diagonal
  let m := spectatorBulkCount k L
  let value := fun i => (x i : ℕ)
  let T := movingPatternFinBulkData e n m t (fun _ => small) slot perm pattern
  let hf := movingPatternFinBulkData_frequencies e t (fun _ => small) slot perm
    pattern (· ≠ 0) hfreq
  let nodes := fun b => (T b).formulaNodes value (fun i => (hprimes _ (x i).property).ne_zero)
    childBound pivotBound (hf b) (.prime false) (.prime true)
  let M := ∏ b, movingArithmeticModuli r p P Finset.univ b
  intro hB htier hdisjoint hV hlarge hfnorm hg hgnorm hout hR hprecision hsmallR hres hspecLarge hP hinj hc
    hRegEq hcop hfull hpageReg hpage houtside hreg hqs hsreg hother hgreg henergy
    hVA hwindow hpupper hφ hlip hφout u v a b center hcenter huv hv hvcenter ha hab hb
  have hprime (i) : (value i).Prime := hprimes _ (x i).property
  have hVN (side) : (T side).Frequencies (fun s => s.natAbs ≤ V) :=
    movingPatternFinBulkData_frequencies e t (fun _ => small) slot perm pattern _ hV side
  have hVR (side) : (T side).Frequencies (fun s => |(s : ℝ)| ≤ (V : ℝ)) :=
    (hVN side).mono (fun s hs => by
      simpa only [Nat.cast_natAbs, Int.cast_abs] using (show (s.natAbs : ℝ) ≤ V by exact_mod_cast hs))
  have hsmall (side) := (T side).small_frequency_units value hprime V hlarge (hf side) (hVN side)
  have hfmod (side) := (T side).small_frequency_residues value hprime V hlarge (hf side) (hVN side)
  have hden (side i) : (T side).ModularDenominators value (p i) := by
    apply (T side).modularDenominators_of_units value (p i) (hres i)
    exact movingPatternFinBulkData_frequencies e t (fun _ => small) slot perm
      pattern (fun s => (s : ZMod (p i)) ≠ 0)
      (fun b s hs => intCast_ne_zero_of_natAbs_lt (p i) s (hfreq b s hs)
        ((hV b s hs).trans_lt (hspecLarge i))) side
  have hcover := movingPatternFinBulkData_internal_cover e tierB tierC t (fun _ => small)
    slot perm pattern hB htier (fun q : primes => (q : ℕ)) x
  have hcoverP (side o) (ho : o ∈ (T side).occurrences) (j) (hj : j ∈ o.current.compensationSlots) :
      value j ∈ P := by
    rw [hP]
    exact hcover side o ho j hj
  have hperiod := movingArithmeticModuli_periods r p P Finset.univ R (n + 1) hprecision

  have hweight (side) : ‖movingDataWeight (fun {_} _ => f) (fun {_} _ _ _ _ => 1) (T side)‖ ≤ 1 :=
    movingDataWeight_unit_norm_le_one (fun {_} _ => f) (fun s _ => hfnorm s) (T side)
  have hregular (side) : MovingSlotReversal.naturalProduct value (T side).regularSlots = ∏ j, reg j :=
    (movingPatternFinBulkData_regular_product_permuted e t small slot perm pattern value side).trans hRegEq
  have hqpos : 1 ≤ (∏ j, reg j) * M := by
    apply Nat.one_le_iff_ne_zero.mpr
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun j _ => (Fact.out : (reg j).Prime).ne_zero))
      (NeZero.ne M)
  have hh := hL (Fin (N + 1)) J p ((Sum.elim tierB tierC) ∘ e) value hprime hdisjoint outside
    childBound pivotBound T hf t
    (movingPatternFinBulkData_follows e t (fun _ => small) slot perm pattern)
    (movingPatternFinBulkData_levels e tierB tierC n m t (fun _ => small) slot perm pattern hB htier)
    (movingPatternFinBulkData_regular_coherent e t (fun _ => small) slot perm pattern)
    hsmall hfmod (fun _ {_} _ => f) (fun _ {_} _ _ _ _ => 1) g hg (fun _ => Dq)
    R hR hsmallR (fun side i => hden side i) hout reg hregular active sreg other greg
    X lo hi hlo hhi φ G Jleft Jright hφ hlip hφout diagonal V hVR (Nat.cast_nonneg _) hVA hwindow hpupper
    M inferInstance hperiod.1 (fun side o ho j hj => hperiod.2.1 _ (hcoverP side o ho j hj))
    (fun i => hperiod.2.2 i (Finset.mem_univ i))
    (by simpa only [hRegEq] using hcop)
    ((∏ j, reg j) * M) hqpos (by simpa only [hRegEq] using hfull) rfl
    houtside hreg hqs (by simpa only [hRegEq] using hpageReg)
    hsreg hother hgreg henergy u v a b center hcenter huv hv hvcenter ha hab hb hweight hgnorm
  rw [movingPatternPrimeObservable_outer_integral_crt e t (fun _ => small) slot perm
    pattern primes hprimes childBound pivotBound hfreq (fun _ {_} _ => f)
    (fun _ {_} _ _ _ _ => 1) outside R r p g (fun i _ => Dq i) input (giantProgressionCutoff L)
    ψ X lo hi hlo hhi φ G x P hP hinj hR hprecision hcoverP hc hpage]
  exact hh

end Ostmann

end OAI
