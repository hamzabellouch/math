import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternOriginalMatchedNorm
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternMatchedConditions

namespace OAI

/-! # The original signed matched-history bound from actual prime ranges and conductor deletion -/

namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.movingPattern_original_matched_prime_ranges
    (input : PublishedProgressionInput) (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (Afreq Wwin Bφ Dφ : ℝ) (hAfreq : 0 ≤ Afreq) (hWwin : 0 ≤ Wwin)
    (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (B C : Type) [Fintype B] [Fintype C] (N : ℕ)
        (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
        (t : Bool → FrequencyTree ℤ n) (small : TreeLeafTuple (List B) n)
        (slot : (TreeLeafIndex n × Fin m) ↪ B)
        (perm : Equiv.Perm (TreeLeafIndex n × Fin m)) (pattern : Bool × MovingSampleIndex n → C)
        (_rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
        (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
        (μ : ℕ → primes → ℝ) (ν : B → primes → ℝ)
        (p : Fin m → ℕ) [∀ i, Fact (p i).Prime] (_hinjp : Function.Injective p)
        (g : ∀ i, ZMod (p i) → ℂ) (Dq : ∀ i, (ZMod (p i))ˣ)
        (active : Fin (movingPatternRegularSlots e n m small slot).length → Bool)
        (sreg : ℤ) (sets : ∀ q : ℕ, Finset (ZMod q))
        (f : ℤ → ℂ) (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
        (S : Finset ℤ) (ft : FrequencyTree (S × S) n)
        [NeZero (frequencyModelBase S n ft ^ (n - 1 + 2))] (V : ℕ)
        (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
        (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
        (φ : ℝ → ℝ) (G : ℕ → ℝ) (Jleft Jright : ℝ) (diagonal : Bool)
        (E U u v a b center : ℝ),
      let reg := (movingPatternRegularSlots e n m small slot).get
      let other := fun (x : Fin (N + 1) → primes) =>
        movingRegularOther (fun i => (x i : ℕ)) outside (movingPatternRegularSlots e n m small slot)
      let greg := normalizedResidueFamily sets
      let R : ℤ := frequencyModelBase S n ft
      let r := frequencyModelBase S n ft ^ (n - 1 + 2)
      (∀ j q, 0 ≤ μ j q) → (∀ j q, 0 ≤ ν j q) →
      (∀ j, ∑ q, μ j q = 1) → (∀ j, ∑ q, ν j q = 1) →
      0 ≤ E → 0 ≤ U → (∀ j (q : primes), (q : ℝ) * μ j q ≤ E) →
      (∀ q : primes, (q : ℝ) ≤ U) →
      (∀ b, n ≤ tierB b) → (∀ i, tierC (pattern i) = movingSampleTier i.2) →
      (∀ b, ∀ s ∈ allFrequencyList n (t b), s.natAbs ≤ V) →
      (∀ s, ‖f s‖ ≤ 1) → (∀ i, g i 0 = 0) → (∀ i z, ‖g i z‖ ≤ (p i : ℝ)) →
      (∀ q ∈ outside, ∃ i, p i = q) →
      (V : ℝ) ≤ Real.exp (Afreq * m) → hi - lo ≤ Real.exp (Wwin * m) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      (∀ z, |φ z| ≤ Bφ) → (∀ z w, |φ z - φ w| ≤ Dφ * |z - w|) →
      (∀ z, 1 ≤ |z| → φ z = 0) →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ center → u ≤ v → v ≤ u + 1 → v ≤ center + 1 →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ a → a ≤ b → b ≤ a + 1 →
      t = (fun b => frequencyTreeMap Subtype.val n (frequencyPairProjection S n b ft)) →
      (∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ V) →
      ∀ (tier : primes → ℕ) (lower cutoff : ℕ),
      V ≤ lower → V < cutoff → cutoff ≤ lower →
      (∀ j, j < n → ∀ q, μ j q ≠ 0 → tier q = j) →
      (∀ j q, ν j q ≠ 0 → tier q = tierB j) →
      (∀ j q, μ j q ≠ 0 → lower < (q : ℕ)) →
      (∀ j q, ν j q ≠ 0 → lower < (q : ℕ)) →
      (∀ q : primes, (q : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
      (∀ i, cutoff ≤ p i ∧ p i ≤ lower) →
      MovingLeafLengthLE n small r₀ →
      (∀ z, selectedPageZero input (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q →
        ∀ j a, μ j a ≠ 0 → (a : ℕ) ≠ q) →
      (∀ z, selectedPageZero input (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
      (∀ z, selectedPageZero input (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q →
        ∀ j a, ν j a ≠ 0 → (a : ℕ) ≠ q) →
      sreg ≠ 0 → sreg.natAbs ≤ V →
      (∀ q, q.Prime → (sets q).Nonempty ∧ (sets q).card < q) →
      let actual := movingOriginalPatternMatchedObservable e t small slot perm pattern primes hprimes
        p g Dq reg active sreg other greg f outside childBound pivotBound ψ X lo hi φ G
        Jleft Jright diagonal u v a b center
      let integral := fun x => ∫ z in Set.Ioc u v, ∫ y in Set.Ioc a b,
        ((giantOuterWeight φ Jleft Jright diagonal (Real.exp z) (Real.exp y) *
          (inactiveRegularDensity (fun q : primes => (q : ℕ)) reg active x : ℂ)) *
          movingPatternPrimeObservable e t (fun _ => small) slot perm pattern
            primes hprimes childBound pivotBound hfreq (fun _ {_} _ => f)
            (fun _ {_} _ _ _ _ => 1) outside R r p g (fun i _ => Dq i) input
            (giantProgressionCutoff L) y ψ X lo hi hlo hhi φ G (Real.exp z) (Real.exp y) x) *
            (Real.exp (z - center) : ℂ) / (y : ℂ)
      ‖∑ x, movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) n pattern actual x‖ ≤
        (((2 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C)) * U ^ Fintype.card C) *
          (Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) +
            Real.exp (-Real.exp ((1225 / 100000 : ℝ) * L))) +
        ‖∑ x, movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) n pattern integral x *
          movingPatternHaarProduct e (fun q : primes => (q : ℕ)) (fun q => hprimes _ q.property)
            n t (fun _ => small) (movingPatternBulkLeaves n m slot perm) pattern x‖ := by
  filter_upwards [input.movingPattern_original_matched_norm ψ n r₀ k Afreq Wwin Bφ Dφ
    hAfreq hWwin hBφ hDφ, movingPattern_matched_conditions input n r₀ k Afreq hAfreq]
    with L hnorm hconditions
  dsimp only
  intro B C _ _ N e tierB tierC t small slot perm pattern rep primes hprimes μ ν p _ hinjp
    g Dq active sreg sets f outside childBound pivotBound S ft _ V hfreq
    X lo hi hlo hhi φ G Jleft Jright diagonal E U u v a b center
    hμ hν hμmass hνmass hE hU hbound hsize hB htier hV hf hg hgnorm hout
    hVA hwindow hpupper hφ hlip hφout hcenter huv hv hvcenter ha hab hb
    ht hS tier lower cutoff hVlo hVcut hcutlo hμtier hνtier hμlo hνlo hupper
    hp hsmall hdeleteμ hdeletep hdeleteν hsreg hsregV hsets
  let m := spectatorBulkCount k L
  let R := frequencyModelBase S n ft
  let r := R ^ (n - 1 + 2)
  let slots := movingPatternRegularSlots e n m small slot
  let reg := slots.get
  let other := fun (x : Fin (N + 1) → primes) => movingRegularOther (fun i => (x i : ℕ)) outside slots
  have hR (b : Bool) :
      (movingPatternFinBulkData e n m t (fun _ => small) slot perm pattern b).frequencyProduct ∣
        (R : ℤ) := by
    simpa only [ht, R] using
      movingPattern_frequencyProduct_dvd e S ft (fun _ => small) slot perm pattern b
  have hrp (i) : r.Coprime (p i) := by
    exact ((prime_coprime_frequencyModelBase S V (p i) n Fact.out
      (hVcut.trans_le (hp i).1) hS ft).pow_right _).symm
  apply hnorm B C (Fin slots.length) N e tierB tierC t small slot perm pattern rep primes hprimes μ ν
    p hinjp g Dq reg active sreg other (normalizedResidueFamily sets) f outside
    childBound pivotBound (R : ℤ) r V hfreq X lo hi hlo hhi φ G Jleft Jright diagonal
    E U u v a b center hμ hν hμmass hνmass hE hU hbound hsize hB htier hV hf hg hgnorm hout
    hR (frequencyModelModulus_precision R n) hrp (fun i => hVcut.trans_le (hp i).1)
    hVA hwindow hpupper hφ hlip hφout hcenter huv hv hvcenter ha hab hb
  · intro x
    exact naturalProduct_eq_finprod (fun i => (x i : ℕ)) slots
  · intro x hx hgood
    have hh := hconditions primes B C N e (fun q : primes => (q : ℕ))
      (fun q => hprimes _ q.property) tier tierB μ ν pattern rep S V ft small slot perm p lower cutoff E
      sreg sets Subtype.val_injective hμ hν hbound hμtier hνtier hB hS hVA hVlo hVcut hcutlo
      hμlo hνlo hupper (fun i => ⟨Fact.out, (hp i).1, (hp i).2, hpupper i⟩) hsmall
      hdeleteμ hdeletep hdeleteν hsreg hsregV hsets x hx outside
    have hteq : tierC = fun c => movingSampleTier (rep c).val.2 := by
      funext c
      have hh := htier (rep c).val
      simpa only [(rep c).property] using hh
    simpa only [← ht, ← hteq] using hh (by simpa only [← ht] using hgood)

end Ostmann

end OAI
