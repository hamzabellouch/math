import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternMatchedObservable
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternMatchedHaarComparison
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternCoefficientMass
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternRegularSupport
import OAI.NumberTheory.Ostmann.Arithmetic.MovingDiagonalOuterWeight
import OAI.NumberTheory.Ostmann.Arithmetic.MovingRegularCollisionSupport

namespace OAI

/-! # The original signed matched-history sum and its arithmetic integral -/

namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.movingPattern_original_matched_norm
    (input : PublishedProgressionInput) (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (Afreq Wwin Bφ Dφ : ℝ) (hAfreq : 0 ≤ Afreq) (hWwin : 0 ≤ Wwin)
    (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (B C J : Type) [Fintype B] [Fintype C] [Fintype J] (N : ℕ)
        (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
        (t : Bool → FrequencyTree ℤ n) (small : TreeLeafTuple (List B) n)
        (slot : (TreeLeafIndex n × Fin m) ↪ B)
        (perm : Equiv.Perm (TreeLeafIndex n × Fin m)) (pattern : Bool × MovingSampleIndex n → C)
        (_rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
        (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
        (μ : ℕ → primes → ℝ) (ν : B → primes → ℝ)
        (p : Fin m → ℕ) [∀ i, Fact (p i).Prime] (_hinjp : Function.Injective p)
        (g : ∀ i, ZMod (p i) → ℂ) (Dq : ∀ i, (ZMod (p i))ˣ)
        (reg : J → Fin (N + 1)) (active : J → Bool) (sreg : ℤ)
        (other : (Fin (N + 1) → primes) → J → ℤ) (greg : ∀ q : ℕ, ZMod q → ℂ)
        (f : ℤ → ℂ) (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
        (R : ℤ) (r : ℕ) [NeZero r] (V : ℕ)
        (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
        (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
        (φ : ℝ → ℝ) (G : ℕ → ℝ) (Jleft Jright : ℝ) (diagonal : Bool)
        (E U u v a b center : ℝ),
      let : ∀ q : primes, Fact (q : ℕ).Prime := fun q => ⟨hprimes _ q.property⟩
      let T := movingPatternFinBulkData e n m t (fun _ => small) slot perm pattern
      let coeff := movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) n pattern (fun _ => 1)
      let Pi := fun x => movingPatternInternalPrimes e (fun q : primes => (q : ℕ)) x
      let M := fun x => ∏ z, movingArithmeticModuli r p (Pi x) Finset.univ z
      let Reg := fun x => MovingSlotReversal.naturalProduct (fun i => (x i : ℕ))
        (movingPatternRegularSlots e n m small slot)
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
      (V : ℝ) ≤ Real.exp (Afreq * m) → hi - lo ≤ Real.exp (Wwin * m) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      (∀ z, |φ z| ≤ Bφ) → (∀ z w, |φ z - φ w| ≤ Dφ * |z - w|) →
      (∀ z, 1 ≤ |z| → φ z = 0) →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ center → u ≤ v → v ≤ u + 1 → v ≤ center + 1 →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ a → a ≤ b → b ≤ a + 1 →
      (∀ x, Reg x = ∏ j, (x (reg j) : ℕ)) →
      (∀ x, coeff x ≠ 0 →
        (∀ b, movingRegularOutsidePairwise (fun i => (x i : ℕ)) outside (T b)) →
        (∀ i j, (Sum.elim tierB tierC) (e i) ≠ (Sum.elim tierB tierC) (e j) →
          (x i : ℕ) ≠ (x j : ℕ)) ∧
        (∀ i, V < (x i : ℕ)) ∧
        (∀ i, IsCoprime ((x i : ℕ) : ℤ) R) ∧
        (∀ i, r.Coprime (x i : ℕ)) ∧
        (∀ i j, ((x j : ℕ) : ZMod (p i)) ≠ 0) ∧
        (Reg x).Coprime (M x) ∧ Reg x * M x ≤ giantProgressionCutoff L ∧
        pageAtModulus (Reg x * M x) (selectedPageZero input (giantProgressionCutoff L)) =
          pageAtModulus (M x) (selectedPageZero input (giantProgressionCutoff L)) ∧
        pageAtModulus (M x) (selectedPageZero input (giantProgressionCutoff L)) =
          pageAtModulus r (selectedPageZero input (giantProgressionCutoff L)) ∧
        Pairwise (fun i j => (x (reg i) : ℕ).Coprime (x (reg j) : ℕ)) ∧
        (∀ i, (sreg : ZMod (x (reg i) : ℕ)) ≠ 0) ∧
        (∀ i, (other x i : ZMod (x (reg i) : ℕ)) ≠ 0) ∧
        (∀ i, greg (x (reg i) : ℕ) 0 = 0) ∧
        (∀ i, (∑ z : ZMod (x (reg i) : ℕ), ‖greg (x (reg i) : ℕ) z‖ ^ 2) = (x (reg i) : ℕ))) →
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
  filter_upwards [input.moving_pattern_matched_haar_rate ψ n r₀ k Afreq Wwin Bφ Dφ
    hAfreq hWwin hBφ hDφ] with L hL
  dsimp only
  intro B C J _ _ _ N e tierB tierC t small slot perm pattern rep primes hprimes μ ν
    p _ hinjp g Dq reg active sreg other greg f outside childBound pivotBound R r _ V hfreq
    X lo hi hlo hhi φ G Jleft Jright diagonal E U u v a b center
    hμ hν hμmass hνmass hE hU hbound hsize hB htier hV hf hg hgnorm hout hR
    hprecision hrp hspecLarge hVA hwindow hpupper hφ hlip hφout hcenter huv hv hvcenter
    ha hab hb hRegEq hdata
  let m := spectatorBulkCount k L
  let T := movingPatternFinBulkData e n m t (fun _ => small) slot perm pattern
  let Pi := fun x => movingPatternInternalPrimes e (fun q : primes => (q : ℕ)) x
  let haar := movingPatternHaarProduct e (fun q : primes => (q : ℕ)) (fun q => hprimes _ q.property)
    n t (fun _ => small) (movingPatternBulkLeaves n m slot perm) pattern
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
  let ε := Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) +
    Real.exp (-Real.exp ((1225 / 100000 : ℝ) * L))
  have hcompare (x : Fin (N + 1) → primes)
      (hx : movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) n pattern (fun _ => 1) x ≠ 0) :
      ‖actual x - integral x * haar x‖ ≤ ε := by
    by_cases hgood : ∀ b, movingRegularOutsidePairwise (fun i => (x i : ℕ)) outside (T b)
    ·
      obtain ⟨hdisjoint, hlarge, hsmallR, hrcop, hres, hcop, hfull, hpageReg, hpage,
        hreg, hsreg, hother, hgreg, henergy⟩ := hdata x hx hgood
      have hprime (i) : (x i : ℕ).Prime := hprimes _ (x i).property
      let : ∀ j, Fact (x (reg j) : ℕ).Prime := fun j => ⟨hprime _⟩
      have hPi := movingPatternInternalPrimes_prime e (fun q : primes => (q : ℕ))
        (fun q => hprimes _ q.property) x
      let : ∀ q : Pi x, Fact q.val.Prime := fun q => ⟨hPi _ q.property⟩
      have hnz (z) : movingArithmeticModuli r p (Pi x) Finset.univ z ≠ 0 :=
        movingArithmeticModuli_ne_zero r p (Pi x) Finset.univ (NeZero.ne r) hPi
          (fun i _ => (Fact.out : (p i).Prime)) z
      let : ∀ z, NeZero (movingArithmeticModuli r p (Pi x) Finset.univ z) := fun z => ⟨hnz z⟩
      let : NeZero (∏ z, movingArithmeticModuli r p (Pi x) Finset.univ z) :=
        ⟨Finset.prod_ne_zero_iff.mpr (fun z _ => hnz z)⟩
      have hsep (i : Fin m) (j : Fin (N + 1)) : (x j : ℕ) ≠ p i := by
        intro heq
        apply hres i j
        rw [heq]
        exact ZMod.natCast_self (p i)
      have hc := movingPattern_prime_moduli_coprime e (fun q : primes => (q : ℕ))
        (fun q => hprimes _ q.property) x r p (fun i => (Fact.out : (p i).Prime))
        hinjp hrcop hrp hsep
      have hinj := movingPattern_nonzero_internal_injective e μ ν (fun q : primes => (q : ℕ))
        Subtype.val_injective pattern (fun _ => 1) x hx
      have hqs (i : Fin m) : (∏ j, (x (reg j) : ℕ)).Coprime (p i) := by
        apply Nat.coprime_prod_left_iff.mpr
        intro j _
        exact (Nat.coprime_primes (hprime _) (Fact.out : (p i).Prime)).mpr (hsep i _)
      have hh := hL B C J N e tierB tierC t small slot perm pattern primes hprimes x p g Dq
        (fun j => (x (reg j) : ℕ)) active sreg (fun j => (other x j : ZMod (x (reg j) : ℕ)))
        (fun j => greg (x (reg j) : ℕ)) f outside childBound pivotBound R r (Pi x) hfreq V
        X lo hi hlo hhi φ G Jleft Jright diagonal hB htier hdisjoint hV hlarge hf hg hgnorm
        hout hR hprecision hsmallR hres hspecLarge rfl hinj hc (hRegEq x) hcop hfull hpageReg hpage
        hgood hreg hqs hsreg hother hgreg henergy hVA hwindow hpupper hφ hlip hφout
        u v a b center hcenter huv hv hvcenter ha hab hb
      exact hh
    · have ha0 (XL XR : ℕ) : movingOriginalSupportedOuterPair p (fun i => (x i : ℕ)) outside
          childBound pivotBound (fun _ {_} _ => f) (fun _ {_} _ _ _ _ => 1) g
          (fun _ => Dq) Finset.univ ψ X lo hi φ G Jleft Jright diagonal T t XL XR = 0 :=
        movingOriginalSupportedOuterPair_zero_of_not_regular p _ outside childBound pivotBound
          _ _ g _ Finset.univ ψ X lo hi φ G Jleft Jright diagonal T t hgood XL XR
      have hraw (z y : ℝ) : movingPatternPrimeObservable e t (fun _ => small) slot perm
          pattern primes hprimes childBound pivotBound hfreq (fun _ {_} _ => f)
          (fun _ {_} _ _ _ _ => 1) outside R r p g (fun i _ => Dq i) input
          (giantProgressionCutoff L) y ψ X lo hi hlo hhi φ G (Real.exp z) (Real.exp y) x = 0 := by
        change _ * (movingFrequencyPageAverage (fun i => (x i : ℕ)) outside
          (fun _ {_} _ => f) (fun _ {_} _ _ _ _ => 1) T _ R r input
          (giantProgressionCutoff L) y * _) = 0
        rw [movingFrequencyPageAverage_zero_of_not_regular _ outside _ _ T _ R r input
          (giantProgressionCutoff L) y hgood, zero_mul, mul_zero]
      dsimp only [T, m] at ha0
      have hactual : actual x = 0 := by
        simp only [actual, movingOriginalPatternMatchedObservable, ha0, zero_mul,
          complexIntegerInterval, complexPrimeInterval, ite_self, Finset.sum_const_zero]
      have hideal : integral x = 0 := by
        simp only [integral, hraw, mul_zero, zero_mul, zero_div, integral_zero]
      rw [hactual, hideal, zero_mul, sub_self, norm_zero]
      dsimp only [ε]
      positivity
  have hbnd := movingPattern_comparison_norm e μ ν (fun q : primes => (q : ℕ)) pattern rep
    E U ε hE hU (by dsimp only [ε]; positivity) (fun q => hprimes _ q.property)
    hμ hν hμmass hνmass hbound hsize actual (fun x => integral x * haar x) hcompare
  have he : (∑ x, movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) n pattern
      (fun x => integral x * haar x) x) =
      ∑ x, movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) n pattern integral x * haar x := by
    apply Finset.sum_congr rfl
    intro x _
    conv_lhs => rw [movingOriginalPatternWeight_eq_coefficient_mul]
    conv_rhs => rw [movingOriginalPatternWeight_eq_coefficient_mul]
    ring
  simpa only [he] using hbnd

end Ostmann

end OAI
