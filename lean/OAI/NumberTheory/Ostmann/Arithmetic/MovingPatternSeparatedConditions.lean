import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternGiantConditions
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternGiantSupport
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternUniformBudget
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternRegularSupport
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSeparatedModulusRange

namespace OAI

/-! # Supplying the giant arithmetic conditions from the original prime priors -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

/-- All assignment-dependent conditions of the giant comparison follow from
actual prime ranges, original-prior support, and the prescribed conductor
prime deletion. No arithmetic comparison is assumed in this statement. -/
theorem movingPattern_separated_giant_conditions (input : PublishedProgressionInput)
    (n r₀ k : ℕ) (Cfreq : ℝ) (hCfreq : 0 ≤ Cfreq) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (A B C : Type) [Fintype A] [Fintype B] [Fintype C] (N : ℕ)
        (e : Fin (N + 1) ≃ B ⊕ C) (prime : A → ℕ)
        (tier : A → ℕ) (tierB : B → ℕ)
        (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
        (pattern : Bool × MovingSampleIndex n → C)
        (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
        (S : Finset ℤ) (V : ℕ) (t : FrequencyTree (S × S) n)
        (small : TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
        (p : Fin m → ℕ) (lo cutoff : ℕ) (E : ℝ),
      let R := frequencyModelBase S n t
      let Pi := fun x => movingPatternInternalPrimes e prime x
      let M := fun x => ∏ b, movingArithmeticModuli (R ^ (n - 1 + 2)) p (Pi x) Finset.univ b
      let Reg := fun x => MovingSlotReversal.naturalProduct (fun i => prime (x i))
        (movingPatternRegularSlots e n m small slot)
      Function.Injective prime → (∀ a, (prime a).Prime) →
      (∀ j a, 0 ≤ μ j a) → (∀ j a, 0 ≤ ν j a) →
      (∀ j a, (prime a : ℝ) * μ j a ≤ E) →
      (∀ j, j < n → ∀ a, μ j a ≠ 0 → tier a = j) →
      (∀ j a, ν j a ≠ 0 → tier a = tierB j) → (∀ b, n ≤ tierB b) →
      (∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ V) → (V : ℝ) ≤ Real.exp (Cfreq * m) →
      V ≤ lo → V < cutoff → cutoff ≤ lo →
      (∀ j a, μ j a ≠ 0 → lo < prime a) →
      (∀ j a, ν j a ≠ 0 → lo < prime a) →
      (∀ a, (prime a : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
      (∀ i, (p i).Prime ∧ cutoff ≤ p i ∧ p i ≤ lo ∧
        (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      MovingLeafLengthLE n small r₀ →
      (∀ z, selectedPageZero input (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q →
        ∀ j a, μ j a ≠ 0 → prime a ≠ q) →
      (∀ z, selectedPageZero input (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
      (∀ z, selectedPageZero input (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q →
        ∀ j a, ν j a ≠ 0 → prime a ≠ q) →
      ∀ x : Fin (N + 1) → A,
      movingOriginalPatternWeight e μ ν prime n pattern (fun _ => 1) x ≠ 0 →
      (∀ i j, (Sum.elim tierB (fun c => movingSampleTier (rep c).val.2)) (e i) ≠
        (Sum.elim tierB (fun c => movingSampleTier (rep c).val.2)) (e j) →
          prime (x i) ≠ prime (x j)) ∧
      (∀ i, V < prime (x i)) ∧
      (∀ i, IsCoprime (prime (x i) : ℤ) (R : ℤ)) ∧
      (∀ i, (R ^ (n - 1 + 2)).Coprime (prime (x i))) ∧
      (∀ i j, (prime (x j) : ZMod (p i)) ≠ 0) ∧
      Reg x * M x ≤ giantProgressionCutoff L ∧
      (Reg x).Coprime (M x) ∧
      pageAtModulus (Reg x * M x) (selectedPageZero input (giantProgressionCutoff L)) =
        pageAtModulus (M x) (selectedPageZero input (giantProgressionCutoff L)) ∧
      pageAtModulus (M x) (selectedPageZero input (giantProgressionCutoff L)) =
        pageAtModulus (R ^ (n - 1 + 2)) (selectedPageZero input (giantProgressionCutoff L)) ∧
      Real.log (M x : ℝ) ≤ Real.exp ((12 / 1000 : ℝ) * L) := by
  filter_upwards [movingPattern_giant_conditions input n r₀ k Cfreq hCfreq,
    movingPattern_actual_separated_modulus_range n r₀ k Cfreq hCfreq]
    with L hbase hmod
  dsimp only
  intro A B C _ _ _ N e prime tier tierB μ ν pattern rep S V t small slot p lo cutoff E
    hinj hprime hμ hν hbound hμtier hνtier hB hS hV hVlo hVcut hcutlo hμlo hνlo hupper
    hp hsmall hdeleteμ hdeletep hdeleteν x hx
  have hb := hbase A B C N e prime tier tierB μ ν pattern rep S V t small slot p lo cutoff E
    hinj hprime hμ hν hbound hμtier hνtier hB hS hV hVlo hVcut hcutlo hμlo hνlo hupper
    hp hsmall hdeleteμ hdeletep x hx
  dsimp only at hb
  rcases hb with ⟨hsep, hsize, hcop, hrcop, hres, _, hpage, hlog, _⟩
  let Pi := movingPatternInternalPrimes e prime x
  have hprior := movingPattern_nonzero_prior e μ ν prime pattern rep E hprime hμ hν hbound
    (fun _ => 1) x hx
  have hlarge := movingPattern_prior_lower e μ ν prime pattern rep lo hμlo hνlo x hprior
  have hcross := (movingPattern_prior_prime_separation e μ ν pattern rep tier tierB prime hinj
    hμtier hνtier hB x hprior).2
  have hspec (i j) : prime (x j) ≠ p i := by
    intro he
    have hh := (hp i).2.2.1.trans_lt (hlarge j)
    omega
  have hregcop := movingPattern_regular_arithmetic_coprime e prime hprime x
    (frequencyModelBase S n t ^ (n - 1 + 2)) p (fun i => (hp i).1)
    small slot hrcop hcross hspec
  have hdelete (z : PrimitiveRealZero)
      (hz : selectedPageZero input (giantProgressionCutoff L) = some z)
      (q : ℕ) (hq : deletedConductorPrime z.modulus cutoff = some q) :
      ∀ i, prime (x i) ≠ q := by
    intro i
    have hi := Finset.prod_ne_zero_iff.mp hprior i (Finset.mem_univ i)
    cases he : e i with
    | inl b =>
      have hνi : ν b (x i) ≠ 0 := by simpa only [he, Sum.elim_inl] using hi
      exact hdeleteν z hz q hq b (x i) hνi
    | inr c =>
      have hμi : μ (movingSampleTier (rep c).val.2) (x i) ≠ 0 := by
        simpa only [he, Sum.elim_inr] using hi
      exact hdeleteμ z hz q hq _ _ hμi
  have hregpage := movingPattern_regular_page_projection e prime hprime x p
    (fun i => (hp i).1) small slot S V cutoff t hS hVcut
    (fun i => hcutlo.trans (hlarge i).le) (selectedPageZero input (giantProgressionCutoff L))
    hdelete hdeletep
  have hPi : ∀ q ∈ Pi, q.Prime ∧ (q : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L)) := by
    intro q hq
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hq
    exact ⟨hprime _, hupper _⟩
  have hcard : Pi.card ≤ 4 * n * 2 ^ n := by
    calc
      Pi.card ≤ (Finset.univ : Finset C).card := Finset.card_image_le
      _ = Fintype.card C := Finset.card_univ
      _ ≤ 4 * n * 2 ^ n := movingPattern_class_card_le n pattern rep
  have hfull := hmod B C N e small slot (fun i => prime (x i)) S V t p Pi hsmall
    (fun i => hupper _) hS hV hcard hPi (fun i => ⟨(hp i).1, (hp i).2.2.2⟩)
  exact ⟨hsep, hsize, hcop, hrcop, hres, hfull, hregcop, hregpage, hpage, hlog⟩

end Ostmann

end OAI
