import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternSeparatedConditions
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternRegularUnits
import OAI.NumberTheory.Ostmann.Characters.NormalizedResidueFamily

namespace OAI

/-! # The complete diagonal arithmetic data under the original prime priors -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem movingPattern_diagonal_conditions (input : PublishedProgressionInput)
    (n r₀ k : ℕ) (Cfreq : ℝ) (hCfreq : 0 ≤ Cfreq) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (A B C : Type) [Fintype A] [Fintype B] [Fintype C] (N : ℕ)
        (e : Fin (N + 1) ≃ B ⊕ C) (prime : A → ℕ) (hprime : ∀ a, (prime a).Prime)
        (tier : A → ℕ) (tierB : B → ℕ)
        (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
        (pattern : Bool × MovingSampleIndex n → C)
        (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
        (S : Finset ℤ) (V : ℕ) (t : FrequencyTree (S × S) n)
        (small : TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
        (p : Fin m → ℕ) (lo cutoff : ℕ) (E : ℝ)
        (sreg : ℤ) (sets : ∀ q : ℕ, Finset (ZMod q)),
      let R := frequencyModelBase S n t
      let Pi := fun x => movingPatternInternalPrimes e prime x
      let M := fun x => ∏ b, movingArithmeticModuli (R ^ (n - 1 + 2)) p (Pi x) Finset.univ b
      let Reg := fun x => MovingSlotReversal.naturalProduct (fun i => prime (x i))
        (movingPatternRegularSlots e n m small slot)
      Function.Injective prime →
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
      sreg ≠ 0 → sreg.natAbs ≤ V →
      (∀ q, q.Prime → (sets q).Nonempty ∧ (sets q).card < q) →
      ∀ x : Fin (N + 1) → A,
      movingOriginalPatternWeight e μ ν prime n pattern (fun _ => 1) x ≠ 0 →
      let t₀ := fun b => frequencyTreeMap Subtype.val n (frequencyPairProjection S n b t)
      let slots := movingPatternRegularSlots e n m small slot
      let T := movingPatternFinBulkData e n m t₀ (fun _ => small) slot (Equiv.refl _) pattern
      ∀ (outside : List ℕ),
      (∀ b, movingRegularOutsidePairwise (fun i => prime (x i)) outside (T b)) →
      let : ∀ j : Fin slots.length, Fact (prime (x (slots.get j))).Prime :=
        fun _ => ⟨hprime _⟩
      (∀ i j, (Sum.elim tierB (fun c => movingSampleTier (rep c).val.2)) (e i) ≠
        (Sum.elim tierB (fun c => movingSampleTier (rep c).val.2)) (e j) →
          prime (x i) ≠ prime (x j)) ∧
      (∀ i, V < prime (x i)) ∧
      (∀ i, IsCoprime (prime (x i) : ℤ) (R : ℤ)) ∧
      (∀ i, (R ^ (n - 1 + 2)).Coprime (prime (x i))) ∧
      (∀ i j, (prime (x j) : ZMod (p i)) ≠ 0) ∧
      (Reg x).Coprime (M x) ∧ Reg x * M x ≤ giantProgressionCutoff L ∧
      pageAtModulus (Reg x * M x) (selectedPageZero input (giantProgressionCutoff L)) =
        pageAtModulus (M x) (selectedPageZero input (giantProgressionCutoff L)) ∧
      pageAtModulus (M x) (selectedPageZero input (giantProgressionCutoff L)) =
        pageAtModulus (R ^ (n - 1 + 2)) (selectedPageZero input (giantProgressionCutoff L)) ∧
      Pairwise (fun i j : Fin slots.length =>
        (prime (x (slots.get i))).Coprime (prime (x (slots.get j)))) ∧
      (∀ i : Fin slots.length, (sreg : ZMod (prime (x (slots.get i)))) ≠ 0) ∧
      (∀ i : Fin slots.length,
        (movingRegularOther (fun j => prime (x j)) outside slots i :
          ZMod (prime (x (slots.get i)))) ≠ 0) ∧
      (∀ i : Fin slots.length, normalizedResidueFamily sets (prime (x (slots.get i))) 0 = 0) ∧
      (∀ i : Fin slots.length,
        (∑ z : ZMod (prime (x (slots.get i))),
          ‖normalizedResidueFamily sets (prime (x (slots.get i))) z‖ ^ 2) =
          prime (x (slots.get i))) := by
  filter_upwards [movingPattern_separated_giant_conditions input n r₀ k Cfreq hCfreq]
    with L hbase
  dsimp only
  intro A B C _ _ _ N e prime hprime tier tierB μ ν pattern rep S V t small slot p lo cutoff E
    sreg sets hinj hμ hν hbound hμtier hνtier hB hS hV hVlo hVcut hcutlo hμlo hνlo
    hupper hp hsmall hdeleteμ hdeletep hdeleteν hsreg hsregV hsets x hx outside hgood
  have hb := hbase A B C N e prime tier tierB μ ν pattern rep S V t small slot p lo cutoff E
    hinj hprime hμ hν hbound hμtier hνtier hB hS hV hVlo hVcut hcutlo hμlo hνlo hupper
    hp hsmall hdeleteμ hdeletep hdeleteν x hx
  dsimp only at hb
  rcases hb with ⟨hsep, hlarge, hcop, hrcop, hres, hfull, hregcop, hpageReg, hpage, _⟩
  let t₀ := fun b => frequencyTreeMap Subtype.val n (frequencyPairProjection S n b t)
  let slots := movingPatternRegularSlots e n (spectatorBulkCount k L) small slot
  let : ∀ j : Fin slots.length, Fact (prime (x (slots.get j))).Prime := fun _ => ⟨hprime _⟩
  refine ⟨hsep, hlarge, hcop, hrcop, hres, hregcop, hfull, hpageReg, hpage, ?_, ?_, ?_, ?_, ?_⟩
  · exact movingPattern_regular_pairwise e t₀ small slot pattern (fun i => prime (x i))
      outside false (hgood false)
  · exact movingPattern_regular_frequency_unit (fun i => prime (x i)) (fun _ => hprime _)
      slots V hlarge sreg hsreg hsregV
  · exact movingPattern_regular_other_unit e t₀ small slot pattern (fun i => prime (x i))
      (fun _ => hprime _) outside false (hgood false)
  · intro i
    exact normalizedResidueFamily_zero sets _
  · intro i
    exact normalizedResidueFamily_energy sets _ (hsets _ (hprime _)).1 (hsets _ (hprime _)).2

end Ostmann

end OAI
