import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternGiantBounds
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternGiantSupport
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternUniformBudget

namespace OAI

/-! # Supplying the giant arithmetic conditions from the original prime priors -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

/-- All assignment-dependent conditions of the giant comparison follow from
actual prime ranges, original-prior support, and the prescribed conductor
prime deletion. No arithmetic comparison is assumed in this statement. -/
theorem movingPattern_giant_conditions (input : PublishedProgressionInput)
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
      ∀ x : Fin (N + 1) → A,
      movingOriginalPatternWeight e μ ν prime n pattern (fun _ => 1) x ≠ 0 →
      (∀ i j, (Sum.elim tierB (fun c => movingSampleTier (rep c).val.2)) (e i) ≠
        (Sum.elim tierB (fun c => movingSampleTier (rep c).val.2)) (e j) →
          prime (x i) ≠ prime (x j)) ∧
      (∀ i, V < prime (x i)) ∧
      (∀ i, IsCoprime (prime (x i) : ℤ) (R : ℤ)) ∧
      (∀ i, (R ^ (n - 1 + 2)).Coprime (prime (x i))) ∧
      (∀ i j, (prime (x j) : ZMod (p i)) ≠ 0) ∧
      M x ≤ giantProgressionCutoff L ∧
      pageAtModulus (M x) (selectedPageZero input (giantProgressionCutoff L)) =
        pageAtModulus (R ^ (n - 1 + 2)) (selectedPageZero input (giantProgressionCutoff L)) ∧
      Real.log (M x : ℝ) ≤ Real.exp ((12 / 1000 : ℝ) * L) ∧
      Real.log (MovingSlotReversal.naturalProduct (fun i => prime (x i))
        (flattenMovingSlots n (movingPatternFiniteSmall e n small) ++
          flattenMovingSlots n (bulkSlotLeaves n m (movingPatternBulkEmbedding e slot))) : ℝ) ≤
        Real.exp ((12 / 1000 : ℝ) * L) := by
  filter_upwards [movingPattern_actual_modulus_range n k Cfreq hCfreq,
    movingPattern_regular_giant_log_range n r₀ k] with L hmod hreg
  dsimp only
  intro A B C _ _ _ N e prime tier tierB μ ν pattern rep S V t small slot p lo cutoff E
    hinj hprime hμ hν hbound hμtier hνtier hB hS hV hVlo hVcut hcutlo hμlo hνlo hupper
    hp hsmall hdeleteμ hdeletep x hx
  let m := spectatorBulkCount k L
  let R := frequencyModelBase S n t
  let Pi := movingPatternInternalPrimes e prime x
  have hprior := movingPattern_nonzero_prior e μ ν prime pattern rep E hprime hμ hν hbound
    (fun _ => 1) x hx
  have hlarge := movingPattern_prior_lower e μ ν prime pattern rep lo hμlo hνlo x hprior
  obtain ⟨hsep, hsize, hcop, hrcop, hres⟩ := movingPattern_prior_giant_support e μ ν prime hinj
    hprime pattern rep tier tierB hμtier hνtier hB S V lo t hS hVlo hμlo hνlo p
    (fun i => (hp i).1) (fun i => (hp i).2.2.1) E hμ hν hbound x hx
  have hPi : ∀ q ∈ Pi, q.Prime ∧ (q : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L)) := by
    intro q hq
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hq
    exact ⟨hprime _, hupper _⟩
  have hcard : Pi.card ≤ 4 * n * 2 ^ n := by
    calc
      Pi.card ≤ (Finset.univ : Finset C).card := Finset.card_image_le
      _ = Fintype.card C := Finset.card_univ
      _ ≤ 4 * n * 2 ^ n := movingPattern_class_card_le n pattern rep
  have hm := hmod S V t p Pi hS hV hcard hPi (fun i => ⟨(hp i).1, (hp i).2.2.2⟩)
  have hpage := frequencyModel_page_projection S n V cutoff t hS hVcut Pi p
    (selectedPageZero input (giantProgressionCutoff L))
    (by
      intro q hq
      obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hq
      exact ⟨hprime _, hcutlo.trans (hlarge _).le⟩)
    (fun i => ⟨(hp i).1, (hp i).2.1⟩)
    (by
      intro z hz q hq hmem
      obtain ⟨c, _, hqc⟩ := Finset.mem_image.mp hmem
      have hpc := movingPattern_internal_prior_nonzero e μ ν prime pattern (fun _ => 1) x hx
        (rep c).val
      rw [(rep c).property] at hpc
      exact hdeleteμ z hz q hq _ _ hpc hqc)
    (fun z hz q hq i => (hdeletep z hz q hq i).symm)
  have hr := hreg B C N e small slot (fun i => prime (x i)) hsmall
    (fun i => (hprime _).ne_zero) (fun i => hupper _)
  exact ⟨hsep, hsize, hcop, hrcop, hres, hm.1, hpage, hm.2, hr⟩

end Ostmann

end OAI
