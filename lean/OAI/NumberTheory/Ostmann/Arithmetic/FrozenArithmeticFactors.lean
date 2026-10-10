import OAI.NumberTheory.Ostmann.Arithmetic.FrozenFrequencyAverage
import OAI.NumberTheory.Ostmann.Arithmetic.FrozenSpectatorAverage
import OAI.NumberTheory.Ostmann.Arithmetic.FrozenRegularSupport

namespace OAI

/-! # CRT identification of the actual bulk arithmetic factors -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingCoreSpectator_bulk_residues {σ I : Type*} [Fintype I]
    (base value : σ → ℕ) (n m : ℕ) (slot : (TreeLeafIndex n × Fin m) ↪ σ)
    (hv : ∀ i ∉ Set.range slot, value i = base i)
    (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List σ) n)
    (samples : Bool → MovingSampleSlots σ n)
    (hvsmall : ∀ b, movingSlotValues value n (small b) = movingSlotValues base n (small b))
    (hvsamples : ∀ b, (samples b).values value = (samples b).values base)
    (e : Equiv.Perm (TreeLeafIndex n × Fin m))
    (T : Bool → MovingSlotData σ n)
    (hT : ∀ b, T b = buildMovingSlotData n (t b) (small b)
      (if b then bulkSlotLeaves n m (slot ∘ e.symm) else bulkSlotLeaves n m slot) (samples b))
    (F : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℂ)
    (E : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℤ → ℤ → ℝ)
    (R : ℤ) (r : ℕ) [NeZero r]
    (hf : ∀ b, (T b).Frequencies (· ≠ 0))
    (hcomp : ∀ b j, (T b).CompensationAbsent (slot j))
    (hR : ∀ b, (T b).frequencyProduct ∣ R) (hr : R ^ (n + 1) ∣ (r : ℤ))
    (p : I → ℕ) [∀ i, Fact (p i).Prime]
    (hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
    (g : ∀ i, ZMod (p i) → ℂ) (hg : ∀ i, g i 0 = 0)
    (D : ∀ i, Bool → (ZMod (p i))ˣ)
    (z : TreeLeafIndex n × Fin m → (ZMod (∏ i, bulkResidueModuli r p i))ˣ)
    (hz : ∀ j, (value (slot j) : ZMod (∏ i, bulkResidueModuli r p i)) = (z j : ZMod _))
    (input : PublishedProgressionInput) (Q : ℕ) (y : ℝ) :
    movingFrequencyCorePageAverage value F E T R r input Q y *
      ∏ i, movingSpectatorHaarAverage value (p i) (g i) (D i) T =
    movingFrequencyCorePageAverage
        (Function.extend slot (fun j => ((bulkResidueEquiv r p hc z).1 j).val.val) base)
        F E T R r input Q y *
      ∏ i, frozenBulkSpectatorHaar base n m t small samples (D i) e (g i)
        ((bulkResidueEquiv r p hc z).2 i) := by
  rw [movingFrequencyCorePageAverage_bulk_residues base value slot hv r
    (bulkResidueEquiv r p hc z).1
    (bulkResidueEquiv_frequency_lift r p hc (value ∘ slot) z hz)
    F E T R hf hcomp hR hr input Q y]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  have ht : T = fun b => buildMovingSlotData n (t b) (small b)
      (if b then bulkSlotLeaves n m (slot ∘ e.symm) else bulkSlotLeaves n m slot) (samples b) :=
    funext hT
  rw [ht]
  exact frozenBulkSpectatorHaar_actual base n m t small samples (D i) e value
    hvsmall hvsamples slot (g i) (hg i) ((bulkResidueEquiv r p hc z).2 i)
    (bulkResidueEquiv_spectator_lift r p hc (value ∘ slot) z hz i)

end Ostmann

end OAI
