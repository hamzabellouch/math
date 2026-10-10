import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SourceCoreEquiv
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SlotEdgeProduct

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.PivotSummation
open OrdinaryCorrelations.NumericalSubtrees
open Finset Classical Filter
variable {h ℓ : ℕ} {w : ClosedLine h ℓ} {σ : Type*} [Fintype σ]

lemma all_slot_masses (S : PrimeSystem) (q : σ → Shape w) (core : σ → Prop)
    (hc : 1 ≤ S.harmonicCore) :
    (∏ s : Unselected (orderedPivot q core),
      if core s.val then S.harmonicCore else S.harmonicCenter) ≤
      ∏ s : σ, if core s then S.harmonicCore else S.harmonicCenter := by
  have hm (s : σ) : 0 ≤ if core s then S.harmonicCore else S.harmonicCenter := by
    rw [← slotWeight_sum S (core s)]
    exact sum_nonneg (fun p _ => slotWeight_nonneg S _ p)
  rw [prod_slots (orderedPivot q core) (orderedPivot_injective q core)]
  have hp : 1 ≤ ∏ i : Fin (pivotEdges q core).card,
      if core (orderedPivot q core i) then S.harmonicCore else S.harmonicCenter := by
    apply one_le_prod₀
    intro i hi
    rw [ite_eq_left (orderedPivot_core q core i)]
    exact hc
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hp
    (prod_nonneg (fun s _ => hm s.val))

theorem source_named_prime_sum (τ : ℝ) (hτ : 0 < τ) :
    ∀ᶠ B : ℝ in atTop, ∀ (h ℓ : ℕ) (w : ClosedLine h ℓ) (σ : Type) [Fintype σ],
      ∀ (q : σ → Shape w) (core : σ → Prop)
      (C : Fin ℓ → ℝ), (∀ e, 0 < C e) → ∀ H : ℝ,
      (∑ x : σ → (sourceSystem B).Index,
        pivotBinIndicator q core (sourceSystem B) C H τ x *
          ∏ s, slotWeight (sourceSystem B) (core s) (x s)) ≤
      (((Real.log 4+1)*τ)/B^(1-eta))^(pivotEdges q core).card *
        ∏ s : σ, if core s then (sourceSystem B).harmonicCore else (sourceSystem B).harmonicCenter := by
  have hr : 0 < 1-eta := by norm_num [eta,epsilon]
  filter_upwards [named_prime_sum (1-eta) τ hr hτ,
    source_core_eventually_one,eventually_ge_atTop (1 : ℝ)] with B hB hc hB1
  intro h ℓ w σ _ q core C hC H
  have hcore : ∀ p ∈ (sourceSystem B).core, Real.exp (B^(1-eta)) < (p : ℝ) := by
    intro p hp
    have hp' : p ∈ SourcePrimeBands.corePrimes B := hp
    obtain ⟨_,hpprime,hplog⟩ := mem_filter.mp hp'
    have hlog : B^(1-eta) < Real.log (p : ℝ) := hplog
    exact (Real.exp_lt_exp.mpr hlog).trans_eq (Real.exp_log (by exact_mod_cast hpprime.pos))
  have hK : 0 ≤ (((Real.log 4+1)*τ)/B^(1-eta))^(pivotEdges q core).card := by positivity
  exact (hB (sourceSystem B) hcore h ℓ w σ q core C hC H).trans
    (mul_le_mul_of_nonneg_left (all_slot_masses (sourceSystem B) q core hc) hK)

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
