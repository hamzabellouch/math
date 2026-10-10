import OAI.NumberTheory.Ostmann.Construction.TailSpectatorFamily
import OAI.NumberTheory.Ostmann.Construction.ScheduledComparisonCutoffs

namespace OAI

namespace Ostmann
open scoped Classical

def frozenInitialSpectatorPrimes {P : Finset ℕ} {d : ℕ}
    (sl sr : Fin d → P) (i : Fin (d + d)) : ℕ := ((Fin.append sl sr i : P) : ℕ)

theorem frozenInitialSpectatorPrimes_injective {P : Finset ℕ} {d : ℕ}
    (sl sr : Fin d → P) (hinj : Function.Injective (Fin.append sl sr)) :
    Function.Injective (frozenInitialSpectatorPrimes sl sr) :=
  Subtype.val_injective.comp hinj

theorem frozenInitialSpectatorPrimes_mem {P Q : Finset ℕ} {d : ℕ}
    (sl sr : Fin d → P) (hl : ∀ i, (sl i : ℕ) ∈ Q) (hr : ∀ i, (sr i : ℕ) ∈ Q) :
    ∀ i, frozenInitialSpectatorPrimes sl sr i ∈ Q := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [frozenInitialSpectatorPrimes, Fin.append_left] using hl j
  · simpa only [frozenInitialSpectatorPrimes, Fin.append_right] using hr j

/-- This packages consequences of the selected support, without selecting another family. -/
structure FrozenInitialSpectatorData (A : Set ℕ) (N : ℕ) {d : ℕ}
    (p : Fin (d + d) → ℕ) (L ε : ℝ) (cutoff : ℕ) (D : Finset ℕ) : Prop where
  injective : Function.Injective p
  prime : ∀ i, (p i).Prime
  ge_cutoff : ∀ i, cutoff ≤ p i
  avoids : ∀ i, p i ∉ D
  lower : ∀ i, Real.exp (Real.exp ((4 / 10000 : ℝ) * L)) ≤ p i
  upper : ∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((6 / 10000 : ℝ) * L))
  balanced_lower : ∀ i, (1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N (p i))
  balanced_upper : ∀ i, residueDensity (tailDensityMask A N (p i)) ≤ 2 / 3
  nonempty : ∀ i, (tailDensityMask A N (p i)).Nonempty
  proper : ∀ i, (tailDensityMask A N (p i)).card < p i
  character_bound : ∀ i (χ : DirichletCharacter ℂ (p i)), χ ≠ 1 → ∀ a : ZMod (p i),
    ‖((tailDensityMask A N (p i)).card : ℂ)⁻¹ *
      ∑ x ∈ tailDensityMask A N (p i), χ⁻¹ (-a - x)‖ ≤ ε / 2

theorem frozen_initial_spectator_data {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite)
    (N : ℕ) (hN : ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p))
    {P Q D : Finset ℕ} {d cutoff : ℕ} {L ε : ℝ} (hcutoff : 3 ≤ cutoff)
    (hQ : Q ⊆ primeLogCellSet 1 0 (Real.exp ((4 / 10000 : ℝ) * L))
      (Real.exp ((6 / 10000 : ℝ) * L)) \ D)
    (hgood : ∀ p ∈ Q, cutoff ≤ p ∧
      ((1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N p) ∧
        residueDensity (tailDensityMask A N p) ≤ 2 / 3) ∧ tailCharacterBias A N p ≤ ε / 2)
    (sl sr : Fin d → P) (hinj : Function.Injective (Fin.append sl sr))
    (hl : ∀ i, (sl i : ℕ) ∈ Q) (hr : ∀ i, (sr i : ℕ) ∈ Q) :
    FrozenInitialSpectatorData A N (frozenInitialSpectatorPrimes sl sr) L ε cutoff D := by
  let p := frozenInitialSpectatorPrimes sl sr
  have hmem := frozenInitialSpectatorPrimes_mem sl sr hl hr
  have hp (i) : (p i).Prime :=
    (mem_primeLogCellSet_iff.mp (Finset.mem_sdiff.mp (hQ (hmem i))).1).1
  have hc (i) : cutoff ≤ p i := (hgood _ (hmem i)).1
  have hne (i) : p i ≠ 2 := by have := hcutoff.trans (hc i); omega
  refine ⟨frozenInitialSpectatorPrimes_injective sl sr hinj, hp, hc,
    fun i => (Finset.mem_sdiff.mp (hQ (hmem i))).2, ?_, ?_,
    fun i => (hgood _ (hmem i)).2.1.1, fun i => (hgood _ (hmem i)).2.1.2,
    fun i => tailDensityMask_nonempty hA N (p i) (hp i).pos, ?_, ?_⟩
  · intro i
    have hb := mem_primeLogCellSet_iff.mp (Finset.mem_sdiff.mp (hQ (hmem i))).1
    exact ((Real.lt_log_iff_exp_lt (by exact_mod_cast (hp i).pos)).mp hb.2.2.1).le
  · intro i
    have hb := mem_primeLogCellSet_iff.mp (Finset.mem_sdiff.mp (hQ (hmem i))).1
    exact (Real.log_le_iff_le_exp (by exact_mod_cast (hp i).pos)).mp hb.2.2.2
  · intro i
    let : NeZero (p i) := ⟨(hp i).ne_zero⟩
    exact tailDensityMask_card_lt hB N (p i) (hp i).pos (hN _ (hp i))
  · intro i χ hχ a
    let : Fact (p i).Prime := ⟨hp i⟩
    exact (tailDensityMask_reverse_character_mean_bound A N (p i) (hne i) χ hχ a).trans
      (hgood _ (hmem i)).2.2

theorem FrozenInitialSpectatorData.comparison_upper {A : Set ℕ} {N d cutoff : ℕ}
    {p : Fin (d + d) → ℕ} {L ε : ℝ} {D : Finset ℕ}
    (F : FrozenInitialSpectatorData A N p L ε cutoff D) (hL : 0 ≤ L) (i) :
    (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L)) :=
  (F.upper i).trans (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by nlinarith only [hL])))

theorem FrozenInitialSpectatorData.mono {A : Set ℕ} {N d cutoff cutoff' : ℕ}
    {p : Fin (d + d) → ℕ} {L ε ε' : ℝ} {D : Finset ℕ}
    (F : FrozenInitialSpectatorData A N p L ε cutoff D)
    (hε : ε ≤ ε') (hcutoff : cutoff' ≤ cutoff) :
    FrozenInitialSpectatorData A N p L ε' cutoff' D := by
  refine ⟨F.injective, F.prime, fun i => hcutoff.trans (F.ge_cutoff i),
    F.avoids, F.lower, F.upper, F.balanced_lower, F.balanced_upper,
    F.nonempty, F.proper, ?_⟩
  intro i χ hχ a
  exact (F.character_bound i χ hχ a).trans (by linarith)

end Ostmann

end OAI
