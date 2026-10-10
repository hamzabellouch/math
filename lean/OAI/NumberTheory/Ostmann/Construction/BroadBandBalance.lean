import OAI.NumberTheory.Ostmann.Supply.PrimeBandSelection

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction
open Filter
open scoped BigOperators

def balancedPrimePart (d : Decomposition) (P : Finset ℕ) : Finset ℕ := by
  classical
  exact P.filter (fun p => Supply.balancedDensity d p)

def balancedPrimeIndicator (d : Decomposition) (p : ℕ) : ℝ := by
  classical
  exact if Supply.balancedDensity d p then 1 else 0

theorem broadBand_balanced_mass_eventually (d : Decomposition) {α β : ℝ}
    (hα : 0≤α) (hαβ : α<β) (hβ : β≤(9/10:ℝ)) :
    ∀ᶠ L : ℝ in atTop, ∀ E : Finset ℕ, E.card≤2 →
      0<harmonicPrimeMass (logLogPrimeBand (α*L) (β*L) \ E) ∧
      harmonicPrimeMass (logLogPrimeBand (α*L) (β*L) \ E)/2≤
        harmonicPrimeMass (balancedPrimePart d (logLogPrimeBand (α*L) (β*L) \ E)) := by
  classical
  have hδ : 0<(β-α)/4 := by linarith
  filter_upwards [logLogPrimeBand_mass_eventually hα hαβ,
    Supply.unbalancedPrimePrefix_mass_small d hδ,eventually_ge_atTop (0:ℝ)]
    with L hmass hbad hL
  intro E hE
  obtain ⟨hZ,hlo,hhi⟩ := hmass E hE
  let P := logLogPrimeBand (α*L) (β*L) \ E
  have hsub : P.filter (fun p => ¬Supply.balancedDensity d p) ⊆
      Supply.unbalancedPrimePrefix d (Supply.supplyBandCutoff L) := by
    intro p hp
    obtain ⟨hp,hbad⟩ := Finset.mem_filter.mp hp
    have hband := (Finset.mem_sdiff.mp hp).1
    have hprime := logLogPrimeBand_prime hband
    have hpupper := (Finset.mem_Ioc.mp (Finset.mem_filter.mp (Finset.mem_sdiff.mp hband).1).1).2
    have hcut : ⌊Real.exp (Real.exp (β*L))⌋₊≤Supply.supplyBandCutoff L :=
      Nat.floor_mono (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right hβ hL)))
    exact Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hpupper.trans hcut,hprime⟩,hbad⟩
  have hbadmass := (Supply.harmonicPrimeMass_mono hsub).trans hbad
  have hsplit : harmonicPrimeMass (P.filter (fun p => Supply.balancedDensity d p))+
      harmonicPrimeMass (P.filter (fun p => ¬Supply.balancedDensity d p))=harmonicPrimeMass P := by
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  refine ⟨hZ,?_⟩
  change harmonicPrimeMass P/2≤harmonicPrimeMass (P.filter (fun p => Supply.balancedDensity d p))
  change (β-α)*L/2≤harmonicPrimeMass P at hlo
  linarith

end Ostmann.Construction

end

end OAI
