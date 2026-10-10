import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateSourceDefs
import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceScaleCutoff

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.DiagonalEstimate
open Template HigherBiasSource HigherBiasSource.SourceTemplate HigherBiasSourceWord
open HigherBiasSourceRoleBounds InitialCharacterScale Preliminaries Filter
attribute [local instance] Classical.propDecidable

theorem sourceScheduledShells_mass_lower
    {d : Decomposition} {E : Finset ℕ} {δ L α β ρ γ c₀ c BD μ : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀} (w : FixedConfigurationWitness s c BD)
    (hb : μ ≤ primeShellMass (s.locations.base 0))
    (ht : μ ≤ primeShellMass (s.locations.base 2))
    (hc : ∀i,μ ≤ primeShellMass (w.cells i)) (j : ℕ)
    (i : (schedule k j).Constituent (sourceWidth w.configuration (wordSize k L))) :
    μ ≤ primeShellMass (sourceScheduledShells w j i) := by
  have hword : ∀a : Fin (wordSize k L+1), μ ≤ primeShellMass
      (roleShells (s.locations.base 0) (s.locations.base 2) (wordSize k L) a) := by
    intro a
    refine Fin.addCases ?_ ?_ a
    · intro b
      simpa only [roleShells,Fin.append_left] using hb
    · intro b
      simpa only [roleShells,Fin.append_right] using ht
  have hroles : ∀a,μ ≤ primeShellMass (w.roles a) := by
    intro a
    refine Fin.addCases ?_ ?_ a
    · intro b
      simpa only [FixedConfigurationWitness.roles,halfRoleShells,Fin.append_left] using hword b
    · intro b
      simpa only [FixedConfigurationWitness.roles,halfRoleShells,Fin.append_right] using hc b
  unfold sourceScheduledShells
  rw [scheduledPrimeShells_eq_origin]
  generalize he : scheduledConstituentOrigin k
    (sourceWidth w.configuration (wordSize k L)) j i = a
  rcases a with ⟨⟨r,b⟩,a⟩
  erw [sourcePrimeShells_half]
  exact hroles _

theorem exp_neg_le_source_constant {a L : ℝ} (ha : 0 < a) (hL : -Real.log a ≤ L) :
    Real.exp (-L) ≤ a := by
  calc
    _ ≤ Real.exp (Real.log a) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := Real.exp_log ha

theorem eventually_sourceScheduled_mass_lower (k : ℕ)
    {α β ρ γ c₀ c : ℝ} (hα : 0 < α) (hαβ : α < β)
    (hρ : 0 < ρ) (hγ : 0 < γ) (hc₀ : 0 < c₀) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,∀(d : Decomposition)(E : Finset ℕ)(δ BD : ℝ),
      (∀p∈E,p.Prime) →
      ∀s : SelectedWordSource d E δ L k α β ρ γ c₀,∀w : FixedConfigurationWitness s c BD,
      ∀j i,Real.exp (-(β+1)*L) ≤ primeShellMass (sourceScheduledShells w j i) := by
  have hβ : 0 < β := hα.trans hαβ
  have hnum : ∀ᶠ L : ℝ in atTop,1 ≤ α*L :=
    (Filter.tendsto_id.const_mul_atTop hα).eventually_ge_atTop 1
  filter_upwards [eventually_higherSource_collisionScale10 k α hα,hnum,
    eventually_ge_atTop (1:ℝ),eventually_ge_atTop (-Real.log ρ),
    eventually_ge_atTop (-Real.log c₀),eventually_ge_atTop (-Real.log c)]
    with L hcut hnum hL hLρ hLc₀ hLc
  intro d E δ BD hE s w j i
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hu : 0 ≤ s.locations.u := by linarith [s.locations.top_lower]
  have hsource := source_base_mass s.locations hu (mul_nonneg hγ.le hL0)
    hE (hcut s.locations.u s.locations.top_lower)
  have hbase : Real.exp (-(β+1)*L) ≤ Real.exp (-L) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hb : Real.exp (-(β+1)*L) ≤ ρ*L :=
    (hbase.trans (exp_neg_le_source_constant hρ hLρ)).trans
      (by nlinarith)
  have ht : Real.exp (-(β+1)*L) ≤ c₀ :=
    hbase.trans (exp_neg_le_source_constant hc₀ hLc₀)
  have he : Real.exp (-(β+1)*L) ≤ c/Real.exp (β*L) := by
    calc
      _ = Real.exp (-L)/Real.exp (β*L) := by rw [←Real.exp_sub];congr 1;ring
      _ ≤ _ := div_le_div_of_nonneg_right (exp_neg_le_source_constant hc hLc) (Real.exp_pos _).le
  obtain ⟨n,hn⟩ := w.nonempty
  exact sourceScheduledShells_mass_lower w (hb.trans hsource.1) (ht.trans hsource.2.2)
    (fun a=>he.trans (w.good n hn a).2.2.1) j i

end Ostmann.Characters.DiagonalEstimate

end

end OAI
