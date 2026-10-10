import OAI.NumberTheory.Ostmann.Construction.InitialEtaPrior
import OAI.NumberTheory.Ostmann.Construction.InitialSourceChoice
import OAI.NumberTheory.Ostmann.Construction.SourceRangeSeparationScales

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction.RepeatedPriorBounds
open Filter

theorem harmonic_mass_le {P : Finset ℕ} (hP : ∀p∈P,Nat.Prime p)
    (hZ : 0<harmonicPrimeMass P) {A : ℝ} (hA : (harmonicPrimeMass P)⁻¹≤A)
    (p : (harmonicPrimeSource P hP hZ).Sample) :
    (harmonicPrimeSource P hP hZ).law.mass p≤A/(p:ℕ) := by
  rw [harmonicPrimeSource_mass]
  have he : (1:ℝ)/((p:ℕ)*harmonicPrimeMass P)=(harmonicPrimeMass P)⁻¹/(p:ℕ) := by
    simp only [div_eq_mul_inv,mul_inv_rev,one_mul]
  rw [he]
  exact div_le_div_of_nonneg_right hA (Nat.cast_nonneg _)

theorem cell_mass_le {c : ℝ} {E : Finset ℕ} (hZ : 0<logCellMass c E)
    {A : ℝ} (hA : (logCellMass c E)⁻¹≤A)
    (p : (logCellPrimeSource c E hZ).Sample) :
    (logCellPrimeSource c E hZ).law.mass p≤A/(p:ℕ) := by
  apply (logCellPrior_mass_le c E hZ p).trans
  have he : (1:ℝ)/((p:ℕ)*logCellMass c E)=(logCellMass c E)⁻¹/(p:ℕ) := by
    simp only [div_eq_mul_inv,mul_inv_rev,one_mul]
  rw [he]
  exact div_le_div_of_nonneg_right hA (Nat.cast_nonneg _)

theorem cell_mass_exp_bound_eventually :
    ∀ᶠ L : ℝ in atTop, ∀ c : ℝ, favorableBlockWidth L/100≤c → c≤Real.exp L/2 →
      ∀ E : Finset ℕ, E.card≤2 → ∀ hZ : 0<logCellMass c E,
        ∀ p : (logCellPrimeSource c E hZ).Sample,
          (logCellPrimeSource c E hZ).law.mass p≤Real.exp L/(p:ℕ) := by
  obtain ⟨M,hM⟩ := eventually_atTop.mp logCell_normalization_eventually
  filter_upwards [(exp_mul_tendsto (by norm_num : (0:ℝ)<1/100)).eventually_ge_atTop
    (100*max M 1)] with L hL
  intro c hc hcu E hE hZ p
  have hMc : M≤c := by
    change 100*max M 1≤favorableBlockWidth L at hL
    linarith [le_max_left M 1]
  exact cell_mass_le hZ ((hM c hMc E hE).2.2.trans (by linarith)) p

theorem bulk_mass_lower_eventually :
    ∀ᶠ L : ℝ in atTop, ∀ E : Finset ℕ, E.card≤2 →
      L/1000≤harmonicPrimeMass (bulkPrimeBand L E) := by
  filter_upwards [logLogPrimeBand_mass_eventually (by norm_num : (0:ℝ)≤1/250)
    (by norm_num : (1/250:ℝ)<3/500)] with L hL
  intro E hE
  have h := (hL E hE).2.1
  change L/1000≤harmonicPrimeMass (logLogPrimeBand ((1/250:ℝ)*L) ((3/500:ℝ)*L) \ E)
  linarith

end Ostmann.Construction.RepeatedPriorBounds

end

end OAI
