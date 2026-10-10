import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateIntegerPriorSource
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedSourceScalesShells

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.DiagonalEstimate
open Construction Preliminaries Template HigherBiasSource HigherBiasSource.SourceTemplate
open InitialCharacterScale TemplateOneSidedSourceScales
attribute [local instance] Classical.propDecidable

theorem integerPrimeSupport_positive_prime {Q : ℕ} {E : Finset (PrimeUpTo Q)}
    {n : ℤ} (hn : n∈integerPrimeSupport E) : 0 < n ∧ n.natAbs.Prime := by
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
  exact ⟨by exact_mod_cast (primeUpTo_prime p).pos,by simpa using primeUpTo_prime p⟩

theorem integerPrimeSupport_eq_nat_image {Q : ℕ} (E : Finset (PrimeUpTo Q)) :
    integerPrimeSupport E=(E.image (fun p=>p.val)).image (fun p:ℕ=>(p:ℤ)) := by
  simp only [integerPrimeSupport,Finset.image_image,Function.comp_def]

theorem integerPrimeWeight_pos_iff {Q : ℕ} (E : Finset (PrimeUpTo Q))
    (hE : 0 < primeShellMass E) (n : ℤ) :
    0 < integerPrimeWeight E n ↔ n∈integerPrimeSupport E := by
  by_cases hn : n∈integerPrimeSupport E
  · simp only [integerPrimeWeight,hn,ite_true,iff_true]
    exact div_pos (inv_pos.mpr (by exact_mod_cast (integerPrimeSupport_positive_prime hn).1)) hE
  · simp only [integerPrimeWeight,hn,ite_false,lt_self_iff_false]

theorem integerPrimeSupport_exp_bounds {Q : ℕ} {E : Finset (PrimeUpTo Q)}
    {lo hi : ℝ} (hlog : ∀p∈E,lo ≤ Real.log p.val ∧ Real.log p.val ≤ hi)
    {n : ℤ} (hn : n∈integerPrimeSupport E) :
    Real.exp lo ≤ (n:ℝ) ∧ (n:ℝ) ≤ Real.exp hi := by
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
  have hp0 : 0 < (p.val:ℝ) := by exact_mod_cast (primeUpTo_prime p).pos
  simpa only [Int.cast_natCast,Real.exp_log hp0] using
    And.intro (Real.exp_le_exp.mpr (hlog p hp).1) (Real.exp_le_exp.mpr (hlog p hp).2)

section
variable {d : Decomposition} {E : Finset ℕ} {δ L α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀} (w : FixedConfigurationWitness s c BD)
    (j : ℕ)

def sourceSurvivorNaturalSupport := fun i=>(sourceSurvivorShells w j i).image (fun p=>p.val)

theorem sourceSurvivorIntegerSupport_eq_nat_image (i) :
    sourceSurvivorIntegerSupport w j i=
      (sourceSurvivorNaturalSupport w j i).image (fun p:ℕ=>(p:ℤ)) :=
  integerPrimeSupport_eq_nat_image _

theorem sourceSurvivorNaturalSupport_prime (i) {p : ℕ}
    (hp : p∈sourceSurvivorNaturalSupport w j i) : p.Prime := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
  exact primeUpTo_prime q

theorem sourceSurvivorIntegerSupport_positive_prime (i) {n : ℤ}
    (hn : n∈sourceSurvivorIntegerSupport w j i) : 0 < n ∧ n.natAbs.Prime :=
  integerPrimeSupport_positive_prime hn

theorem sourceSurvivorIntegerWeight_nonneg (i) (n : ℤ) :
    0 ≤ sourceSurvivorIntegerWeight w j i n :=
  integerPrimeWeight_nonneg _ (sourceSurvivorShells_pos w j i) n

theorem sourceSurvivorIntegerWeight_pos_iff (i) (n : ℤ) :
    0 < sourceSurvivorIntegerWeight w j i n ↔ n∈sourceSurvivorIntegerSupport w j i :=
  integerPrimeWeight_pos_iff _ (sourceSurvivorShells_pos w j i) n

theorem sourceSurvivorIntegerWeight_sum (i) :
    (∑n∈sourceSurvivorIntegerSupport w j i,sourceSurvivorIntegerWeight w j i n)=1 :=
  integerPrimeWeight_sum _ (sourceSurvivorShells_pos w j i)

theorem sourceSurvivorIntegerSupport_bounds
    (hband : ∀p∈E,α*L ≤ Real.log (Real.log p) ∧ Real.log (Real.log p) ≤ β*L)
    (i) {n : ℤ} (hn : n∈sourceSurvivorIntegerSupport w j i) :
    Real.exp (Real.exp (α*L)) ≤ (n:ℝ) ∧ (n:ℝ) ≤ Real.exp (Real.exp (β*L)) :=
  integerPrimeSupport_exp_bounds (sourceSurvivorShells_log_bounds w hband j i) hn

theorem sourceSurvivorIntegerSupport_abs_le
    (hband : ∀p∈E,α*L ≤ Real.log (Real.log p) ∧ Real.log (Real.log p) ≤ β*L)
    (i) {n : ℤ} (hn : n∈sourceSurvivorIntegerSupport w j i) :
    |(n:ℝ)| ≤ Real.exp (Real.exp (β*L)) := by
  rw [abs_of_pos (by exact_mod_cast (sourceSurvivorIntegerSupport_positive_prime w j i hn).1)]
  exact (sourceSurvivorIntegerSupport_bounds w j hband i hn).2

end
end Ostmann.Characters.DiagonalEstimate

end

end OAI
