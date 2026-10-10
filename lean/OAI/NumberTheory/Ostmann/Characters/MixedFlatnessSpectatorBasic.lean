import OAI.NumberTheory.Ostmann.Characters.HigherBiasValue
import OAI.NumberTheory.Ostmann.Characters.MixedFlatnessFinite
import OAI.NumberTheory.Ostmann.Characters.MixedPrimeBiasDefs
import OAI.NumberTheory.Ostmann.Construction.HarmonicPriorEvent
import OAI.NumberTheory.Ostmann.Construction.LogLogPrimeBandSupport
import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticBiasLittleOHarmonic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Characters
open Construction QuadraticCenter Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem mixedPrimeBias_sq_le_first (d : Decomposition) {p : ℕ} (hp : p.Prime)
    (hp2 : p≠2) (hb : Supply.balancedDensity d p) :
    (mixedPrimeBias d p)^2 ≤ 48*(quadraticBiasValue d p+higherPrimeBias d p+(p:ℝ)⁻¹) := by
  let : Fact p.Prime := ⟨hp⟩
  have hb' : (1/3:ℝ)≤Supply.density (d.residueSupport p) ∧
      Supply.density (d.residueSupport p)≤2/3 := by
    simpa only [Supply.balancedDensity,Supply.residueDensityTotal_eq] using hb
  have hh := correlationBound_sq_le_quadratic_higher (d.residueSupport p) hp2
    (by linarith : 1/4≤Supply.density (d.residueSupport p))
    (by linarith : Supply.density (d.residueSupport p)≤3/4)
  rw [←mixedPrimeBias_prime,←quadraticBiasValue_prime,←higherPrimeBias_prime] at hh
  have hq0 := quadraticBiasValue_nonneg d p
  have hq1 := quadraticBiasValue_le_one d p
  have ha0 := higherPrimeBias_nonneg d p
  have ha1 := higherPrimeBias_le_one d p
  nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hq1),mul_nonneg ha0 (sub_nonneg.mpr ha1)]

def mixedBadPrimes (d : Decomposition) (P : Finset ℕ) (δ : ℝ) : Finset ℕ :=
  P.filter (fun p=>δ ≤ mixedPrimeBias d p)

theorem mixedBadPrimes_mass_bound (d : Decomposition) (P : Finset ℕ)
    (hP : ∀p∈P,p.Prime) (hodd : ∀p∈P,p≠2)
    (hbal : ∀p∈P,Supply.balancedDensity d p)
    {δ r : ℝ} (hδ : 0<δ) (hr : 0≤r) (hrad : ∀p∈P,(p:ℝ)⁻¹≤r) :
    δ^2*harmonicPrimeMass (mixedBadPrimes d P δ) ≤
      48*((∑p∈P,quadraticBiasValue d p/p)+(∑p∈P,higherPrimeBias d p/p)+r*harmonicPrimeMass P) := by
  unfold harmonicPrimeMass
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑p∈mixedBadPrimes d P δ,
        48*(quadraticBiasValue d p/p+higherPrimeBias d p/p+r*(1/p)) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hp,hbad⟩ := Finset.mem_filter.mp hp
      have hs : δ^2≤(mixedPrimeBias d p)^2 :=
        (sq_le_sq₀ hδ.le (mixedPrimeBias_nonneg d p)).mpr hbad
      have hh := hs.trans (mixedPrimeBias_sq_le_first d (hP p hp) (hodd p hp) (hbal p hp))
      have hh' : δ^2≤48*(quadraticBiasValue d p+higherPrimeBias d p+r) := by
        linarith [hrad p hp]
      have hd := mul_le_mul_of_nonneg_right hh' (inv_nonneg.mpr (Nat.cast_nonneg p : (0:ℝ)≤p))
      convert hd using 1 <;> simp only [div_eq_mul_inv] <;> ring
    _ ≤ ∑p∈P,48*(quadraticBiasValue d p/p+higherPrimeBias d p/p+r*(1/p)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro p hp _
      have hq := quadraticBiasValue_nonneg d p
      have ha := higherPrimeBias_nonneg d p
      positivity
    _ = _ := by
      rw [←Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_add_distrib,←Finset.mul_sum]

end Ostmann.Characters

end

end OAI
