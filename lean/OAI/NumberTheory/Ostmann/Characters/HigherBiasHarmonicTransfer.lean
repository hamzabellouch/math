import OAI.NumberTheory.Ostmann.Characters.HigherBiasHarmonicThreshold
import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticBiasLittleOHarmonic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Characters
open Construction Filter
open scoped BigOperators

theorem eventually_higher_harmonic_band_le_of_no_biased_mass (d : Decomposition)
    {α β : ℝ} (hα : 0 < α) (hαβ : α < β)
    (hno : ∀ δ : ℝ,0 < δ → δ ≤ 1 → ∀ mass : ℝ,0 < mass →
      ∀ᶠ L : ℝ in atTop,∀ E : Finset ℕ,
        (∀ p∈E,p.Prime ∧ α*L ≤ Real.log (Real.log p) ∧ Real.log (Real.log p) ≤ β*L) →
        mass*L ≤ harmonicPrimeMass E → (∀ p∈E,δ ≤ higherPrimeBias d p) → False)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop,∀ P : Finset ℕ,(∀ p∈P,p.Prime) →
      (∀ p∈P,α*L ≤ Real.log (Real.log p) ∧ Real.log (Real.log p) ≤ β*L) →
      (∑ p∈P,higherPrimeBias d p/p) ≤ ε*L := by
  obtain ⟨δ,hδ,hδu,hextract⟩ := exists_higher_harmonic_threshold d hα hαβ ε hε
  filter_upwards [hextract,hno δ hδ hδu (ε/2) (by positivity)] with L he hn
  intro P hP hband
  by_contra hh
  have hs : ε*L ≤ ∑ p∈P,higherPrimeBias d p/p := (lt_of_not_ge hh).le
  obtain ⟨hm,hE⟩ := he P (fun p hp=>⟨hP p hp,hband p hp⟩) hs
  exact hn (higherBiasedSubset d P δ)
    (fun p hp=>⟨(hE p hp).2.1,(hE p hp).2.2.1,(hE p hp).2.2.2.1⟩)
    hm (fun p hp=>(hE p hp).2.2.2.2)

def higherHarmonicBandMass (d : Decomposition) (α β L : ℝ) : ℝ :=
  ∑ p∈QuadraticCenter.closedLogLogPrimeBand α β L,higherPrimeBias d p/p

lemma higherHarmonicBandMass_nonneg (d : Decomposition) (α β L : ℝ) :
    0 ≤ higherHarmonicBandMass d α β L :=
  Finset.sum_nonneg (fun p _=>div_nonneg (higherPrimeBias_nonneg d p) (Nat.cast_nonneg _))

theorem higherHarmonicBandMass_isLittleO_of_eventually (d : Decomposition)
    {α β : ℝ}
    (hbound : ∀ ε : ℝ,0 < ε → ∀ᶠ L : ℝ in atTop,∀ P : Finset ℕ,
      (∀ p∈P,p.Prime) →
      (∀ p∈P,α*L ≤ Real.log (Real.log p) ∧ Real.log (Real.log p) ≤ β*L) →
      (∑ p∈P,higherPrimeBias d p/p) ≤ ε*L) :
    higherHarmonicBandMass d α β =o[atTop] (fun L : ℝ=>L) := by
  apply Asymptotics.isLittleO_iff.mpr
  intro ε hε
  filter_upwards [hbound ε hε,eventually_ge_atTop (0:ℝ)] with L hL hL0
  have hh := hL (QuadraticCenter.closedLogLogPrimeBand α β L)
    (fun p hp=>(QuadraticCenter.mem_closedLogLogPrimeBand.mp hp).1)
    (fun p hp=>(QuadraticCenter.mem_closedLogLogPrimeBand.mp hp).2)
  change higherHarmonicBandMass d α β L ≤ ε*L at hh
  simpa only [Real.norm_eq_abs,abs_of_nonneg (higherHarmonicBandMass_nonneg d α β L),
    abs_of_nonneg hL0] using hh

end Ostmann.Characters

end

end OAI
