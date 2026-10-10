import OAI.NumberTheory.Ostmann.Arithmetic.PrimeBandHarmonicTransfer
import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticBiasLittleO

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.QuadraticCenter
open Ostmann.Characters Ostmann.Preliminaries Filter
open scoped BigOperators

theorem eventually_quadratic_harmonic_band_le (d : Decomposition) {α β : ℝ}
    (hα : 0 < α) (hαβ : α < β) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, α*L ≤ Real.log (Real.log p) ∧ Real.log (Real.log p) ≤ β*L) →
      (∑ p ∈ P, quadraticBiasValue d p/p) ≤ ε*L :=
  Arithmetic.PrimeBandHarmonicTransfer.eventually_harmonic_band_le
    (quadraticBiasValue d) (quadraticBiasValue_nonneg d)
    (eventually_quadratic_prime_band_le d) hα hαβ ε hε

def closedLogLogPrimeBand (α β L : ℝ) : Finset ℕ := by
  classical
  exact (⌊Real.exp (Real.exp (β*L))⌋₊).primesLE.filter
    (fun p => α*L ≤ Real.log (Real.log p) ∧ Real.log (Real.log p) ≤ β*L)

@[simp] lemma mem_closedLogLogPrimeBand {α β L : ℝ} {p : ℕ} :
    p ∈ closedLogLogPrimeBand α β L ↔
      p.Prime ∧ α*L ≤ Real.log (Real.log p) ∧ Real.log (Real.log p) ≤ β*L := by
  classical
  simp only [closedLogLogPrimeBand,Finset.mem_filter,Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨_,hp⟩,hband⟩
    exact ⟨hp,hband⟩
  · rintro ⟨hp,hlo,hhi⟩
    have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hl : 0 < Real.log p := Real.log_pos hpR
    have hu : (p : ℝ) ≤ Real.exp (Real.exp (β*L)) :=
      (Real.log_le_iff_le_exp (lt_trans zero_lt_one hpR)).mp
        ((Real.log_le_iff_le_exp hl).mp hhi)
    exact ⟨⟨Nat.le_floor hu,hp⟩,hlo,hhi⟩

def quadraticHarmonicBandMass (d : Decomposition) (α β L : ℝ) : ℝ :=
  ∑ p ∈ closedLogLogPrimeBand α β L, quadraticBiasValue d p/p

lemma quadraticHarmonicBandMass_nonneg (d : Decomposition) (α β L : ℝ) :
    0 ≤ quadraticHarmonicBandMass d α β L := by
  unfold quadraticHarmonicBandMass
  exact Finset.sum_nonneg (fun p hp => div_nonneg (quadraticBiasValue_nonneg d p) (Nat.cast_nonneg _))

theorem quadraticHarmonicBandMass_isLittleO (d : Decomposition) {α β : ℝ}
    (hα : 0 < α) (hαβ : α < β) :
    quadraticHarmonicBandMass d α β =o[atTop] (fun L : ℝ => L) := by
  apply Asymptotics.isLittleO_iff.mpr
  intro ε hε
  filter_upwards [eventually_quadratic_harmonic_band_le d hα hαβ ε hε,
    eventually_ge_atTop (0 : ℝ)] with L hL hnonneg
  have hh := hL (closedLogLogPrimeBand α β L)
    (fun p hp => (mem_closedLogLogPrimeBand.mp hp).1)
    (fun p hp => (mem_closedLogLogPrimeBand.mp hp).2)
  have hh' : quadraticHarmonicBandMass d α β L ≤ ε*L := by
    unfold quadraticHarmonicBandMass
    exact hh
  simpa only [Real.norm_eq_abs,abs_of_nonneg (quadraticHarmonicBandMass_nonneg d α β L),
    abs_of_nonneg hnonneg] using hh'

end Ostmann.QuadraticCenter

end

end OAI
