import OAI.NumberTheory.Ostmann.QuadraticCenter.BiasBandSelectionBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Ostmann.Characters Ostmann.Preliminaries Filter
open scoped BigOperators

theorem eventually_bad_band_oriented_dyadic (d : Decomposition) {δ ρ : ℝ}
    (hδ : 0 < δ) (hρ : 0 < ρ) :
    ∀ᶠ T : ℝ in atTop, ρ*T < quadraticBadBandMass d δ T →
      ∃ (j : ℕ) (G : Finset ℕ) (ε t : ℕ → ℤ),
        T/2 ≤ Real.log (2^j : ℕ) ∧ Real.log (2^j : ℕ) ≤ 2*T ∧
        (ρ/20)*(2^j : ℕ)/Real.log (2^j : ℕ) ≤ (G.card : ℝ) ∧
        (∀ p ∈ G, p.Prime ∧ p ≠ 2 ∧ 2^j ≤ p ∧ p ≤ 2*2^j ∧
          (ε p = 1 ∨ ε p = -1) ∧
          δ/4 ≤ (∑ a ∈ positiveIntegerWindow d.A (parameterX T),
            ((ε p*jacobiSym (a-t p) p : ℤ) : ℝ))/(positiveIntegerWindow d.A (parameterX T)).card ∧
          (∑ a ∈ negativeIntegerWindow d.B (parameterX T),
            ((ε p*jacobiSym (a-t p) p : ℤ) : ℝ))/(negativeIntegerWindow d.B (parameterX T)).card ≤ -δ/4) := by
  classical
  filter_upwards [parameterX_tendsto.eventually (eventually_biased_dyadic_prime_block d hδ),
    eventually_biasSelectionCost_le δ hρ, eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop (2*Real.log 2)] with T hselect hcost hT1 hT2
  intro hmass
  let X := parameterX T
  let Q := collisionScale 4 X
  let N := ⌊Real.exp (2*T)⌋₊
  let P := boundedClosedLogarithmicPrimeBand Q T
  have hT : 0 < T := by linarith
  have hN : ∀ p ∈ P, p.val ≤ N := by
    intro p hp
    have hh := (mem_boundedClosedLogarithmicPrimeBand.mp hp).2
    exact Nat.le_floor ((Real.log_le_iff_le_exp (by exact_mod_cast (primeUpTo_prime p).pos)).mp hh)
  obtain ⟨j,G,ε,t,hj,hG,hgood,hcard⟩ := hselect P N hN
  have hmass' : ρ*T/2 ≤ boundedPrimeWeight (quadraticBiasedPrimes d Q δ P) -
      biasSelectionCost δ*Real.log (Real.log (X : ℝ)) := by
    change ρ*T < boundedPrimeWeight (quadraticBiasedPrimes d Q δ P) at hmass
    linarith
  have hz : (0 : ℝ) < (2^j : ℕ) := by positivity
  have hcard' : (ρ*T/2)*(2^j : ℕ) ≤
      (Nat.log 2 N+1 : ℕ)*Real.log (2*(2^j : ℕ))*G.card :=
    (mul_le_mul_of_nonneg_right hmass' hz.le).trans hcard
  have hne : G.Nonempty := by
    by_contra hn
    have he : G = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [he,Finset.card_empty,Nat.cast_zero,mul_zero] at hcard'
    exact (not_le_of_gt (mul_pos (by positivity) hz)) hcard'
  have hband : ∀ p ∈ G, T ≤ Real.log p ∧ Real.log p ≤ 2*T := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp (hG hp)
    exact mem_boundedClosedLogarithmicPrimeBand.mp hq
  obtain ⟨p,hp⟩ := hne
  have hpR : (0 : ℝ) < p := by exact_mod_cast (hgood p hp).1.pos
  have hzp : ((2^j : ℕ) : ℝ) ≤ p := by exact_mod_cast (hgood p hp).2.2.1
  have hpz : (p : ℝ) ≤ 2*(2^j : ℕ) := by exact_mod_cast (hgood p hp).2.2.2.1.le
  have hlogzu : Real.log (2^j : ℕ) ≤ 2*T :=
    (Real.log_le_log hz hzp).trans (hband p hp).2
  have hlogzl : T/2 ≤ Real.log (2^j : ℕ) := by
    have hh := Real.log_le_log hpR hpz
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hz.ne'] at hh
    linarith [(hband p hp).1]
  have hlogz : 0 < Real.log (2^j : ℕ) := by linarith
  have hlog2z : Real.log (2*(2^j : ℕ)) ≤ 2*Real.log (2^j : ℕ) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hz.ne']
    linarith
  have hlog2z0 : 0 ≤ Real.log (2*(2^j : ℕ)) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hz.ne']
    linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  have hlogN : Real.log N ≤ 2*T :=
    (log_floor_exp_bounds (show Real.log 2 ≤ 2*T by linarith)).2.2
  have hncount := dyadic_count_le_five N hT1 hlogN
  have hupper : (Nat.log 2 N+1 : ℕ)*Real.log (2*(2^j : ℕ))*G.card ≤
      (5*T)*(2*Real.log (2^j : ℕ))*G.card := by gcongr
  have hraw := hcard'.trans hupper
  have hprod : (ρ/20)*(2^j : ℕ) ≤ (G.card : ℝ)*Real.log (2^j : ℕ) := by
    apply (mul_le_mul_iff_right₀ hT).mp
    nlinarith
  refine ⟨j,G,ε,t,hlogzl,hlogzu,(div_le_iff₀ hlogz).mpr hprod,?_⟩
  intro q hq
  have hh := hgood q hq
  exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1.le,hh.2.2.2.2⟩

end Ostmann.QuadraticCenter

end

end OAI
