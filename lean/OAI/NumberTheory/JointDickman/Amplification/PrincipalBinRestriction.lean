import OAI.NumberTheory.JointDickman.Counting.NonprincipalBinShort
import OAI.NumberTheory.JointDickman.Counting.BinPrincipalShort

namespace OAI

/-! # Principal characters are exact finite-prime restrictions -/
namespace JointDickman
open Finset Filter Classical PublishedInputs
open scoped Topology

noncomputable def coprimePrimeWeight (P : Finset ℕ) (t : ℕ → ℝ) (q : ℕ) : ArithmeticFunction ℝ :=
  finitePrimeWeight (P ∪ q.primeFactors) (fun p => if p ∈ q.primeFactors then 0 else t p)

theorem coprimePrimeWeight_eq (P : Finset ℕ) (t : ℕ → ℝ) {q : ℕ} (hq : q ≠ 0) (n : ℕ) :
    coprimePrimeWeight P t q n = if n.Coprime q then finitePrimeWeight P t n else 0 := by
  by_cases hn : n = 0
  · subst n
    simp [coprimePrimeWeight]
  unfold coprimePrimeWeight
  simp only [finitePrimeWeight,ArithmeticFunction.coe_mk,hn,ite_false]
  by_cases hc : n.Coprime q
  · rw [ite_eq_left hc]
    have hd p (hp : p ∈ q.primeFactors) : ¬p ∣ n := by
      intro hpn
      have hpp := Nat.mem_primeFactors.mp hp
      exact hpp.1.ne_one (Nat.eq_one_of_dvd_coprimes hc hpn hpp.2.1)
    rw [prod_union_eq_left (fun p hp _ => by simp [hd p hp])]
    apply prod_congr rfl
    intro p _
    by_cases hp : p ∈ q.primeFactors
    · simp [hd p hp]
    · simp [hp]
  · rw [ite_eq_right hc]
    obtain ⟨p,hp,hpn,hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
    have hpQ : p ∈ q.primeFactors := Nat.mem_primeFactors.mpr ⟨hp,hpq,hq⟩
    exact prod_eq_zero (mem_union_right P hpQ) (by simp [hpn,hpQ])

theorem principal_twistedWeightedBinAverage {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (ζ : ι → ℂ) (μ : ℂ) (P : Finset ℕ) (t : ℕ → ℝ)
    {q : ℕ} [NeZero q] (H z : ℝ) :
    twistedWeightedBinAverage E ζ μ (finitePrimeWeight P t) (1 : DirichletCharacter ℂ q) H z =
      weightedBinAverage E ζ μ (coprimePrimeWeight P t q) H z := by
  unfold twistedWeightedBinAverage weightedBinAverage
  congr 1
  apply sum_congr rfl
  intro n _
  rw [coprimePrimeWeight_eq P t (NeZero.ne q)]
  by_cases hc : n.Coprime q
  · rw [ite_eq_left hc,MulChar.one_apply ((ZMod.isUnit_iff_coprime n q).mpr hc),mul_one]
  · rw [ite_eq_right hc,MulChar.map_nonunit _ (fun h => hc ((ZMod.isUnit_iff_coprime n q).mp h))]
    simp

theorem principal_weightedBinAverage_short
    (hMR : RealShortIntervalInput) (hBill : FiniteBinDistributionInput)
    {J : ℕ} (hJ : 2 ≤ J) (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖ = 1)
    (P : ℕ → Finset ℕ) (hP : ∀ B p, p ∈ P B → p.Prime)
    (t : ℕ → ℕ → ℝ) (ht : ∀ B p, p ∈ P B → 0 ≤ t B p ∧ t B p ≤ 1)
    {q : ℕ} [NeZero q] (A scale H : ℕ → ℝ) (hA : ∀ B, 0 < A B)
    (hscale : Tendsto scale atTop atTop) (hH : Tendsto H atTop atTop) :
    ∃ μ : ℂ, ‖μ‖ ≤ 1 ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ B in atTop, ∀ᶠ n in atTop,
      (1/(A B*scale n))*(∫ z in (A B*scale n)..2*(A B*scale n),
        ‖twistedWeightedBinAverage (fun i : Fin (J-1) => primeBin (scale n) J (i.val+1)) ζ μ
          (finitePrimeWeight (P B) (t B)) (1 : DirichletCharacter ℂ q) (H B) z‖^2) < ε := by
  have hp B p (h : p ∈ P B ∪ q.primeFactors) : p.Prime := by
    rcases mem_union.mp h with h | h
    · exact hP B p h
    · exact (Nat.mem_primeFactors.mp h).1
  have hb B p (h : p ∈ P B ∪ q.primeFactors) :
      0 ≤ (if p ∈ q.primeFactors then 0 else t B p) ∧ (if p ∈ q.primeFactors then 0 else t B p) ≤ (1 : ℝ) := by
    by_cases hh : p ∈ q.primeFactors
    · simp [hh]
    · simpa only [ite_eq_right hh] using ht B p ((mem_union.mp h).resolve_right hh)
  obtain ⟨μ,hμ,hbound⟩ := finitePrimeWeight_short_averages hMR hBill hJ ζ hζ
    (fun B => P B ∪ q.primeFactors) hp (fun B p => if p ∈ q.primeFactors then 0 else t B p) hb
    A scale H hA hscale hH
  refine ⟨μ,hμ,?_⟩
  simpa only [principal_twistedWeightedBinAverage,coprimePrimeWeight] using hbound

end JointDickman

end OAI
