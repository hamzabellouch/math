import Mathlib
import OAI.Combinatorics.KMedian.Rounding.RationalTaper
import OAI.Combinatorics.KMedian.Rounding.RationalTaperZero

namespace OAI

section
section
namespace MetricKMedian.Taper
open Finset
variable {I : Type*} [Fintype I] [LinearOrder I]

def rationalColocatedMass (g : ℚ) (d : I → ℚ) : ℚ :=
  ∑ i, if d i=0 then g else 0

omit [LinearOrder I] in
theorem cast_rationalColocatedMass (g : ℚ) (d : I → ℚ) :
    (rationalColocatedMass g d:ℝ)=colocatedMass g (fun i => (d i:ℝ)) := by
  simp only [rationalColocatedMass,colocatedMass,Rat.cast_sum,apply_ite,
    Rat.cast_zero,Rat.cast_eq_zero]

def rationalRadius (g P : ℚ) (d : I → ℚ) : ℚ :=
  if 1 ≤ rationalColocatedMass g d then 0 else 1/inverseRadius g P d

def sourceMarginals (g P : ℚ) (d : I → ℚ) (own : Finset I) (Δ : ℕ) : I → ℚ :=
  if 1 ≤ rationalColocatedMass g d then zeroMarginal d own Δ
  else fun i => rationalMarginal P (d i) (inverseRadius g P d)

theorem rational_data (g P : ℚ) (d : I → ℚ) (own : Finset I) (Δ : ℕ)
    (hg : 0 < (g:ℝ)) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hP : 0 < (P:ℝ)) (hP1 : (P:ℝ) ≤ 1/2)
    (hd : ∀ i, 0 ≤ d i) (htotal : 1 ≤ ∑ _i : I, (g:ℝ))
    (hown : ∀ i ∈ own, d i=0) (howncard : own.card ≤ Δ) :
    let N := rationalRadius g P d
    let q := sourceMarginals g P d own Δ
    0 ≤ N ∧ (∀ i, 0 ≤ q i) ∧ (∀ i, q i ≤ 1) ∧
      (∑ i, g*q i=1) ∧ (∑ i, q i=Δ) ∧ (∀ i ∈ own, q i=1) ∧
      (∀ i, q i < 1 → N*(1-P*q i) ≤ d i) ∧
      (∀ i, 0 < q i → d i ≤ N*(1-P*q i)) ∧
      (∀ R : ℝ, 0 < R → 1 ≤ mass g P (fun i => (d i:ℝ)) (1/R) → (N:ℝ) ≤ R) := by
  by_cases hc : 1 ≤ rationalColocatedMass g d
  · have hcR : 1 ≤ colocatedMass g (fun i => (d i:ℝ)) := by
      rw [← cast_rationalColocatedMass]
      exact_mod_cast hc
    obtain ⟨hq0,hq1,hs,hn,ho,hz⟩ := zero_data g d own Δ hg hunit hcR hown howncard
    dsimp only
    simp only [rationalRadius,sourceMarginals,ite_eq_left hc]
    refine ⟨le_refl _,hq0,hq1,hs,hn,ho,?_,?_,?_⟩
    · intro i _; simpa only [zero_mul] using hd i
    · intro i hi; simp only [hz i hi,zero_mul,le_refl]
    · intro R hR _; simpa only [Rat.cast_zero] using hR.le
  · have hcR : colocatedMass g (fun i => (d i:ℝ)) < 1 := by
      rw [← cast_rationalColocatedMass]
      exact_mod_cast (lt_of_not_ge hc)
    obtain ⟨hN,hq0,hq1,hs,hn,ho,hl,hu,hr⟩ := positive_data g P d Δ hg hunit hP hP1 hd htotal hcR
    dsimp only
    simp only [rationalRadius,sourceMarginals,ite_eq_right hc]
    exact ⟨hN.le,hq0,hq1,hs,hn,fun i hi => ho i (hown i hi),hl,hu,hr⟩

end MetricKMedian.Taper
end
end

end OAI
