import OAI.NumberTheory.Ostmann.Characters.HigherBiasValue
import OAI.NumberTheory.Ostmann.Characters.RichShellSelectionMass

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters
open Construction Filter
open scoped BigOperators

def higherBiasedSubset (d : Decomposition) (P : Finset ℕ) (δ : ℝ) : Finset ℕ := by
  classical
  exact P.filter (fun p=>δ ≤ higherPrimeBias d p)

lemma higherPrimeBias_threshold_sum_le (d : Decomposition) (P : Finset ℕ) (δ : ℝ)
    (hδ : 0 ≤ δ) :
    (∑ p∈P,higherPrimeBias d p/p) ≤
      δ*harmonicPrimeMass P+harmonicPrimeMass (higherBiasedSubset d P δ) := by
  classical
  unfold harmonicPrimeMass higherBiasedSubset
  rw [Finset.sum_filter,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p hp
  have hp0 : (0:ℝ)≤p := Nat.cast_nonneg _
  by_cases hb : δ ≤ higherPrimeBias d p
  · rw [ite_eq_left hb]
    have hh := div_le_div_of_nonneg_right (higherPrimeBias_le_one d p) hp0
    have hd : 0 ≤ δ*((1:ℝ)/p) := mul_nonneg hδ (by positivity)
    linarith
  · rw [ite_eq_right hb,add_zero]
    have hh := div_le_div_of_nonneg_right (le_of_not_ge hb) hp0
    simpa only [mul_one_div] using hh

theorem eventually_closed_prime_harmonic_mass_le {α β : ℝ}
    (hα : 0 < α) (hαβ : α < β) :
    ∀ᶠ L : ℝ in atTop,∀ P : Finset ℕ,
      (∀ p∈P,p.Prime ∧ α*L ≤ Real.log (Real.log p) ∧ Real.log (Real.log p) ≤ β*L) →
      harmonicPrimeMass P ≤ (β+1)*L := by
  obtain ⟨C,hC,hbound⟩ := harmonicIntervalMass_mertens
  filter_upwards [eventually_ge_atTop C,eventually_gt_atTop (0:ℝ)] with L hCL hL
  intro P hP
  have hb : 0 ≤ β*L := mul_nonneg (hα.trans hαβ).le hL.le
  have he : harmonicIntervalMass P 0 (β*L)=harmonicPrimeMass P :=
    harmonicIntervalMass_eq_of_support P 0 (β*L)
      (fun p hp=>⟨(mul_pos hα hL).trans_le (hP p hp).2.1,(hP p hp).2.2⟩)
  have hh := hbound P (fun p hp=>(hP p hp).1) 0 (β*L) le_rfl hb
  rw [he] at hh
  linarith

theorem exists_higher_harmonic_threshold (d : Decomposition) {α β : ℝ}
    (hα : 0 < α) (hαβ : α < β) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ,0 < δ ∧ δ ≤ 1 ∧ ∀ᶠ L : ℝ in atTop,∀ P : Finset ℕ,
      (∀ p∈P,p.Prime ∧ α*L ≤ Real.log (Real.log p) ∧ Real.log (Real.log p) ≤ β*L) →
      ε*L ≤ (∑ p∈P,higherPrimeBias d p/p) →
      (ε/2)*L ≤ harmonicPrimeMass (higherBiasedSubset d P δ) ∧
      (∀ p∈higherBiasedSubset d P δ,
        p∈P ∧ p.Prime ∧ α*L ≤ Real.log (Real.log p) ∧
        Real.log (Real.log p) ≤ β*L ∧ δ ≤ higherPrimeBias d p) := by
  classical
  let δ : ℝ := min (ε/(4*(β+1))) (1/2)
  have hβ : 0 < β+1 := by linarith
  have hδ : 0 < δ := lt_min (div_pos hε (by positivity)) (by norm_num)
  have hδ1 : δ ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hδsmall : δ*(β+1) ≤ ε/4 := by
    have hh := mul_le_mul_of_nonneg_right (min_le_left (ε/(4*(β+1))) (1/2)) hβ.le
    have he : ε/(4*(β+1))*(β+1)=ε/4 := by field_simp
    exact hh.trans_eq he
  refine ⟨δ,hδ,hδ1,?_⟩
  filter_upwards [eventually_closed_prime_harmonic_mass_le hα hαβ,
    eventually_ge_atTop (0:ℝ)] with L hmass hL
  intro P hP hsum
  have hbound := higherPrimeBias_threshold_sum_le d P δ hδ.le
  have hm := mul_le_mul_of_nonneg_left (hmass P hP) hδ.le
  have hs := mul_le_mul_of_nonneg_right hδsmall hL
  constructor
  · nlinarith
  · intro p hp
    obtain ⟨hp,hbias⟩ := Finset.mem_filter.mp hp
    exact ⟨hp,(hP p hp).1,(hP p hp).2.1,(hP p hp).2.2,hbias⟩

end Ostmann.Characters

end

end OAI
