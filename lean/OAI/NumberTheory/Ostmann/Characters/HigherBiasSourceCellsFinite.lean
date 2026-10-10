import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceCellsMass

namespace OAI

noncomputable section
namespace Ostmann.Characters.HigherBiasSource
open scoped BigOperators

theorem good_cells_mass_lower {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (m y : ι → ℝ) (valid : ι → Prop) [DecidablePred valid]
    (a θ t : ℝ) (hθ : 0 ≤ θ) (ht : 0 ≤ t)
    (hm : ∀ i∈S,0 ≤ m i) (hy : ∀ i∈S,y i ≤ m i)
    (hmean : a*(∑ i∈S,m i) ≤ ∑ i∈S,y i) :
    (a-θ)*(∑ i∈S,m i) - (∑ i∈S.filter (fun i => ¬valid i),m i) - S.card*t ≤
      ∑ i∈S.filter (fun i => valid i ∧ θ*m i ≤ y i ∧ t ≤ m i),m i := by
  classical
  have hp (i : ι) (hi : i∈S) :
      y i ≤ θ*m i + (if valid i ∧ θ*m i ≤ y i ∧ t ≤ m i then m i else 0) +
        (if ¬valid i then m i else 0) + t := by
    have htm := mul_nonneg hθ (hm i hi)
    by_cases hv : valid i
    · simp only [hv,not_true_eq_false,ite_false,true_and]
      by_cases hg : θ*m i ≤ y i ∧ t ≤ m i
      · simp only [hg,and_self,ite_true]
        linarith [hy i hi]
      · simp only [hg,ite_false]
        rcases not_and_or.mp hg with hn | hn
        · linarith
        · linarith [hy i hi]
    · simp only [hv,false_and,ite_false,not_false_eq_true,ite_true]
      linarith [hy i hi]
  have hsum := Finset.sum_le_sum hp
  simp only [Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,nsmul_eq_mul,
    ←Finset.sum_filter] at hsum
  linarith

theorem card_lower_of_cell_mass {ι : Type*} (S : Finset ι) (m : ι → ℝ)
    (b C q : ℝ) (hb : 0<b) (hC : 0<C)
    (hm : ∀ i∈S,m i ≤ C/b) (hs : q ≤ ∑ i∈S,m i) :
    (q/C)*b ≤ (S.card:ℝ) := by
  have hsum : (∑ i∈S,m i) ≤ (S.card:ℝ)*(C/b) := by
    simpa only [Finset.sum_const,nsmul_eq_mul] using Finset.sum_le_sum hm
  have hh := (le_div_iff₀ hb).mp (show q ≤ (S.card:ℝ)*C/b by simpa only [mul_div_assoc] using hs.trans hsum)
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hC).mpr
  nlinarith

end Ostmann.Characters.HigherBiasSource

end

end OAI
