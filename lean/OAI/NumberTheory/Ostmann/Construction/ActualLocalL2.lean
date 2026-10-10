import OAI.NumberTheory.Ostmann.Construction.FavorableGiant

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction
open scoped BigOperators

lemma residueTest_sq_sum (d : Decomposition) {p : ℕ} [NeZero p] (hp : p.Prime) :
    (∑x:ZMod p,‖residueTest d p x‖^2)=(p:ℝ) := by
  have hlo : 0<Supply.density (d.residueSupport p) := by
    simpa only [Supply.density,Decomposition.residueDensity,ZMod.card] using d.residueDensity_pos p hp
  have hhi : Supply.density (d.residueSupport p)<1 := by
    simpa only [Supply.density,Decomposition.residueDensity,ZMod.card] using d.residueDensity_lt_one p hp
  simp only [residueTest_eq,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  simpa only [ZMod.card] using Supply.sum_normalizedIndicator_sq (d.residueSupport p) hlo hhi

lemma favorableGiantResidueTest_sq_sum_le (d : Decomposition) (P : Finset ℕ)
    (p : ℕ) [NeZero p] : (∑x:ZMod p,‖favorableGiantResidueTest d P p x‖^2)≤(p:ℝ) := by
  by_cases hP : p∈P
  · simp only [favorableGiantResidueTest,hP,ite_true,giantResidueTest_eq]
    exact giantTest_sum_sq_le _
  · simp only [favorableGiantResidueTest,hP,ite_false,norm_zero,zero_pow (by decide : 2≠0),Finset.sum_const_zero]
    exact Nat.cast_nonneg _

lemma favorableGiantResidueTest_sum_zero (d : Decomposition) (P : Finset ℕ)
    (p : ℕ) [NeZero p] : (∑x:ZMod p,favorableGiantResidueTest d P p x)=0 := by
  by_cases hP : p∈P
  · simp only [favorableGiantResidueTest,hP,ite_true,giantResidueTest_eq]
    exact giantTest_sum_zero _
  · simp only [favorableGiantResidueTest,hP,ite_false,Finset.sum_const_zero]

end Ostmann.Construction

end

end OAI
