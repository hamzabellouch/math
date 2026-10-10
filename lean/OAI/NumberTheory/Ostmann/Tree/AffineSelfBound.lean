import OAI.NumberTheory.Ostmann.Tree.UnitSums
import OAI.NumberTheory.Ostmann.Tree.WeightedAffineBound

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [Fact p.Prime]

theorem weightedAffine_add_const (w : (ZMod p)ˣ → ℂ) (f : ZMod p → ℂ) (c : ℂ) :
    weightedAffine w (fun t => f t+c) =
      fun t => weightedAffine w f t + c*((p:ℂ)⁻¹ * ∑ r, w r) := by
  funext t
  simp only [weightedAffine, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
  ring

theorem weightedAffine_self_bound (g : ZMod p → ℂ) (hg0 : g 0=0) (hg : l2Sq g ≤ 1) :
    l2Sq (weightedAffine (fun r => conj (g r)) g) ≤
      ‖mean g‖^4 + Real.sqrt (3/(p:ℝ)) := by
  have hp : 0 < (p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  let f : ZMod p → ℂ := fun t => g t-mean g
  let w : (ZMod p)ˣ → ℂ := fun r => conj (g r)
  have hf : mean f=0 := mean_sub_mean g
  have he : (fun t => f t+mean g) = g := by funext t; dsimp [f]; ring
  have hsplit : l2Sq g=l2Sq f+‖mean g‖^2 := by
    simpa only [he] using l2Sq_add_const f (mean g) hf
  have hfn : l2Sq f ≤ 1 := by nlinarith [sq_nonneg ‖mean g‖]
  have hsum : (∑ t : ZMod p, ‖g t‖^2) ≤ (p:ℝ) := by
    have hh : (∑ t : ZMod p, ‖g t‖^2)/(p:ℝ) ≤ 1 := by
      simpa only [l2Sq, div_eq_mul_inv, mul_comm] using hg
    simpa only [one_mul] using (div_le_iff₀ hp).mp hh
  have hw : ∑ r : (ZMod p)ˣ, ‖w r‖^2 ≤ (p:ℝ) := by
    dsimp [w]
    simp only [Complex.norm_conj]
    rw [sum_units_of_zero (fun t => ‖g t‖^2) (by simp [hg0])]
    exact hsum
  have hwm : (p:ℂ)⁻¹*∑ r : (ZMod p)ˣ, w r = conj (mean g) := by
    dsimp [w]
    rw [sum_units_of_zero (fun t => conj (g t)) (by simp [hg0])]
    exact mean_conj g
  have hTf : mean (weightedAffine w f)=0 := by rw [weightedAffine_mean, hf, mul_zero]
  have hbound := weightedAffine_meanzero_bound w f hw hf hfn
  have hdecomp : weightedAffine w g =
      fun t => weightedAffine w f t + mean g*conj (mean g) := by
    calc
      weightedAffine w g = weightedAffine w (fun t => f t+mean g) := congrArg (weightedAffine w) he.symm
      _ = _ := by rw [weightedAffine_add_const, hwm]
  change l2Sq (weightedAffine w g) ≤ _
  rw [hdecomp, l2Sq_add_const _ _ hTf]
  have hn : ‖mean g*conj (mean g)‖^2=‖mean g‖^4 := by
    rw [norm_mul, Complex.norm_conj]
    ring
  rw [hn]
  linarith

end
end Ostmann.FiniteField

end OAI
