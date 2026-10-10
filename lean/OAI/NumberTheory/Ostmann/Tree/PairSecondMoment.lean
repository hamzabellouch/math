import OAI.NumberTheory.Ostmann.Tree.PairEnergy
import OAI.NumberTheory.Ostmann.Tree.PairMellinVariables

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [Fact p.Prime]

def pairSecondMoment (g : ZMod p → ℂ) (σ : (ZMod p)ˣ) (d : ZMod p) : ℝ :=
  (Fintype.card (ZMod p)ˣ:ℝ)⁻¹*∑ t : (ZMod p)ˣ,‖pairTest g σ d t‖^2

theorem pairSecondMoment_nonneg (g : ZMod p → ℂ) (σ : (ZMod p)ˣ) (d : ZMod p) :
    0≤pairSecondMoment g σ d := by unfold pairSecondMoment; positivity

theorem pairTest_zero (g : ZMod p → ℂ) (σ : (ZMod p)ˣ) (hg0 : g 0=0) (t : ZMod p) :
    pairTest g σ 0 t=0 := by simp [pairTest,pairFirst,pairSecond,hg0]

theorem pairSecondMoment_zero (g : ZMod p → ℂ) (σ : (ZMod p)ˣ) (hg0 : g 0=0) :
    pairSecondMoment g σ 0=0 := by simp [pairSecondMoment,pairTest_zero g σ hg0]

theorem pairTest_unit (g : ZMod p → ℂ) (σ d : (ZMod p)ˣ) (t : ZMod p) :
    pairTest g σ d t=bottomPair g (σ*d) t := by
  dsimp [pairTest,pairFirst,pairSecond,bottomPair,pairMobiusValue]

theorem pairSecondMoment_total (g : ZMod p → ℂ) (σ : (ZMod p)ˣ)
    (hg0 : g 0=0) (hg : l2Sq g≤1) :
    (∑ d : ZMod p,pairSecondMoment g σ d) ≤ (p:ℝ)^2/(Fintype.card (ZMod p)ˣ:ℝ) := by
  have hp : 0<(p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have henergy : (∑ x : ZMod p,‖g x‖^2)≤(p:ℝ) := by
    have hh : (∑ x : ZMod p,‖g x‖^2)/(p:ℝ)≤1 := by simpa only [l2Sq,div_eq_mul_inv,mul_comm] using hg
    simpa only [one_mul] using (div_le_iff₀ hp).mp hh
  rw [← sum_units_of_zero (pairSecondMoment g σ) (pairSecondMoment_zero g σ hg0)]
  simp only [pairSecondMoment,pairTest_unit,← Finset.mul_sum]
  have he := (Equiv.mulLeft σ).bijective.sum_comp (fun d : (ZMod p)ˣ => ∑ t : (ZMod p)ˣ,‖bottomPair g d t‖^2)
  change (∑ d : (ZMod p)ˣ,∑ t : (ZMod p)ˣ,‖bottomPair g (σ*d) t‖^2)=
    ∑ d : (ZMod p)ˣ,∑ t : (ZMod p)ˣ,‖bottomPair g d t‖^2 at he
  rw [he]
  calc
    _ ≤ (Fintype.card (ZMod p)ˣ:ℝ)⁻¹*(∑ x : ZMod p,‖g x‖^2)^2 :=
      mul_le_mul_of_nonneg_left (bottomPair_total_energy g hg0) (by positivity)
    _ ≤ (Fintype.card (ZMod p)ˣ:ℝ)⁻¹*(p:ℝ)^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) henergy 2) (by positivity)
    _ = _ := by ring

theorem pairSecondMoment_parameter_average (g : ZMod p → ℂ) (σ k : (ZMod p)ˣ) (d : ZMod p) :
    (Fintype.card (ZMod p)ˣ:ℝ)⁻¹*(∑ lam : (ZMod p)ˣ,‖pairTest g σ d ((lam:ZMod p)*k)‖^2)=
      pairSecondMoment g σ d := by
  unfold pairSecondMoment
  congr 1
  have he := (Equiv.mulRight k).bijective.sum_comp (fun t : (ZMod p)ˣ => ‖pairTest g σ d t‖^2)
  change (∑ t : (ZMod p)ˣ,‖pairTest g σ d (t*k)‖^2)=∑ t : (ZMod p)ˣ,‖pairTest g σ d t‖^2 at he
  simpa only [Units.val_mul] using he

end
end Ostmann.FiniteField

end OAI
