import Mathlib
import OAI.Probability.BinarySweep.GridBounds.DenseAssembly
import OAI.Probability.BinarySweep.FiniteLaws.SoutheastDimension

namespace OAI

noncomputable section
open scoped BigOperators Classical
open Filter

namespace BinaryCoordinateSweeps
open Young Irrep Representation GridSplit Signed

lemma diagramF_nonneg (μ : YoungDiagram) : 0≤diagramF μ := by
  apply Real.log_nonneg
  have hpos := irreducible_finrank_pos (hilbertSpecht μ)
  rw [hilbertSpecht_finrank] at hpos
  exact_mod_cast Nat.one_le_of_lt hpos

theorem dense_induction_step_eventually (q : ℕ) (hq : 2≤q) : ∀ᶠ s : ℕ in atTop,
    ∀ m n h r : ℕ, ∀ bits : Fin (m+n) → ℕ, ∀ H : PathFamily bits h,
    gridSize bits=s →
    1≤Real.log (gridSize (leftBits bits)) → 1≤Real.log (gridSize (rightBits bits)) →
    Real.log (gridSize (leftBits bits))≤(4/5:ℝ)*Real.log s →
    Real.log (gridSize (rightBits bits))≤(4/5:ℝ)*Real.log s →
    (∀j, bits j≤2*r) → Real.log 4*(m+n)≤(1/1000:ℝ)*Real.log s →
    ∀ μ : YoungDiagram, ∀ e : Cell μ ≃ FreeSlot H 0,
    (s:ℝ)^(399/400:ℝ)≤diagramF μ → ∀z : ℝ,
    0≤z → z≤linePerturbationRadius r →
    EnumeratedMomentBound q (leftBits bits) z → EnumeratedMomentBound q (rightBits bits) z →
    evenMoment q (groupAverage ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
      (fun a => (conditionalGroupLaw H z a:ℂ)))≤
      Real.exp (-cExponent s*diagramF μ+eExponent s*h*Real.log s-pathCost H) := by
  filter_upwards [dense_branch_operator_eventually q hq,
    dense_induction_absorption_eventually (Real.log 2+1),eventually_ge_atTop (1:ℕ)] with s hop hab hs
  intro m n h r bits H hsize hu hv hub hvb hd haxes μ e hF z hz hzr hR hC
  have hs0 : 0<s := by omega
  have hs1 : (1:ℝ)≤ s := by exact_mod_cast hs
  let p := ⌊(s:ℝ)^(1/100:ℝ)⌋₊
  have hp : 0<p := Nat.floor_pos.mpr (Real.one_le_rpow hs1 (by norm_num))
  have hps : (p:ℝ)≤(s:ℝ)^(1/100:ℝ) := Nat.floor_le (by positivity)
  have hM : Fintype.card (Cell μ)≤ s := by
    rw [Fintype.card_congr e,card_freeSlot,hsize]
    omega
  have hdim := hook_log_dimension_upper μ p s hs0 hM
  have hc := hab (m+n) h (Fintype.card (Cell (southeast μ p)))
    (diagramF μ) (diagramF (hookPart μ p)) (diagramF (southeast μ p))
    (by positivity) (by positivity) (diagramF_nonneg _) haxes hdim hF
    (southeast_dense_saving μ s hs0 hM)
  have hm := hop m n h r bits H hsize hu hv hub hvb hd p hp hps μ e z hz hzr hR hC
  refine hm.trans (Real.exp_le_exp.mpr ?_)
  have he := sub_le_sub_right hc (pathCost H)
  convert he using 1; ring

end BinaryCoordinateSweeps

end

end OAI
