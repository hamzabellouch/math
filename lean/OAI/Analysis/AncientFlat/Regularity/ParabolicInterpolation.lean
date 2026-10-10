import OAI.Analysis.AncientFlat.Regularity.JetSpaceHolder
import OAI.Analysis.AncientFlat.Regularity.JetTimeHolder
import OAI.Analysis.AncientFlat.Geometry.InteriorCore

namespace OAI
noncomputable section
open Set Filter Metric ParabolicInterior
open scoped ContDiff
namespace ParabolicInterpolation
variable {V : Type} {E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma lower_parabolic_bound [FiniteDimensional ℝ V] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (j : ℕ) (hj : j≤3) (u ut : ℝ → V → E)
    (I : Set ℝ) (hI : OrdConnected I) (r R q U M α : ℝ)
    (hq : 0<q) (hq1 : q≤1) (hgap : r+12*q≤R)
    (hU : 0≤U) (hM : 0≤M) (hα : 0≤α) (hα1 : α≤1)
    (hs : ∀ t∈I, ContDiff ℝ 4 (u t))
    (hdt : ∀ t∈I, ∀ x, ‖x‖<R → HasDerivAt (fun t => u t x) (ut t x) t)
    (hUt : ∀ t∈I, ∀ x, ‖x‖<R → ‖ut t x‖≤M)
    (hu : ∀ t∈I, ∀ x, ‖x‖<R → ‖u t x‖≤U)
    (hD : ∀ t∈I, ∀ x, ‖x‖<R → ‖iteratedFDeriv ℝ 4 (u t) x‖≤M) :
    HolderBound α {p : V × ℝ | ‖p.1‖<r ∧ p.2∈I}
      (fun p => iteratedFDeriv ℝ j (u p.2) p.1)
      (110*(U/q^j+q^(4-j)*M)/q^α) := by
  let B := U/q^j+q^(4-j)*M
  have hB : 0≤B := by dsimp [B]; positivity
  have hqa : 0<q^α := Real.rpow_pos_of_pos hq _
  have hqa1 : q^α≤1 := Real.rpow_le_one hq.le hq1 hα
  constructor
  · intro p hp
    have hb := lower_jet_bound j hj (u p.2) (hs _ hp.2) p.1 R q U M hq hU hM (by linarith [hp.1])
      (hu _ hp.2) (hD _ hp.2)
    apply hb.trans
    change 22*B≤110*B/q^α
    apply (le_div_iff₀ hqa).mpr
    calc
      _≤22*B*1 := mul_le_mul_of_nonneg_left hqa1 (by positivity)
      _≤_ := by nlinarith
  · intro p hp z hz
    have hspace := space_lower_holder j hj (u p.2) (hs _ hp.2) p.1 z.1 R q U M α hq hU hM hα hα1
      (by linarith [hp.1]) (by linarith [hz.1]) (hu _ hp.2) (hD _ hp.2)
    have htime := time_lower_holder j hj u ut z.2 p.2 R q U M α hq hU hM hα hα1 (hs _ hz.2) (hs _ hp.2)
      (fun t ht => hdt t (hI.uIcc_subset hz.2 hp.2 ht))
      (fun t ht => hUt t (hI.uIcc_subset hz.2 hp.2 ht))
      (hu _ hz.2) (hu _ hp.2) (hD _ hz.2) (hD _ hp.2) z.1 (by linarith [hz.1])
    have hps : ‖p.1-z.1‖^α≤pdist p z^α := Real.rpow_le_rpow (norm_nonneg _)
      (le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg _) _)) hα
    have hpt : (|p.2-z.2|^((1:ℝ)/4))^α≤pdist p z^α := Real.rpow_le_rpow
      (Real.rpow_nonneg (abs_nonneg _) _) (le_add_of_nonneg_left (norm_nonneg _)) hα
    change _≤110*B/q^α*pdist p z^α
    calc
      _≤‖iteratedFDeriv ℝ j (u p.2) p.1-iteratedFDeriv ℝ j (u p.2) z.1‖+
        ‖iteratedFDeriv ℝ j (u p.2) z.1-iteratedFDeriv ℝ j (u z.2) z.1‖ := norm_sub_le_norm_sub_add_norm_sub ..
      _≤44*B/q^α*‖p.1-z.1‖^α+66*B/q^α*(|p.2-z.2|^((1:ℝ)/4))^α := add_le_add hspace htime
      _≤44*B/q^α*pdist p z^α+66*B/q^α*pdist p z^α := add_le_add
        (mul_le_mul_of_nonneg_left hps (by positivity)) (mul_le_mul_of_nonneg_left hpt (by positivity))
      _=_ := by ring
end ParabolicInterpolation

end

end OAI
