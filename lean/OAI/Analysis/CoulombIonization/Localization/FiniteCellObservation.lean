import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.ArbitraryCutExcess

namespace OAI

open MeasureTheory Set Metric
noncomputable section
namespace CoulombAtom
namespace CoreObservationEnsemble

 def observeCell (E : CoreObservationEnsemble) (y : Space) : CoreObservationEnsemble :=
    if h : y = 0 then E else
      E.observe (coreFirstRadialCut y (localCellRadius_pos h).le (localCellRadius_pos h))
        (coreFirstRadialCut_partition y (localCellRadius_pos h).le (localCellRadius_pos h))

 def observeCells (E : CoreObservationEnsemble) : List Space → CoreObservationEnsemble
    | [] => E
    | y::ys => (E.observeCell y).observeCells ys

 lemma observeCell_mass (E : CoreObservationEnsemble) (y : Space) :
    (E.observeCell y).mass = E.mass := by
  classical
  unfold observeCell
  split_ifs <;> simp only [observe_mass]

 lemma observeCell_countMoment (E : CoreObservationEnsemble) (y z : Space) (R : ℝ) :
    (E.observeCell y).countMoment z R ≤ E.countMoment z R := by
  classical
  unfold observeCell
  split_ifs
  · exact le_rfl
  · exact observe_countMoment ..

 lemma observeCells_mass (E : CoreObservationEnsemble) (ys : List Space) :
    (E.observeCells ys).mass = E.mass := by
  induction ys generalizing E with
  | nil => rfl
  | cons y ys ih => rw [observeCells,ih,observeCell_mass]

 lemma observeCells_countMoment (E : CoreObservationEnsemble) (ys : List Space)
    (z : Space) (R : ℝ) :
    (E.observeCells ys).countMoment z R ≤ E.countMoment z R := by
  induction ys generalizing E with
  | nil => exact le_rfl
  | cons y ys ih => exact (ih _).trans (observeCell_countMoment ..)

 theorem observeCells_excess (E : CoreObservationEnsemble) (ys : List Space)
    {Z lam C H : ℝ} (hmass : E.mass = 1) (hZ : 0 ≤ Z) (hlam : 0 < lam)
    (hC : 1 ≤ C) (hH : 0 ≤ H)
    (hb : ∀ y ∈ ys, y ≠ 0 ∧ ∃ m : ℝ, 1 ≤ m ∧ 1/(localCellRadius y)^3 ≤ m ∧
      E.countMoment y (16*localCellRadius y) ≤ C*m^2 ∧ m^2/localCellRadius y ≤ H) :
    max ((E.observeCells ys).excess Z lam) 0+H ≤
      (radialCutExcessConstant C+1)^ys.length*(max (E.excess Z lam) 0+H) := by
  classical
  induction ys generalizing E with
  | nil => simpa only [observeCells,List.length_nil,pow_zero,one_mul] using (le_refl (max (E.excess Z lam) 0+H))
  | cons y ys ih =>
    obtain ⟨hy,m,hm,h3,hB,hmH⟩ := hb y (List.mem_cons_self ..)
    have ha := localCellRadius_pos hy
    have hf := E.observe_excess_linear y ha ha.le (by linarith)
      (by unfold localCellRadius; nlinarith [norm_nonneg y]) hmass hZ hlam hm h3 hC hB
    have hp : max ((E.observeCell y).excess Z lam) 0 ≤
        radialCutExcessConstant C*(max (E.excess Z lam) 0+H) := by
      rw [observeCell, dite_eq_right hy]
      apply max_le
      · exact (le_max_left _ _).trans (hf.trans
          (mul_le_mul_of_nonneg_left (add_le_add le_rfl hmH)
            (zero_le_one.trans (radialCutExcessConstant_one_le hC))))
      · exact mul_nonneg (zero_le_one.trans (radialCutExcessConstant_one_le hC))
          (add_nonneg (le_max_right _ _) hH)
    have hb' : ∀ z ∈ ys, z ≠ 0 ∧ ∃ m : ℝ, 1 ≤ m ∧ 1/(localCellRadius z)^3 ≤ m ∧
        (E.observeCell y).countMoment z (16*localCellRadius z) ≤ C*m^2 ∧
          m^2/localCellRadius z ≤ H := by
      intro z hz
      obtain ⟨hz0,m,hm,h3,hB,hH⟩ := hb z (List.mem_cons_of_mem y hz)
      exact ⟨hz0,m,hm,h3,(observeCell_countMoment ..).trans hB,hH⟩
    have h0 : 0 ≤ max (E.excess Z lam) 0 := le_max_right _ _
    have hK : 0 ≤ radialCutExcessConstant C+1 := by
      have := radialCutExcessConstant_one_le hC; linarith
    have hh : max ((E.observeCell y).excess Z lam) 0+H ≤
        (radialCutExcessConstant C+1)*(max (E.excess Z lam) 0+H) := by
      nlinarith only [hp,h0]
    calc
      _ ≤ (radialCutExcessConstant C+1)^ys.length*
            (max ((E.observeCell y).excess Z lam) 0+H) :=
          ih _ ((observeCell_mass E y).trans hmass) hb'
      _ ≤ (radialCutExcessConstant C+1)^ys.length*
            ((radialCutExcessConstant C+1)*(max (E.excess Z lam) 0+H)) :=
          mul_le_mul_of_nonneg_left hh (pow_nonneg hK _)
      _ = _ := by simp only [List.length_cons,pow_succ]; ring

end CoreObservationEnsemble
end CoulombAtom

end

end OAI
