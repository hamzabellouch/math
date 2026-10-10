import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.AnnularCellGeometryBarrier
import OAI.Analysis.CoulombIonization.Localization.FiniteCellObservation

namespace OAI

open MeasureTheory Set Metric
noncomputable section
namespace CoulombAtom

 lemma localOffsetMass_annular_bound_norm {alpha beta u D : ℝ}
    (ha : 0 < alpha) (hu : 0 < u) (hD : 0 ≤ D) {y : Space}
    (hya : alpha*u ≤ ‖y‖) (hyb : ‖y‖ ≤ beta*u) :
    localOffsetMass D y ≤ annularCellScaleConstant alpha beta*annularOffsetMass D u := by
  have hn : ‖u⁻¹ • y‖ = ‖y‖/u := by
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hu.le)]; ring
  have hy1 : alpha ≤ ‖u⁻¹ • y‖ := by rw [hn]; exact (le_div_iff₀ hu).2 hya
  have hy2 : ‖u⁻¹ • y‖ ≤ beta := by rw [hn]; exact (div_le_iff₀ hu).2 hyb
  simpa only [smul_smul,mul_inv_cancel₀ hu.ne',one_smul] using
    localOffsetMass_annular_bound ha hu hD hy1 hy2

 def annularCellCostConstant (alpha beta : ℝ) : ℝ :=
    (annularCellScaleConstant alpha beta)^2*100000/alpha

 lemma annularCellCostConstant_pos {alpha beta : ℝ} (ha : 0 < alpha) :
    0 < annularCellCostConstant alpha beta := by
  have := annularCellScaleConstant_one_le alpha beta
  unfold annularCellCostConstant
  positivity

 lemma localOffsetMass_annular_cost {alpha beta u D : ℝ}
    (ha : 0 < alpha) (hu : 0 < u) (hD : 0 ≤ D) {y : Space}
    (hya : alpha*u ≤ ‖y‖) (hyb : ‖y‖ ≤ beta*u) :
    (localOffsetMass D y)^2/localCellRadius y ≤
      annularCellCostConstant alpha beta*(annularOffsetMass D u)^2/u := by
  have hyp : 0 < ‖y‖ := (mul_pos ha hu).trans_le hya
  have hr : 0 < localCellRadius y := localCellRadius_pos (norm_pos_iff.mp hyp)
  have hrad : alpha*u/100000 ≤ localCellRadius y := by
    unfold localCellRadius
    linarith
  have hn := localOffsetMass_annular_bound_norm ha hu hD hya hyb
  calc
    _ ≤ (annularCellScaleConstant alpha beta*annularOffsetMass D u)^2/localCellRadius y :=
      div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (zero_le_one.trans (localOffsetMass_one_le D y)) hn 2) hr.le
    _ ≤ (annularCellScaleConstant alpha beta*annularOffsetMass D u)^2/(alpha*u/100000) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hrad
    _ = _ := by unfold annularCellCostConstant; field_simp

 theorem actual_finite_annular_cut_excess {N : ℕ} {psi : FormVector N}
    (hpsi : SobolevFermion psi) (hm : formMass psi = 1) {Z lam alpha beta u D : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 < lam) (ha : 0 < alpha) (hu : 0 < u) (hD : 0 ≤ D)
    (he : max (corePriceExcess Z lam psi) 0 ≤ D) (ys : List Space)
    (hys : ∀ y ∈ ys, alpha*u ≤ ‖y‖ ∧ ‖y‖ ≤ beta*u) :
    max (((CoreObservationEnsemble.initial psi hpsi).observeCells ys).excess Z lam) 0 ≤
      (radialCutExcessConstant actualCellMomentConstant+1)^ys.length*
        (D+annularCellCostConstant alpha beta*(annularOffsetMass D u)^2/u) := by
  let E := CoreObservationEnsemble.initial psi hpsi
  let H := annularCellCostConstant alpha beta*(annularOffsetMass D u)^2/u
  have hH : 0 ≤ H := by
    have := annularCellCostConstant_pos (beta := beta) ha
    dsimp [H]; positivity
  have hb (y : Space) (hy : y ∈ ys) : y ≠ 0 ∧ ∃ m : ℝ, 1 ≤ m ∧
      1/(localCellRadius y)^3 ≤ m ∧
      E.countMoment y (16*localCellRadius y) ≤ actualCellMomentConstant*m^2 ∧
      m^2/localCellRadius y ≤ H := by
    obtain ⟨hya,hyb⟩ := hys y hy
    have hy0 : y ≠ 0 := norm_pos_iff.mp ((mul_pos ha hu).trans_le hya)
    have hr := localCellRadius_pos hy0
    refine ⟨hy0,localOffsetMass D y,localOffsetMass_one_le D y,
      localOffsetMass_cube_le D y,?_,localOffsetMass_annular_cost ha hu hD hya hyb⟩
    have hcount := priced_enlarged_cell_count hpsi hm hZ hlam hy0
    have hmon := E.countMoment_le_of_radius y y
      (show ‖y-y‖+16*localCellRadius y ≤ 32*localCellRadius y by simp only [sub_self,norm_zero]; linarith)
    calc
      _ ≤ E.countMoment y (32*localCellRadius y) := hmon
      _ = rawCountMoment psi y (32*localCellRadius y) := CoreObservationEnsemble.initial_countMoment ..
      _ ≤ actualCellMomentConstant*(localOffsetMass (max (corePriceExcess Z lam psi) 0) y)^2 := hcount
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (zero_le_one.trans (localOffsetMass_one_le _ _))
          (localOffsetMass_mono he y) 2) (zero_le_one.trans actualCellMomentConstant_one_le)
  have hh := E.observeCells_excess ys ((CoreObservationEnsemble.initial_mass ..).trans hm)
    hZ hlam actualCellMomentConstant_one_le hH hb
  have hK : 0 ≤ radialCutExcessConstant actualCellMomentConstant+1 := by
    have := radialCutExcessConstant_one_le actualCellMomentConstant_one_le; linarith
  have hex : max (E.excess Z lam) 0 ≤ D := by
    simpa only [E,CoreObservationEnsemble.initial_excess] using he
  exact (le_add_of_nonneg_right hH).trans (hh.trans
    (mul_le_mul_of_nonneg_left (add_le_add hex le_rfl) (pow_nonneg hK _)))

end CoulombAtom

end

end OAI
