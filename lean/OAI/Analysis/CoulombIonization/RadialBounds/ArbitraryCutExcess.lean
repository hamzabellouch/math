import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.LocalFieldScalarBoundBarrier

namespace OAI

open MeasureTheory Set Metric
noncomputable section
namespace CoulombAtom

 def radialCutExcessConstant (C : ℝ) : ℝ :=
    1+localizationIMSConstant*C+radialOutLinearConstant C+C

 lemma radialCutExcessConstant_one_le {C : ℝ} (hC : 1 ≤ C) :
    1 ≤ radialCutExcessConstant C := by
  have hI := localizationIMSConstant_nonneg
  have hL := radialOutLinearConstant_one_le hC
  unfold radialCutExcessConstant
  have : 0 ≤ localizationIMSConstant*C := mul_nonneg hI (zero_le_one.trans hC)
  linarith

 lemma sqrt_product_weighted_young {a O B : ℝ} (ha : 0 < a)
    (hO : 0 ≤ O) (hB : 0 ≤ B) :
    Real.sqrt O*Real.sqrt B ≤ (a*O+B/a)/2 := by
  have hh := sq_nonneg (a*Real.sqrt O-Real.sqrt B)
  have hOs := Real.sq_sqrt hO
  have hBs := Real.sq_sqrt hB
  have hn : 2*a*(Real.sqrt O*Real.sqrt B) ≤ a^2*O+B := by nlinarith
  apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).2
  apply (mul_le_mul_iff_left₀ ha).mp
  calc (Real.sqrt O*Real.sqrt B*2)*a ≤ a^2*O+B := by nlinarith only [hn]
       _ = (a*O+B/a)*a := by field_simp

namespace CoreObservationEnsemble

 theorem observe_excess_linear (E : CoreObservationEnsemble) (y : Space)
    {a r Z lam m C : ℝ} (ha : 0 < a) (hr : 0 ≤ r) (hra : r ≤ 6*a)
    (hsep : 20*a ≤ ‖y‖) (hmass : E.mass = 1) (hZ : 0 ≤ Z) (hlam : 0 < lam)
    (hm : 1 ≤ m) (h3 : 1/a^3 ≤ m) (hC : 1 ≤ C)
    (hBC : E.countMoment y (16*a) ≤ C*m^2) :
    max ((E.observe (coreFirstRadialCut y hr ha)
      (coreFirstRadialCut_partition y hr ha)).excess Z lam) 0 ≤
      radialCutExcessConstant C*(max (E.excess Z lam) 0+m^2/a) := by
  let D := max (E.excess Z lam) 0
  let B := E.countMoment y (16*a)
  let O := E.outMoment y hr ha Z lam
  let L := radialOutLinearConstant C
  let T := m^2/a
  have hD : 0 ≤ D := le_max_right _ _
  have hB : 0 ≤ B := E.countMoment_nonneg _ _
  have hO : 0 ≤ O := E.outMoment_nonneg ..
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hL : 1 ≤ L := radialOutLinearConstant_one_le hC
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hroot : Real.sqrt B ≤ C*m := by
    simpa using sqrt_count_scale hB hC (by norm_num : (0:ℝ) ≤ 1)
      (zero_le_one.trans hm) (by simpa using hBC)
  have hout : O ≤ L*(D/a+(m/a)^2) :=
    (E.thin_out_bound y ha hr hra ha le_rfl hsep hmass hZ hlam).trans
      (thinOutMajorant_linear_bound ha hm h3 hD hB hC hBC)
  have hyoung := sqrt_product_weighted_young ha hO hB
  have hmul := mul_le_mul_of_nonneg_left hout ha.le
  have hmul' : a*O ≤ L*(D+T) := by
    calc a*O ≤ a*(L*(D/a+(m/a)^2)) := hmul
         _ = L*(D+T) := by dsimp [T]; field_simp
  have hbdiv : B/a ≤ C*T := by
    calc B/a ≤ (C*m^2)/a := div_le_div_of_nonneg_right hBC ha.le
         _ = C*T := by dsimp [T]; ring
  have hma : m/a^2 ≤ T := by
    have hh := mul_le_mul_of_nonneg_left (cell_reciprocal_bounds ha hm h3).1
      (show 0 ≤ m/a by positivity)
    calc m/a^2 = (m/a)*(1/a) := by ring
         _ ≤ (m/a)*m := hh
         _ = T := by dsimp [T]; ring
  have hI := localizationIMSConstant_nonneg
  have hims : (localizationIMSConstant/a^2)*Real.sqrt B ≤
      localizationIMSConstant*C*T := by
    calc _ ≤ (localizationIMSConstant/a^2)*(C*m) :=
                mul_le_mul_of_nonneg_left hroot (by positivity)
         _ = localizationIMSConstant*C*(m/a^2) := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_left hma (by positivity)
  have hbudget := E.observe_excess_budget y hr ha (by linarith)
    (R := 16*a) (by linarith) hZ hlam.le
  rw [hmass,Real.sqrt_one,mul_one] at hbudget
  have heq : (3/2:ℝ)*(Real.pi*smoothTransitionBound/a)^2 =
      localizationIMSConstant/a^2 := by unfold localizationIMSConstant; ring
  rw [heq] at hbudget
  have hcost : Real.sqrt O*Real.sqrt B ≤ L*(D+T)+C*T := by
    have hp : 0 ≤ L*(D+T)+C*T := by positivity
    linarith only [hyoung,hmul',hbdiv,hp]
  have hpos : 0 ≤ radialCutExcessConstant C*(D+T) :=
    mul_nonneg (zero_le_one.trans (radialCutExcessConstant_one_le hC)) (by positivity)
  apply max_le _ hpos
  have hiD : 0 ≤ localizationIMSConstant*C*D := by positivity
  have hcD : 0 ≤ C*D := by positivity
  have heD : E.excess Z lam ≤ D := le_max_left _ _
  change _ ≤ radialCutExcessConstant C*(D+T)
  unfold radialCutExcessConstant
  dsimp only [L] at hcost
  have hbudget' : (E.observe (coreFirstRadialCut y hr ha)
      (coreFirstRadialCut_partition y hr ha)).excess Z lam ≤
      E.excess Z lam+(localizationIMSConstant/a^2)*Real.sqrt B+
        Real.sqrt O*Real.sqrt B := hbudget
  nlinarith only [hbudget',hims,hcost,heD,hiD,hcD,hT]

end CoreObservationEnsemble
end CoulombAtom

end

end OAI
