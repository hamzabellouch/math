import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.CellCountSupremumBarrier
import OAI.Analysis.CoulombIonization.FieldAnalysis.ThinFieldConstantsBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.CellScaleBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

namespace CoulombAtom

lemma thinFieldBase_antitone {a A b D B : ℝ} (ha : 0 < a) (haA : a ≤ A)
    (hb : 0 < b) (hD : 0 ≤ D) (hB : 0 ≤ B) :
    thinFieldBase A b D B ≤ thinFieldBase a b D B := by
  have hA := lt_of_lt_of_le ha haA
  have hI := localizationIMSConstant_nonneg
  unfold thinFieldBase localFieldScale
  gcongr

lemma sqrt_count_scale {B C P m : ℝ} (_hB : 0 ≤ B) (hC : 1 ≤ C) (hP : 0 ≤ P)
    (hm : 0 ≤ m) (hh : B ≤ C*P*m^2) : Real.sqrt B ≤ C*Real.sqrt P*m := by
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  have hcc : C ≤ C^2 := by nlinarith
  have hs := Real.sq_sqrt hP
  have he : (C*Real.sqrt P*m)^2 = C^2*P*m^2 := by rw [mul_pow,mul_pow,hs]
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity,hh.trans ?_⟩
  rw [he]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcc hP) (sq_nonneg m)

lemma thinFieldBase_normalized {a m e D B C P : ℝ}
    (ha : 0 < a) (hm : 1 ≤ m) (h3 : 1/a^3 ≤ m) (he : 0 < e)
    (_hD : 0 ≤ D) (hDm : D*a ≤ m^2) (hB : 0 ≤ B) (hC : 1 ≤ C)
    (hP : 1 ≤ P) (hBC : B ≤ C*P*m^2) :
    thinFieldBase a (e*a) D B ≤
      (6+C+localizationIMSConstant*C)*(m/a)^2*(P+1/e^4) := by
  let S := (m/a)^2
  let V := P+1/e^4
  have hm0 : 0 ≤ m := le_trans zero_le_one hm
  have hP0 : 0 ≤ P := le_trans zero_le_one hP
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  have hS : 0 ≤ S := sq_nonneg _
  have hV : 1 ≤ V := by dsimp [V]; have := one_div_nonneg.mpr (by positivity : 0 ≤ e^4); linarith
  have hPV : P ≤ V := by dsimp [V]; have := one_div_nonneg.mpr (by positivity : 0 ≤ e^4); linarith
  have hI := localizationIMSConstant_nonneg
  have hrec := cell_reciprocal_bounds ha hm h3
  have ham := cell_mass_product ha hm h3
  have hma : 0 ≤ m/a := div_nonneg hm0 ha.le
  have h4 : 1/a^4 ≤ m/a := by
    have hh := div_le_div_of_nonneg_right h3 ha.le
    calc _ = (1/a^3)/a := by ring
         _ ≤ m/a := hh
  have h1 : 1/a ≤ m/a := div_le_div_of_nonneg_right hm ha.le
  have hfirst : (1/a^4+1/a)^2 ≤ 4*S := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ 1/a^4+1/a) (add_le_add h4 h1) 2
    dsimp [S]
    nlinarith
  have hsecond : 1/a^4 ≤ S := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ 1/a) hrec.1 2
    have hh := div_le_div_of_nonneg_right h (sq_nonneg a)
    calc _ = (1/a)^2/a^2 := by ring
         _ ≤ m^2/a^2 := hh
         _ = S := by dsimp [S]; ring
  have hthird : D/a ≤ S := by
    have h := div_le_div_of_nonneg_right hDm (sq_nonneg a)
    calc _ = (D*a)/a^2 := by field_simp
         _ ≤ m^2/a^2 := h
         _ = S := by dsimp [S]; ring
  have hfourth : B/a^2 ≤ C*P*S := by
    have h := div_le_div_of_nonneg_right hBC (sq_nonneg a)
    calc _ ≤ (C*P*m^2)/a^2 := h
         _ = C*P*S := by dsimp [S]; ring
  have hsqrt := sqrt_count_scale hB hC hP0 hm0 hBC
  have hroot : Real.sqrt P/e^2 ≤ V := by
    have hs := Real.sq_sqrt hP0
    have hx : (1/e^2)^2 = 1/e^4 := by ring
    have hh := sq_nonneg (Real.sqrt P-1/e^2)
    calc _ = Real.sqrt P*(1/e^2) := by ring
         _ ≤ V := by dsimp [V]; nlinarith
  have hnorm : m/a^3 ≤ S := by
    have hh := mul_le_mul_of_nonneg_right ham (show 0 ≤ m/a^3 by positivity)
    calc _ ≤ (a*m)*(m/a^3) := by simpa using hh
         _ = S := by dsimp [S]; field_simp
  have hims : localizationIMSConstant*Real.sqrt B/((e*a)^2*a) ≤
      localizationIMSConstant*C*V*S := by
    calc _ ≤ localizationIMSConstant*(C*Real.sqrt P*m)/((e*a)^2*a) := by gcongr
         _ = localizationIMSConstant*C*(Real.sqrt P/e^2)*(m/a^3) := by ring
         _ ≤ localizationIMSConstant*C*V*S := by gcongr
  have ht1 := mul_le_mul_of_nonneg_right hV hS
  have ht2 := mul_le_mul_of_nonneg_right hPV (mul_nonneg hC0 hS)
  unfold thinFieldBase localFieldScale
  change (1/a^4+1/a)^2+1/a^4+D/a+B/a^2+_ ≤ (6+C+localizationIMSConstant*C)*S*V
  nlinarith

 def cellFieldNormConstant : ℝ := 1+thinFieldUniversalConstant*
    (6+localCountCoverConstant+localizationIMSConstant*localCountCoverConstant)
lemma cellFieldNormConstant_one_le : 1 ≤ cellFieldNormConstant := by
  have hC := localCountCoverConstant_one_le
  have hI := localizationIMSConstant_nonneg
  have hT := thinFieldUniversalConstant_pos
  unfold cellFieldNormConstant
  have : 0 ≤ thinFieldUniversalConstant*(6+localCountCoverConstant+localizationIMSConstant*localCountCoverConstant) := by positivity
  linarith

lemma cellField_norm_square {a m e D B P : ℝ}
    (ha : 0 < a) (hm : 1 ≤ m) (h3 : 1/a^3 ≤ m) (he : 0 < e)
    (hD : 0 ≤ D) (hDm : D*a ≤ m^2) (hB : 0 ≤ B)
    (hP : 1 ≤ P) (hBC : B ≤ localCountCoverConstant*P*m^2) :
    thinFieldUniversalConstant*thinFieldBase (2*a) (e*a) D B ≤
      (cellFieldNormConstant*(m/a)*(Real.sqrt P+1/e^2))^2 := by
  have hm0 : 0 ≤ m := le_trans zero_le_one hm
  have hP0 : 0 ≤ P := le_trans zero_le_one hP
  have hC := localCountCoverConstant_one_le
  have hI := localizationIMSConstant_nonneg
  have hT := thinFieldUniversalConstant_pos.le
  let K := thinFieldUniversalConstant*(6+localCountCoverConstant+localizationIMSConstant*localCountCoverConstant)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hF : K ≤ cellFieldNormConstant^2 := by change K ≤ (1+K)^2; nlinarith
  have hthin := (thinFieldBase_antitone ha (by linarith : a ≤ 2*a) (mul_pos he ha) hD hB).trans
    (thinFieldBase_normalized ha hm h3 he hD hDm hB hC hP hBC)
  have hV : P+1/e^4 ≤ (Real.sqrt P+1/e^2)^2 := by
    have hs := Real.sq_sqrt hP0
    have hx : (1/e^2)^2 = 1/e^4 := by ring
    have hh : 0 ≤ Real.sqrt P*(1/e^2) := by positivity
    nlinarith
  calc _ ≤ K*(m/a)^2*(P+1/e^4) := by
          have hh := mul_le_mul_of_nonneg_left hthin hT
          calc _ ≤ thinFieldUniversalConstant*
              ((6+localCountCoverConstant+localizationIMSConstant*localCountCoverConstant)*(m/a)^2*(P+1/e^4)) := hh
               _ = K*(m/a)^2*(P+1/e^4) := by dsimp [K]; ring
       _ ≤ cellFieldNormConstant^2*(m/a)^2*(Real.sqrt P+1/e^2)^2 := by gcongr
       _ = _ := by ring

theorem cell_fresh_field_mass {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (hm : formMass ψ = 1) {y : Space} (hy : y ≠ 0)
    {e r Z lam : ℝ} (he : 0 < e) (he1 : e ≤ 1/8)
    (hr : r ∈ Set.Icc (10*localCellRadius y) (12*localCellRadius y))
    (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    let a := localCellRadius y
    let D := max (corePriceExcess Z lam ψ) 0
    let m := localOffsetMass D y
    let P := localCountSupremum ψ D
    ∃ hr0 : 0 ≤ r,
      freshOutMaximumSecondMoment (coreFirstRadialCut y hr0 (mul_pos he (localCellRadius_pos hy)))
        (coreFirstRadialCut_partition y hr0 (mul_pos he (localCellRadius_pos hy))) ψ Z lam ≤
          (cellFieldNormConstant*(m/a)*(Real.sqrt P+1/e^2))^2 ∧
      freshPatchMass (coreFirstRadialCut y hr0 (mul_pos he (localCellRadius_pos hy)))
        (coreFirstRadialCut_partition y hr0 (mul_pos he (localCellRadius_pos hy))) ψ Z lam y (r-4*(e*a)) ≤
          1536*cellFieldNormConstant*m*(Real.sqrt P+1/e^2) := by
  dsimp only
  let a := localCellRadius y
  let D := max (corePriceExcess Z lam ψ) 0
  let m := localOffsetMass D y
  let P := localCountSupremum ψ D
  have ha : 0 < a := localCellRadius_pos hy
  have hr0 : 0 ≤ r := le_trans (by positivity : 0 ≤ 10*a) hr.1
  have hb : 0 < e*a := mul_pos he ha
  have hba : e*a ≤ 2*a := by nlinarith
  have hsep : 20*(2*a) ≤ ‖y‖ := by dsimp [a,localCellRadius]; nlinarith [norm_nonneg y]
  have hrb : 4*(e*a) < r := by nlinarith [hr.1]
  let Q := cellFieldNormConstant*(m/a)*(Real.sqrt P+1/e^2)
  have hQ : 0 ≤ Q := by
    have hF := cellFieldNormConstant_one_le
    have hm1 := localOffsetMass_one_le D y
    dsimp [Q]
    positivity
  have hsq := cellField_norm_square ha (localOffsetMass_one_le D y) (localOffsetMass_cube_le D y) he
    (le_max_right _ _) (localOffsetMass_offset (le_max_right _ _) hy)
    (rawCountMoment_nonneg ψ y (32*a)) (localCountSupremum_one_le ψ D)
    (enlarged_cell_count_le hψ.sobolevVector (le_max_right _ _) hy)
  change thinFieldUniversalConstant*thinFieldBase (2*a) (e*a) D (rawCountMoment ψ y (32*a)) ≤ Q^2 at hsq
  have hscale : 16*(2*a) = 32*a := by ring
  have hh := freshOutMaximum_thin_bound hψ hm y (by positivity : 0 < 2*a) hr0 (by nlinarith [hr.2]) hb hba hsep hZ hlam
  have hh' := freshPatchMass_thin_bound hψ hm y (by positivity : 0 < 2*a) hr0 (by nlinarith [hr.2]) hb hrb hba hsep hZ hlam
  rw [hscale] at hh hh'
  refine ⟨hr0,hh.trans hsq,?_⟩
  have hs : Real.sqrt (thinFieldUniversalConstant*thinFieldBase (2*a) (e*a) D (rawCountMoment ψ y (32*a))) ≤ Q :=
    Real.sqrt_le_iff.mpr ⟨hQ,hsq⟩
  calc _ ≤ 768*(2*a)*Real.sqrt (thinFieldUniversalConstant*thinFieldBase (2*a) (e*a) D (rawCountMoment ψ y (32*a))) := hh'
       _ ≤ 768*(2*a)*Q := mul_le_mul_of_nonneg_left hs (by positivity)
       _ = 1536*cellFieldNormConstant*m*(Real.sqrt P+1/e^2) := by dsimp [Q]; field_simp; ring

end CoulombAtom

end

end OAI
