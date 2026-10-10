import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.UnshiftedCellCountBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

namespace CoulombAtom

lemma localFieldScale_linear_bound {a m D B C : ℝ}
    (ha : 0 < a) (hm : 1 ≤ m) (h3 : 1/a^3 ≤ m) (_hC : 1 ≤ C)
    (hBC : B ≤ C*m^2) :
    localFieldScale a D B ≤ D/a+(5+C)*(m/a)^2 := by
  let S := (m/a)^2
  have h4 : 1/a^4 ≤ m/a := by
    have hh := div_le_div_of_nonneg_right h3 ha.le
    calc _ = (1/a^3)/a := by ring
         _ ≤ m/a := hh
  have h1 : 1/a ≤ m/a := div_le_div_of_nonneg_right hm ha.le
  have hfirst : (1/a^4+1/a)^2 ≤ 4*S := by
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 1/a^4+1/a) (add_le_add h4 h1) 2
    dsimp [S]
    nlinarith only [hh]
  have hsecond : 1/a^4 ≤ S := by
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 1/a) (cell_reciprocal_bounds ha hm h3).1 2
    have ht := div_le_div_of_nonneg_right hh (sq_nonneg a)
    calc _ = (1/a)^2/a^2 := by ring
         _ ≤ m^2/a^2 := ht
         _ = S := by dsimp [S]; ring
  have hb : B/a^2 ≤ C*S := by
    have hh := div_le_div_of_nonneg_right hBC (sq_nonneg a)
    calc _ ≤ (C*m^2)/a^2 := hh
         _ = C*S := by dsimp [S]; ring
  unfold localFieldScale
  change _ ≤ D/a+(5+C)*S
  nlinarith only [hfirst,hsecond,hb]

lemma thinFieldBase_linear_bound {a m D B C : ℝ}
    (ha : 0 < a) (hm : 1 ≤ m) (h3 : 1/a^3 ≤ m) (hB : 0 ≤ B)
    (hC : 1 ≤ C) (hBC : B ≤ C*m^2) :
    thinFieldBase a a D B ≤ D/a+(5+C+localizationIMSConstant*C)*(m/a)^2 := by
  have hh := localFieldScale_linear_bound ha hm h3 hC hBC (D := D)
  have hr : Real.sqrt B ≤ C*m := by
    simpa using sqrt_count_scale hB hC (by norm_num : (0:ℝ) ≤ 1)
      (le_trans zero_le_one hm) (by simpa using hBC)
  have hI := localizationIMSConstant_nonneg
  have hma : m/a^3 ≤ (m/a)^2 := by
    have ht := mul_le_mul_of_nonneg_right (cell_mass_product ha hm h3)
      (show 0 ≤ m/a^3 by positivity)
    calc _ ≤ (a*m)*(m/a^3) := by simpa using ht
         _ = (m/a)^2 := by field_simp
  have hi : localizationIMSConstant*Real.sqrt B/(a^2*a) ≤
      localizationIMSConstant*C*(m/a)^2 := by
    calc _ ≤ localizationIMSConstant*(C*m)/(a^2*a) := by gcongr
         _ = localizationIMSConstant*C*(m/a^3) := by ring
         _ ≤ _ := by gcongr
  unfold thinFieldBase
  nlinarith only [hh,hi]

 def radialOutLinearConstant (C : ℝ) : ℝ :=
    1+1024*localFieldUniversalConstant*(6+C+localizationIMSConstant*C)+
      (512*localFieldUniversalConstant)^2*C
lemma radialOutLinearConstant_one_le {C : ℝ} (hC : 1 ≤ C) : 1 ≤ radialOutLinearConstant C := by
  have := localizationIMSConstant_nonneg
  have := localFieldUniversalConstant_pos
  unfold radialOutLinearConstant
  have hC0 := le_trans zero_le_one hC
  have h1 : 0 ≤ 1024*localFieldUniversalConstant*(6+C+localizationIMSConstant*C) := by positivity
  have h2 : 0 ≤ (512*localFieldUniversalConstant)^2*C := by positivity
  linarith only [h1,h2]

lemma thinOutMajorant_linear_bound {a m D B C : ℝ}
    (ha : 0 < a) (hm : 1 ≤ m) (h3 : 1/a^3 ≤ m) (hD : 0 ≤ D) (hB : 0 ≤ B)
    (hC : 1 ≤ C) (hBC : B ≤ C*m^2) :
    thinOutMajorant a a D B ≤ radialOutLinearConstant C*(D/a+(m/a)^2) := by
  let S := (m/a)^2
  let Q := 5+C+localizationIMSConstant*C
  let H := D/a+S
  have hS : 0 ≤ S := sq_nonneg _
  have hD' : 0 ≤ D/a := by positivity
  have hH : 0 ≤ H := add_nonneg hD' hS
  have hI := localizationIMSConstant_nonneg
  have hF := localFieldUniversalConstant_pos.le
  have hC0 := le_trans zero_le_one hC
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hh := thinFieldBase_linear_bound ha hm h3 hB hC hBC (D := D)
  have hf : thinFieldBase a a D B ≤ (1+Q)*H := by
    have hc := mul_nonneg hQ hD'
    dsimp [H]
    nlinarith only [hh,hS,hc]
  have hb : B/a^2 ≤ C*H := by
    have ht := div_le_div_of_nonneg_right hBC (sq_nonneg a)
    have hc := mul_nonneg hC0 hD'
    have hid : (C*m^2)/a^2 = C*S := by dsimp [S]; ring
    rw [hid] at ht
    dsimp [H]
    nlinarith only [ht,hc]
  have h1 := mul_le_mul_of_nonneg_left hf (show 0 ≤ 1024*localFieldUniversalConstant by positivity)
  have h2 := mul_le_mul_of_nonneg_left hb (sq_nonneg (512*localFieldUniversalConstant))
  have ht : thinOutMajorant a a D B ≤ (radialOutLinearConstant C-1)*H := by
    calc _ = 1024*localFieldUniversalConstant*thinFieldBase a a D B+
          (512*localFieldUniversalConstant)^2*(B/a^2) := by unfold thinOutMajorant; ring
         _ ≤ 1024*localFieldUniversalConstant*((1+Q)*H)+
          (512*localFieldUniversalConstant)^2*(C*H) := add_le_add h1 h2
         _ = _ := by unfold radialOutLinearConstant Q; ring
  nlinarith only [ht,hH]

lemma thinFieldBase_collar_bound {a b m D B C : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hm : 1 ≤ m) (h3 : 1/a^3 ≤ m)
    (hDm : D*a ≤ m^2) (hbm : a ≤ b^2*m) (hB : 0 ≤ B)
    (hC : 1 ≤ C) (hBC : B ≤ C*m^2) :
    thinFieldBase a b D B ≤ (6+C+localizationIMSConstant*C)*(m/a)^2 := by
  have hfield := localFieldScale_linear_bound ha hm h3 hC hBC (D := D)
  have hr : Real.sqrt B ≤ C*m := by
    simpa using sqrt_count_scale hB hC (by norm_num : (0:ℝ) ≤ 1)
      (le_trans zero_le_one hm) (by simpa using hBC)
  have hD : D/a ≤ (m/a)^2 := by
    have hh := div_le_div_of_nonneg_right hDm (sq_nonneg a)
    calc _ = (D*a)/a^2 := by field_simp
         _ ≤ m^2/a^2 := hh
         _ = _ := by ring
  have hcollar : m/(b^2*a) ≤ (m/a)^2 := by
    have hh := mul_le_mul_of_nonneg_left hbm (show 0 ≤ m/(b^2*a^2) by positivity)
    calc _ = m/(b^2*a^2)*a := by field_simp
         _ ≤ m/(b^2*a^2)*(b^2*m) := hh
         _ = _ := by field_simp
  have hI := localizationIMSConstant_nonneg
  have hC0 := le_trans zero_le_one hC
  have hi : localizationIMSConstant*Real.sqrt B/(b^2*a) ≤
      localizationIMSConstant*C*(m/a)^2 := by
    calc _ ≤ localizationIMSConstant*(C*m)/(b^2*a) := by gcongr
         _ = localizationIMSConstant*C*(m/(b^2*a)) := by ring
         _ ≤ _ := by gcongr
  unfold thinFieldBase
  nlinarith only [hfield,hD,hi]

 def actualCellMomentConstant : ℝ := localCountCoverConstant*universalCellCountConstant
lemma actualCellMomentConstant_one_le : 1 ≤ actualCellMomentConstant := by
  have h1 := localCountCoverConstant_one_le
  have h2 := universalCellCountConstant_one_le
  unfold actualCellMomentConstant
  nlinarith

lemma priced_enlarged_cell_count {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (hm : formMass ψ = 1) {Z lam : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 < lam) {y : Space} (hy : y ≠ 0) :
    rawCountMoment ψ y (32*localCellRadius y) ≤
      actualCellMomentConstant*(localOffsetMass (max (corePriceExcess Z lam ψ) 0) y)^2 := by
  have hh := enlarged_cell_count_le hψ.sobolevVector (le_max_right (corePriceExcess Z lam ψ) 0) hy
  have hP := priced_cell_supremum_bound hψ hm hZ hlam canonicalRealPacket_smooth
    canonicalRealPacket_compact canonicalRealPacket_normalized canonicalRealPacket_radial canonicalRealPacket_support
  have hC := localCountCoverConstant_one_le
  unfold actualCellMomentConstant
  exact hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hP (le_trans zero_le_one hC)) (sq_nonneg _))

 def sharpFreshFieldConstant : ℝ := 1+thinFieldUniversalConstant*
    (6+actualCellMomentConstant+localizationIMSConstant*actualCellMomentConstant)
lemma sharpFreshFieldConstant_one_le : 1 ≤ sharpFreshFieldConstant := by
  have hC := actualCellMomentConstant_one_le
  have hI := localizationIMSConstant_nonneg
  have hT := thinFieldUniversalConstant_pos
  unfold sharpFreshFieldConstant
  have h : 0 ≤ thinFieldUniversalConstant*(6+actualCellMomentConstant+
      localizationIMSConstant*actualCellMomentConstant) := by positivity
  linarith only [h]

lemma sharpFreshField_square {a b D B m : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hm : 1 ≤ m) (h3 : 1/a^3 ≤ m) (hDm : D*a ≤ m^2) (hbm : a ≤ b^2*m)
    (hB : 0 ≤ B) (hBC : B ≤ actualCellMomentConstant*m^2) :
    thinFieldUniversalConstant*thinFieldBase a b D B ≤ (sharpFreshFieldConstant*(m/a))^2 := by
  have hh := thinFieldBase_collar_bound ha hb hm h3 hDm hbm hB actualCellMomentConstant_one_le hBC
  let K := thinFieldUniversalConstant*(6+actualCellMomentConstant+
    localizationIMSConstant*actualCellMomentConstant)
  have hK : 0 ≤ K := by
    have := thinFieldUniversalConstant_pos
    have := actualCellMomentConstant_one_le
    have := localizationIMSConstant_nonneg
    dsimp [K]; positivity
  have hKK : K ≤ sharpFreshFieldConstant^2 := by change K ≤ (1+K)^2; nlinarith only [hK]
  calc _ ≤ K*(m/a)^2 := by
          have ht := mul_le_mul_of_nonneg_left hh thinFieldUniversalConstant_pos.le
          exact ht.trans_eq (by dsimp [K]; ring)
       _ ≤ sharpFreshFieldConstant^2*(m/a)^2 := mul_le_mul_of_nonneg_right hKK (sq_nonneg _)
       _ = _ := by ring

theorem sharp_cell_fresh_field_mass {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (hm : formMass ψ = 1) {y : Space} (hy : y ≠ 0)
    {b r Z lam : ℝ} (hb : 0 < b) (hba : b ≤ localCellRadius y)
    (hr : r ∈ Set.Icc (5*localCellRadius y) (6*localCellRadius y))
    (hZ : 0 ≤ Z) (hlam : 0 < lam)
    (hcollar : localCellRadius y ≤ b^2*localOffsetMass (max (corePriceExcess Z lam ψ) 0) y) :
    ∃ hr0 : 0 ≤ r,
      freshOutMaximumSecondMoment (coreFirstRadialCut y hr0 hb)
        (coreFirstRadialCut_partition y hr0 hb) ψ Z lam ≤
          (sharpFreshFieldConstant*(localOffsetMass (max (corePriceExcess Z lam ψ) 0) y/localCellRadius y))^2 ∧
      freshPatchMass (coreFirstRadialCut y hr0 hb) (coreFirstRadialCut_partition y hr0 hb)
        ψ Z lam y (r-4*b) ≤
          768*sharpFreshFieldConstant*localOffsetMass (max (corePriceExcess Z lam ψ) 0) y := by
  let a := localCellRadius y
  let D := max (corePriceExcess Z lam ψ) 0
  let m := localOffsetMass D y
  let B := rawCountMoment ψ y (16*a)
  have ha : 0 < a := localCellRadius_pos hy
  have hr0 : 0 ≤ r := le_trans (by positivity : 0 ≤ 5*a) hr.1
  have hsep : 20*a ≤ ‖y‖ := by dsimp [a,localCellRadius]; nlinarith [norm_nonneg y]
  have hbcount : B ≤ actualCellMomentConstant*m^2 :=
    (rawCountMoment_le_of_radius hψ.sobolevVector y y (by simp only [sub_self,norm_zero,zero_add]; linarith : ‖y-y‖+16*a ≤ 32*a)).trans
      (priced_enlarged_cell_count hψ hm hZ hlam hy)
  have hsq := sharpFreshField_square ha hb (localOffsetMass_one_le D y)
    (localOffsetMass_cube_le D y) (localOffsetMass_offset (le_max_right _ _) hy) hcollar
    (rawCountMoment_nonneg ψ y (16*a)) hbcount
  refine ⟨hr0,(freshOutMaximum_thin_bound hψ hm y ha hr0 hr.2 hb hba hsep hZ hlam).trans hsq,?_⟩
  have hh := freshPatchMass_thin_bound hψ hm y ha hr0 hr.2 hb (by linarith [hr.1]) hba hsep hZ hlam
  have hQ : 0 ≤ sharpFreshFieldConstant*(m/a) := by
    have := sharpFreshFieldConstant_one_le
    have := localOffsetMass_one_le D y
    positivity
  have hroot := Real.sqrt_le_iff.mpr ⟨hQ,hsq⟩
  calc _ ≤ 768*a*Real.sqrt (thinFieldUniversalConstant*thinFieldBase a b D B) := hh
       _ ≤ 768*a*(sharpFreshFieldConstant*(m/a)) := mul_le_mul_of_nonneg_left hroot (by positivity)
       _ = _ := by dsimp [m,D]; field_simp

end CoulombAtom

end

end OAI
