import Mathlib.Tactic.Linarith
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup006
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup007
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup008
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup009
import OAI.NumberTheory.Catalan.Estimates.ManuscriptCaseOneX4PointRounding

namespace OAI

section

namespace InternalCatalan
open scoped BigOperators

def manuscriptNormP2_0SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-77366649157093 / 2500000000000000) (74491825385797 / 5000000000000000) (0) (-1) (54161 / 40000) (81 / 319)

private theorem manuscriptNormP2_0SubstituteRat_interval :
    manuscriptNormP2_0SubstituteRat ∈ Set.Icc manuscriptNormP2_0Interval.1 manuscriptNormP2_0Interval.2 := by
  simpa only [manuscriptNormP2_0SubstituteRat, manuscriptNormP2_0Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-77366649157093 / 2500000000000000) (74491825385797 / 5000000000000000) (0) (-1) (54161 / 40000) (81 / 319) (by norm_num))

private theorem manuscriptNormP2_0SubstituteRat_upper :
    manuscriptNormP2_0SubstituteRat ≤ (826697653453844082618353217 / 250000000000000000000000000000) :=
  manuscriptNormP2_0SubstituteRat_interval.2.trans manuscriptNormP2_0_rounded_endpoints.2

def manuscriptNormP2_1SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-70967383232149 / 10000000000000000) (68330346181621 / 20000000000000000) (0) (-1) (358241 / 250000) (171 / 829)

private theorem manuscriptNormP2_1SubstituteRat_interval :
    manuscriptNormP2_1SubstituteRat ∈ Set.Icc manuscriptNormP2_1Interval.1 manuscriptNormP2_1Interval.2 := by
  simpa only [manuscriptNormP2_1SubstituteRat, manuscriptNormP2_1Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-70967383232149 / 10000000000000000) (68330346181621 / 20000000000000000) (0) (-1) (358241 / 250000) (171 / 829) (by norm_num))

private theorem manuscriptNormP2_1SubstituteRat_upper :
    manuscriptNormP2_1SubstituteRat ≤ (711831734440164842505553349 / 1000000000000000000000000000000) :=
  manuscriptNormP2_1SubstituteRat_interval.2.trans manuscriptNormP2_1_rounded_endpoints.2

def manuscriptNormP2_2SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-3374669985148323 / 40000000000000000) (1057383684695809 / 10000000000000000) (1) (0) (22201 / 20000) (0 / 1)

private theorem manuscriptNormP2_2SubstituteRat_interval :
    manuscriptNormP2_2SubstituteRat ∈ Set.Icc manuscriptNormP2_2Interval.1 manuscriptNormP2_2Interval.2 := by
  simpa only [manuscriptNormP2_2SubstituteRat, manuscriptNormP2_2Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-3374669985148323 / 40000000000000000) (1057383684695809 / 10000000000000000) (1) (0) (22201 / 20000) (0 / 1) (by norm_num))

private theorem manuscriptNormP2_2SubstituteRat_upper :
    manuscriptNormP2_2SubstituteRat ≤ (-3364344507035090433041040741 / 100000000000000000000000000000) :=
  manuscriptNormP2_2SubstituteRat_interval.2.trans manuscriptNormP2_2_rounded_endpoints.2

def manuscriptNormP2_3SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-1082171180825569 / 8000000000000000) (0 / 1) (-2) (0) (2601 / 2500) (0 / 1)

private theorem manuscriptNormP2_3SubstituteRat_interval :
    manuscriptNormP2_3SubstituteRat ∈ Set.Icc manuscriptNormP2_3Interval.1 manuscriptNormP2_3Interval.2 := by
  simpa only [manuscriptNormP2_3SubstituteRat, manuscriptNormP2_3Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-1082171180825569 / 8000000000000000) (0 / 1) (-2) (0) (2601 / 2500) (0 / 1) (by norm_num))

private theorem manuscriptNormP2_3SubstituteRat_upper :
    manuscriptNormP2_3SubstituteRat ≤ (91084258788489307023051407697 / 1000000000000000000000000000000) :=
  manuscriptNormP2_3SubstituteRat_interval.2.trans manuscriptNormP2_3_rounded_endpoints.2

def manuscriptNormP2_4SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-273161078429227 / 40000000000000000) (-358543847837271 / 40000000000000000) (1) (0) (101761 / 80000) (0 / 1)

private theorem manuscriptNormP2_4SubstituteRat_interval :
    manuscriptNormP2_4SubstituteRat ∈ Set.Icc manuscriptNormP2_4Interval.1 manuscriptNormP2_4Interval.2 := by
  simpa only [manuscriptNormP2_4SubstituteRat, manuscriptNormP2_4Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-273161078429227 / 40000000000000000) (-358543847837271 / 40000000000000000) (1) (0) (101761 / 80000) (0 / 1) (by norm_num))

private theorem manuscriptNormP2_4SubstituteRat_upper :
    manuscriptNormP2_4SubstituteRat ≤ (-3188293332018223017813008911 / 1000000000000000000000000000000) :=
  manuscriptNormP2_4SubstituteRat_interval.2.trans manuscriptNormP2_4_rounded_endpoints.2

def manuscriptNormP2_5SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (109898540610783 / 40000000000000000) (437141826370109 / 40000000000000000) (-3) (0) (6561 / 5000) (0 / 1)

private theorem manuscriptNormP2_5SubstituteRat_interval :
    manuscriptNormP2_5SubstituteRat ∈ Set.Icc manuscriptNormP2_5Interval.1 manuscriptNormP2_5Interval.2 := by
  simpa only [manuscriptNormP2_5SubstituteRat, manuscriptNormP2_5Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (109898540610783 / 40000000000000000) (437141826370109 / 40000000000000000) (-3) (0) (6561 / 5000) (0 / 1) (by norm_num))

private theorem manuscriptNormP2_5SubstituteRat_upper :
    manuscriptNormP2_5SubstituteRat ≤ (-1241672467370077627171235311 / 500000000000000000000000000000) :=
  manuscriptNormP2_5SubstituteRat_interval.2.trans manuscriptNormP2_5_rounded_endpoints.2

def manuscriptNormP2_6SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-249342691992771 / 20000000000000000) (-244406797738203 / 20000000000000000) (1) (0) (16918021 / 12500000) (-161 / 4110)

private theorem manuscriptNormP2_6SubstituteRat_interval :
    manuscriptNormP2_6SubstituteRat ∈ Set.Icc manuscriptNormP2_6Interval.1 manuscriptNormP2_6Interval.2 := by
  simpa only [manuscriptNormP2_6SubstituteRat, manuscriptNormP2_6Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-249342691992771 / 20000000000000000) (-244406797738203 / 20000000000000000) (1) (0) (16918021 / 12500000) (-161 / 4110) (by norm_num))

private theorem manuscriptNormP2_6SubstituteRat_upper :
    manuscriptNormP2_6SubstituteRat ≤ (-6685833039281012504403289509 / 1000000000000000000000000000000) :=
  manuscriptNormP2_6SubstituteRat_interval.2.trans manuscriptNormP2_6_rounded_endpoints.2

def manuscriptNormP2_7SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (284284403283 / 160000000000000) (69467599782309 / 4000000000000000) (-3) (0) (818021 / 781250) (-161 / 890)

private theorem manuscriptNormP2_7SubstituteRat_interval :
    manuscriptNormP2_7SubstituteRat ∈ Set.Icc manuscriptNormP2_7Interval.1 manuscriptNormP2_7Interval.2 := by
  simpa only [manuscriptNormP2_7SubstituteRat, manuscriptNormP2_7Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (284284403283 / 160000000000000) (69467599782309 / 4000000000000000) (-3) (0) (818021 / 781250) (-161 / 890) (by norm_num))

private theorem manuscriptNormP2_7SubstituteRat_upper :
    manuscriptNormP2_7SubstituteRat ≤ (1301547649377044894797660753 / 1000000000000000000000000000000) :=
  manuscriptNormP2_7SubstituteRat_interval.2.trans manuscriptNormP2_7_rounded_endpoints.2

def manuscriptNormP2_8SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (150530316475111 / 40000000000000000) (334867072933799 / 20000000000000000) (1) (0) (16918021 / 12500000) (161 / 4110)

private theorem manuscriptNormP2_8SubstituteRat_interval :
    manuscriptNormP2_8SubstituteRat ∈ Set.Icc manuscriptNormP2_8Interval.1 manuscriptNormP2_8Interval.2 := by
  simpa only [manuscriptNormP2_8SubstituteRat, manuscriptNormP2_8Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (150530316475111 / 40000000000000000) (334867072933799 / 20000000000000000) (1) (0) (16918021 / 12500000) (161 / 4110) (by norm_num))

private theorem manuscriptNormP2_8SubstituteRat_upper :
    manuscriptNormP2_8SubstituteRat ≤ (121817418346790177253223493 / 100000000000000000000000000000) :=
  manuscriptNormP2_8SubstituteRat_interval.2.trans manuscriptNormP2_8_rounded_endpoints.2

def manuscriptNormP2_9SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-85926283605499 / 8000000000000000) (-53536907546363 / 4000000000000000) (-3) (0) (818021 / 781250) (161 / 890)

private theorem manuscriptNormP2_9SubstituteRat_interval :
    manuscriptNormP2_9SubstituteRat ∈ Set.Icc manuscriptNormP2_9Interval.1 manuscriptNormP2_9Interval.2 := by
  simpa only [manuscriptNormP2_9SubstituteRat, manuscriptNormP2_9Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-85926283605499 / 8000000000000000) (-53536907546363 / 4000000000000000) (-3) (0) (818021 / 781250) (161 / 890) (by norm_num))

private theorem manuscriptNormP2_9SubstituteRat_upper :
    manuscriptNormP2_9SubstituteRat ≤ (1664463244265932879979458429 / 125000000000000000000000000000) :=
  manuscriptNormP2_9SubstituteRat_interval.2.trans manuscriptNormP2_9_rounded_endpoints.2

def manuscriptNormPSubstituteRow2 : ℚ :=
  manuscriptNormP2_0SubstituteRat +
    manuscriptNormP2_1SubstituteRat +
    manuscriptNormP2_2SubstituteRat +
    manuscriptNormP2_3SubstituteRat +
    manuscriptNormP2_4SubstituteRat +
    manuscriptNormP2_5SubstituteRat +
    manuscriptNormP2_6SubstituteRat +
    manuscriptNormP2_7SubstituteRat +
    manuscriptNormP2_8SubstituteRat +
    manuscriptNormP2_9SubstituteRat

theorem manuscriptNormPSubstituteRow2_upper : manuscriptNormPSubstituteRow2 ≤ (64937392547326962796226760577 / 1000000000000000000000000000000) := by
  unfold manuscriptNormPSubstituteRow2
  linarith only [manuscriptNormP2_0SubstituteRat_upper,
    manuscriptNormP2_1SubstituteRat_upper,
    manuscriptNormP2_2SubstituteRat_upper,
    manuscriptNormP2_3SubstituteRat_upper,
    manuscriptNormP2_4SubstituteRat_upper,
    manuscriptNormP2_5SubstituteRat_upper,
    manuscriptNormP2_6SubstituteRat_upper,
    manuscriptNormP2_7SubstituteRat_upper,
    manuscriptNormP2_8SubstituteRat_upper,
    manuscriptNormP2_9SubstituteRat_upper]

end InternalCatalan

end

section

noncomputable section
namespace InternalCatalan
open scoped BigOperators

private theorem manuscriptNormP2_0SubstituteRat_composition_error :
    |manuscriptNormP2_0Term - (manuscriptNormP2_0SubstituteRat : ℝ)| ≤ (((540098219653 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP2_0SubstituteRat ∈ Set.Icc manuscriptNormP2_0Interval.1 manuscriptNormP2_0Interval.2 := by
    simpa only [manuscriptNormP2_0SubstituteRat, manuscriptNormP2_0Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-77366649157093 / 2500000000000000) (74491825385797 / 5000000000000000) (0) (-1) (54161 / 40000) (81 / 319) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP2_0Interval.1 manuscriptNormP2_0Interval.2 manuscriptNormP2_0SubstituteRat
    (661358122763075158075038643 / 200000000000000000000000000000) (826697653453844082618353217 / 250000000000000000000000000000) manuscriptNormP2_0Term
    manuscriptNormP2_0_exact_interval hq manuscriptNormP2_0_rounded_endpoints.1 manuscriptNormP2_0_rounded_endpoints.2
  have hw : ((826697653453844082618353217 / 250000000000000000000000000000) - (661358122763075158075038643 / 200000000000000000000000000000) : ℚ) = (540098219653 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP2_1SubstituteRat_composition_error :
    |manuscriptNormP2_1Term - (manuscriptNormP2_1SubstituteRat : ℝ)| ≤ (((123856202107 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP2_1SubstituteRat ∈ Set.Icc manuscriptNormP2_1Interval.1 manuscriptNormP2_1Interval.2 := by
    simpa only [manuscriptNormP2_1SubstituteRat, manuscriptNormP2_1Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-70967383232149 / 10000000000000000) (68330346181621 / 20000000000000000) (0) (-1) (358241 / 250000) (171 / 829) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP2_1Interval.1 manuscriptNormP2_1Interval.2 manuscriptNormP2_1SubstituteRat
    (355915867220082359324675621 / 500000000000000000000000000000) (711831734440164842505553349 / 1000000000000000000000000000000) manuscriptNormP2_1Term
    manuscriptNormP2_1_exact_interval hq manuscriptNormP2_1_rounded_endpoints.1 manuscriptNormP2_1_rounded_endpoints.2
  have hw : ((711831734440164842505553349 / 1000000000000000000000000000000) - (355915867220082359324675621 / 500000000000000000000000000000) : ℚ) = (123856202107 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP2_2SubstituteRat_composition_error :
    |manuscriptNormP2_2Term - (manuscriptNormP2_2SubstituteRat : ℝ)| ≤ (((1139372379 / 200000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP2_2SubstituteRat ∈ Set.Icc manuscriptNormP2_2Interval.1 manuscriptNormP2_2Interval.2 := by
    simpa only [manuscriptNormP2_2SubstituteRat, manuscriptNormP2_2Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-3374669985148323 / 40000000000000000) (1057383684695809 / 10000000000000000) (1) (0) (22201 / 20000) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP2_2Interval.1 manuscriptNormP2_2Interval.2 manuscriptNormP2_2SubstituteRat
    (-6728689014070180867221453861 / 200000000000000000000000000000) (-3364344507035090433041040741 / 100000000000000000000000000000) manuscriptNormP2_2Term
    manuscriptNormP2_2_exact_interval hq manuscriptNormP2_2_rounded_endpoints.1 manuscriptNormP2_2_rounded_endpoints.2
  have hw : ((-3364344507035090433041040741 / 100000000000000000000000000000) - (-6728689014070180867221453861 / 200000000000000000000000000000) : ℚ) = (1139372379 / 200000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP2_3SubstituteRat_composition_error :
    |manuscriptNormP2_3Term - (manuscriptNormP2_3SubstituteRat : ℝ)| ≤ (((18268393031 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP2_3SubstituteRat ∈ Set.Icc manuscriptNormP2_3Interval.1 manuscriptNormP2_3Interval.2 := by
    simpa only [manuscriptNormP2_3SubstituteRat, manuscriptNormP2_3Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-1082171180825569 / 8000000000000000) (0 / 1) (-2) (0) (2601 / 2500) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP2_3Interval.1 manuscriptNormP2_3Interval.2 manuscriptNormP2_3SubstituteRat
    (45542129394244653502391507333 / 500000000000000000000000000000) (91084258788489307023051407697 / 1000000000000000000000000000000) manuscriptNormP2_3Term
    manuscriptNormP2_3_exact_interval hq manuscriptNormP2_3_rounded_endpoints.1 manuscriptNormP2_3_rounded_endpoints.2
  have hw : ((91084258788489307023051407697 / 1000000000000000000000000000000) - (45542129394244653502391507333 / 500000000000000000000000000000) : ℚ) = (18268393031 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP2_4SubstituteRat_composition_error :
    |manuscriptNormP2_4Term - (manuscriptNormP2_4SubstituteRat : ℝ)| ≤ (((230564907 / 500000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP2_4SubstituteRat ∈ Set.Icc manuscriptNormP2_4Interval.1 manuscriptNormP2_4Interval.2 := by
    simpa only [manuscriptNormP2_4SubstituteRat, manuscriptNormP2_4Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-273161078429227 / 40000000000000000) (-358543847837271 / 40000000000000000) (1) (0) (101761 / 80000) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP2_4Interval.1 manuscriptNormP2_4Interval.2 manuscriptNormP2_4SubstituteRat
    (-127531733280728920730965549 / 40000000000000000000000000000) (-3188293332018223017813008911 / 1000000000000000000000000000000) manuscriptNormP2_4Term
    manuscriptNormP2_4_exact_interval hq manuscriptNormP2_4_rounded_endpoints.1 manuscriptNormP2_4_rounded_endpoints.2
  have hw : ((-3188293332018223017813008911 / 1000000000000000000000000000000) - (-127531733280728920730965549 / 40000000000000000000000000000) : ℚ) = (230564907 / 500000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP2_5SubstituteRat_composition_error :
    |manuscriptNormP2_5Term - (manuscriptNormP2_5SubstituteRat : ℝ)| ≤ (((278283571 / 500000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP2_5SubstituteRat ∈ Set.Icc manuscriptNormP2_5Interval.1 manuscriptNormP2_5Interval.2 := by
    simpa only [manuscriptNormP2_5SubstituteRat, manuscriptNormP2_5Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (109898540610783 / 40000000000000000) (437141826370109 / 40000000000000000) (-3) (0) (6561 / 5000) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP2_5Interval.1 manuscriptNormP2_5Interval.2 manuscriptNormP2_5SubstituteRat
    (-620836233685038813724759441 / 250000000000000000000000000000) (-1241672467370077627171235311 / 500000000000000000000000000000) manuscriptNormP2_5Term
    manuscriptNormP2_5_exact_interval hq manuscriptNormP2_5_rounded_endpoints.1 manuscriptNormP2_5_rounded_endpoints.2
  have hw : ((-1241672467370077627171235311 / 500000000000000000000000000000) - (-620836233685038813724759441 / 250000000000000000000000000000) : ℚ) = (278283571 / 500000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP2_6SubstituteRat_composition_error :
    |manuscriptNormP2_6Term - (manuscriptNormP2_6SubstituteRat : ℝ)| ≤ (((21046071 / 25000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP2_6SubstituteRat ∈ Set.Icc manuscriptNormP2_6Interval.1 manuscriptNormP2_6Interval.2 := by
    simpa only [manuscriptNormP2_6SubstituteRat, manuscriptNormP2_6Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-249342691992771 / 20000000000000000) (-244406797738203 / 20000000000000000) (1) (0) (16918021 / 12500000) (-161 / 4110) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP2_6Interval.1 manuscriptNormP2_6Interval.2 manuscriptNormP2_6SubstituteRat
    (-6685833039281012505245132349 / 1000000000000000000000000000000) (-6685833039281012504403289509 / 1000000000000000000000000000000) manuscriptNormP2_6Term
    manuscriptNormP2_6_exact_interval hq manuscriptNormP2_6_rounded_endpoints.1 manuscriptNormP2_6_rounded_endpoints.2
  have hw : ((-6685833039281012504403289509 / 1000000000000000000000000000000) - (-6685833039281012505245132349 / 1000000000000000000000000000000) : ℚ) = (21046071 / 25000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP2_7SubstituteRat_composition_error :
    |manuscriptNormP2_7Term - (manuscriptNormP2_7SubstituteRat : ℝ)| ≤ (((179965263 / 500000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP2_7SubstituteRat ∈ Set.Icc manuscriptNormP2_7Interval.1 manuscriptNormP2_7Interval.2 := by
    simpa only [manuscriptNormP2_7SubstituteRat, manuscriptNormP2_7Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (284284403283 / 160000000000000) (69467599782309 / 4000000000000000) (-3) (0) (818021 / 781250) (-161 / 890) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP2_7Interval.1 manuscriptNormP2_7Interval.2 manuscriptNormP2_7SubstituteRat
    (1301547649377044894437730227 / 1000000000000000000000000000000) (1301547649377044894797660753 / 1000000000000000000000000000000) manuscriptNormP2_7Term
    manuscriptNormP2_7_exact_interval hq manuscriptNormP2_7_rounded_endpoints.1 manuscriptNormP2_7_rounded_endpoints.2
  have hw : ((1301547649377044894797660753 / 1000000000000000000000000000000) - (1301547649377044894437730227 / 1000000000000000000000000000000) : ℚ) = (179965263 / 500000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP2_8SubstituteRat_composition_error :
    |manuscriptNormP2_8Term - (manuscriptNormP2_8SubstituteRat : ℝ)| ≤ (((254113863 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP2_8SubstituteRat ∈ Set.Icc manuscriptNormP2_8Interval.1 manuscriptNormP2_8Interval.2 := by
    simpa only [manuscriptNormP2_8SubstituteRat, manuscriptNormP2_8Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (150530316475111 / 40000000000000000) (334867072933799 / 20000000000000000) (1) (0) (16918021 / 12500000) (161 / 4110) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP2_8Interval.1 manuscriptNormP2_8Interval.2 manuscriptNormP2_8SubstituteRat
    (1218174183467901772278121067 / 1000000000000000000000000000000) (121817418346790177253223493 / 100000000000000000000000000000) manuscriptNormP2_8Term
    manuscriptNormP2_8_exact_interval hq manuscriptNormP2_8_rounded_endpoints.1 manuscriptNormP2_8_rounded_endpoints.2
  have hw : ((121817418346790177253223493 / 100000000000000000000000000000) - (1218174183467901772278121067 / 1000000000000000000000000000000) : ℚ) = (254113863 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP2_9SubstituteRat_composition_error :
    |manuscriptNormP2_9Term - (manuscriptNormP2_9SubstituteRat : ℝ)| ≤ (((543953379 / 250000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP2_9SubstituteRat ∈ Set.Icc manuscriptNormP2_9Interval.1 manuscriptNormP2_9Interval.2 := by
    simpa only [manuscriptNormP2_9SubstituteRat, manuscriptNormP2_9Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-85926283605499 / 8000000000000000) (-53536907546363 / 4000000000000000) (-3) (0) (818021 / 781250) (161 / 890) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP2_9Interval.1 manuscriptNormP2_9Interval.2 manuscriptNormP2_9SubstituteRat
    (3328926488531865759414963479 / 250000000000000000000000000000) (1664463244265932879979458429 / 125000000000000000000000000000) manuscriptNormP2_9Term
    manuscriptNormP2_9_exact_interval hq manuscriptNormP2_9_rounded_endpoints.1 manuscriptNormP2_9_rounded_endpoints.2
  have hw : ((1664463244265932879979458429 / 125000000000000000000000000000) - (3328926488531865759414963479 / 250000000000000000000000000000) : ℚ) = (543953379 / 250000000000000000000000000000) := by norm_num
  simpa only [hw] using h

theorem manuscriptNormPCompositionRow2_error :
    |manuscriptNormLogRow barrierP2Tail (barrierP2Tail.getD 2 (0, 0)) - (manuscriptNormPSubstituteRow2 : ℝ)| ≤ (((692569074387 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have h0 := manuscriptNormP2_0SubstituteRat_composition_error
  have h1 := manuscriptNormP2_1SubstituteRat_composition_error
  have h2 := manuscriptNormP2_2SubstituteRat_composition_error
  have h3 := manuscriptNormP2_3SubstituteRat_composition_error
  have h4 := manuscriptNormP2_4SubstituteRat_composition_error
  have h5 := manuscriptNormP2_5SubstituteRat_composition_error
  have h6 := manuscriptNormP2_6SubstituteRat_composition_error
  have h7 := manuscriptNormP2_7SubstituteRat_composition_error
  have h8 := manuscriptNormP2_8SubstituteRat_composition_error
  have h9 := manuscriptNormP2_9SubstituteRat_composition_error
  push_cast at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  change |(manuscriptNormP2_0Term + (manuscriptNormP2_1Term + (manuscriptNormP2_2Term + (manuscriptNormP2_3Term + (manuscriptNormP2_4Term + (manuscriptNormP2_5Term + (manuscriptNormP2_6Term + (manuscriptNormP2_7Term + (manuscriptNormP2_8Term + (manuscriptNormP2_9Term + (0 : ℝ))))))))))) - (manuscriptNormPSubstituteRow2 : ℝ)| ≤ _
  unfold manuscriptNormPSubstituteRow2
  push_cast
  apply abs_le.mpr
  constructor
  · linarith only [(abs_le.mp h0).1,
    (abs_le.mp h1).1,
    (abs_le.mp h2).1,
    (abs_le.mp h3).1,
    (abs_le.mp h4).1,
    (abs_le.mp h5).1,
    (abs_le.mp h6).1,
    (abs_le.mp h7).1,
    (abs_le.mp h8).1,
    (abs_le.mp h9).1]
  · linarith only [(abs_le.mp h0).2,
    (abs_le.mp h1).2,
    (abs_le.mp h2).2,
    (abs_le.mp h3).2,
    (abs_le.mp h4).2,
    (abs_le.mp h5).2,
    (abs_le.mp h6).2,
    (abs_le.mp h7).2,
    (abs_le.mp h8).2,
    (abs_le.mp h9).2]

end InternalCatalan

end

end

section

noncomputable section
namespace InternalCatalan

def manuscriptNormP2_0RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-77366649157093 / 2500000000000000) (74491825385797 / 5000000000000000) (0) (-1) (54161 / 40000) (81 / 319)

private theorem manuscriptNormP2_0RoundedSubstituteRat_error :
    |(manuscriptNormP2_0SubstituteRat : ℝ) - (manuscriptNormP2_0RoundedSubstituteRat : ℝ)| ≤
      (((229225123699983 / 5000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-77366649157093 / 2500000000000000) (74491825385797 / 5000000000000000) (0) (-1) (54161 / 40000) (81 / 319) (by norm_num) (by norm_num)
  have hw : |(((-77366649157093 / 2500000000000000) : ℚ) : ℝ)| + |(((74491825385797 / 5000000000000000) : ℚ) : ℝ)| =
      (((229225123699983 / 5000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP2_1RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-70967383232149 / 10000000000000000) (68330346181621 / 20000000000000000) (0) (-1) (358241 / 250000) (171 / 829)

private theorem manuscriptNormP2_1RoundedSubstituteRat_error :
    |(manuscriptNormP2_1SubstituteRat : ℝ) - (manuscriptNormP2_1RoundedSubstituteRat : ℝ)| ≤
      (((210265112645919 / 20000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-70967383232149 / 10000000000000000) (68330346181621 / 20000000000000000) (0) (-1) (358241 / 250000) (171 / 829) (by norm_num) (by norm_num)
  have hw : |(((-70967383232149 / 10000000000000000) : ℚ) : ℝ)| + |(((68330346181621 / 20000000000000000) : ℚ) : ℝ)| =
      (((210265112645919 / 20000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP2_2RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-3374669985148323 / 40000000000000000) (1057383684695809 / 10000000000000000) (1) (0) (22201 / 20000) (0 / 1)

private theorem manuscriptNormP2_2RoundedSubstituteRat_error :
    |(manuscriptNormP2_2SubstituteRat : ℝ) - (manuscriptNormP2_2RoundedSubstituteRat : ℝ)| ≤
      (((7604204723931559 / 40000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-3374669985148323 / 40000000000000000) (1057383684695809 / 10000000000000000) (1) (0) (22201 / 20000) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((-3374669985148323 / 40000000000000000) : ℚ) : ℝ)| + |(((1057383684695809 / 10000000000000000) : ℚ) : ℝ)| =
      (((7604204723931559 / 40000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP2_3RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-1082171180825569 / 8000000000000000) (0 / 1) (-2) (0) (2601 / 2500) (0 / 1)

private theorem manuscriptNormP2_3RoundedSubstituteRat_error :
    |(manuscriptNormP2_3SubstituteRat : ℝ) - (manuscriptNormP2_3RoundedSubstituteRat : ℝ)| ≤
      (((1082171180825569 / 8000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-1082171180825569 / 8000000000000000) (0 / 1) (-2) (0) (2601 / 2500) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((-1082171180825569 / 8000000000000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)| =
      (((1082171180825569 / 8000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP2_4RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-273161078429227 / 40000000000000000) (-358543847837271 / 40000000000000000) (1) (0) (101761 / 80000) (0 / 1)

private theorem manuscriptNormP2_4RoundedSubstituteRat_error :
    |(manuscriptNormP2_4SubstituteRat : ℝ) - (manuscriptNormP2_4RoundedSubstituteRat : ℝ)| ≤
      (((315852463133249 / 20000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-273161078429227 / 40000000000000000) (-358543847837271 / 40000000000000000) (1) (0) (101761 / 80000) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((-273161078429227 / 40000000000000000) : ℚ) : ℝ)| + |(((-358543847837271 / 40000000000000000) : ℚ) : ℝ)| =
      (((315852463133249 / 20000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP2_5RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (109898540610783 / 40000000000000000) (437141826370109 / 40000000000000000) (-3) (0) (6561 / 5000) (0 / 1)

private theorem manuscriptNormP2_5RoundedSubstituteRat_error :
    |(manuscriptNormP2_5SubstituteRat : ℝ) - (manuscriptNormP2_5RoundedSubstituteRat : ℝ)| ≤
      (((136760091745223 / 10000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (109898540610783 / 40000000000000000) (437141826370109 / 40000000000000000) (-3) (0) (6561 / 5000) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((109898540610783 / 40000000000000000) : ℚ) : ℝ)| + |(((437141826370109 / 40000000000000000) : ℚ) : ℝ)| =
      (((136760091745223 / 10000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP2_6RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-249342691992771 / 20000000000000000) (-244406797738203 / 20000000000000000) (1) (0) (16918021 / 12500000) (-161 / 4110)

private theorem manuscriptNormP2_6RoundedSubstituteRat_error :
    |(manuscriptNormP2_6SubstituteRat : ℝ) - (manuscriptNormP2_6RoundedSubstituteRat : ℝ)| ≤
      (((246874744865487 / 10000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-249342691992771 / 20000000000000000) (-244406797738203 / 20000000000000000) (1) (0) (16918021 / 12500000) (-161 / 4110) (by norm_num) (by norm_num)
  have hw : |(((-249342691992771 / 20000000000000000) : ℚ) : ℝ)| + |(((-244406797738203 / 20000000000000000) : ℚ) : ℝ)| =
      (((246874744865487 / 10000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP2_7RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (284284403283 / 160000000000000) (69467599782309 / 4000000000000000) (-3) (0) (818021 / 781250) (-161 / 890)

private theorem manuscriptNormP2_7RoundedSubstituteRat_error :
    |(manuscriptNormP2_7SubstituteRat : ℝ) - (manuscriptNormP2_7RoundedSubstituteRat : ℝ)| ≤
      (((1196479841631 / 62500000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (284284403283 / 160000000000000) (69467599782309 / 4000000000000000) (-3) (0) (818021 / 781250) (-161 / 890) (by norm_num) (by norm_num)
  have hw : |(((284284403283 / 160000000000000) : ℚ) : ℝ)| + |(((69467599782309 / 4000000000000000) : ℚ) : ℝ)| =
      (((1196479841631 / 62500000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP2_8RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (150530316475111 / 40000000000000000) (334867072933799 / 20000000000000000) (1) (0) (16918021 / 12500000) (161 / 4110)

private theorem manuscriptNormP2_8RoundedSubstituteRat_error :
    |(manuscriptNormP2_8SubstituteRat : ℝ) - (manuscriptNormP2_8RoundedSubstituteRat : ℝ)| ≤
      (((820264462342709 / 40000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (150530316475111 / 40000000000000000) (334867072933799 / 20000000000000000) (1) (0) (16918021 / 12500000) (161 / 4110) (by norm_num) (by norm_num)
  have hw : |(((150530316475111 / 40000000000000000) : ℚ) : ℝ)| + |(((334867072933799 / 20000000000000000) : ℚ) : ℝ)| =
      (((820264462342709 / 40000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP2_9RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-85926283605499 / 8000000000000000) (-53536907546363 / 4000000000000000) (-3) (0) (818021 / 781250) (161 / 890)

private theorem manuscriptNormP2_9RoundedSubstituteRat_error :
    |(manuscriptNormP2_9SubstituteRat : ℝ) - (manuscriptNormP2_9RoundedSubstituteRat : ℝ)| ≤
      (((7720003947929 / 320000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-85926283605499 / 8000000000000000) (-53536907546363 / 4000000000000000) (-3) (0) (818021 / 781250) (161 / 890) (by norm_num) (by norm_num)
  have hw : |(((-85926283605499 / 8000000000000000) : ℚ) : ℝ)| + |(((-53536907546363 / 4000000000000000) : ℚ) : ℝ)| =
      (((7720003947929 / 320000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormPRoundedSubstituteRow2 : ℚ :=
  manuscriptNormP2_0RoundedSubstituteRat +
    manuscriptNormP2_1RoundedSubstituteRat +
    manuscriptNormP2_2RoundedSubstituteRat +
    manuscriptNormP2_3RoundedSubstituteRat +
    manuscriptNormP2_4RoundedSubstituteRat +
    manuscriptNormP2_5RoundedSubstituteRat +
    manuscriptNormP2_6RoundedSubstituteRat +
    manuscriptNormP2_7RoundedSubstituteRat +
    manuscriptNormP2_8RoundedSubstituteRat +
    manuscriptNormP2_9RoundedSubstituteRat

theorem manuscriptNormPRoundedRow2_error :
    |(manuscriptNormPSubstituteRow2 : ℝ) - (manuscriptNormPRoundedSubstituteRow2 : ℝ)| ≤
      (((9993324085069059 / 20000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h0 := manuscriptNormP2_0RoundedSubstituteRat_error
  have h1 := manuscriptNormP2_1RoundedSubstituteRat_error
  have h2 := manuscriptNormP2_2RoundedSubstituteRat_error
  have h3 := manuscriptNormP2_3RoundedSubstituteRat_error
  have h4 := manuscriptNormP2_4RoundedSubstituteRat_error
  have h5 := manuscriptNormP2_5RoundedSubstituteRat_error
  have h6 := manuscriptNormP2_6RoundedSubstituteRat_error
  have h7 := manuscriptNormP2_7RoundedSubstituteRat_error
  have h8 := manuscriptNormP2_8RoundedSubstituteRat_error
  have h9 := manuscriptNormP2_9RoundedSubstituteRat_error
  unfold manuscriptNormPSubstituteRow2 manuscriptNormPRoundedSubstituteRow2
  push_cast at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢
  apply abs_le.mpr
  constructor
  · linarith only [(abs_le.mp h0).1,
    (abs_le.mp h1).1,
    (abs_le.mp h2).1,
    (abs_le.mp h3).1,
    (abs_le.mp h4).1,
    (abs_le.mp h5).1,
    (abs_le.mp h6).1,
    (abs_le.mp h7).1,
    (abs_le.mp h8).1,
    (abs_le.mp h9).1]
  · linarith only [(abs_le.mp h0).2,
    (abs_le.mp h1).2,
    (abs_le.mp h2).2,
    (abs_le.mp h3).2,
    (abs_le.mp h4).2,
    (abs_le.mp h5).2,
    (abs_le.mp h6).2,
    (abs_le.mp h7).2,
    (abs_le.mp h8).2,
    (abs_le.mp h9).2]

end InternalCatalan

end

end

end OAI
