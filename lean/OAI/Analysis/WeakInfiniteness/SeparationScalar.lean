import Mathlib
import OAI.Analysis.WeakInfiniteness.SpectralCut

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

def separationFloor (l s : ℝ) : ℝ := max l (Real.sqrt s)

def separationR (l s : ℝ) : ℝ := Real.sqrt l / Real.sqrt (separationFloor l s)

def separationV (l s : ℝ) : ℝ := separationR l s / separationFloor l s

def separationK (l s : ℝ) : ℝ := (Real.sqrt l * Real.sqrt (separationFloor l s))⁻¹

def separationG (l s : ℝ) : ℝ := spectralRamp l (Real.sqrt s)

def separationN (l s : ℝ) : ℝ := spectralRamp (4*l) (Real.sqrt s)

def separationL (l s : ℝ) : ℝ := 1-separationN l s

lemma separationFloor_pos {l : ℝ} (hl : 0 < l) (s : ℝ) : 0 < separationFloor l s :=
  hl.trans_le (le_max_left _ _)

lemma continuous_separationFloor (l : ℝ) : Continuous (separationFloor l) :=
  continuous_const.max Real.continuous_sqrt

lemma continuous_separationR {l : ℝ} (hl : 0 < l) : Continuous (separationR l) := by
  unfold separationR
  exact continuous_const.div (Real.continuous_sqrt.comp (continuous_separationFloor l))
    (fun s => ne_of_gt (Real.sqrt_pos.mpr (separationFloor_pos hl s)))

lemma continuous_separationV {l : ℝ} (hl : 0 < l) : Continuous (separationV l) := by
  unfold separationV
  exact (continuous_separationR hl).div (continuous_separationFloor l)
    (fun s => ne_of_gt (separationFloor_pos hl s))

lemma continuous_separationK {l : ℝ} (hl : 0 < l) : Continuous (separationK l) := by
  unfold separationK
  exact (continuous_const.mul (Real.continuous_sqrt.comp (continuous_separationFloor l))).inv₀
    (fun s => ne_of_gt (mul_pos (Real.sqrt_pos.mpr hl) (Real.sqrt_pos.mpr (separationFloor_pos hl s))))

lemma continuous_separationG (l : ℝ) : Continuous (separationG l) :=
  (continuous_spectralRamp l).comp Real.continuous_sqrt

lemma continuous_separationN (l : ℝ) : Continuous (separationN l) :=
  (continuous_spectralRamp (4*l)).comp Real.continuous_sqrt

lemma continuous_separationL (l : ℝ) : Continuous (separationL l) :=
  continuous_const.sub (continuous_separationN l)

lemma separationR_nonneg {l : ℝ} (_hl : 0 ≤ l) (s : ℝ) : 0 ≤ separationR l s := by
  exact div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

lemma separationV_nonneg {l : ℝ} (hl : 0 < l) (s : ℝ) : 0 ≤ separationV l s :=
  div_nonneg (separationR_nonneg hl.le s) (separationFloor_pos hl s).le

lemma separationR_sq {l : ℝ} (hl : 0 < l) (s : ℝ) :
    (separationR l s)^2=l/separationFloor l s := by
  rw [separationR,div_pow,Real.sq_sqrt hl.le,Real.sq_sqrt (separationFloor_pos hl s).le]

lemma separationV_sq {l : ℝ} (hl : 0 < l) (s : ℝ) :
    (separationV l s)^2=l/(separationFloor l s)^3 := by
  rw [separationV,div_pow,separationR_sq hl]
  ring

lemma separationR_le_one {l : ℝ} (hl : 0 < l) (s : ℝ) : separationR l s ≤ 1 := by
  apply (div_le_one₀ (Real.sqrt_pos.mpr (separationFloor_pos hl s))).mpr
  exact Real.sqrt_le_sqrt (le_max_left _ _)

lemma separation_floor_ge_sqrt (l s : ℝ) : Real.sqrt s ≤ separationFloor l s := le_max_right _ _

lemma separation_floor_eq {l s : ℝ} (h : l ≤ Real.sqrt s) : separationFloor l s=Real.sqrt s :=
  max_eq_right h

lemma separation_sV_sq_le_one {l s : ℝ} (hl : 0 < l) (hs : 0 ≤ s) :
    s*(separationV l s)^2 ≤ 1 := by
  rw [separationV_sq hl]
  have hm := separationFloor_pos hl s
  have hml : l ≤ separationFloor l s := le_max_left _ _
  have hsr := separation_floor_ge_sqrt l s
  have hs2 : s ≤ (separationFloor l s)^2 := by nlinarith [Real.sq_sqrt hs,Real.sqrt_nonneg s]
  rw [← mul_div_assoc]
  apply (div_le_one₀ (pow_pos hm 3)).mpr
  calc
    s*l ≤ (separationFloor l s)^2*separationFloor l s := by gcongr
    _ = (separationFloor l s)^3 := by ring

lemma separationG_zero {l : ℝ} (hl : 0 < l) : separationG l 0=0 := by
  exact spectralRamp_eq_zero hl (by simpa using hl.le)

lemma separationN_zero {l : ℝ} (hl : 0 < l) : separationN l 0=0 := by
  exact spectralRamp_eq_zero (by positivity) (by simpa using (show 0 ≤ 4*l by positivity))

lemma separationGN {l : ℝ} (hl : 0 < l) (s : ℝ) :
    separationG l s*separationN l s=separationN l s := by
  by_cases h : Real.sqrt s ≤ 4*l
  · rw [show separationN l s=0 from spectralRamp_eq_zero (by positivity) h,mul_zero]
  · rw [show separationG l s=1 from spectralRamp_eq_one hl (by linarith [lt_of_not_ge h]),one_mul]

lemma separationVRG {l s : ℝ} (hl : 0 < l) (hs : 0 ≤ s) :
    s*separationV l s*separationR l s*separationG l s=l*separationG l s := by
  by_cases h : Real.sqrt s ≤ l
  · rw [show separationG l s=0 from spectralRamp_eq_zero hl h,mul_zero,mul_zero]
  · have hp : 0 < Real.sqrt s := hl.trans (lt_of_not_ge h)
    have he : s*separationV l s*separationR l s=l := by
      rw [separationV]
      calc
        s*(separationR l s/separationFloor l s)*separationR l s =
            s*(separationR l s)^2/separationFloor l s := by ring
        _=l := by rw [separationR_sq hl,separation_floor_eq (le_of_not_ge h)]
                  field_simp
                  nlinarith [Real.sq_sqrt hs]
    rw [he]

lemma separation_low_support {l s : ℝ} (hl : 0 < l) (h : 8*l ≤ Real.sqrt s) :
    separationL l s=0 := by
  have hn : separationN l s=1 := spectralRamp_eq_one (by positivity) (by linarith)
  simp only [separationL,hn,sub_self]

lemma separationL_bounds (l s : ℝ) : 0 ≤ separationL l s ∧ separationL l s ≤ 1 := by
  constructor
  · exact sub_nonneg.mpr (spectralRamp_le_one (4*l) (Real.sqrt s))
  · exact sub_le_self _ (spectralRamp_nonneg (4*l) (Real.sqrt s))

end

end WeakPureInfiniteness
end

end OAI
