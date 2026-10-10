import OAI.Probability.GammaPassage.CoordinateTails
import Mathlib.Data.Int.Interval

namespace OAI

namespace GammaFPP.Grid
open PlanarFPP Finset

noncomputable def verticalIntervalEdges (X lo hi : ℤ) : Finset Edge :=
  (Finset.Ico lo hi).image (fun y => ((X,y),true))

lemma verticalIntervalEdges_card (X lo hi : ℤ) :
    (verticalIntervalEdges X lo hi).card=(hi-lo).toNat := by
  rw [verticalIntervalEdges,Finset.card_image_of_injective]
  · exact Int.card_Ico lo hi
  · intro a b hab
    exact congrArg (fun e : Edge => e.1.2) hab

noncomputable def transverseIntervalEdges (b : ℝ) (X : ℤ) (lo hi : ℝ) : Finset Edge :=
  verticalIntervalEdges X ⌈lo+b*X⌉ ⌊hi+b*X⌋

lemma transverseIntervalEdges_card_le (b : ℝ) (X : ℤ) (lo hi A : ℝ)
    (hA : 0 ≤ A) (hwidth : hi-lo ≤ A) :
    ((transverseIntervalEdges b X lo hi).card : ℝ) ≤ A := by
  rw [transverseIntervalEdges,verticalIntervalEdges_card]
  by_cases hle : ⌈lo+b*X⌉ ≤ ⌊hi+b*X⌋
  · have he : ((⌊hi+b*X⌋-⌈lo+b*X⌉).toNat : ℝ) = (⌊hi+b*X⌋ : ℝ)-(⌈lo+b*X⌉ : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (show 0 ≤ ⌊hi+b*X⌋-⌈lo+b*X⌉ by omega)
    rw [he]
    have hl := Int.le_ceil (lo+b*X)
    have hh := Int.floor_le (hi+b*X)
    linarith
  · rw [Int.toNat_eq_zero.mpr (by omega)]
    simpa using hA

noncomputable def gridIntervalLower (h w : ℤ) : ℝ := (h : ℝ)*w-2
noncomputable def gridIntervalUpper (j : ℕ) (h w : ℤ) : ℝ :=
  (h : ℝ)*w+(30*(j : ℝ)^2+9)*w+2

lemma grid_interval_card (b : ℝ) (X h w : ℤ) (j : ℕ) (hj : 1 ≤ j) (hw : 1 ≤ w) :
    ((transverseIntervalEdges b X (gridIntervalLower h w) (gridIntervalUpper j h w)).card : ℝ) ≤
      50*(j : ℝ)^2*w := by
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hw' : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hj2 : (1 : ℝ) ≤ (j : ℝ)^2 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_right hj2 (show 0 ≤ (w : ℝ) by linarith)
  apply transverseIntervalEdges_card_le _ _ _ _ _ (by positivity)
  unfold gridIntervalLower gridIntervalUpper
  nlinarith

end GammaFPP.Grid

end OAI
