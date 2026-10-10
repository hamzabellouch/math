import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.DimensionFunctions.DimensionContentMeasure
import OAI.Analysis.JiangSu.TraceCone.CuntzDenseMaps

namespace OAI


noncomputable section
namespace Pureness
open TraceCone Set
open scoped ComplexOrder NNReal ENNReal

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

def continuousNNRealComplex (f : C(X, ℝ≥0)) : C(X, ℂ) :=
  ⟨fun x => ((f x : ℝ) : ℂ), Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp f.continuous)⟩

def continuousNNRealPositive (f : C(X, ℝ≥0)) : Positive C(X, ℂ) :=
  ⟨continuousNNRealComplex f, by
    intro x
    change (0 : ℂ) ≤ ((f x : ℝ) : ℂ)
    exact_mod_cast (f x).2⟩

lemma continuousNNRealPositive_add (f g : C(X, ℝ≥0)) :
    continuousNNRealPositive (f+g) = Positive.add (continuousNNRealPositive f) (continuousNNRealPositive g) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  change (((f x+g x : ℝ≥0) : ℝ) : ℂ) = ((f x : ℝ) : ℂ)+((g x : ℝ) : ℂ)
  simp

lemma continuousNNRealPositive_zero : continuousNNRealPositive (0 : C(X, ℝ≥0)) = Positive.zero := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  change ((0 : ℝ) : ℂ) = 0
  exact Complex.ofReal_zero

lemma continuousNNRealPositive_mono : Monotone (continuousNNRealPositive (X := X)) := by
  intro lower upper ordered point
  change ((lower point : ℝ) : ℂ) ≤ ((upper point : ℝ) : ℂ)
  exact_mod_cast ordered point

lemma continuousNNRealPositive_mul_zero (f g : C(X, ℝ≥0)) (h : f*g = 0) :
    (continuousNNRealPositive f).1*(continuousNNRealPositive g).1 = 0 := by
  apply ContinuousMap.ext
  intro x
  have hx : f x*g x = 0 := congrArg (fun k : C(X, ℝ≥0) => k x) h
  change ((f x : ℝ) : ℂ)*((g x : ℝ) : ℂ) = 0
  exact_mod_cast hx

lemma continuousNNRealPositive_cut (f : C(X, ℝ≥0)) (ε : ℝ≥0) :
    continuousNNRealPositive (continuousNNRealCut ε f) = Positive.cut ε (continuousNNRealPositive f) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  let e := (ContinuousMap.evalStarAlgHom ℂ ℂ x).toNonUnitalStarAlgHom
  have h := Positive.map_cut e ε (continuousNNRealPositive f)
  have hv := congrArg Subtype.val h
  change e (cfcₙ (fun t : ℝ => max (t-ε) 0) (continuousNNRealComplex f)) =
    cfcₙ (fun t : ℝ => max (t-ε) 0) (((f x : ℝ) : ℂ)) at hv
  change (((f x-ε : ℝ≥0) : ℝ) : ℂ) = e (cfcₙ (fun t : ℝ => max (t-ε) 0) (continuousNNRealComplex f))
  rw [hv]
  rw [cfcₙ_eq_cfc (hf0 := by simp)]
  change (((f x-ε : ℝ≥0) : ℝ) : ℂ) = cfc (fun t : ℝ => max (t-ε) 0) (algebraMap ℝ ℂ (f x))
  rw [cfc_algebraMap]
  change Complex.ofReal ((f x-ε : ℝ≥0) : ℝ) = Complex.ofReal (max ((f x : ℝ)-ε) 0)
  apply congrArg Complex.ofReal
  by_cases hx : ε ≤ f x
  · rw [NNReal.coe_sub hx,max_eq_left (sub_nonneg.mpr (show (ε : ℝ) ≤ f x from hx))]
  · rw [tsub_eq_zero_of_le (le_of_not_ge hx)]
    exact (max_eq_right (sub_nonpos.mpr (show (f x : ℝ) ≤ ε from (le_of_not_ge hx)))).symm

end Pureness
end

end OAI
