import OAI.Analysis.LipschitzHilbert.Trees.SourceL2Gram
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

namespace OAI

/-! Measurable cutoffs as contractions on the actual complex L2 space. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert
variable {X : Type*} [MeasurableSpace X]

def l2IndicatorLM (mu : Measure X) (S : Set X) (hS : MeasurableSet S) :
    Lp ℂ 2 mu →ₗ[ℂ] Lp ℂ 2 mu where
  toFun f := ((Lp.memLp f).indicator hS).toLp (S.indicator f)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [((Lp.memLp (f+g)).indicator hS).coeFn_toLp,
      ((Lp.memLp f).indicator hS).coeFn_toLp,
      ((Lp.memLp g).indicator hS).coeFn_toLp,
      Lp.coeFn_add f g,
      Lp.coeFn_add (((Lp.memLp f).indicator hS).toLp _) (((Lp.memLp g).indicator hS).toLp _)]
      with z hz hf hg hadd hout
    rw [hz,hout]
    simp only [Pi.add_apply,hf,hg]
    by_cases h : z∈S
    · simp only [Set.indicator_of_mem h,hadd,Pi.add_apply]
    · simp only [Set.indicator_of_notMem h,add_zero]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [((Lp.memLp (c • f)).indicator hS).coeFn_toLp,
      ((Lp.memLp f).indicator hS).coeFn_toLp,
      Lp.coeFn_smul c f,
      Lp.coeFn_smul c (((Lp.memLp f).indicator hS).toLp _)] with z hz hf hc hout
    simp only [RingHom.id_apply]
    rw [hz,hout]
    simp only [Pi.smul_apply,hf]
    by_cases h : z∈S
    · simp only [Set.indicator_of_mem h,hc,Pi.smul_apply]
    · simp only [Set.indicator_of_notMem h,smul_zero]

theorem l2IndicatorLM_norm (mu : Measure X) (S : Set X) (hS : MeasurableSet S)
    (f : Lp ℂ 2 mu) : ‖l2IndicatorLM mu S hS f‖≤‖f‖ := by
  change ‖((Lp.memLp f).indicator hS).toLp (S.indicator f)‖≤‖f‖
  rw [Lp.norm_toLp,Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.memLp f).eLpNorm_ne_top (eLpNorm_indicator_le f hS)

def l2Indicator (mu : Measure X) (S : Set X) (hS : MeasurableSet S) :
    Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu :=
  (l2IndicatorLM mu S hS).mkContinuous 1 (fun f => by simpa only [one_mul] using l2IndicatorLM_norm mu S hS f)

theorem l2Indicator_toLp (mu : Measure X) (S : Set X) (hS : MeasurableSet S)
    (f : X → ℂ) (hf : MemLp f 2 mu) :
    l2Indicator mu S hS (hf.toLp f)=(hf.indicator hS).toLp (S.indicator f) := by
  apply Lp.ext
  filter_upwards [((Lp.memLp (hf.toLp f)).indicator hS).coeFn_toLp,
    (hf.indicator hS).coeFn_toLp,hf.coeFn_toLp] with z hz hz' hfz
  change (((Lp.memLp (hf.toLp f)).indicator hS).toLp (S.indicator (hf.toLp f))) z=_
  rw [hz,hz']
  by_cases h : z∈S
  · simp only [Set.indicator_of_mem h,hfz]
  · simp only [Set.indicator_of_notMem h]

theorem l2Indicator_coe (mu : Measure X) (S : Set X) (hS : MeasurableSet S)
    (f : Lp ℂ 2 mu) : l2Indicator mu S hS f=ᵐ[mu] S.indicator f :=
  ((Lp.memLp f).indicator hS).coeFn_toLp

theorem l2Indicator_inner (mu : Measure X) (S : Set X) (hS : MeasurableSet S)
    (f g : Lp ℂ 2 mu) :
    inner ℂ (l2Indicator mu S hS f) g=inner ℂ f (l2Indicator mu S hS g) := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [l2Indicator_coe mu S hS f,l2Indicator_coe mu S hS g] with z hf hg
  rw [hf,hg]
  by_cases hz : z∈S
  · simp only [Set.indicator_of_mem hz]
  · simp only [Set.indicator_of_notMem hz,inner_zero_left,inner_zero_right]

end LipschitzHilbert

end

end OAI
