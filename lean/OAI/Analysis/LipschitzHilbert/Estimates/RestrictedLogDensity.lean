import OAI.Analysis.LipschitzHilbert.Estimates.RestrictedTestOpenApproximation
import Mathlib.Analysis.Normed.Operator.Bilinear

namespace OAI

/-! Passing a logarithmic restricted estimate from bounded Schwartz
functions to measurable bounded tests, preserving the support masses. -/
noncomputable section
open Set MeasureTheory Filter Function
open scoped ENNReal Topology
namespace LipschitzHilbert.PacketRepresentation

def restrictedLogFactor (C a b : ℝ) : ℝ :=
  C*((1+|Real.log (a/b)|)^3)⁻¹*Real.sqrt a*Real.sqrt b

theorem restrictedLogFactor_tendsto (C : ℝ) (a b : ℕ → ℝ) (A B : ℝ)
    (ha : Tendsto a atTop (𝓝 A)) (hb : Tendsto b atTop (𝓝 B)) (hA : 0<A) (hB : 0<B) :
    Tendsto (fun n => restrictedLogFactor C (a n) (b n)) atTop (𝓝 (restrictedLogFactor C A B)) := by
  have hlog := (ha.div hb hB.ne').log (div_ne_zero hA.ne' hB.ne')
  have hden : (1+|Real.log (A/B)|)^3≠0 := by positivity
  have hinv : Tendsto (fun n => ((1+|Real.log (a n/b n)|)^3)⁻¹) atTop
      (𝓝 (((1+|Real.log (A/B)|)^3)⁻¹)) :=
    (((tendsto_const_nhds (x:=(1:ℝ))).add hlog.abs).pow 3).inv₀ hden
  exact ((tendsto_const_nhds.mul hinv).mul ha.sqrt).mul hb.sqrt

theorem restricted_log_density (B : Lp ℂ 2 planeMeasure →L[ℝ] Lp ℂ 2 planeMeasure →L[ℝ] ℂ)
    (C : ℝ) (V : Set (ℝ×ℝ)) (hV : IsOpen V)
    (hbound : ∀ (f g : SchwartzMap (ℝ×ℝ) ℂ),
      (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) → support f⊆V → support g⊆V →
      ∀ F G : Set (ℝ×ℝ), MeasurableSet F → MeasurableSet G →
        planeMeasure F≠∞ → planeMeasure G≠∞ → 0<planeMeasure.real F → 0<planeMeasure.real G →
        support f⊆F → support g⊆G →
        ‖B (f.toLp 2 planeMeasure) (g.toLp 2 planeMeasure)‖≤
          restrictedLogFactor C (planeMeasure.real F) (planeMeasure.real G))
    (f g : (ℝ×ℝ) → ℂ) (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ z, ‖f z‖≤1) (hg : ∀ z, ‖g z‖≤1)
    (hfV : support f⊆V) (hgV : support g⊆V)
    (F G : Set (ℝ×ℝ)) (hF : MeasurableSet F) (hG : MeasurableSet G)
    (hFfin : planeMeasure F≠∞) (hGfin : planeMeasure G≠∞)
    (hFpos : 0<planeMeasure.real F) (hGpos : 0<planeMeasure.real G)
    (hfs : support f⊆F) (hgs : support g⊆G)
    (hf2 : MemLp f 2 planeMeasure) (hg2 : MemLp g 2 planeMeasure) :
    ‖B (hf2.toLp f) (hg2.toLp g)‖≤restrictedLogFactor C (planeMeasure.real F) (planeMeasure.real G) := by
  obtain ⟨fn,Fn,hfn,hflim,hFmass⟩ := exists_schwartz_open_approx_sequence f hfm hf hf2 F V hF hFfin hfs hV hfV
  obtain ⟨gn,Gn,hgn,hglim,hGmass⟩ := exists_schwartz_open_approx_sequence g hgm hg hg2 G V hG hGfin hgs hV hgV
  have hlim := (B.isBoundedBilinearMap.continuous.tendsto _).comp (hflim.prodMk_nhds hglim)
  have hright := restrictedLogFactor_tendsto C _ _ _ _ hFmass hGmass hFpos hGpos
  apply le_of_tendsto_of_tendsto hlim.norm hright
  filter_upwards [] with n
  rcases hfn n with ⟨hfnb,hfns,hFn,hFFn,hfnV,hFnfin⟩
  rcases hgn n with ⟨hgnb,hgns,hGn,hGGn,hgnV,hGnfin⟩
  exact hbound (fn n) (gn n) hfnb hgnb hfnV hgnV (Fn n) (Gn n) hFn.measurableSet hGn.measurableSet
    hFnfin hGnfin (hFpos.trans_le (measureReal_mono hFFn hFnfin))
    (hGpos.trans_le (measureReal_mono hGGn hGnfin)) hfns hgns

end LipschitzHilbert.PacketRepresentation

end

end OAI
