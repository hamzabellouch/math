import Mathlib
import OAI.Probability.SKValue.Equations.BurgersMild
import OAI.Probability.SKValue.Equations.DuhamelJets

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma BoundedSmooth.heat_iteratedDeriv {f : ℝ → ℝ} (hf : BoundedSmooth f) (h : ℝ) (n : ℕ) :
    _root_.iteratedDeriv n (heat h f)=heat h (_root_.iteratedDeriv n f) :=
  SKValue.heat_iteratedDeriv hf.smooth (fun n ↦ (hf.iteratedDeriv n).expGrowth) h n

lemma SmoothEvolution.burgers_jet_mild {T a b : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (hm : Measurable γ) (hγ : MonotoneOn γ (Icc (0 : ℝ) T))
    (hi : IntervalIntegrable γ volume 0 T) (ha : 0≤a) (hab : a≤b) (hb : b≤T) (m : ℕ) :
    iteratedDeriv (m+1) (deriv (V a)) =
      fun x ↦ deriv (heat (b-a) (iteratedDeriv m (deriv (V b)))) x+
        ∫ s in a..b, γ s*deriv (heat (s-a) (iteratedDeriv m
          (fun y ↦ deriv (V s) y*deriv (deriv (V s)) y))) x := by
  have haT : a∈Icc (0 : ℝ) T := ⟨ha,hab.trans hb⟩
  have hbT : b∈Icc (0 : ℝ) T := ⟨ha.trans hab,hb⟩
  have hiab : IntervalIntegrable γ volume a b := hi.mono_set (by
    simp only [uIcc_of_le hab,uIcc_of_le (ha.trans (hab.trans hb))]
    exact Icc_subset_Icc ha hb)
  have hF := h.gradient_family.mul h.gradient_family.deriv
  have hid : deriv (V a)=fun x ↦ heat (b-a) (deriv (V b)) x+
      duhamel a b γ (fun s y ↦ deriv (V s) y*deriv (deriv (V s)) y) x :=
    funext (h.burgers_mild hm hγ hi ha hab hb)
  have hdD (n : ℕ) : Differentiable ℝ (iteratedDeriv n
      (duhamel a b γ (fun s y ↦ deriv (V s) y*deriv (deriv (V s)) y))) := by
    rw [hF.duhamel_iteratedDeriv hiab ha hab hb]
    exact fun x ↦ ((hF.iteratedDeriv n).duhamel_hasDerivAt hiab ha hab hb x).differentiableAt
  have hcD : ContDiff ℝ ∞ (duhamel a b γ (fun s y ↦ deriv (V s) y*deriv (deriv (V s)) y)) :=
    (contDiff_iff_iteratedDeriv).mpr ⟨fun n _ ↦ (hdD n).continuous,fun n _ ↦ hdD n⟩
  have hfb := (h.slices b hbT).jets
  have hcH := SKValue.heat_contDiff hfb.smooth (fun n ↦ (hfb.iteratedDeriv n).expGrowth) (b-a)
  have horder := ENat.natCast_le_of_coe_top_le_withTop le_rfl (m+1)
  rw [hid]
  funext x
  rw [iteratedDeriv_fun_add (hcH.of_le horder).contDiffAt (hcD.of_le horder).contDiffAt]
  rw [hfb.heat_iteratedDeriv,hF.duhamel_iteratedDeriv hiab ha hab hb]
  rw [iteratedDeriv_succ,←(hfb.iteratedDeriv m).heat_deriv]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hab] at hs
  have hsT : s∈Icc (0 : ℝ) T := ⟨ha.trans hs.1,hs.2.trans hb⟩
  dsimp only
  rw [iteratedDeriv_succ,←((hF.slices s hsT).iteratedDeriv m).heat_deriv]

end SKValue

end

end OAI
