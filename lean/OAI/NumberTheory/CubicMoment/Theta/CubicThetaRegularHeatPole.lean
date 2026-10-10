import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRegularHeatLow
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRegularHeatHigh
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace OAI

/-! The scalar row Mellin transform has the exact pole supplied by the
four-dimensional affine lattice. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace CubicFirstMoment

def cubicThetaRegularHeatMass (p : ℂ × ℝ) (s : ℝ) : ℝ :=
  (∫ t in Ioc (0:ℝ) 1,cubicThetaRegularHeatLow p s t)+
    ∫ t in Ioi (1:ℝ),t^(s-1)*cubicThetaFullGaussian p t

lemma cubicThetaRegularHeatMass_tendsto {p : ℂ × ℝ} (hp : 0<p.2) :
    Tendsto (cubicThetaRegularHeatMass p) (𝓝[>] 2) (𝓝 (cubicThetaRegularHeatMass p 2)) :=
  (cubicThetaRegularHeatLow_integral_tendsto hp).add
    (cubicThetaRegularHeatHigh_integral_tendsto hp)

lemma cubicThetaHeatPole_integral {s : ℝ} (hs : 2<s) :
    (∫ t in Ioc (0:ℝ) 1,t^(s-3))=1/(s-2) := by
  rw [←intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
    integral_rpow (Or.inl (by linarith : -1<s-3))]
  rw [Real.one_rpow,Real.zero_rpow (by linarith : s-3+1≠0)]
  congr 1 <;> ring

lemma cubicThetaRegularHeatLow_integral_eq {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℝ} (hs : 2<s) :
    (∫ t in Ioc (0:ℝ) 1,cubicThetaRegularHeatLow p s t)=
      (∫ t in Ioc (0:ℝ) 1,t^(s-1)*cubicThetaFullGaussian p t)-
        (4*Real.pi^2/243)/(s-2) := by
  have hf : IntegrableOn (fun t : ℝ => t^(s-1)*cubicThetaFullGaussian p t) (Ioc 0 1) :=
    (cubicThetaFullGaussian_mellin_integrable hp hs).mono_set Ioc_subset_Ioi_self
  have hg : IntegrableOn (fun t : ℝ => (4*Real.pi^2/243)*t^(s-3)) (Ioc 0 1) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by norm_num : (0:ℝ)≤1)).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1<s-3))).const_mul _
  have he : ∀ t∈Ioc (0:ℝ) 1,cubicThetaRegularHeatLow p s t=
      t^(s-1)*cubicThetaFullGaussian p t-(4*Real.pi^2/243)*t^(s-3) := by
    intro t ht
    have ht0 := ht.1
    unfold cubicThetaRegularHeatLow
    have hpow : t^(s-1)/t^2=t^(s-3) := by
      rw [←Real.rpow_two,←Real.rpow_sub ht0]
      congr 1
      ring
    rw [mul_sub]
    congr 1
    calc
      _ = (4*Real.pi^2/243)*(t^(s-1)/t^2) := by ring
      _ = _ := by rw [hpow]
  rw [setIntegral_congr_fun measurableSet_Ioc he,integral_sub hf hg,
    integral_const_mul,cubicThetaHeatPole_integral hs]
  ring

theorem cubicThetaFullHeightMass_pole_identity {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℝ} (hs : 2<s) :
    Real.Gamma s*cubicThetaFullHeightMass p s=
      (4*Real.pi^2/243)/(s-2)+cubicThetaRegularHeatMass p s := by
  rw [←cubicThetaFullGaussian_mellin hp hs,←Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ)≤1),
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      ((cubicThetaFullGaussian_mellin_integrable hp hs).mono_set Ioc_subset_Ioi_self)
      ((cubicThetaFullGaussian_mellin_integrable hp hs).mono_set
        (Ioi_subset_Ioi (by norm_num : (0:ℝ)≤1)))]
  rw [cubicThetaRegularHeatMass,cubicThetaRegularHeatLow_integral_eq hp hs]
  ring

end CubicFirstMoment

end

end OAI
