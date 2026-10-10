import OAI.Analysis.LienardCycles.AxisZeros

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter Metric
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.RealAnalysis
lemma continuousOn_segment_integral {f : ℝ×ℝ → ℝ} {l r : ℝ}
    (hf : ContinuousOn f (Icc l r ×ˢ Icc 0 1)) :
    ContinuousOn (fun x=>∫ s : ℝ in (0:ℝ)..1,f (x,s)) (Icc l r) := by
  let F : Icc l r → ℝ → ℝ := fun x s=>f (x,projIcc 0 1 (by norm_num) s)
  have hF : Continuous F.uncurry := by
    apply hf.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk ((continuous_subtype_val.comp continuous_projIcc).comp continuous_snd))
    intro q
    exact ⟨q.1.property,(projIcc 0 1 (by norm_num) q.2).property⟩
  have hc := continuous_parametric_integral_of_continuous (μ:=MeasureTheory.volume) (s:=Icc (0:ℝ) 1) hF isCompact_Icc
  apply continuousOn_iff_continuous_domRestrict.mpr
  convert! hc using 1
  ext x
  change (∫ s : ℝ in (0:ℝ)..1,f ((x:ℝ),s))=∫ s : ℝ in Icc (0:ℝ) 1,F x s
  rw [intervalIntegral.integral_of_le (by norm_num)]
  rw [←MeasureTheory.integral_Icc_eq_integral_Ioc]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
  intro s hs
  simp only [F,projIcc_of_mem (by norm_num : (0:ℝ)≤1) hs]

lemma isolated_zero_count_linear {f a b q : ℝ → ℝ} {J : Set ℝ}
    (hJ : OrdConnected J) (ha : ∀ l ∈ J, ∀ r ∈ J, l≤r → ContinuousOn a (Icc l r))
    (hf : ∀ x ∈ J, HasDerivAt f (a x*f x+b x*q x) x)
    (hb : ∀ x ∈ J, 0<b x) (hq : MonotoneOn q J) :
    {x | IsIsolatedZeroOn f J x}.encard≤2 := by
  apply encard_le_two_of_no_three
  intro x hx y hy z hz hxy hyz
  have hsub := hJ.out hx.1 hz.1
  obtain ⟨w,hw,_,hd⟩ := ScalarComparison.weighted_deriv (E:=f) (F:=fun u=>b u*q u)
    (hxy.trans hyz).le ((ha x hx.1 z hz.1 (hxy.trans hyz).le).neg)
  have hd' (u : ℝ) (hu : u ∈ Icc x z) :
      HasDerivAt (fun u=>w u*f u) ((w u*b u)*q u) u := by
    have he : HasDerivAt f (-(-a u)*f u+b u*q u) u := by simpa using hf u (hsub hu)
    simpa only [mul_assoc] using hd u hu he
  have hIso : IsIsolatedZeroOn (fun u=>w u*f u) (Icc x z) y := by
    obtain ⟨_,hy0,ε,hε,he⟩ := hy
    refine ⟨⟨hxy.le,hyz.le⟩,by simp [hy0],ε,hε,?_⟩
    intro u hu huJ huz
    exact he u hu (hsub huJ) ((mul_eq_zero.mp huz).resolve_left (hw u).ne')
  exact middle_zero_not_isolated (ordConnected_Icc) hd' (fun u hu=>mul_pos (hw u) (hb u (hsub hu)))
    (hq.mono hsub) ⟨le_rfl,(hxy.trans hyz).le⟩ ⟨hxy.le,hyz.le⟩ ⟨(hxy.trans hyz).le,le_rfl⟩
    hxy hyz (by simp [hx.2.1]) (by simp [hy.2.1]) (by simp [hz.2.1]) hIso
end QuinticLienard.RealAnalysis

end OAI
