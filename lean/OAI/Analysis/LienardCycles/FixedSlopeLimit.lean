import OAI.Analysis.LienardCycles.ActualCharacteristic

namespace OAI

universe uι

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter Metric
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.QuadraticFit
open QuadraticCoordinates
lemma slope_scaled {κ r m : ℝ} (hr : 0<r) (hm : |m|<r) :
    slope ((r^3*κ,1),m/r)=r*slope ((κ,r),m) := by
  have hmr : |m/r|<1 := by rw [abs_div,abs_of_pos hr]; exact (div_lt_one hr).mpr hm
  apply slope_eq (by norm_num) hmr
  have hh := scaling_width (slope ((κ,r),m)) κ hr (by norm_num : (0:ℝ)<1)
  rw [mul_one,slope_spec hr hm] at hh
  exact (eq_div_iff hr.ne').mpr (by simpa only [mul_comm] using hh.symm)
end QuinticLienard.QuadraticFit
namespace QuinticLienard.QuinticFit
open QuadraticFit
lemma fixed_slope_limit {a : Fin 6 → ℝ} {h₀ : ℝ} (hh₀ : 0<h₀) (κ : ℝ)
    {ι : Type uι} {l : Filter ι} {h r : ι → ℝ}
    (hh : Tendsto h l (𝓝 h₀)) (hr : Tendsto r l (𝓝 0)) (hp : ∀ᶠ z in l, 0<r z) :
    Tendsto (fun z => slope ((κ,r z),M a (h z,r z))) l (𝓝 (ScaledProfile.slope a h₀)) := by
  have hf := fit_limits (a:=a) hh₀ hh hr hp
  have hn := (normalized_limits (a:=a) hh₀ hh hr hp).1
  have hx : Tendsto (fun z => (((r z)^3*κ,(1:ℝ)),M a (h z,r z)/r z)) l (𝓝 (((0:ℝ),(1:ℝ)),0)) := by
    have h0 : Tendsto (fun z => (r z)^3*κ) l (𝓝 (0:ℝ)) := by simpa using ((hr.pow 3).mul_const κ)
    exact (h0.prodMk_nhds tendsto_const_nhds).prodMk_nhds hn
  have hy : Tendsto (fun z => (((r z)^3*kappa a (h z,r z),(1:ℝ)),M a (h z,r z)/r z)) l (𝓝 (((0:ℝ),(1:ℝ)),0)) := by
    have h0 : Tendsto (fun z => (r z)^3*kappa a (h z,r z)) l (𝓝 (0:ℝ)) := by simpa using ((hr.pow 3).mul hf.2)
    exact (h0.prodMk_nhds tendsto_const_nhds).prodMk_nhds hn
  obtain ⟨K,U,hU,hLip⟩ := ((slope_analytic (k:=0) (by norm_num : (0:ℝ)<1) (by norm_num : |(0:ℝ)|<1)).of_le (by simp : (1:WithTop ℕ∞)≤ω)).exists_lipschitzOnWith
  have hbound : ∀ᶠ z in l,
      |slope ((κ,r z),M a (h z,r z))-lambda a (h z,r z)| ≤
        K*(r z)^2*|κ-kappa a (h z,r z)| := by
    filter_upwards [hp,hh.eventually (eventually_gt_nhds hh₀),hx.eventually hU,hy.eventually hU] with z hz hhz hxz hyz
    have hl := hLip.dist_le_mul _ hxz _ hyz
    have hm := M_abs_lt a hhz hz
    have hs : slope ((kappa a (h z,r z),r z),M a (h z,r z))=lambda a (h z,r z) :=
      slope_eq hz hm (spec a hhz hz).1
    rw [slope_scaled hz hm,slope_scaled hz hm,hs] at hl
    simp only [Prod.dist_eq,dist_self,Real.dist_eq] at hl
    simp only [max_eq_left (abs_nonneg (r z^3*κ-r z^3*kappa a (h z,r z)))] at hl
    rw [←mul_sub,abs_mul,abs_of_pos hz] at hl
    have hd : |r z^3*κ-r z^3*kappa a (h z,r z)|=(r z)^3*|κ-kappa a (h z,r z)| := by
      rw [←mul_sub,abs_mul,abs_of_pos (pow_pos hz 3)]
    rw [hd] at hl
    apply (mul_le_mul_iff_right₀ hz).mp
    nlinarith [hl]
  have hb : Tendsto (fun z => (K:ℝ)*(r z)^2*|κ-kappa a (h z,r z)|) l (𝓝 0) := by
    simpa using ((hr.pow 2).const_mul (K:ℝ)).mul ((tendsto_const_nhds.sub hf.2).abs)
  have he : Tendsto (fun z => slope ((κ,r z),M a (h z,r z))-lambda a (h z,r z)) l (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) hbound hb)
  simpa only [sub_add_cancel,zero_add] using he.add hf.1
end QuinticLienard.QuinticFit

end OAI
