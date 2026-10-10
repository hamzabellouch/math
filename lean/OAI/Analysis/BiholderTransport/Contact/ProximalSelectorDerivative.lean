import Mathlib
import OAI.Analysis.BiholderTransport.Contact.SubgradientDifferential

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma semiconvex_subgradient_along_selector {f : E → ℝ} {Y ξ : E → E}
    {x p : E} {A R : E →L[ℝ] E}
    (hA : ∀ v w, inner ℝ (A v) w=inner ℝ v (A w))
    (hexp : HasQuadraticExpansion (fun h => f (Y x+h)) p A)
    {r : ℝ} (hr : 0 < r) (K : ℝ) (hY : HasFDerivAt Y R x)
    (hξ : ξ x=p)
    (hg : ∀ᶠ z in 𝓝 x,
      IsSemiconvexSubgradientOn f (Metric.ball (Y x) r) K (Y z) (ξ z)) :
    HasFDerivAt ξ (A.comp R) x := by
  obtain ⟨C,hC,hCb⟩ := hY.isBigO_sub.exists_pos
  have hs : (fun z => ξ z-p-A (Y z-Y x)) =o[𝓝 x] (fun z => z-x) := by
    rw [Asymptotics.isLittleO_iff]
    intro eps heps
    obtain ⟨d,hd,H⟩ := semiconvex_subgradient_uniform_differential hA hexp hr K
      (eps/C) (div_pos heps hC)
    have hn : ∀ᶠ z in 𝓝 x, ‖Y z-Y x‖ < d := by
      simpa only [Metric.mem_ball,dist_eq_norm] using
        hY.continuousAt.eventually (Metric.ball_mem_nhds (Y x) hd)
    filter_upwards [hg,hCb.bound,hn] with z hz hbound hnear
    have HH := H (Y z-Y x) (ξ z) hnear (by
      intro w hw
      have hw' : Y x+w∈Metric.ball (Y x) r := by
        simpa only [Metric.mem_ball,dist_eq_norm,add_sub_cancel_left,sub_zero] using hw
      have hh := hz (Y x+w) hw'
      simpa only [add_sub_cancel,show w-(Y z-Y x)=Y x+w-Y z by abel] using hh)
    calc
      ‖ξ z-p-A (Y z-Y x)‖ ≤ (eps/C)*‖Y z-Y x‖ := HH
      _ ≤ (eps/C)*(C*‖z-x‖) := mul_le_mul_of_nonneg_left hbound (div_nonneg heps.le hC.le)
      _ = eps*‖z-x‖ := by field_simp
  have ha := A.hasFDerivAt.comp x hY
  rw [hasFDerivAt_iff_isLittleO] at ha ⊢
  convert hs.add ha using 1
  first
  | rfl
  | (ext z
     simp only [Function.comp_def,ContinuousLinearMap.comp_apply,map_sub,hξ]
     abel)
end WeakMTWTransport

end

end OAI
