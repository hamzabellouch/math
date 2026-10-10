import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.BilinearClose

namespace OAI

section

noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport
section BilinearAbsorption
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance bilinearAbsorptionDualNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance bilinearAbsorptionDualNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance bilinearAbsorptionBilinearNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance bilinearAbsorptionBilinearNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

def covectorSquare (p:E →L[ℝ] ℝ) : E →L[ℝ] E →L[ℝ] ℝ :=
  p.smulRight p

lemma covectorSquare_apply (p:E →L[ℝ] ℝ) (d e:E) : covectorSquare p d e=p d*p e := rfl

lemma covectorSquare_continuous : Continuous (covectorSquare (E := E)) := by
  exact isBoundedBilinearMap_smulRight.continuous.comp (continuous_id.prodMk continuous_id)

lemma eventual_moving_rank_lower {ι:Type*} {l:Filter ι}
    {G R H:ι → E →L[ℝ] E →L[ℝ] ℝ} {G₀ R₀:E →L[ℝ] E →L[ℝ] ℝ}
    {A C δ:ℝ} (hA:0<A) (hδ:0<δ) (hG₀:∀d:E,δ*‖d‖^2≤G₀ d d)
    (hG:Tendsto G l (𝓝 G₀)) (hR:Tendsto R l (𝓝 R₀))
    (hH:∀ ε:ℝ,0<ε → ∀ᶠ k in l,∀d:E,
      A*G₀ d d+C*R₀ d d-ε*‖d‖^2≤H k d d) :
    ∀ᶠ k in l,∀d:E,A/2*G k d d+C*R k d d≤H k d d := by
  let ε := A*δ/4
  have he:0<ε := by dsimp [ε]; positivity
  have hlim : Tendsto (fun k=>(A/2) • G k+C • R k) l (𝓝 ((A/2) • G₀+C • R₀)) :=
    (hG.const_smul _).add (hR.const_smul _)
  have hn : ∀ᶠ k in l,‖((A/2) • G k+C • R k)-((A/2) • G₀+C • R₀)‖≤ε := by
    have ht := (hlim.sub_const ((A/2) • G₀+C • R₀)).norm
    simp only [sub_self,norm_zero] at ht
    exact (ht.eventually (gt_mem_nhds he)).mono (fun _ h=>h.le)
  filter_upwards [hn,hH ε he] with k hk hhk
  intro d
  have hb := bilinear_quadratic_close hk d
  simp only [add_apply,smul_apply,smul_eq_mul] at hb
  have hpos := mul_le_mul_of_nonneg_left (hG₀ d) (show 0≤A/2 by positivity)
  dsimp only [ε] at hb hhk
  nlinarith only [hb,hhk d,hpos]

end BilinearAbsorption
end WeakMTWTransport

end
end

end OAI
