import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.NormalInverseVecNorm

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace YauCounterexamples

lemma compact_normal_image_neighborhood
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K V : Set NormalWaveSpace} (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V) :
    ∃ r > 0, ∀ q ∈ metricFrameSet g K, ∀ x : Fin 3 → ℝ, ‖x‖ < r →
      normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2) (normalWaveEquiv x) ∈ V := by
  let F : NormalWaveParameter × (Fin 3 → ℝ) → NormalWaveSpace := fun w =>
    (normalFamilyTotal g (w.1,normalWaveEquiv w.2)).2
  have hF : Continuous F := ((normalFamilyTotal_smooth g).continuous.comp
    (continuous_fst.prodMk (normalWaveEquiv.continuous.comp continuous_snd))).snd
  have hprod : metricFrameSet g K ×ˢ ({0} : Set (Fin 3 → ℝ)) ⊆ F ⁻¹' V := by
    rintro ⟨q,x⟩ ⟨hq,hx⟩
    obtain rfl := Set.mem_singleton_iff.mp hx
    change normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2) (normalWaveEquiv 0) ∈ V
    rw [map_zero,normalJetMap_zero]
    exact hKV hq.1
  obtain ⟨U,W,hU,hW,hKU,h0W,hUW⟩ := generalized_tube_lemma (metricFrameSet_isCompact g hK)
    isCompact_singleton (hV.preimage hF) hprod
  obtain ⟨r,hr,hrW⟩ := Metric.isOpen_iff.mp hW 0 (h0W (mem_singleton 0))
  refine ⟨r,hr,?_⟩
  intro q hq x hx
  have hxW : x ∈ W := hrW (by simpa only [Metric.mem_ball,dist_zero_right] using hx)
  have ht : (q,x) ∈ F ⁻¹' V := hUW ⟨hKU hq,hxW⟩
  exact ht
end YauCounterexamples
end

end OAI
