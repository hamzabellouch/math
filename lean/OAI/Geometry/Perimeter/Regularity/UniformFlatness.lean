import OAI.Geometry.Perimeter.Regularity.IsometricMinimizer
import OAI.Geometry.Perimeter.Regularity.FlatnessImprovement

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

theorem FullSlab.isometric_preimage {E : Set (Euc n)} {v : Euc n} {R a : ℝ}
    (h : FullSlab E v R a) (e : Euc n ≃ₗᵢ[ℝ] Euc n) :
    FullSlab (e ⁻¹' E) (e.symm v) R a := by
  have hi (x : Euc n) : inner ℝ (e.symm v) x=inner ℝ v (e x) := by
    exact (e.inner_map_map (e.symm v) x).symm.trans (by rw [e.apply_symm_apply])
  refine ⟨?_,?_⟩
  · intro x hx
    rw [perimeterSupport_isometric_preimage] at hx
    rw [hi]
    apply h.1 (e x) ⟨hx.1,?_⟩
    simpa only [Metric.mem_ball,dist_zero_right,e.norm_map] using hx.2
  · have hh := e.measurePreserving.quasiMeasurePreserving.ae h.2
    filter_upwards [hh] with x hx
    intro hxb hxa
    rw [hi] at hxa ⊢
    exact hx (by simpa only [Metric.mem_ball,dist_zero_right,e.norm_map] using hxb) hxa

theorem exists_uniform_normal_height_improvement (hn : 1 < n)
    {v₀ : Euc n} (hv₀ : ‖v₀‖=1)
    (hH : IsLocallyPerimeterMinimizing {x : Euc n | inner ℝ x v₀ < 0}) :
    ∃ K B : ℝ, 0 < K ∧ 0 ≤ B ∧ ∀ r : ℝ, 0 < r → r < 1/8 →
      ∃ δ : ℝ, 0 < δ ∧ ∀ (v : Euc n), ‖v‖=1 →
        ∀ (E : Set (Euc n)), IsLocallyPerimeterMinimizing E →
          (0:Euc n)∈perimeterSupport E → ∀ a : ℝ, 0 < a → a < δ → FullSlab E v 8 a →
            ∃ w : Euc n, ‖w‖=1 ∧ ‖w-v‖≤2*a*B ∧
              ∀ x∈perimeterSupport E ∩ Metric.ball 0 r, |inner ℝ w x|≤a*K*r^2 := by
  obtain ⟨K,B,hK,hB,himp⟩ := exists_fixed_normal_improvement_constants n hn
  refine ⟨K,B,hK,hB,fun r hr hr8 ↦ ?_⟩
  obtain ⟨δ,hδ,hd⟩ := himp v₀ hv₀ hH r hr hr8
  refine ⟨δ,hδ,fun v hv E hmin hzero a ha haδ hs ↦ ?_⟩
  obtain ⟨e,he⟩ := exists_normal_rotation (hv₀.trans hv.symm)
  have hpre := hs.isometric_preimage e
  have hve : e.symm v=v₀ := by rw [← he,e.symm_apply_apply]
  rw [hve] at hpre
  have hz : (0:Euc n)∈perimeterSupport (e ⁻¹' E) := by
    rw [perimeterSupport_isometric_preimage]
    simpa only [mem_preimage,map_zero] using hzero
  obtain ⟨L,hLv,hLB,hflat⟩ := hd (e ⁻¹' E)
    (locally_minimizing_isometric_preimage e hmin) hz a ha haδ hpre
  obtain ⟨w₀,hw₀,hwd,hwflat⟩ := exists_adjusted_unit_normal hv₀ L hLv ha.le
  refine ⟨e w₀,by simpa only [e.norm_map] using hw₀,?_,?_⟩
  · rw [← he,← map_sub,e.norm_map]
    exact hwd.trans (mul_le_mul_of_nonneg_left hLB (by positivity))
  · intro x hx
    have hx' : e.symm x∈perimeterSupport (e ⁻¹' E) ∩ Metric.ball 0 r := by
      rw [perimeterSupport_isometric_preimage]
      exact ⟨by simpa only [mem_preimage,e.apply_symm_apply] using hx.1,
        by simpa only [Metric.mem_ball,dist_zero_right,e.symm.norm_map] using hx.2⟩
    have hh := (hwflat (e.symm x)).trans (hflat (e.symm x) hx')
    have hi : inner ℝ (e w₀) x=inner ℝ w₀ (e.symm x) := by
      exact e.inner_map_eq_flip w₀ x
    simpa only [hi] using hh

end RPISingularHarnack

end

end OAI
