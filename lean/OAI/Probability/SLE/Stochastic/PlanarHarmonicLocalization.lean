import OAI.Probability.SLE.Stochastic.PlanarOptional
import OAI.Probability.SLE.Geometry.CompactSmoothExtension

namespace OAI

/-! Compact localization of harmonic tests uses actual stopped planar
Wiener paths, retaining the original two-coordinate filtration. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open Target

lemma planarGenerator_congr_germ {f g : ℝ×ℝ → ℝ} {z : ℝ×ℝ}
    (h : f =ᶠ[𝓝 z] g) : planarGenerator f z=planarGenerator g z := by
  have hx : (fun x => f (x,z.2)) =ᶠ[𝓝 z.1] (fun x => g (x,z.2)) :=
    h.comp_tendsto (continuous_id.prodMk continuous_const).continuousAt.tendsto
  have hy : (fun y => f (z.1,y)) =ᶠ[𝓝 z.2] (fun y => g (z.1,y)) :=
    h.comp_tendsto (continuous_const.prodMk continuous_id).continuousAt.tendsto
  unfold planarGenerator
  rw [hx.iteratedDeriv_eq 2,hy.iteratedDeriv_eq 2]

theorem planar_local_harmonic_optional
    (W : WienerLaw) (hW : IsWiener W) (U K : Set (ℝ×ℝ))
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (u : ℝ×ℝ → ℝ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U)
    (hhar : ∀ z∈U, planarGenerator u z=0)
    (τ : Driver×Driver → ℝ≥0)
    (hτ : IsStoppingTime planarWienerFiltration (fun b => (τ b : WithTop ℝ≥0)))
    (T : ℝ≥0) (hb : ∀ b, τ b ≤ T)
    (hpath : ∀ b t, t ≤ τ b → planarWiener t b∈K) :
    (∫ b, u (planarWiener (τ b) b) ∂W.prod W)=∫ b, u (planarWiener 0 b) ∂W.prod W := by
  obtain ⟨f,hf,hfc,_,he,_,_⟩ := exists_compact_smooth_extension U K hU hK hKU u hu
  have hzero (b : Driver×Driver) (v : ℝ) (hv : 0 ≤ v) (hvτ : v<(τ b:ℝ)) :
      planarGenerator f (planarWiener v.toNNReal b)=0 := by
    have ht : v.toNNReal ≤ τ b := (Real.toNNReal_le_iff_le_coe).mpr hvτ.le
    have hz := hpath b v.toNNReal ht
    rw [planarGenerator_congr_germ (he _ hz)]
    exact hhar _ (hKU hz)
  have hh := planar_compact_optional W hW f hf hfc τ hτ T hb hzero
  have ht (b) : f (planarWiener (τ b) b)=u (planarWiener (τ b) b) :=
    (he _ (hpath b (τ b) le_rfl)).self_of_nhds
  have h0 (b) : f (planarWiener 0 b)=u (planarWiener 0 b) :=
    (he _ (hpath b 0 zero_le)).self_of_nhds
  simpa only [ht,h0] using hh

end SLEExactGauge

end

end OAI
