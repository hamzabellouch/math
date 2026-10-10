import OAI.Geometry.SurfaceImmersion.Atlas.SurfaceCoordinateTranslation
import OAI.Geometry.SurfaceImmersion.Geometry.CompactTranslationStability

namespace OAI

/-! A compact set of regular surface double pairs stays regular under a
small scalar-weighted translation, inside fixed coordinate patches. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

theorem surface_chart_pair_stability (p q : M)
    {f : M → ProjectionTarget 3} {χ : M → ℝ}
    {F G : Base → ProjectionTarget 3} {ρ σ : Base → ℝ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hρ : ContDiff ℝ ∞ ρ) (hσ : ContDiff ℝ ∞ σ)
    {U V : Set M} (hU : IsOpen U) (hV : IsOpen V)
    (hUp : U ⊆ (chart p).source) (hVq : V ⊆ (chart q).source)
    (heF : EqOn f (F ∘ chart p) U) (heG : EqOn f (G ∘ chart q) V)
    (heρ : EqOn χ (ρ ∘ chart p) U) (heσ : EqOn χ (σ ∘ chart q) V)
    {K : Set (M × M)} (hK : IsCompact K) (hKU : K ⊆ U ×ˢ V)
    (hreg : ∀ z ∈ K, f z.1 = f z.2 → Function.Surjective (surfacePairDerivative f z.1 z.2)) :
    ∃ δ > 0, ∀ a : ProjectionTarget 3, ‖a‖ < δ → ∀ z ∈ K,
      surfaceTranslation f χ a z.1 = surfaceTranslation f χ a z.2 →
      Function.Surjective (surfacePairDerivative (surfaceTranslation f χ a) z.1 z.2) := by
  let κ : M × M → Base × Base := fun z => (chart p z.1,chart q z.2)
  let D : Base × Base → ProjectionTarget 3 := fun z => F z.1-G z.2
  let c : Base × Base → ℝ := fun z => ρ z.1-σ z.2
  have hDc : ContDiff ℝ ∞ D := (hF.comp contDiff_fst).sub (hG.comp contDiff_snd)
  have hcc : ContDiff ℝ ∞ c := (hρ.comp contDiff_fst).sub (hσ.comp contDiff_snd)
  have hκ : ContinuousOn κ K := by
    intro z hz
    exact (((chart p).continuousAt (hUp (hKU hz).1)).comp continuous_fst.continuousAt).prodMk
      (((chart q).continuousAt (hVq (hKU hz).2)).comp continuous_snd.continuousAt) |>.continuousWithinAt
  have hKc : IsCompact (κ '' K) := hK.image_of_continuousOn hκ
  have hregc : ∀ w ∈ κ '' K, D w = 0 → Function.Surjective (fderiv ℝ D w) := by
    rintro w ⟨z,hz,rfl⟩ hw
    have hzU := (hKU hz).1
    have hzV := (hKU hz).2
    have hv : f z.1 = f z.2 := by
      rw [heF hzU,heG hzV]
      exact sub_eq_zero.mp hw
    exact (surface_pair_coordinate_regular_iff p q (hUp hzU) (hVq hzV) hF hG
      (heF.eventuallyEq_of_mem (hU.mem_nhds hzU))
      (heG.eventuallyEq_of_mem (hV.mem_nhds hzV))).mp (hreg z hz hv)
  obtain ⟨δ,hδ,hstable⟩ := compact_translation_stability hDc hcc hKc hregc
  refine ⟨δ,hδ,?_⟩
  intro a ha z hz hval
  have hzU := (hKU hz).1
  have hzV := (hKU hz).2
  apply (surface_pair_translation_coordinate_iff p q (hUp hzU) (hVq hzV) hF hG hρ hσ
    (heF.eventuallyEq_of_mem (hU.mem_nhds hzU))
    (heG.eventuallyEq_of_mem (hV.mem_nhds hzV))
    (heρ.eventuallyEq_of_mem (hU.mem_nhds hzU))
    (heσ.eventuallyEq_of_mem (hV.mem_nhds hzV)) a).mpr
  apply hstable a ha (κ z) ⟨z,hz,rfl⟩
  change (F (chart p z.1)-G (chart q z.2))+(ρ (chart p z.1)-σ (chart q z.2)) • a = 0
  have hf1 := heF hzU
  have hf2 := heG hzV
  have hχ1 := heρ hzU
  have hχ2 := heσ hzV
  change f z.1+χ z.1 • a = f z.2+χ z.2 • a at hval
  rw [hf1,hf2,hχ1,hχ2] at hval
  rw [sub_smul]
  calc
    _ = (F (chart p z.1)+ρ (chart p z.1) • a)-
      (G (chart q z.2)+σ (chart q z.2) • a) := by abel
    _ = 0 := sub_eq_zero.mpr hval

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
