import OAI.MeasureTheory.Falconer.Geometry.SimilarityGeometry
import OAI.MeasureTheory.Falconer.Measures.StartingMeasures

namespace OAI

/-! # Original measure and radial-cap transport under a common similarity -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal

variable {d : ℕ}

theorem homeomorph_support_map_subset (f : Space d ≃ₜ Space d)
    (μ : Measure (Space d)) : (μ.map f).support ⊆ f '' μ.support := by
  apply Measure.support_subset_of_isClosed (f.isClosedMap _ Measure.isClosed_support)
  change (μ.map f) (f '' μ.support)ᶜ = 0
  rw [f.measurableEmbedding.map_apply]
  simpa only [preimage_compl,f.injective.preimage_image] using μ.measure_compl_support

@[simp] theorem pairHomeomorph_mem_image (f : Space d ≃ₜ Space d)
    (G : Set (Space d × Space d)) (x y : Space d) :
    (f x,f y) ∈ pairHomeomorph f '' G ↔ (x,y) ∈ G :=
  (pairHomeomorph f).injective.mem_set_image (s := G) (a := (x,y))

theorem homeomorph_pair_measure_image (f : Space d ≃ₜ Space d)
    (μ ν : Measure (Space d)) [SFinite μ] [SFinite ν] (G : Set (Space d × Space d)) :
    ((μ.map f).prod (ν.map f)) (pairHomeomorph f '' G) = (μ.prod ν) G := by
  rw [Measure.map_prod_map μ ν f.continuous.measurable f.continuous.measurable]
  change ((μ.prod ν).map (pairHomeomorph f)) (pairHomeomorph f '' G) = _
  rw [(pairHomeomorph f).measurableEmbedding.map_apply,
    (pairHomeomorph f).injective.preimage_image]

theorem scaledIsometry_frostman (e : Space d ≃ₗᵢ[ℝ] Space d) (a : ℝ) (ha : 0 < a)
    (μ : Measure (Space d)) {s C : ℝ} (hf : FrostmanBallBound μ s C) :
    FrostmanBallBound (μ.map (scaledIsometry e a ha)) s (C/a^s) := by
  intro x r hr
  rw [Measure.map_apply (scaledIsometry e a ha).continuous.measurable measurableSet_ball,
    scaledIsometry_ball_preimage]
  apply (hf _ (r/a) (by positivity)).trans_eq
  congr 1
  rw [Real.div_rpow hr.le ha.le]
  ring

theorem scaledIsometry_radial_dist (e : Space d ≃ₗᵢ[ℝ] Space d)
    (a : ℝ) (ha : 0 < a) (x y w : Space d) :
    dist (radialDirection (scaledIsometry e a ha x) (scaledIsometry e a ha y)) w =
      dist (radialDirection x y) (e.symm w) := by
  rw [scaledIsometry_radial]
  calc
    _ = dist (e (radialDirection x y)) (e (e.symm w)) := by rw [e.apply_symm_apply]
    _ = _ := e.dist_map _ _

theorem RadialCapBound.scaledIsometry (e : Space d ≃ₗᵢ[ℝ] Space d)
    (a : ℝ) (ha : 0 < a) {μ ν : ProbabilityMeasure (Space d)}
    {G : Set (Space d × Space d)} {N : ℕ} {loss q : ℝ}
    (h : RadialCapBound μ ν G N loss q) :
    RadialCapBound (μ.map (scaledIsometry e a ha)) (ν.map (scaledIsometry e a ha))
      (pairHomeomorph (scaledIsometry e a ha) '' G) N loss q := by
  let f := Falconer.scaledIsometry e a ha
  constructor
  · intro x hx w hw u hu hu1
    obtain ⟨x,hxs,rfl⟩ := homeomorph_support_map_subset f (μ : Measure _) hx
    change ((ν : Measure _).map f) _ ≤ _
    rw [f.measurableEmbedding.map_apply]
    have he : f ⁻¹' {y | (f x,y) ∈ pairHomeomorph f '' G ∧
        dist (radialDirection (f x) y) w < u} =
        {y | (x,y) ∈ G ∧ dist (radialDirection x y) (e.symm w) < u} := by
      ext y
      simp only [mem_preimage,mem_ofPred_eq,pairHomeomorph_mem_image]
      rw [scaledIsometry_radial_dist]
    rw [he]
    exact h.1 x hxs (e.symm w) (by simpa only [e.symm.norm_map] using hw) u hu hu1
  · intro y hy w hw u hu hu1
    obtain ⟨y,hys,rfl⟩ := homeomorph_support_map_subset f (ν : Measure _) hy
    change ((μ : Measure _).map f) _ ≤ _
    rw [f.measurableEmbedding.map_apply]
    have he : f ⁻¹' {x | (x,f y) ∈ pairHomeomorph f '' G ∧
        dist (radialDirection (f y) x) w < u} =
        {x | (x,y) ∈ G ∧ dist (radialDirection y x) (e.symm w) < u} := by
      ext x
      simp only [mem_preimage,mem_ofPred_eq,pairHomeomorph_mem_image]
      rw [scaledIsometry_radial_dist]
    rw [he]
    exact h.2 y hys (e.symm w) (by simpa only [e.symm.norm_map] using hw) u hu hu1

theorem CapAvailable.scaledIsometry (e : Space d ≃ₗᵢ[ℝ] Space d)
    (a : ℝ) (ha : 0 < a) {μ ν : ProbabilityMeasure (Space d)}
    {Γ : ℕ → Set (Space d × Space d)} {q : ℝ} (h : CapAvailable μ ν Γ q) :
    CapAvailable (μ.map (scaledIsometry e a ha)) (ν.map (scaledIsometry e a ha))
      (fun N => pairHomeomorph (scaledIsometry e a ha) '' Γ N) q := by
  let f := Falconer.scaledIsometry e a ha
  let F := pairHomeomorph f
  intro loss hloss
  obtain ⟨c,C,hc,hC,K,hK⟩ := h loss hloss
  refine ⟨c,C,hc,hC,K,?_⟩
  intro N hN
  obtain ⟨B,hB,hsub,hmass,hcap⟩ := hK N hN
  refine ⟨F '' B,F.measurableEmbedding.measurableSet_image.mpr hB,
    Set.image_mono hsub,?_,?_⟩
  · exact (homeomorph_pair_measure_image f (μ : Measure _) (ν : Measure _) B).le.trans hmass
  · have he : F '' Γ N \ F '' B = F '' (Γ N \ B) := by
      ext z
      obtain ⟨z,rfl⟩ := F.surjective z
      simp only [mem_sdiff,F.injective.mem_set_image]
    rw [he]
    exact hcap.scaledIsometry e a ha

end Falconer

end OAI
