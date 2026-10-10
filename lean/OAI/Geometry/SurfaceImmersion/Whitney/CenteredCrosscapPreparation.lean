import OAI.Geometry.SurfaceImmersion.Whitney.QuadraticCrosscapPreparation

namespace OAI

/-! The local polynomial preparation centered at the actual chart
coordinate of a singular point. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def translatedSurface (f : Base → ProjectionTarget 3) (a : Base) : Base → ProjectionTarget 3 :=
  fun x => f (x+a)

def centeredSurfaceTaylor (f : Base → ProjectionTarget 3) (a : Base) (x : Base) : ProjectionTarget 3 :=
  surfaceTaylorTwo (translatedSurface f a) (x-a)

lemma surfaceDirection_translated (f : Base → ProjectionTarget 3) (a : Base)
    (b : Bool) (z : Base × ℝ) :
    surfaceDirection (translatedSurface f a) b z = surfaceDirection f b (z+(a,0)) := by
  unfold surfaceDirection translatedSurface
  rw [fderiv_comp_add_right]
  simp only [Prod.fst_add,Prod.snd_add,add_zero]

lemma surfaceDirection_translated_fderiv (f : Base → ProjectionTarget 3) (a : Base)
    (b : Bool) (z : Base × ℝ) :
    fderiv ℝ (surfaceDirection (translatedSurface f a) b) z =
      fderiv ℝ (surfaceDirection f b) (z+(a,0)) := by
  have he : surfaceDirection (translatedSurface f a) b =
      fun w => surfaceDirection f b (w+(a,0)) := funext (surfaceDirection_translated f a b)
  rw [he,fderiv_comp_add_right]

theorem centered_quadratic_crosscap_preparation {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (b : Bool) (a : Base) (t₀ : ℝ)
    (hzero : surfaceDirection f b (a,t₀) = 0)
    (hreg : Function.Bijective (fderiv ℝ (surfaceDirection f b) (a,t₀)))
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ (r : ℝ) (g : Base → ProjectionTarget 3), 0 < r ∧ r ≤ ρ ∧
      ContDiff ℝ ∞ g ∧ g =ᶠ[𝓝 a] centeredSurfaceTaylor f a ∧
      (∀ x, r ≤ ‖x-a‖ → g x = f x) ∧
      tsupport (g-f) ⊆ closedBall a (r/2) ∧
      ∀ x ∈ ball a r, (¬ Function.Injective (fderiv ℝ g x) ↔ x = a) := by
  have htrans : ContDiff ℝ ∞ (translatedSurface f a) := hf.comp (contDiff_id.add contDiff_const)
  have hzero' : surfaceDirection (translatedSurface f a) b (0,t₀) = 0 := by
    simpa only [surfaceDirection_translated,Prod.mk_add_mk,zero_add,add_zero] using hzero
  have hreg' : Function.Bijective (fderiv ℝ (surfaceDirection (translatedSurface f a) b) (0,t₀)) := by
    simpa only [surfaceDirection_translated_fderiv,Prod.mk_add_mk,zero_add,add_zero] using hreg
  obtain ⟨r,g,hr,hrρ,hg,he,hout,hsupp,hlocal⟩ :=
    quadratic_crosscap_preparation htrans b t₀ hzero' hreg' hρ
  refine ⟨r,(fun x => g (x-a)),hr,hrρ,hg.comp (contDiff_id.sub contDiff_const),?_,?_,?_,?_⟩
  · have ht : Tendsto (fun x : Base => x-a) (𝓝 a) (𝓝 0) := by
        have hc : Continuous (fun x : Base => x-a) := by fun_prop
        simpa only [sub_self] using hc.tendsto a
    exact he.comp_tendsto ht
  · intro x hx
    have h := hout (x-a) hx
    simpa only [translatedSurface,sub_add_cancel] using h
  · apply closure_minimal _ isClosed_closedBall
    intro x hx
    by_contra hn
    have hnot : x-a ∉ tsupport (g-translatedSurface f a) := by
      intro hm
      apply hn
      simpa only [mem_closedBall,dist_eq_norm,sub_zero] using hsupp hm
    have hz := image_eq_zero_of_notMem_tsupport hnot
    change g (x-a)-translatedSurface f a (x-a) = 0 at hz
    have hx' : g (x-a)-f x ≠ 0 := hx
    exact hx' (by simpa only [translatedSurface,sub_add_cancel] using hz)
  · intro x hx
    rw [fderiv_comp_sub]
    have h := hlocal (x-a) (by simpa only [mem_ball,dist_eq_norm,sub_zero] using hx)
    exact h.trans sub_eq_zero

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
