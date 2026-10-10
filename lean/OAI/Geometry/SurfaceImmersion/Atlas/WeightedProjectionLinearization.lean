import OAI.Geometry.SurfaceImmersion.Geometry.TangentSlopeLinearization

namespace OAI

/-! Positive scalar weights do not alter the crosscap linearization at a
projection kernel, except by the same nonzero scalar factor. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {n : ℕ}

lemma weightedJet_product_germ {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {w : Base → ℝ} {F l : Base → V} {x : Base}
    (hw : ContDiff ℝ ∞ w) (hF : ContDiff ℝ ∞ F)
    (he : l =ᶠ[𝓝 x] fun y => w y • F y) :
    weightedJet w l =ᶠ[𝓝 x] fun y => (w y)^2 • fderiv ℝ F y := by
  filter_upwards [he.eventuallyEq_nhds] with y hy
  exact weightedJet_eq_smul (hw.differentiable (by simp) y)
    (hF.differentiable (by simp) y) hy

lemma directionJetLinearization_congr_germ
    {H K : Base → Base →L[ℝ] ProjectionTarget n × ℝ}
    {x : Base} (he : H =ᶠ[𝓝 x] K) (b : Bool) (t : ℝ) :
    directionJetLinearization H b (x,t) = directionJetLinearization K b (x,t) := by
  unfold directionJetLinearization
  rw [he.self_of_nhds,he.fderiv_eq]

lemma projected_directionJet_scaled
    {H : Base → Base →L[ℝ] ProjectionTarget n × ℝ} {w : Base → ℝ}
    (hH : ContDiff ℝ ∞ H) (hw : ContDiff ℝ ∞ w)
    (a : ProjectionTarget n) (b : Bool) (x : Base) (t : ℝ)
    (hker : graphProjection a (H x (tangentRay b t)) = 0) :
    (graphProjection a).comp (directionJetLinearization (fun y => w y • H y) b (x,t)) =
      w x • (graphProjection a).comp (directionJetLinearization H b (x,t)) := by
  apply ContinuousLinearMap.ext
  intro z
  have hd : fderiv ℝ (fun y => w y • H y) x =
      w x • fderiv ℝ H x + (fderiv ℝ w x).smulRight (H x) :=
    ((hw.differentiable (by simp) x).hasFDerivAt.smul
      (hH.differentiable (by simp) x).hasFDerivAt).fderiv
  simp only [ContinuousLinearMap.comp_apply,directionJetLinearization_apply,hd,
    smul_apply,add_apply,ContinuousLinearMap.smulRight_apply,
    map_add,map_smul,smul_add,smul_smul,hker,smul_zero,add_zero]
  rw [mul_comm z.2 (w x)]

theorem regular_weighted_directionJet
    {H : Base → Base →L[ℝ] ProjectionTarget 3 × ℝ} {w : Base → ℝ}
    {K : Base → Base →L[ℝ] ProjectionTarget 3 × ℝ}
    (hH : ContDiff ℝ ∞ H) (hw : ContDiff ℝ ∞ w)
    (a : ProjectionTarget 3) (b : Bool) (x : Base) (t : ℝ)
    (hw0 : w x ≠ 0) (he : K =ᶠ[𝓝 x] fun y => w y • H y)
    (hker : graphProjection a (H x (tangentRay b t)) = 0)
    (hbij : Function.Bijective ((graphProjection a).comp (directionJetLinearization K b (x,t)))) :
    Function.Bijective ((graphProjection a).comp (directionJetLinearization H b (x,t))) := by
  rw [directionJetLinearization_congr_germ he b t,
    projected_directionJet_scaled hH hw a b x t hker] at hbij
  constructor
  · intro v u h
    apply hbij.1
    exact congrArg (w x • ·) h
  · intro y
    obtain ⟨v,hv⟩ := hbij.2 (w x • y)
    exact ⟨v,(smul_right_injective _ hw0) hv⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
