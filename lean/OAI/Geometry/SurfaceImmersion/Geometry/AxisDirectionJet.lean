import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapSecondDerivative
import OAI.Geometry.SurfaceImmersion.Geometry.SurfaceDirectionBlock

namespace OAI

/-! The derivative-direction jet with the longitudinal vector in the kernel. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def axisDirectionJet (f : Base → V) (p : Base) : (Base × ℝ) →L[ℝ] V :=
  (fderiv ℝ f p).comp ((ContinuousLinearMap.snd ℝ Base ℝ).smulRight (![1,0] : Base)) +
    ((fderiv ℝ (fderiv ℝ f) p).comp (ContinuousLinearMap.fst ℝ Base ℝ)).flip (![0,1] : Base)

lemma axisDirectionJet_apply (f : Base → V) (p : Base) (z : Base × ℝ) :
    axisDirectionJet f p z = z.2 • fderiv ℝ f p (![1,0] : Base) +
      fderiv ℝ (fderiv ℝ f) p z.1 (![0,1] : Base) := by
  change fderiv ℝ f p (z.2 • (![1,0] : Base)) +
    fderiv ℝ (fderiv ℝ f) p z.1 (![0,1] : Base) = _
  rw [map_smul]

lemma axisDirectionJet_surfaceDirection {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (p : Base) :
    fderiv ℝ (surfaceDirection f true) (p,0) = axisDirectionJet f p := by
  rw [(surfaceDirection_hasFDerivAt hf true (p,0)).fderiv]
  apply ContinuousLinearMap.ext
  intro z
  simp [surfaceDirectionLinearization,axisDirectionJet,tangentRay,tangentRayVelocity]

lemma axisDirectionJet_postcompose {f : Base → V} {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] {g : V → W} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (p : Base) (hz : fderiv ℝ f p (![0,1] : Base) = 0) :
    axisDirectionJet (g ∘ f) p = (fderiv ℝ g (f p)).comp (axisDirectionJet f p) := by
  apply ContinuousLinearMap.ext
  intro z
  rw [axisDirectionJet_apply,ContinuousLinearMap.comp_apply,axisDirectionJet_apply,
    kernel_secondDerivative_comp hf isOpen_univ hg.contDiffOn (mem_univ _) _ _ hz,
    fderiv_comp p (hg.differentiable (by simp) _) (hf.differentiable (by simp) p)]
  simp

lemma bijective_base_vertical_columns (L : Base →L[ℝ] Base)
    (hL : Function.Bijective L) (hz : L (![0,1] : Base) 0 = 0) :
    L (![0,1] : Base) 1 ≠ 0 ∧ L (![1,0] : Base) 0 ≠ 0 := by
  have hcol : ∀ x : Base, L x = (x 0) • L (![1,0] : Base) + (x 1) • L (![0,1] : Base) := by
    intro x
    have he : x = (x 0) • (![1,0] : Base) + (x 1) • (![0,1] : Base) := by
      ext i; fin_cases i <;> simp
    conv_lhs => rw [he]
    rw [map_add,map_smul,map_smul]
  constructor
  · intro hn
    have he : L (![0,1] : Base) = L 0 := by
      rw [map_zero]
      ext i
      fin_cases i
      · exact hz
      · exact hn
    have hh := congrFun (hL.1 he) 1
    norm_num at hh
  · intro hn
    obtain ⟨x,hx⟩ := hL.2 (![1,0] : Base)
    have h0 := congrFun hx 0
    rw [hcol] at h0
    simp [hn,hz] at h0

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
