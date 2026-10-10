import OAI.Geometry.SurfaceImmersion.Whitney.StandardCrosscapDerivative
import OAI.Geometry.SurfaceImmersion.Correction.NormalizedJetCorrection

namespace OAI

/-! The exact second derivative of the standard crosscap and the chain
rule in a kernel direction. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma standardCrosscapDerivative_zero_apply (v : Base) :
    standardCrosscapDerivative 0 v = ((0:Base),v 0) := by
  apply Prod.ext
  · ext i
    fin_cases i <;> simp [standardCrosscapDerivative]
  · simp [standardCrosscapDerivative]

lemma standardCrosscap_second (p v w : Base) :
    fderiv ℝ (fderiv ℝ standardCrosscap) p v w =
      (![v 1*w 0+v 0*w 1,2*v 1*w 1],(0:ℝ)) := by
  have he : (fun x => fderiv ℝ standardCrosscap x w) =
      fun x : Base => (x 1*w 0+x 0*w 1) • ((![1,0],0) : Base × ℝ) +
        (2*x 1*w 1) • ((![0,1],0) : Base × ℝ) + ((0,w 0) : Base × ℝ) := by
    funext x
    rw [(standardCrosscap_hasFDerivAt x).fderiv]
    apply Prod.ext
    · ext i
      fin_cases i <;> simp [standardCrosscapDerivative]
    · simp [standardCrosscapDerivative]
  have h0 := hasFDerivAt_apply (𝕜 := ℝ) (0:Fin 2) p
  have h1 := hasFDerivAt_apply (𝕜 := ℝ) (1:Fin 2) p
  have hd := ((((h1.mul_const (w 0)).add (h0.mul_const (w 1))).smul_const
    ((![1,0],0) : Base × ℝ)).add
      (((h1.const_mul 2).mul_const (w 1)).smul_const ((![0,1],0) : Base × ℝ))).add_const
        ((0,w 0) : Base × ℝ)
  change HasFDerivAt (fun x : Base => (x 1*w 0+x 0*w 1) • ((![1,0],0) : Base × ℝ) +
    (2*x 1*w 1) • ((![0,1],0) : Base × ℝ) + ((0,w 0) : Base × ℝ)) _ p at hd
  rw [← SphericalJets.secondDerivative_apply standardCrosscap_smooth.contDiffAt v w,he,hd.fderiv]
  apply Prod.ext
  · ext i
    fin_cases i <;> simp <;> ring
  · simp

lemma kernel_secondDerivative_comp {E H Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {f : E → H} {g : H → Z} (hf : ContDiff ℝ ∞ f) {U : Set H}
    (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) {p : E} (hp : f p ∈ U)
    (v w : E) (hw : fderiv ℝ f p w = 0) :
    fderiv ℝ (fderiv ℝ (g ∘ f)) p v w =
      fderiv ℝ g (f p) (fderiv ℝ (fderiv ℝ f) p v w) := by
  rw [SphericalJets.secondDerivative_comp hf hU hg hp v w,hw,map_zero,zero_add]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
