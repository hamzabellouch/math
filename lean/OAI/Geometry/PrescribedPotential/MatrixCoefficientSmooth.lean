import Mathlib
import OAI.Geometry.PrescribedPotential.MatrixHilbertCoordinates

namespace OAI

/-! Matrix Coefficient Smooth. -/

section

noncomputable section
open Set Filter Topology Matrix Finset
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace MetricSystem
open EllipticKernel KaehlerCalculus
variable {n : ℕ}
lemma W_smooth (a : ℂ) (v : V n) : ContDiff ℝ ∞ (W (n := n) a v) := by
  unfold W
  apply ContDiff.const_smul
  apply ContDiff.add
  · exact (encode n).symm.contDiff.comp (contDiff_id.clm_apply contDiff_const)
  · exact ((encode n).symm.contDiff.comp (contDiff_id.clm_apply contDiff_const)).const_smul a

lemma quadraticCoefficient_smooth {p : HM n × (EC n →L[ℝ] HM n)}
    (hp : ((encode n).symm p.1).det ≠ 0) : ContDiffAt ℝ ∞ (quadraticCoefficient (n := n)) p := by
  apply (encode n).contDiff.contDiffAt.comp p
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  have hi := (inverseCoefficient_smooth hp).comp p contDiffAt_fst
  have hentry := contDiffAt_pi.mp (contDiffAt_pi.mp hi i) j
  apply hentry.smul
  have hW (a : ℂ) (v : V n) : ContDiffAt ℝ ∞ (fun q : HM n × (EC n →L[ℝ] HM n) => W a v q.2) p :=
    (W_smooth a v).contDiffAt.comp p contDiffAt_snd
  apply contDiffAt_pi.mpr
  intro k
  apply contDiffAt_pi.mpr
  intro l
  simp only [Matrix.mul_apply]
  apply ContDiffAt.sum
  intro s _
  apply ContDiffAt.mul
  · apply ContDiffAt.sum
    intro t _
    exact (contDiffAt_pi.mp (contDiffAt_pi.mp (hW Complex.I (e j)) k) t).mul
      (contDiffAt_pi.mp (contDiffAt_pi.mp hi t) s)
  · exact contDiffAt_pi.mp (contDiffAt_pi.mp (hW (-Complex.I) (e i)) s) l
end MetricSystem

end
end

end OAI
