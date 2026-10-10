import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.RetractH

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius ContDiff

variable {d : ℕ}

private local instance : NormedAddCommGroup (H d) := inferInstance
private local instance : NormedSpace ℝ (H d) := inferInstance
private local instance : TopologicalSpace (H d) :=
  (inferInstance : NormedAddCommGroup (H d)).toUniformSpace.toTopologicalSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma hasFDerivAt_tightPart (t : E →L[ℝ] ℝ) (X Y : E →L[ℝ] H d)
    (S : H d) (η : H d →L[ℝ] H d) (z : E) (hX : X z ∈ pd d) :
    HasFDerivAt (fun v => t v • (one : H d) - invH (X v) - S - η (Y v))
      ((t.smulRight (one : H d) : E →L[ℝ] H d) +
        ((sandwichCLM (invH (X z))).comp X : E →L[ℝ] H d) - η.comp Y) z := by
  have h := (((t.hasFDerivAt.smul_const (one : H d)).sub
    ((hasFDerivAt_invH hX).comp z X.hasFDerivAt)).sub_const S).sub
    (η.hasFDerivAt.comp z Y.hasFDerivAt)
  refine h.congr_fderiv ?_
  symm
  apply ContinuousLinearMap.ext
  intro v
  change t v • (one : H d) + sandwich (invH (X z)) (X v) - η (Y v) =
    t v • (one : H d) - (-sandwich (invH (X z)) (X v)) - η (Y v)
  module

lemma hasFDerivAt_stationaryPart (X P Q : E →L[ℝ] H d)
    (ε : ℝ) (η : H d →L[ℝ] H d) (z : E) (hX : X z ∈ pd d) :
    HasFDerivAt (fun v => sandwich (invH (X v)) (P v) - η (Q v) - ε • (one : H d))
      (((sandwichCLM (invH (X z))).comp P : E →L[ℝ] H d) - η.comp Q -
        ((jordanCLM (invH (X z)) (sandwich (invH (X z)) (P z))).comp X : E →L[ℝ] H d)) z := by
  have h := (((hasFDerivAt_invSandwich (X z) (P z) hX).comp z
    (X.hasFDerivAt.prodMk P.hasFDerivAt)).sub
    (η.hasFDerivAt.comp z Q.hasFDerivAt)).sub_const (ε • (one : H d))
  refine h.congr_fderiv ?_
  symm
  apply ContinuousLinearMap.ext
  intro v
  change sandwich (invH (X z)) (P v) - η (Q v) -
      jordanCLM (invH (X z)) (sandwich (invH (X z)) (P z)) (X v) =
    -jordanCLM (invH (X z)) (sandwich (invH (X z)) (P z)) (X v) +
      sandwich (invH (X z)) (P v) - η (Q v)
  module

lemma contDiffAt_tightPart {n : WithTop ℕ∞} {t : E → ℝ} {X Y S : E → H d}
    {η : E → (H d →L[ℝ] H d)} {z : E}
    (ht : ContDiffAt ℝ n t z) (hX : ContDiffAt ℝ n X z) (hY : ContDiffAt ℝ n Y z)
    (hS : ContDiffAt ℝ n S z) (hη : ContDiffAt ℝ n η z) (hpos : X z ∈ pd d) :
    ContDiffAt ℝ n (fun v => t v • (one : H d) - invH (X v) - S v - η v (Y v)) z :=
  (((ht.smul contDiffAt_const).sub ((contDiffAt_invH hpos).comp z hX)).sub hS).sub
    (hη.clm_apply hY)

lemma contDiffAt_stationaryPart {n : WithTop ℕ∞} {X P Q : E → H d}
    {η : E → (H d →L[ℝ] H d)} {z : E} (ε : ℝ)
    (hX : ContDiffAt ℝ n X z) (hP : ContDiffAt ℝ n P z) (hQ : ContDiffAt ℝ n Q z)
    (hη : ContDiffAt ℝ n η z) (hpos : X z ∈ pd d) :
    ContDiffAt ℝ n (fun v => sandwich (invH (X v)) (P v) - η v (Q v) - ε • (one : H d)) z :=
  (((contDiffAt_invSandwich (X z) (P z) hpos).comp z (hX.prodMk hP)).sub
    (hη.clm_apply hQ)).sub contDiffAt_const

end
end CurrentKS.Hermitian

end OAI
