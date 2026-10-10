import Mathlib
import OAI.Analysis.MatrixSigning.Calculus.NormSmulRightId
import OAI.Analysis.MatrixSigning.Matrices.JetBoundInverseSandwich

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open CurrentKS.Calculus Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private local instance : NormedAddCommGroup (H d) := inferInstance
private local instance : NormedSpace ℝ (H d) := inferInstance
private local instance : TopologicalSpace (H d) :=
  (inferInstance : NormedAddCommGroup (H d)).toUniformSpace.toTopologicalSpace

local instance : NormedAddCommGroup (H d →L[ℝ] H d) := inferInstance
local instance : NormedSpace ℝ (H d →L[ℝ] H d) := inferInstance
local instance : NormedAddCommGroup (E →L[ℝ] H d) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] H d) := inferInstance

lemma jetBound_tightPart (t : E →L[ℝ] ℝ) (X Y : E →L[ℝ] H d)
    {S : E → H d} {η : E → H d →L[ℝ] H d} {z : E} {B : ℝ}
    (hB : 1 ≤ B) (hI : ‖(one : H d)‖ ≤ B)
    (ht : JetBound t z B) (hX : ‖X‖ ≤ 1) (hY : JetBound Y z B)
    (hpos : X z ∈ pd d) (hinv : ‖invH (X z)‖ ≤ B)
    (hS : ContDiffAt ℝ 3 S z) (hη : ContDiffAt ℝ 3 η z)
    (hSB : JetBound S z B) (hηB : JetBound η z B) :
    JetBound (fun v => t v • (one : H d) - invH (X v) - S v - η v (Y v)) z
      (B*B+6*B^4+B+8*B*B) := by
  have h₁ := ht.smul_const (one : H d) t.contDiff.contDiffAt hI
  have h₂ := jetBound_invH_linear X hX hpos hB hinv
  have h₃ := hηB.apply hη Y.contDiff.contDiffAt hY
  have hc₁ : ContDiffAt ℝ 3 (fun v => t v • (one : H d)) z :=
    t.contDiff.contDiffAt.smul contDiffAt_const
  have hc₂ : ContDiffAt ℝ 3 (fun v => invH (X v)) z :=
    (contDiffAt_invH hpos).comp z X.contDiff.contDiffAt
  exact ((h₁.sub hc₁ hc₂ h₂).sub (hc₁.sub hc₂) hS hSB).sub
    ((hc₁.sub hc₂).sub hS) (hη.clm_apply Y.contDiff.contDiffAt) h₃

lemma jetBound_stationaryPart (X P Q : E →L[ℝ] H d) (ε : ℝ)
    {η : E → H d →L[ℝ] H d} {z : E} {B : ℝ}
    (hB : 1 ≤ B) (hI : ‖(one : H d)‖ ≤ B) (hε : |ε| ≤ B)
    (hX : ‖X‖ ≤ 1) (hP : ‖P‖ ≤ 1) (hPB : ‖P z‖ ≤ 1)
    (hQ : JetBound Q z B) (hpos : X z ∈ pd d) (hinv : ‖invH (X z)‖ ≤ B)
    (hη : ContDiffAt ℝ 3 η z) (hηB : JetBound η z B) :
    JetBound (fun v => sandwich (invH (X v)) (P v) - η v (Q v) - ε • (one : H d)) z
      (42*B^5+8*B*B+B*B) := by
  have h₁ := jetBound_inverse_sandwich X P hX hP hpos hB hinv hPB
  have h₂ := hηB.apply hη Q.contDiff.contDiffAt hQ
  have h₃ := (JetBound.const (ε • (one : H d)) z).mono
    (show ‖ε • (one : H d)‖ ≤ B*B by
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul hε hI (norm_nonneg _) (le_trans zero_le_one hB))
  have hc₁ : ContDiffAt ℝ 3 (fun v => sandwich (invH (X v)) (P v)) z :=
    (contDiffAt_invSandwich _ _ hpos).comp z (X.contDiff.contDiffAt.prodMk P.contDiff.contDiffAt)
  exact (h₁.sub hc₁ (hη.clm_apply Q.contDiff.contDiffAt) h₂).sub
    (hc₁.sub (hη.clm_apply Q.contDiff.contDiffAt)) contDiffAt_const h₃
end
end CurrentKS.Hermitian

end OAI
