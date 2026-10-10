import Mathlib
import OAI.Analysis.MatrixSigning.Potential.Parameters

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff

variable {d : ℕ}

private local instance : NormedAddCommGroup (H d) := inferInstance
private local instance : NormedSpace ℝ (H d) := inferInstance
private local instance : TopologicalSpace (H d) :=
  (inferInstance : NormedAddCommGroup (H d)).toUniformSpace.toTopologicalSpace

def tightSystem (t : ℝ) (S : H d) (η : H d →L[ℝ] H d) (z : Pair d) : Pair d :=
  (t • (Hermitian.one : H d) - invH z.1 - S - η z.2,
   t • (Hermitian.one : H d) - invH z.2 + S - η z.1)

lemma hasFDerivAt_tightSystem (t : ℝ) (S : H d) (η : H d →L[ℝ] H d)
    (z : Pair d) (hX : z.1 ∈ pd d) (hY : z.2 ∈ pd d) :
    HasFDerivAt (tightSystem t S η) (linConstraint z.1 z.2 η) z := by
  have h₁ := (((hasFDerivAt_const (t • (Hermitian.one : H d)) z).sub
    ((hasFDerivAt_invH hX).comp z (hasFDerivAt_fst (p := z)))).sub_const S).sub
      (η.hasFDerivAt.comp z (hasFDerivAt_snd (p := z)))
  have h₂ := (((hasFDerivAt_const (t • (Hermitian.one : H d)) z).sub
    ((hasFDerivAt_invH hY).comp z (hasFDerivAt_snd (p := z)))).add_const S).sub
      (η.hasFDerivAt.comp z (hasFDerivAt_fst (p := z)))
  convert h₁.prodMk h₂ using 1 <;> try rfl
  apply ContinuousLinearMap.ext
  intro v
  apply Prod.ext
  · change sandwich (invH z.1) v.1 - η v.2 = 0 - (-sandwich (invH z.1) v.1) - η v.2
    module
  · change sandwich (invH z.2) v.2 - η v.1 = 0 - (-sandwich (invH z.2) v.2) - η v.1
    module

local instance tightSystemOperatorNormedAddCommGroup : NormedAddCommGroup (H d →L[ℝ] H d) :=
  inferInstance
local instance tightSystemOperatorNormedSpace : NormedSpace ℝ (H d →L[ℝ] H d) := inferInstance
local instance tightSystemPairNormedAddCommGroup : NormedAddCommGroup (Pair d) := inferInstance
local instance tightSystemPairNormedSpace : NormedSpace ℝ (Pair d) := inferInstance
local instance tightSystemParametersNormedAddCommGroup : NormedAddCommGroup (Parameters d) :=
  inferInstance
local instance tightSystemParametersNormedSpace : NormedSpace ℝ (Parameters d) := inferInstance
local instance tightSystemProductNormedAddCommGroup : NormedAddCommGroup (Parameters d × Pair d) :=
  inferInstance
local instance tightSystemProductNormedSpace : NormedSpace ℝ (Parameters d × Pair d) := inferInstance

lemma contDiffAt_tightGiven {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : WithTop ℕ∞} (t : ℝ) {S : E → H d} {η : E → (H d →L[ℝ] H d)}
    {X Y : E → H d} {b : E}
    (hS : ContDiffAt ℝ n S b) (hη : ContDiffAt ℝ n η b)
    (hx : ContDiffAt ℝ n X b) (hy : ContDiffAt ℝ n Y b)
    (hX : X b ∈ pd d) (hY : Y b ∈ pd d) :
    ContDiffAt ℝ n (fun v => tightSystem t (S v) (η v) (X v,Y v)) b := by
  have h₁ := contDiffAt_tightPart (t := fun _ => t) contDiffAt_const hx hy hS hη hX
  have h₂ := contDiffAt_tightPart (t := fun _ => t) contDiffAt_const hy hx hS.neg hη hY
  simpa only [tightSystem,sub_neg_eq_add] using h₁.prodMk h₂

def tightJoint (t : ℝ) (v : Parameters d × Pair d) : Pair d :=
  tightSystem t v.1.1 v.1.2 v.2

lemma contDiffAt_tightJoint {n : WithTop ℕ∞} (t : ℝ) (a : Parameters d) (z : Pair d)
    (hX : z.1 ∈ pd d) (hY : z.2 ∈ pd d) :
    ContDiffAt ℝ n (tightJoint t) (a,z) := by
  exact contDiffAt_tightGiven (E := Parameters d × Pair d) t
    (S := fun v => v.1.1) (η := fun v => v.1.2)
    (X := fun v => v.2.1) (Y := fun v => v.2.2)
    contDiffAt_fst.fst contDiffAt_fst.snd contDiffAt_snd.fst contDiffAt_snd.snd hX hY

theorem exists_smooth_tight_branch (t : ℝ) (a : Parameters d) (z : Pair d)
    (hX : z.1 ∈ pd d) (hY : z.2 ∈ pd d)
    (J : Pair d ≃L[ℝ] Pair d) (hJ : J.toContinuousLinearMap = linConstraint z.1 z.2 a.2) :
    ∃ f : Parameters d → Pair d, f a = z ∧ ContDiffAt ℝ ∞ f a ∧
      ∀ᶠ b in 𝓝 a, tightSystem t b.1 b.2 (f b) = tightSystem t a.1 a.2 z := by
  apply CurrentKS.KKT.smooth_branch (contDiffAt_tightJoint t a z hX hY) J
  erw [hJ]
  exact hasFDerivAt_tightSystem t a.1 a.2 z hX hY

end
end CurrentKS.Variational

end OAI
