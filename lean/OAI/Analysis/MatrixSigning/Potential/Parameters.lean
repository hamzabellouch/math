import Mathlib
import OAI.Analysis.MatrixSigning.Potential.Vars
import OAI.Analysis.MatrixSigning.Optimization.PartialFderiv

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Variational
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff

variable {d : ℕ}

section

private local instance : NormedAddCommGroup (H d) := inferInstance
private local instance : NormedSpace ℝ (H d) := inferInstance
private local instance : TopologicalSpace (H d) :=
  (inferInstance : NormedAddCommGroup (H d)).toUniformSpace.toTopologicalSpace

abbrev Parameters (d : ℕ) := H d × (H d →L[ℝ] H d)

local instance : NormedAddCommGroup (H d →L[ℝ] H d) := inferInstance
local instance : NormedSpace ℝ (H d →L[ℝ] H d) := inferInstance
local instance : NormedAddCommGroup (Parameters d) := inferInstance
local instance : NormedSpace ℝ (Parameters d) := inferInstance
local instance : NormedAddCommGroup (Vars d) := inferInstance
local instance : NormedSpace ℝ (Vars d) := inferInstance
local instance : NormedAddCommGroup (Parameters d × Vars d) := inferInstance
local instance : NormedSpace ℝ (Parameters d × Vars d) := inferInstance

def kktJoint (ε : ℝ) (u : Parameters d × Vars d) : Vars d :=
  kktSystem ε u.1.1 u.1.2 u.2

lemma contDiffAt_kktGiven {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : WithTop ℕ∞} {S : E → H d} {η : E → (H d →L[ℝ] H d)}
    {v : E → Vars d} {b : E} (ε : ℝ)
    (hS : ContDiffAt ℝ n S b) (hη : ContDiffAt ℝ n η b) (hv : ContDiffAt ℝ n v b)
    (hX : xCoord d (v b) ∈ pd d) (hY : yCoord d (v b) ∈ pd d) :
    ContDiffAt ℝ n (fun a => kktSystem ε (S a) (η a) (v a)) b := by
  have ht := (tCoord d).contDiff.contDiffAt.comp b hv
  have hx := (xCoord d).contDiff.contDiffAt.comp b hv
  have hy := (yCoord d).contDiff.contDiffAt.comp b hv
  have hm := (mCoord d).contDiff.contDiffAt.comp b hv
  have hn := (nCoord d).contDiff.contDiffAt.comp b hv
  have hr := (((innerSL ℝ (identityPair d)).contDiff.contDiffAt.comp b
      ((pCoord d).contDiff.contDiffAt.comp b hv)).sub (contDiffAt_const (c := (1 : ℝ))))
  have hfx := contDiffAt_tightPart ht hx hy hS hη hX
  have hfy := contDiffAt_tightPart ht hy hx hS.neg hη hY
  have hfu := (pairEquiv d).symm.contDiff.contDiffAt.comp b (hfx.prodMk hfy)
  have hgx := contDiffAt_stationaryPart ε hx hm hn hη hX
  have hgy := contDiffAt_stationaryPart ε hy hn hm hη hY
  have hgp := (pairEquiv d).symm.contDiff.contDiffAt.comp b (hgx.prodMk hgy)
  have hh := hr.prodMk (hfu.prodMk hgp)
  simp only [sub_neg_eq_add] at hh
  exact hh

lemma contDiffAt_kktJoint (ε : ℝ) (a : Parameters d) (z : Vars d)
    (hX : xCoord d z ∈ pd d) (hY : yCoord d z ∈ pd d) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (kktJoint ε) (a,z) :=
  contDiffAt_kktGiven ε contDiffAt_fst.fst contDiffAt_fst.snd contDiffAt_snd hX hY

theorem exists_smooth_kkt_branch (ε : ℝ) (a : Parameters d) (z : Vars d)
    (hX : xCoord d z ∈ pd d) (hY : yCoord d z ∈ pd d)
    (J : Vars d ≃L[ℝ] Vars d)
    (hJ : ∀ v, J v = CurrentKS.KKT.jacobian (identityPair d)
        (onPairHilbert (linConstraint (xCoord d z) (yCoord d z) a.2))
        (hessian (xCoord d z) (yCoord d z) (mCoord d z) (nCoord d z)) v) :
    ∃ f : Parameters d → Vars d, f a = z ∧ ContDiffAt ℝ ∞ f a ∧
      ∀ᶠ b in 𝓝 a, kktSystem ε b.1 b.2 (f b) = kktSystem ε a.1 a.2 z := by
  have he : CurrentKS.KKT.jacobian (identityPair d)
      (onPairHilbert (linConstraint (xCoord d z) (yCoord d z) a.2))
      (hessian (xCoord d z) (yCoord d z) (mCoord d z) (nCoord d z)) = J.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro v
    exact (hJ v).symm
  have hd := hasFDerivAt_kktSystem ε a.1 a.2 z hX hY
  rw [he] at hd
  exact CurrentKS.KKT.smooth_branch (contDiffAt_kktJoint ε a z hX hY) J hd

end

theorem optimal_of_kkt (ε : ℝ) (S : H d) (η : H d →L[ℝ] H d)
    (hηsym : SymmetricMap η) (z : Point d) (hz : z ∈ domain d)
    (P Q : H d) (hP : P ∈ psdCone d) (hQ : Q ∈ psdCone d)
    (htr : realTrace P + realTrace Q = 1)
    (hX : sandwich (invH z.2.1) P = η Q + ε • (Hermitian.one : H d))
    (hY : sandwich (invH z.2.2) Q = η P + ε • (Hermitian.one : H d))
    (htight : residual S η z = 0) :
    z ∈ feasible S η ∧ ∀ w ∈ feasible S η, objective ε z ≤ objective ε w := by
  have hf : z ∈ feasible S η := by
    refine ⟨hz,?_,?_⟩ <;> simp [htight]
  refine ⟨hf,fun w hw => ?_⟩
  have h₁ := inverse_trace_gap_nonneg P z.2.1 w.2.1 hP hz.1 hw.1.1
  have h₂ := inverse_trace_gap_nonneg Q z.2.2 w.2.2 hQ hz.2 hw.1.2
  rw [hX] at h₁
  rw [hY] at h₂
  have hL : lagrangian ε S η P Q z ≤ lagrangian ε S η P Q w := by
    rw [lagrangian_separate ε S η hηsym, lagrangian_separate ε S η hηsym]
    have hc : 1-realTrace P-realTrace Q = 0 := by linarith
    rw [hc, mul_zero, mul_zero]
    linarith
  rw [lagrangian_eq_objective_of_tight ε S η P Q z htight] at hL
  exact hL.trans (lagrangian_le_objective ε S η P Q hP hQ w hw)

end CurrentKS.Variational

end

end OAI
