import Mathlib
import OAI.Analysis.MatrixSigning.Potential.ValueBranch
import OAI.Analysis.MatrixSigning.Potential.JetBoundProjection
import OAI.Analysis.MatrixSigning.Calculus.NormMultilinearTwo

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian CurrentKS.Calculus Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
private local instance : NormedAddCommGroup (H d) := inferInstance
private local instance : NormedSpace ℝ (H d) := inferInstance
private local instance : TopologicalSpace (H d) :=
  (inferInstance : NormedAddCommGroup (H d)).toUniformSpace.toTopologicalSpace
private local instance : NormedAddCommGroup (PairHilbert d) := inferInstance
private local instance : NormedSpace ℝ (PairHilbert d) := inferInstance
private local instance : TopologicalSpace (PairHilbert d) :=
  (inferInstance : NormedAddCommGroup (PairHilbert d)).toUniformSpace.toTopologicalSpace
local instance : NormedAddCommGroup (Vars d) := inferInstance
local instance : NormedSpace ℝ (Vars d) := inferInstance
private local instance : TopologicalSpace (Vars d) :=
  (inferInstance : NormedAddCommGroup (Vars d)).toUniformSpace.toTopologicalSpace

def objectiveVarsCLM (ε : ℝ) : Vars d →L[ℝ] ℝ :=
  tCoord d+ε • (innerSL ℝ (identityPair d)).comp (uCoord d)

lemma objectiveVarsCLM_apply (ε : ℝ) (z : Vars d) :
    objectiveVarsCLM ε z = objective ε (unpack z) := by
  change tCoord d z + ε * inner ℝ (identityPair d) (uCoord d z) =
    tCoord d z + ε * realTrace (xCoord d z + yCoord d z)
  congr 1
  congr 1
  change inner ℝ (Hermitian.one : H d) (xCoord d z)+
    inner ℝ (Hermitian.one : H d) (yCoord d z) = _
  rw [Hermitian.inner_one,Hermitian.inner_one,Hermitian.realTrace_add]

lemma norm_objectiveVarsCLM (ε : ℝ) :
    ‖objectiveVarsCLM (d := d) ε‖ ≤ 1+|ε| *(2*((d:ℝ)+1)) := by
  have ht := norm_tracePair_le (d := d) (le_refl ((d:ℝ)+1))
  let t : Vars d →L[ℝ] ℝ := tCoord d
  let L : Vars d →L[ℝ] ℝ := (innerSL ℝ (identityPair d)).comp (uCoord d)
  change ‖t+ε • L‖ ≤ _
  calc
    _ ≤ ‖t‖+‖ε • L‖ := norm_add_le _ _
    _ = ‖t‖+|ε| *‖L‖ := by rw [norm_smul,Real.norm_eq_abs]
    _ ≤ 1+|ε| *(2*((d:ℝ)+1)*1) := by
      exact add_le_add norm_tCoord_le (mul_le_mul_of_nonneg_left
        ((ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul ht norm_uCoord_le (norm_nonneg _) (by positivity))) (abs_nonneg ε))
    _ = _ := by ring

lemma fderiv_kkt_parameter_right (ε : ℝ) (S : E → H d) (η : E → H d →L[ℝ] H d)
    (b : E) (z : Vars d) (hS : ContDiffAt ℝ 3 S b) (hη : ContDiffAt ℝ 3 η b)
    (hX : xCoord d z ∈ pd d) (hY : yCoord d z ∈ pd d) (u : Vars d) :
    fderiv ℝ (fun v : E × Vars d => kktSystem ε (S v.1) (η v.1) v.2) (b,z) (0,u) =
      CurrentKS.KKT.jacobian (identityPair d)
        (onPairHilbert (linConstraint (xCoord d z) (yCoord d z) (η b)))
        (hessian (xCoord d z) (yCoord d z) (mCoord d z) (nCoord d z)) u := by
  let F := fun v : E × Vars d => kktSystem ε (S v.1) (η v.1) v.2
  have hF : ContDiffAt ℝ 3 F (b,z) := contDiffAt_kktGiven ε
    (hS.comp (b,z) (contDiffAt_fst)) (hη.comp (b,z) (contDiffAt_fst))
    contDiffAt_snd hX hY
  have hi : HasFDerivAt (fun w : Vars d => (b,w)) (ContinuousLinearMap.inr ℝ E (Vars d)) z := by
    convert (hasFDerivAt_const b z).prodMk (hasFDerivAt_id z) using 1 <;> rfl
  have hh := (hF.differentiableAt (by norm_num)).hasFDerivAt.comp z hi
  have he := hh.unique (hasFDerivAt_kktSystem ε (S b) (η b) z hX hY)
  exact congrArg (fun L : Vars d →L[ℝ] Vars d => L u) he

theorem exists_value_curve [NeZero d] (ε : ℝ) (S : E → H d) (η : E → H d →L[ℝ] H d)
    (b h : E) (hS : ContDiffAt ℝ ∞ S b) (hη : ContDiffAt ℝ ∞ η b)
    (hηsym : ∀ᶠ a in 𝓝 b,SymmetricMap (η a)) (z : Vars d)
    (hX : xCoord d z ∈ pd d) (hY : yCoord d z ∈ pd d)
    (hP : mCoord d z ∈ pd d) (hQ : nCoord d z ∈ pd d)
    (hzero : kktSystem ε (S b) (η b) z=0) (J : Vars d ≃L[ℝ] Vars d)
    (hJ : ∀ u,J u=CurrentKS.KKT.jacobian (identityPair d)
      (onPairHilbert (linConstraint (xCoord d z) (yCoord d z) (η b)))
      (hessian (xCoord d z) (yCoord d z) (mCoord d z) (nCoord d z)) u) :
    ∃ c : ℝ → Vars d, ContDiffAt ℝ 3 c 0 ∧ c 0=z ∧
      (fun t => kktSystem ε (S (b+t • h)) (η (b+t • h)) (c t)) =ᶠ[𝓝 0] (fun _ => 0) ∧
      (fun t => value ε (S (b+t • h)) (η (b+t • h))) =ᶠ[𝓝 0] (objectiveVarsCLM ε ∘ c) := by
  obtain ⟨g,hg,hgc,hge,hgv⟩ := exists_value_branch ε S η b hS hη hηsym z hX hY hP hQ hzero J hJ
  let line := fun t : ℝ => b+t • h
  have hl : ContDiff ℝ ∞ line := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hl0 : line 0=b := by simp [line]
  let c := g ∘ line
  have hl3 : ContDiff ℝ 3 line := contDiff_infty.mp hl 3
  have hc : ContDiffAt ℝ 3 c 0 := by
    have hgg : ContDiffAt ℝ 3 g (line 0) := by rw [hl0]; exact contDiffAt_infty.mp hgc 3
    exact hgg.comp 0 hl3.contDiffAt
  have hc0 : c 0=z := by change g (line 0)=z; rw [hl0,hg]
  have hlt : Tendsto line (𝓝 0) (𝓝 b) := by
    have hx : Tendsto line (𝓝 0) (𝓝 (line 0)) := hl.continuous.continuousAt
    rw [hl0] at hx
    exact hx
  refine ⟨c,hc,hc0,hlt.eventually hge,?_⟩
  have hh := hlt.eventually hgv
  filter_upwards [hh] with t ht
  exact ht.trans (objectiveVarsCLM_apply ε (g (line t))).symm

lemma kkt_curve_derivatives (ε : ℝ) (S : E → H d) (η : E → H d →L[ℝ] H d)
    (b h : E) (hS : ContDiffAt ℝ 3 S b) (hη : ContDiffAt ℝ 3 η b)
    (z : Vars d) (hX : xCoord d z ∈ pd d) (hY : yCoord d z ∈ pd d)
    (J : Vars d ≃L[ℝ] Vars d)
    (hJ : ∀ u,J u=CurrentKS.KKT.jacobian (identityPair d)
      (onPairHilbert (linConstraint (xCoord d z) (yCoord d z) (η b)))
      (hessian (xCoord d z) (yCoord d z) (mCoord d z) (nCoord d z)) u)
    {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hJinv : ‖J.symm.toContinuousLinearMap‖ ≤ A) (hh : ‖h‖ ≤ 1)
    (hFB : JetBound (fun v : E × Vars d => kktSystem ε (S v.1) (η v.1) v.2) (b,z) D)
    (c : ℝ → Vars d) (hc : ContDiffAt ℝ 3 c 0) (hc0 : c 0=z)
    (heq : (fun t => kktSystem ε (S (b+t • h)) (η (b+t • h)) (c t)) =ᶠ[𝓝 0] (fun _ => 0)) :
    ‖iteratedDeriv 2 c 0‖ ≤ A*D*(1+A*D)^2 ∧
    ‖iteratedDeriv 3 c 0‖ ≤ A*D*((1+A*D)^3+3*(1+A*D)*(A*D*(1+A*D)^2)) := by
  let F := fun v : E × Vars d => kktSystem ε (S v.1) (η v.1) v.2
  have hF : ContDiffAt ℝ 3 F (b,z) := contDiffAt_kktGiven ε
    (hS.comp (b,z) contDiffAt_fst) (hη.comp (b,z) contDiffAt_fst) contDiffAt_snd hX hY
  have hfj (u : Vars d) : fderiv ℝ F (b+(0:ℝ) • h,c 0) (0,u)=J u := by
    simp only [zero_smul,add_zero,hc0]
    exact (fderiv_kkt_parameter_right ε S η b z hS hη hX hY u).trans (hJ u).symm
  have hF₁ : ‖fderiv ℝ F (b,z)‖ ≤ D := by
    simpa only [norm_iteratedFDeriv_one] using hFB 1 (by norm_num)
  have hb := CurrentKS.Implicit.graph_bounds F b h c 0
    (by simpa only [zero_smul,add_zero,hc0] using hF) hc heq J hfj hA hD hJinv hh
    (by simpa only [zero_smul,add_zero,hc0] using hF₁)
    (by simpa only [zero_smul,add_zero,hc0] using hFB 2 (by norm_num))
    (by simpa only [zero_smul,add_zero,hc0] using hFB 3 (by norm_num))
  exact hb.2

lemma norm_iteratedDeriv_germ_linear {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (c : ℝ → G) (hc : ContDiffAt ℝ 3 c 0) (L : G →L[ℝ] ℝ) (f : ℝ → ℝ)
    (he : f =ᶠ[𝓝 0] (L ∘ c)) (k : ℕ) (hk : k ≤ 3) :
    |iteratedDeriv k f 0| ≤ ‖L‖ * ‖iteratedDeriv k c 0‖ := by
  rw [he.iteratedDeriv_eq k]
  have hk' : (k : WithTop ℕ∞) ≤ 3 := by exact_mod_cast hk
  rw [CurrentKS.Implicit.iteratedDeriv_clm (hc.of_le hk') L]
  exact L.le_opNorm _

theorem value_curve_derivatives [NeZero d] (ε : ℝ) (S : E → H d) (η : E → H d →L[ℝ] H d)
    (b h : E) (hS : ContDiffAt ℝ ∞ S b) (hη : ContDiffAt ℝ ∞ η b)
    (hηsym : ∀ᶠ a in 𝓝 b,SymmetricMap (η a)) (z : Vars d)
    (hX : xCoord d z ∈ pd d) (hY : yCoord d z ∈ pd d)
    (hP : mCoord d z ∈ pd d) (hQ : nCoord d z ∈ pd d)
    (hzero : kktSystem ε (S b) (η b) z=0) (J : Vars d ≃L[ℝ] Vars d)
    (hJ : ∀ u,J u=CurrentKS.KKT.jacobian (identityPair d)
      (onPairHilbert (linConstraint (xCoord d z) (yCoord d z) (η b)))
      (hessian (xCoord d z) (yCoord d z) (mCoord d z) (nCoord d z)) u)
    {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hJinv : ‖J.symm.toContinuousLinearMap‖ ≤ A) (hh : ‖h‖ ≤ 1)
    (hFB : JetBound (fun v : E × Vars d => kktSystem ε (S v.1) (η v.1) v.2) (b,z) D) :
    let f := fun t : ℝ => value ε (S (b+t • h)) (η (b+t • h))
    |iteratedDeriv 2 f 0| ≤ (1+|ε| *(2*((d:ℝ)+1)))*(A*D*(1+A*D)^2) ∧
    |iteratedDeriv 3 f 0| ≤ (1+|ε| *(2*((d:ℝ)+1)))*
      (A*D*((1+A*D)^3+3*(1+A*D)*(A*D*(1+A*D)^2))) := by
  obtain ⟨c,hc,hc0,heq,hv⟩ := exists_value_curve ε S η b h hS hη hηsym z hX hY hP hQ hzero J hJ
  have hb := kkt_curve_derivatives ε S η b h (contDiffAt_infty.mp hS 3)
    (contDiffAt_infty.mp hη 3) z hX hY J hJ hA hD hJinv hh hFB c hc hc0 heq
  constructor
  · exact (norm_iteratedDeriv_germ_linear c hc (objectiveVarsCLM ε) _ hv 2 (by norm_num)).trans
      (mul_le_mul (norm_objectiveVarsCLM ε) hb.1 (norm_nonneg _) (by positivity))
  · exact (norm_iteratedDeriv_germ_linear c hc (objectiveVarsCLM ε) _ hv 3 (by norm_num)).trans
      (mul_le_mul (norm_objectiveVarsCLM ε) hb.2 (norm_nonneg _) (by positivity))

end
end CurrentKS.Variational

end OAI
