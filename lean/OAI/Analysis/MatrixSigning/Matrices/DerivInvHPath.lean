import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.RetractH

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Hermitian
open Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

variable {d : ℕ}

private local instance : NormedAddCommGroup (H d) := inferInstance
private local instance : NormedSpace ℝ (H d) := inferInstance
private local instance : TopologicalSpace (H d) :=
  (inferInstance : NormedAddCommGroup (H d)).toUniformSpace.toTopologicalSpace

lemma hasDerivAt_invH_path {X : ℝ → H d} {U : H d} {a : ℝ}
    (hX : X a ∈ pd d) (hU : HasDerivAt X U a) :
    HasDerivAt (fun s => invH (X s)) (-sandwich (invH (X a)) U) a := by
  exact (hasFDerivAt_invH hX).comp_hasDerivAt a hU

lemma hasDerivAt_invSandwich_path {X P : ℝ → H d} {U V : H d} {a : ℝ}
    (hX : X a ∈ pd d) (hU : HasDerivAt X U a) (hV : HasDerivAt P V a) :
    HasDerivAt (fun s => sandwich (invH (X s)) (P s))
      (-jordanCLM (invH (X a)) (sandwich (invH (X a)) (P a)) U +
        sandwich (invH (X a)) V) a := by
  exact (hasFDerivAt_invSandwich (X a) (P a) hX).comp_hasDerivAt a (hU.prodMk hV)

lemma hasDerivAt_deriv_invH_path [NeZero d] {X : ℝ → H d} {a : ℝ}
    (hX : X a ∈ pd d) (hc : ContDiffAt ℝ 2 X a) :
    HasDerivAt (deriv (fun s => invH (X s)))
      (jordanCLM (invH (X a)) (sandwich (invH (X a)) (deriv X a)) (deriv X a) -
        sandwich (invH (X a)) (deriv (deriv X) a)) a := by
  have hU := (hc.differentiableAt (by norm_num)).hasDerivAt
  have hc' : ContDiffAt ℝ 1 (deriv X) a := hc.derivWithin (by norm_num)
  have hV := (hc'.differentiableAt (by norm_num)).hasDerivAt
  have hh := (hasDerivAt_invSandwich_path hX hU hV).neg
  have he : deriv (fun s => invH (X s)) =ᶠ[𝓝 a]
      fun s => -sandwich (invH (X s)) (deriv X s) := by
    have hpd : ∀ᶠ s in 𝓝 a, X s ∈ pd d :=
      hc.continuousAt.eventually (isOpen_pd.mem_nhds hX)
    filter_upwards [hpd,hc.eventually (by norm_num)] with s hs hsc
    exact (hasDerivAt_invH_path hs (hsc.differentiableAt (by norm_num)).hasDerivAt).deriv
  simpa only [_root_.neg_apply, neg_add_rev, neg_neg, sub_eq_add_neg, add_comm]
    using hh.congr_of_eventuallyEq he

lemma deriv_deriv_invH_path [NeZero d] {X : ℝ → H d} {a : ℝ}
    (hX : X a ∈ pd d) (hc : ContDiffAt ℝ 2 X a) :
    deriv (deriv (fun s => invH (X s))) a =
      jordanCLM (invH (X a)) (sandwich (invH (X a)) (deriv X a)) (deriv X a) -
        sandwich (invH (X a)) (deriv (deriv X) a) :=
  (hasDerivAt_deriv_invH_path hX hc).deriv

lemma jordan_inverse_square (X U : H d) :
    jordanCLM (invH X) (sandwich (invH X) U) U =
      (2 : ℝ) • sandwich (invH X) (sandwich U (invH X)) := by
  apply Subtype.ext
  simp only [jordanCLM_val,sandwich_val,Submodule.coe_smul]
  change (X : Mat d)⁻¹*(U : Mat d)*((X : Mat d)⁻¹*(U : Mat d)*(X : Mat d)⁻¹) +
      ((X : Mat d)⁻¹*(U : Mat d)*(X : Mat d)⁻¹)*(U : Mat d)*(X : Mat d)⁻¹ =
    (2 : ℝ) • ((X : Mat d)⁻¹*((U : Mat d)*(X : Mat d)⁻¹*(U : Mat d))*(X : Mat d)⁻¹)
  rw [two_smul ℝ]
  noncomm_ring

local instance derivInvHPathNormedAddCommGroup : NormedAddCommGroup (H d →L[ℝ] H d) := inferInstance
local instance derivInvHPathNormedSpace : NormedSpace ℝ (H d →L[ℝ] H d) := inferInstance
private local instance : TopologicalSpace (H d →L[ℝ] H d) :=
  (inferInstance : NormedAddCommGroup (H d →L[ℝ] H d)).toUniformSpace.toTopologicalSpace

lemma constraint_first {X Y S : ℝ → H d} {η : ℝ → (H d →L[ℝ] H d)} {a : ℝ}
    (hX : X a ∈ pd d) (hXd : DifferentiableAt ℝ X a) (hYd : DifferentiableAt ℝ Y a)
    (hSd : DifferentiableAt ℝ S a) (hηd : DifferentiableAt ℝ η a)
    (B : H d) (he : (fun s => invH (X s)+S s+η s (Y s)) =ᶠ[𝓝 a] fun _ => B) :
    sandwich (invH (X a)) (deriv X a) - η a (deriv Y a) =
      deriv S a + deriv η a (Y a) := by
  have hd := (((hasDerivAt_invH_path hX hXd.hasDerivAt).add hSd.hasDerivAt).add
    (hηd.hasDerivAt.clm_apply hYd.hasDerivAt)).deriv
  change deriv (fun s => invH (X s)+S s+η s (Y s)) a = _ at hd
  rw [he.deriv_eq,deriv_const] at hd
  linear_combination (norm := module) hd

lemma constraint_first_eventually [NeZero d] {X Y S : ℝ → H d} {η : ℝ → (H d →L[ℝ] H d)} {a : ℝ}
    (hX : X a ∈ pd d) (hXc : ContDiffAt ℝ 2 X a) (hYc : ContDiffAt ℝ 2 Y a)
    (hSc : ContDiffAt ℝ 2 S a) (hηc : ContDiffAt ℝ 2 η a)
    (B : H d) (he : (fun s => invH (X s)+S s+η s (Y s)) =ᶠ[𝓝 a] fun _ => B) :
    (fun s => sandwich (invH (X s)) (deriv X s) - η s (deriv Y s) - deriv S s - deriv η s (Y s))
      =ᶠ[𝓝 a] fun _ => 0 := by
  let F : ℝ → H d := fun s =>
    sandwich (invH (X s)) (deriv X s) - η s (deriv Y s) - deriv S s - deriv η s (Y s)
  have hpd : ∀ᶠ s in 𝓝 a, X s ∈ pd d :=
    hXc.continuousAt.eventually (isOpen_pd.mem_nhds hX)
  have hf : F =ᶠ[𝓝 a] fun _ => 0 := by
    filter_upwards [hpd,hXc.eventually (by norm_num),hYc.eventually (by norm_num),
      hSc.eventually (by norm_num),hηc.eventually (by norm_num),he.eventuallyEq_nhds] with s hx hxc hyc hsc hηc hec
    have hh := constraint_first hx (hxc.differentiableAt (by norm_num))
      (hyc.differentiableAt (by norm_num)) (hsc.differentiableAt (by norm_num))
      (hηc.differentiableAt (by norm_num)) B hec
    change sandwich (invH (X s)) (deriv X s) - η s (deriv Y s) - deriv S s - deriv η s (Y s) = 0
    rw [hh]
    module
  exact hf

lemma constraint_second [NeZero d] {X Y S : ℝ → H d} {η : ℝ → (H d →L[ℝ] H d)} {a : ℝ}
    (hX : X a ∈ pd d) (hXc : ContDiffAt ℝ 2 X a) (hYc : ContDiffAt ℝ 2 Y a)
    (hSc : ContDiffAt ℝ 2 S a) (hηc : ContDiffAt ℝ 2 η a)
    (B : H d) (he : (fun s => invH (X s)+S s+η s (Y s)) =ᶠ[𝓝 a] fun _ => B) :
    sandwich (invH (X a)) (deriv (deriv X) a) - η a (deriv (deriv Y) a) =
      jordanCLM (invH (X a)) (sandwich (invH (X a)) (deriv X a)) (deriv X a) +
      deriv (deriv S) a + (2 : ℝ) • (deriv η a (deriv Y a)) + deriv (deriv η) a (Y a) := by
  let F : ℝ → H d := fun s =>
    sandwich (invH (X s)) (deriv X s) - η s (deriv Y s) - deriv S s - deriv η s (Y s)
  have hf : F =ᶠ[𝓝 a] fun _ => 0 := constraint_first_eventually hX hXc hYc hSc hηc B he
  have hXd := (hXc.differentiableAt (by norm_num)).hasDerivAt
  have hYd := (hYc.differentiableAt (by norm_num)).hasDerivAt
  have hηd := (hηc.differentiableAt (by norm_num)).hasDerivAt
  have hXc' : ContDiffAt ℝ 1 (deriv X) a := hXc.derivWithin (by norm_num)
  have hXdd := (hXc'.differentiableAt (by norm_num)).hasDerivAt
  have hYc' : ContDiffAt ℝ 1 (deriv Y) a := hYc.derivWithin (by norm_num)
  have hYdd := (hYc'.differentiableAt (by norm_num)).hasDerivAt
  have hSc' : ContDiffAt ℝ 1 (deriv S) a := hSc.derivWithin (by norm_num)
  have hSdd := (hSc'.differentiableAt (by norm_num)).hasDerivAt
  have hηc' : ContDiffAt ℝ 1 (deriv η) a := hηc.derivWithin (by norm_num)
  have hηdd := (hηc'.differentiableAt (by norm_num)).hasDerivAt
  have hd := ((((hasDerivAt_invSandwich_path hX hXd hXdd).sub
    (hηd.clm_apply hYdd)).sub hSdd).sub (hηdd.clm_apply hYd)).deriv
  change deriv F a = _ at hd
  rw [hf.deriv_eq,deriv_const] at hd
  linear_combination (norm := module) -hd

end CurrentKS.Hermitian

end

end OAI
