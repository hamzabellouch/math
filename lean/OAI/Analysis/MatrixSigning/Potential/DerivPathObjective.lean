import Mathlib
import OAI.Analysis.MatrixSigning.Potential.CoarseBudget
import OAI.Analysis.MatrixSigning.Potential.NegativeWeight
import OAI.Analysis.MatrixSigning.Matrices.DerivInvHPath

namespace OAI

open Matrix

namespace CurrentKS.State
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

variable {d N : ℕ}
private local instance : NormedAddCommGroup (H d) := inferInstance
private local instance : NormedSpace ℝ (H d) := inferInstance
private local instance : TopologicalSpace (H d) :=
  (inferInstance : NormedAddCommGroup (H d)).toUniformSpace.toTopologicalSpace
local instance derivPathObjectiveNormedAddCommGroup : NormedAddCommGroup (H d →L[ℝ] H d) :=
  inferInstance
local instance derivPathObjectiveNormedSpace : NormedSpace ℝ (H d →L[ℝ] H d) := inferInstance

lemma hasDerivAt_path_objective {X Y : ℝ → H d} {U V : H d} {a : ℝ}
    (hX : HasDerivAt X U a) (hY : HasDerivAt Y V a) (ε t : ℝ) :
    HasDerivAt (fun s => t+ε*Hermitian.realTrace (X s+Y s)) (ε*Hermitian.realTrace (U+V)) a := by
  have hh := (traceCLM (d := d)).hasFDerivAt.comp_hasDerivAt a (hX.add hY)
  have hh' : HasDerivAt (fun s => Hermitian.realTrace (X s+Y s)) (Hermitian.realTrace (U+V)) a :=
    (hh.congr_deriv (traceCLM_apply (U + V))).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => (traceCLM_apply (X s + Y s)).symm)
  have hhh := (hasDerivAt_const a t).add (hh'.const_mul ε)
  simp only [zero_add] at hhh
  exact hhh

lemma deriv_deriv_path_objective {X Y : ℝ → H d} {a : ℝ}
    (hX : ContDiffAt ℝ 2 X a) (hY : ContDiffAt ℝ 2 Y a) (ε t : ℝ) :
    deriv (deriv (fun s => t+ε*Hermitian.realTrace (X s+Y s))) a =
      ε*Hermitian.realTrace (deriv (deriv X) a+deriv (deriv Y) a) := by
  have hX' : ContDiffAt ℝ 1 (deriv X) a := hX.derivWithin (by norm_num)
  have hY' : ContDiffAt ℝ 1 (deriv Y) a := hY.derivWithin (by norm_num)
  have he : deriv (fun s => t+ε*Hermitian.realTrace (X s+Y s)) =ᶠ[𝓝 a]
      fun s => 0+ε*Hermitian.realTrace (deriv X s+deriv Y s) := by
    filter_upwards [hX.eventually (by norm_num),hY.eventually (by norm_num)] with s hx hy
    simpa only [zero_add] using (hasDerivAt_path_objective
      (hx.differentiableAt (by norm_num)).hasDerivAt (hy.differentiableAt (by norm_num)).hasDerivAt ε t).deriv
  rw [he.deriv_eq]
  exact (hasDerivAt_path_objective (hX'.differentiableAt (by norm_num)).hasDerivAt
    (hY'.differentiableAt (by norm_num)).hasDerivAt ε 0).deriv

lemma first_response_path (c : ℝ) (A : Fin N → H d) (x h : Coordinates N)
    (hx : ∀ i, |x i| < 1) {X Y : ℝ → H d}
    (hX : X 0 ∈ pd d) (hXd : DifferentiableAt ℝ X 0) (hYd : DifferentiableAt ℝ Y 0)
    (B : H d)
    (he : (fun s => invH (X s)+S A (line x h s)+eta c A (line x h s) (Y s)) =ᶠ[𝓝 0] fun _ => B) :
    sandwich (invH (X 0)) (deriv X 0) - eta c A x (deriv Y 0) =
      S A h+eta₁ c A x h (Y 0) := by
  have hS := hasDerivAt_S_line A x h 0
  have hη := hasDerivAt_eta_line c A x h 0 (by simpa using hx)
  have hh := constraint_first hX hXd hYd hS.differentiableAt hη.differentiableAt B he
  rw [hS.deriv,hη.deriv] at hh
  simpa only [line_zero] using hh

lemma first_response_path_neg (c : ℝ) (A : Fin N → H d) (x h : Coordinates N)
    (hx : ∀ i, |x i| < 1) {X Y : ℝ → H d}
    (hY : Y 0 ∈ pd d) (hXd : DifferentiableAt ℝ X 0) (hYd : DifferentiableAt ℝ Y 0)
    (B : H d)
    (he : (fun s => invH (Y s)-S A (line x h s)+eta c A (line x h s) (X s)) =ᶠ[𝓝 0] fun _ => B) :
    sandwich (invH (Y 0)) (deriv Y 0) - eta c A x (deriv X 0) =
      -S A h+eta₁ c A x h (X 0) := by
  have hS := (hasDerivAt_S_line A x h 0).neg
  have hη := hasDerivAt_eta_line c A x h 0 (by simpa using hx)
  have hh := constraint_first hY hYd hXd hS.differentiableAt hη.differentiableAt B
    (by simp only [sub_eq_add_neg] at he; exact he)
  rw [hS.deriv,hη.deriv] at hh
  simpa only [line_zero] using hh

lemma deriv_deriv_S_line (A : Fin N → H d) (x h : Coordinates N) (a : ℝ) :
    deriv (deriv (fun s => S A (line x h s))) a = 0 := by
  have he : deriv (fun s => S A (line x h s)) = fun _ => S A h := by
    funext s
    exact (hasDerivAt_S_line A x h s).deriv
  rw [he,deriv_const]

lemma second_response_path [NeZero d] (c : ℝ) (A : Fin N → H d) (x h : Coordinates N)
    (hx : ∀ i, |x i| < 1) {X Y : ℝ → H d}
    (hX : X 0 ∈ pd d) (hXc : ContDiffAt ℝ 2 X 0) (hYc : ContDiffAt ℝ 2 Y 0)
    (B : H d)
    (he : (fun s => invH (X s)+S A (line x h s)+eta c A (line x h s) (Y s)) =ᶠ[𝓝 0] fun _ => B) :
    sandwich (invH (X 0)) (deriv (deriv X) 0) - eta c A x (deriv (deriv Y) 0) =
      jordanCLM (invH (X 0)) (sandwich (invH (X 0)) (deriv X 0)) (deriv X 0) +
        (2 : ℝ) • eta₁ c A x h (deriv Y 0) + eta₂ c A x h (Y 0) := by
  have hηc : ContDiffAt ℝ 2 (fun s => eta c A (line x h s)) 0 :=
    by
    have hc : ContDiffAt ℝ 2 (eta c A) (line x h 0) := by
      simpa only [line_zero] using contDiffAt_eta c A hx
    exact hc.comp 0 (contDiff_line x h).contDiffAt
  have hh := constraint_second hX hXc hYc
    ((contDiff_S A).comp (contDiff_line x h)).contDiffAt hηc B he
  simp only [Function.comp_def] at hh
  rw [deriv_deriv_S_line,add_zero,(hasDerivAt_eta_line c A x h 0 (by simpa using hx)).deriv,
    (hasDerivAt_deriv_eta_line c A x h 0 (by simpa using hx)).deriv] at hh
  simpa only [line_zero] using hh

lemma deriv_deriv_neg_S_line (A : Fin N → H d) (x h : Coordinates N) (a : ℝ) :
    deriv (deriv (fun s => -S A (line x h s))) a = 0 := by
  have he : deriv (fun s => -S A (line x h s)) = fun _ => -S A h := by
    funext s
    exact ((hasDerivAt_S_line A x h s).neg).deriv
  rw [he,deriv_const]

lemma second_response_path_neg [NeZero d] (c : ℝ) (A : Fin N → H d) (x h : Coordinates N)
    (hx : ∀ i, |x i| < 1) {X Y : ℝ → H d}
    (hY : Y 0 ∈ pd d) (hXc : ContDiffAt ℝ 2 X 0) (hYc : ContDiffAt ℝ 2 Y 0)
    (B : H d)
    (he : (fun s => invH (Y s)-S A (line x h s)+eta c A (line x h s) (X s)) =ᶠ[𝓝 0] fun _ => B) :
    sandwich (invH (Y 0)) (deriv (deriv Y) 0) - eta c A x (deriv (deriv X) 0) =
      jordanCLM (invH (Y 0)) (sandwich (invH (Y 0)) (deriv Y 0)) (deriv Y 0) +
        (2 : ℝ) • eta₁ c A x h (deriv X 0) + eta₂ c A x h (X 0) := by
  have hηc : ContDiffAt ℝ 2 (fun s => eta c A (line x h s)) 0 := by
    have hc : ContDiffAt ℝ 2 (eta c A) (line x h 0) := by
      simpa only [line_zero] using contDiffAt_eta c A hx
    exact hc.comp 0 (contDiff_line x h).contDiffAt
  have hh := constraint_second hY hYc hXc
    ((contDiff_S A).comp (contDiff_line x h)).neg.contDiffAt hηc B
    (by simp only [sub_eq_add_neg] at he; exact he)
  simp only [Function.comp_def] at hh
  rw [deriv_deriv_neg_S_line,add_zero,(hasDerivAt_eta_line c A x h 0 (by simpa using hx)).deriv,
    (hasDerivAt_deriv_eta_line c A x h 0 (by simpa using hx)).deriv] at hh
  simpa only [line_zero] using hh

end
end CurrentKS.State

end OAI
