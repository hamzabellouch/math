import Mathlib
import OAI.Analysis.MatrixSigning.Potential.ValueFeasible
import OAI.Analysis.MatrixSigning.Potential.StationaryPairing
import OAI.Analysis.MatrixSigning.Potential.DerivPathObjective

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.State

section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

variable {d N : ℕ}
private local instance : NormedAddCommGroup (H d) := inferInstance
private local instance : NormedSpace ℝ (H d) := inferInstance
private local instance : TopologicalSpace (H d) :=
  (inferInstance : NormedAddCommGroup (H d)).toUniformSpace.toTopologicalSpace

lemma path_objective_first {c ε : ℝ} (A : Fin N → H d) (x h : Coordinates N)
    (hx : ∀ i, |x i| < 1) (hA : ∀ i, A i ∈ psdCone d)
    (hrank : ∀ i, (A i : Mat d).rank ≤ 1) (P Q : H d) {X Y : ℝ → H d}
    (hX : X 0 ∈ pd d) (hY : Y 0 ∈ pd d)
    (hXd : DifferentiableAt ℝ X 0) (hYd : DifferentiableAt ℝ Y 0)
    (hP : sandwich (invH (X 0)) P = eta c A x Q + ε • (Hermitian.one : H d))
    (hQ : sandwich (invH (Y 0)) Q = eta c A x P + ε • (Hermitian.one : H d))
    (BX BY : H d) (t : ℝ)
    (heX : (fun s => invH (X s)+S A (line x h s)+eta c A (line x h s) (Y s)) =ᶠ[𝓝 0] fun _ => BX)
    (heY : (fun s => invH (Y s)-S A (line x h s)+eta c A (line x h s) (X s)) =ᶠ[𝓝 0] fun _ => BY) :
    deriv (fun s => t+ε*Hermitian.realTrace (X s+Y s)) 0 =
      ∑ i, h i*((1+c*psi₁ (x i)*inner ℝ (A i) (Y 0))*inner ℝ (A i) P -
        (1-c*psi₁ (x i)*inner ℝ (A i) (X 0))*inner ℝ (A i) Q) := by
  rw [(hasDerivAt_path_objective hXd.hasDerivAt hYd.hasDerivAt ε t).deriv]
  erw [← stationary_pairing (X 0) (Y 0) P Q (deriv X 0) (deriv Y 0)
    (eta c A x) (eta_symmetric c A x) ε hP hQ]
  erw [first_response_path c A x h hx hX hXd hYd BX heX,
    first_response_path_neg c A x h hx hY hXd hYd BY heY]
  exact first_input_pairing c A x h (X 0) (Y 0) P Q hA hrank

lemma path_objective_second [NeZero d] {c ε : ℝ} (A : Fin N → H d) (x h : Coordinates N)
    (hx : ∀ i, |x i| < 1) (hA : ∀ i, A i ∈ psdCone d)
    (hrank : ∀ i, (A i : Mat d).rank ≤ 1) (P Q : H d) {X Y : ℝ → H d}
    (hX : X 0 ∈ pd d) (hY : Y 0 ∈ pd d)
    (hXc : ContDiffAt ℝ 2 X 0) (hYc : ContDiffAt ℝ 2 Y 0)
    (hP : sandwich (invH (X 0)) P = eta c A x Q + ε • (Hermitian.one : H d))
    (hQ : sandwich (invH (Y 0)) Q = eta c A x P + ε • (Hermitian.one : H d))
    (BX BY : H d) (t : ℝ)
    (heX : (fun s => invH (X s)+S A (line x h s)+eta c A (line x h s) (Y s)) =ᶠ[𝓝 0] fun _ => BX)
    (heY : (fun s => invH (Y s)-S A (line x h s)+eta c A (line x h s) (X s)) =ᶠ[𝓝 0] fun _ => BY) :
    deriv (deriv (fun s => t+ε*Hermitian.realTrace (X s+Y s))) 0 =
      2*energy (X 0) (Y 0) P Q (deriv X 0) (deriv Y 0) +
      mixedTerm c A x h P Q (deriv X 0) (deriv Y 0) - c*negativeWeight A x h (X 0) (Y 0) P Q := by
  rw [deriv_deriv_path_objective hXc hYc ε t]
  erw [← stationary_pairing (X 0) (Y 0) P Q (deriv (deriv X) 0) (deriv (deriv Y) 0)
    (eta c A x) (eta_symmetric c A x) ε hP hQ]
  erw [second_response_path c A x h hx hX hXc hYc BX heX,
    second_response_path_neg c A x h hx hY hXc hYc BY heY]
  exact second_input_pairing c A x h (X 0) (Y 0) P Q (deriv X 0) (deriv Y 0) hA hrank

lemma path_objective_second_le [NeZero d] {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 ≤ ε)
    (A : Fin N → H d) (x h : Coordinates N) (hx : ∀ i, |x i| < 1)
    (hA : ∀ i, A i ∈ psdCone d) (hrank : ∀ i, (A i : Mat d).rank ≤ 1)
    (P Q : H d) (hPpos : P ∈ psdCone d) (hQpos : Q ∈ psdCone d) {X Y : ℝ → H d}
    (hX : X 0 ∈ pd d) (hY : Y 0 ∈ pd d)
    (hXc : ContDiffAt ℝ 2 X 0) (hYc : ContDiffAt ℝ 2 Y 0)
    (hP : sandwich (invH (X 0)) P = eta c A x Q + ε • (Hermitian.one : H d))
    (hQ : sandwich (invH (Y 0)) Q = eta c A x P + ε • (Hermitian.one : H d))
    (BX BY : H d) (t : ℝ)
    (heX : (fun s => invH (X s)+S A (line x h s)+eta c A (line x h s) (Y s)) =ᶠ[𝓝 0] fun _ => BX)
    (heY : (fun s => invH (Y s)-S A (line x h s)+eta c A (line x h s) (X s)) =ᶠ[𝓝 0] fun _ => BY) :
    deriv (deriv (fun s => t+ε*Hermitian.realTrace (X s+Y s))) 0 ≤
      3*energy (X 0) (Y 0) P Q (deriv X 0) (deriv Y 0) - (c/2)*negativeWeight A x h (X 0) (Y 0) P Q := by
  rw [path_objective_second A x h hx hA hrank P Q hX hY hXc hYc hP hQ BX BY t heX heY]
  exact secondExpansion_bound hc hε A x h hx hA hrank (X 0) (Y 0) P Q
    (deriv X 0) (deriv Y 0) hX hY hPpos hQpos hP hQ

end
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff

variable {d N : ℕ}
private local instance : NormedAddCommGroup (H d) := inferInstance
private local instance : NormedSpace ℝ (H d) := inferInstance
private local instance : TopologicalSpace (H d) :=
  (inferInstance : NormedAddCommGroup (H d)).toUniformSpace.toTopologicalSpace
local instance pathObjectiveFirstNormedAddCommGroup : NormedAddCommGroup (H d →L[ℝ] H d) := inferInstance
local instance pathObjectiveFirstNormedSpace : NormedSpace ℝ (H d →L[ℝ] H d) := inferInstance

theorem value_direction_variations [NeZero d] {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 < ε)
    (A : Fin N → H d) (x h : Coordinates N) (hx : ∀ i, |x i| < 1)
    (hA : ∀ i, A i ∈ psdCone d) (hrank : ∀ i, (A i : Mat d).rank ≤ 1)
    (htr : ∑ i, Hermitian.realTrace (A i) = 1)
    (z : Point d) (hz : z ∈ feasible (S A x) (eta c A x))
    (hmin : ∀ w ∈ feasible (S A x) (eta c A x), objective ε z ≤ objective ε w)
    (P Q : H d) (hPpos : P ∈ psdCone d) (hQpos : Q ∈ psdCone d)
    (hP : sandwich (invH z.2.1) P = eta c A x Q + ε • (Hermitian.one : H d))
    (hQ : sandwich (invH z.2.2) Q = eta c A x P + ε • (Hermitian.one : H d)) :
    ∃ U V : H d,
      sandwich (invH z.2.1) U-eta c A x V = S A h+eta₁ c A x h z.2.2 ∧
      sandwich (invH z.2.2) V-eta c A x U = -S A h+eta₁ c A x h z.2.1 ∧
      deriv (fun s => value ε (S A (line x h s)) (eta c A (line x h s))) 0 =
        ∑ i, h i*((1+c*psi₁ (x i)*inner ℝ (A i) z.2.2)*inner ℝ (A i) P-
          (1-c*psi₁ (x i)*inner ℝ (A i) z.2.1)*inner ℝ (A i) Q) ∧
      deriv (deriv (fun s => value ε (S A (line x h s)) (eta c A (line x h s)))) 0 ≤
        3*energy z.2.1 z.2.2 P Q U V-(c/2)*negativeWeight A x h z.2.1 z.2.2 P Q := by
  have hS : ContDiffAt ℝ ∞ (fun s => S A (line x h s)) 0 :=
    ((contDiff_S A).comp (contDiff_line x h)).contDiffAt
  have hη : ContDiffAt ℝ ∞ (fun s => eta c A (line x h s)) 0 := by
    have he : ContDiffAt ℝ ∞ (eta c A) (line x h 0) := by
      simpa only [line_zero] using contDiffAt_eta c A hx
    exact he.comp 0 (contDiff_line x h).contDiffAt
  have hp : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ B ∈ psdCone d, eta c A (line x h s) B ∈ psdCone d := by
    filter_upwards [eventually_line_interior x h (a := 0) (by simpa only [line_zero] using hx)] with s hs
    exact eta_positive hc A (fun i => (hs i).le)
  have hs : ∀ᶠ s in 𝓝 (0 : ℝ), SymmetricMap (eta c A (line x h s)) :=
    Filter.Eventually.of_forall fun s => eta_symmetric c A _
  obtain ⟨hlo,hhi⟩ := S_bounds A hA htr (fun i => (hx i).le)
  obtain ⟨g,hg,hgc,hres,hd,hdd⟩ := value_derivatives_majorant ε hε
    (fun s => S A (line x h s)) (fun s => eta c A (line x h s)) 0 hS hη hp hs
    (K := 1) (by
      simpa only [line_zero,show (-1 : ℝ) • (Hermitian.one : H d) = -Hermitian.one by module] using hlo)
    (by simpa only [line_zero,one_smul,neg_one_smul] using hhi) z
    (by simpa only [line_zero] using hz) (by simpa only [line_zero] using hmin)
  let X : ℝ → H d := fun s => (g s).1
  let Y : ℝ → H d := fun s => (g s).2
  have hX0 : X 0 = z.2.1 := congrArg Prod.fst hg
  have hY0 : Y 0 = z.2.2 := congrArg Prod.snd hg
  have hX : X 0 ∈ pd d := hX0 ▸ hz.1.1
  have hY : Y 0 ∈ pd d := hY0 ▸ hz.1.2
  have hXc : ContDiffAt ℝ 2 X 0 := contDiffAt_infty.mp hgc.fst 2
  have hYc : ContDiffAt ℝ 2 Y 0 := contDiffAt_infty.mp hgc.snd 2
  have heX : (fun s => invH (X s)+S A (line x h s)+eta c A (line x h s) (Y s)) =ᶠ[𝓝 0]
      fun _ => z.1 • (Hermitian.one : H d) := by
    filter_upwards [hres] with s hs
    exact sub_eq_zero.mp (congrArg Prod.fst hs)
  have heY : (fun s => invH (Y s)-S A (line x h s)+eta c A (line x h s) (X s)) =ᶠ[𝓝 0]
      fun _ => z.1 • (Hermitian.one : H d) := by
    filter_upwards [hres] with s hs
    exact sub_eq_zero.mp (congrArg Prod.snd hs)
  have hPX : sandwich (invH (X 0)) P = eta c A x Q+ε • (Hermitian.one : H d) := by rw [hX0]; exact hP
  have hQY : sandwich (invH (Y 0)) Q = eta c A x P+ε • (Hermitian.one : H d) := by rw [hY0]; exact hQ
  refine ⟨deriv X 0,deriv Y 0,?_,?_,?_,?_⟩
  · simpa only [hX0,hY0] using first_response_path c A x h hx hX
      (hXc.differentiableAt (by norm_num)) (hYc.differentiableAt (by norm_num)) _ heX
  · simpa only [hX0,hY0] using first_response_path_neg c A x h hx hY
      (hXc.differentiableAt (by norm_num)) (hYc.differentiableAt (by norm_num)) _ heY
  · rw [hd]
    simpa only [objective,hX0,hY0] using path_objective_first A x h hx hA hrank P Q hX hY
      (hXc.differentiableAt (by norm_num)) (hYc.differentiableAt (by norm_num)) hPX hQY _ _ z.1 heX heY
  · apply hdd.trans
    simpa only [objective,hX0,hY0] using path_objective_second_le hc hε.le A x h hx hA hrank
      P Q hPpos hQpos hX hY hXc hYc hPX hQY _ _ z.1 heX heY

end CurrentKS.State

end

end OAI
