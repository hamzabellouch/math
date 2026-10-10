import Mathlib
import OAI.Analysis.MatrixSigning.Potential.PathObjectiveFirst

namespace OAI

open Matrix

namespace CurrentKS.State
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff

variable {d N : ℕ}
private local instance : NormedAddCommGroup (H d) := inferInstance
private local instance : NormedSpace ℝ (H d) := inferInstance
private local instance : TopologicalSpace (H d) :=
  (inferInstance : NormedAddCommGroup (H d)).toUniformSpace.toTopologicalSpace
local instance faceValueDirectionNormedAddCommGroup : NormedAddCommGroup (H d →L[ℝ] H d) := inferInstance
local instance faceValueDirectionNormedSpace : NormedSpace ℝ (H d →L[ℝ] H d) := inferInstance

theorem face_value_direction_variations [NeZero d] {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 < ε)
    (A : Fin N → H d) (x h : Coordinates N) (hx : ∀ i, |x i| < 1)
    (hA : ∀ i, A i ∈ psdCone d) (hrank : ∀ i, (A i : Mat d).rank ≤ 1)
    (S₀ : H d) (K : ℝ) (hlo : -K • (Hermitian.one : H d) ≤ S₀+S A x)
    (hhi : S₀+S A x ≤ K • (Hermitian.one : H d))
    (z : Point d) (hz : z ∈ feasible (S₀+S A x) (eta c A x))
    (hmin : ∀ w ∈ feasible (S₀+S A x) (eta c A x), objective ε z ≤ objective ε w)
    (P Q : H d) (hPpos : P ∈ psdCone d) (hQpos : Q ∈ psdCone d)
    (hP : sandwich (invH z.2.1) P = eta c A x Q + ε • (Hermitian.one : H d))
    (hQ : sandwich (invH z.2.2) Q = eta c A x P + ε • (Hermitian.one : H d)) :
    ∃ U V : H d,
      sandwich (invH z.2.1) U-eta c A x V = S A h+eta₁ c A x h z.2.2 ∧
      sandwich (invH z.2.2) V-eta c A x U = -S A h+eta₁ c A x h z.2.1 ∧
      deriv (fun s => value ε (S₀+S A (line x h s)) (eta c A (line x h s))) 0 =
        ∑ i, h i*((1+c*psi₁ (x i)*inner ℝ (A i) z.2.2)*inner ℝ (A i) P-
          (1-c*psi₁ (x i)*inner ℝ (A i) z.2.1)*inner ℝ (A i) Q) ∧
      deriv (deriv (fun s => value ε (S₀+S A (line x h s)) (eta c A (line x h s)))) 0 ≤
        3*energy z.2.1 z.2.2 P Q U V-(c/2)*negativeWeight A x h z.2.1 z.2.2 P Q := by
  have hS : ContDiffAt ℝ ∞ (fun s => S₀+S A (line x h s)) 0 :=
    contDiffAt_const.add (((contDiff_S A).comp (contDiff_line x h)).contDiffAt)
  have hη : ContDiffAt ℝ ∞ (fun s => eta c A (line x h s)) 0 := by
    have he : ContDiffAt ℝ ∞ (eta c A) (line x h 0) := by
      simpa only [line_zero] using contDiffAt_eta c A hx
    exact he.comp 0 (contDiff_line x h).contDiffAt
  have hp : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ B ∈ psdCone d, eta c A (line x h s) B ∈ psdCone d := by
    filter_upwards [eventually_line_interior x h (a := 0) (by simpa only [line_zero] using hx)] with s hs
    exact eta_positive hc A (fun i => (hs i).le)
  have hs : ∀ᶠ s in 𝓝 (0 : ℝ), SymmetricMap (eta c A (line x h s)) :=
    Filter.Eventually.of_forall fun s => eta_symmetric c A _
  obtain ⟨g,hg,hgc,hres,hd,hdd⟩ := value_derivatives_majorant ε hε
    (fun s => S₀+S A (line x h s)) (fun s => eta c A (line x h s)) 0 hS hη hp hs
    (K := K) (by simpa only [line_zero] using hlo)
    (by simpa only [line_zero] using hhi) z
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
      fun _ => z.1 • (Hermitian.one : H d)-S₀ := by
    filter_upwards [hres] with s hs
    have he := sub_eq_zero.mp (congrArg Prod.fst hs)
    change invH (X s)+(S₀+S A (line x h s))+eta c A (line x h s) (Y s) = _ at he
    rw [eq_sub_iff_add_eq]
    convert he using 1; first | rfl | abel
  have heY : (fun s => invH (Y s)-S A (line x h s)+eta c A (line x h s) (X s)) =ᶠ[𝓝 0]
      fun _ => z.1 • (Hermitian.one : H d)+S₀ := by
    filter_upwards [hres] with s hs
    have he := sub_eq_zero.mp (congrArg Prod.snd hs)
    change invH (Y s)-(S₀+S A (line x h s))+eta c A (line x h s) (X s) = _ at he
    apply (sub_eq_iff_eq_add).mp
    convert he using 1; first | rfl | abel
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

end
end CurrentKS.State

end OAI
