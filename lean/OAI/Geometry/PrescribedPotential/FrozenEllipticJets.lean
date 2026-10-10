import Mathlib
import OAI.Geometry.PrescribedPotential.RealJetEnergy

namespace OAI

/-! Frozen Elliptic Jets. -/

section

 

noncomputable section
open Set Filter Topology Finset
open scoped ContDiff
namespace HigherJet
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {ι : Type*} [Fintype ι]

def hessian (u : E → F) : E → E →L[ℝ] E →L[ℝ] F := fderiv ℝ (fderiv ℝ u)

lemma hessian_smoothOn {U : Set E} (hU : IsOpen U) {u : E → F}
    (hu : ContDiffOn ℝ ∞ u U) : ContDiffOn ℝ ∞ (hessian u) U :=
  (hu.fderiv_of_isOpen hU (m := ∞) (by simp)).fderiv_of_isOpen hU (m := ∞) (by simp)

lemma word_sum {U : Set E} (hU : IsOpen U) (u : ι → E → F)
    (hu : ∀ i, ContDiffOn ℝ ∞ (u i) U) (ws : List E) {x : E} (hx : x ∈ U) :
    word ws (fun y => ∑ i, u i y) x = ∑ i, word ws (u i) x := by
  induction ws generalizing x with
  | nil => rfl
  | cons w ws ih =>
    change dir w (word ws (fun y => ∑ i, u i y)) x = _
    rw [dir_congr (by filter_upwards [hU.mem_nhds hx] with y hy using ih hy)]
    exact dir_sum _ (fun i => ((word_smoothOn hU (hu i) ws).contDiffAt
      (hU.mem_nhds hx)).differentiableAt (by simp)) w

lemma word_sub {U : Set E} (hU : IsOpen U) {f g : E → F}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (ws : List E) {x : E} (hx : x ∈ U) :
    word ws (fun y => f y-g y) x = word ws f x-word ws g x := by
  induction ws generalizing x with
  | nil => rfl
  | cons w ws ih =>
    change dir w (word ws (fun y => f y-g y)) x = _
    rw [dir_congr (by filter_upwards [hU.mem_nhds hx] with y hy using ih hy)]
    exact congrArg (fun T : E →L[ℝ] F => T w)
      ((((word_smoothOn hU hf ws).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt.sub
       (((word_smoothOn hU hg ws).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt).fderiv

lemma frameLaplace_word {U : Set E} (hU : IsOpen U) {u : E → F}
    (hu : ContDiffOn ℝ ∞ u U) (v : ι → E) (ws : List E) {x : E} (hx : x ∈ U) :
    frameLaplace v (word ws u) x = word ws (frameLaplace v u) x := by
  rw [show frameLaplace v u = fun y => ∑ i, dir (v i) (dir (v i) u) y from rfl,
    word_sum hU _ (fun i => dir_smoothOn hU (dir_smoothOn hU hu _) _) ws hx]
  apply Finset.sum_congr rfl
  intro i _
  exact (word_dir_dir_comm hU hu _ _ ws hx).symm

lemma frozen_equation_word (B : G →L[ℝ] (E →L[ℝ] E →L[ℝ] F) →L[ℝ] F)
    {U : Set E} (hU : IsOpen U) {u r : E → F} {a : E → G}
    (hu : ContDiffOn ℝ ∞ u U) (hr : ContDiffOn ℝ ∞ r U)
    (ha : ContDiffOn ℝ ∞ a U) (heq : ∀ y ∈ U, B (a y) (hessian u y) = r y)
    {x : E} (hx : x ∈ U) (v : ι → E)
    (hframe : ∀ H : E →L[ℝ] E →L[ℝ] F, B (a x) H = ∑ i, H (v i) (v i))
    (ws : List E) :
    frameLaplace v (word ws u) x = word ws r x-
      word ws (fun y => B (a y-a x) (hessian u y)) x := by
  have hg : frameLaplace v u =ᶠ[𝓝 x]
      (fun y => r y-B (a y-a x) (hessian u y)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    rw [← heq y hy,map_sub,sub_apply,sub_sub_cancel]
    rw [hframe]
    apply Finset.sum_congr rfl
    intro i _
    exact dir_dir (hu.contDiffAt (hU.mem_nhds hy)) _ _
  rw [frameLaplace_word hU hu v ws hx,word_congr hg]
  exact word_sub hU hr ((B.contDiff.comp_contDiffOn (ha.sub contDiffOn_const)).clm_apply (hessian_smoothOn hU hu)) ws hx

end HigherJet

end
end

end OAI
