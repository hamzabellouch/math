import Mathlib

namespace OAI

/-! Higher Directional Jets. -/

section

 

noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace HigherJet
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def dir (v : E) (f : E → F) (x : E) : F := fderiv ℝ f x v

def word : List E → (E → F) → E → F
  | [], f => f
  | v::ws, f => dir v (word ws f)

lemma dir_smoothAt {f : E → F} {x : E} (hf : ContDiffAt ℝ ∞ f x) (v : E) :
    ContDiffAt ℝ ∞ (dir v f) x :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const

lemma dir_smoothOn {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) (v : E) : ContDiffOn ℝ ∞ (dir v f) U :=
  (hf.fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply contDiffOn_const

lemma word_smoothOn {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) (ws : List E) : ContDiffOn ℝ ∞ (word ws f) U := by
  induction ws with
  | nil => exact hf
  | cons v ws ih => exact dir_smoothOn hU ih v

lemma dir_congr {f g : E → F} {x : E} (h : f =ᶠ[𝓝 x] g) (v : E) :
    dir v f x = dir v g x := congrArg (fun T : E →L[ℝ] F => T v) h.fderiv_eq

lemma word_congr {f g : E → F} {x : E} (h : f =ᶠ[𝓝 x] g) (ws : List E) :
    word ws f x = word ws g x := by
  induction ws generalizing x with
  | nil => exact h.self_of_nhds
  | cons v ws ih =>
    exact dir_congr (h.eventually_nhds.mono (fun y hy => ih hy)) v

lemma dir_dir {f : E → F} {x : E} (hf : ContDiffAt ℝ ∞ f x) (u v : E) :
    dir u (dir v f) x = fderiv ℝ (fderiv ℝ f) x u v := by
  have hd := (hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  exact congrArg (fun T : E →L[ℝ] F => T u)
    ((ContinuousLinearMap.apply ℝ F v).hasFDerivAt.comp x hd.hasFDerivAt).fderiv

lemma dir_comm {f : E → F} {x : E} (hf : ContDiffAt ℝ ∞ f x) (u v : E) :
    dir u (dir v f) x = dir v (dir u f) x := by
  rw [dir_dir hf,dir_dir hf]
  exact hf.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top) u v

lemma dir_word_comm {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) (v : E) (ws : List E) {x : E} (hx : x ∈ U) :
    dir v (word ws f) x = word ws (dir v f) x := by
  induction ws generalizing x with
  | nil => rfl
  | cons w ws ih =>
    change dir v (dir w (word ws f)) x = dir w (word ws (dir v f)) x
    rw [dir_comm ((word_smoothOn hU hf ws).contDiffAt (hU.mem_nhds hx))]
    exact dir_congr (by filter_upwards [hU.mem_nhds hx] with y hy using ih hy) w

lemma word_dir_dir_comm {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) (v w : E) (ws : List E) {x : E} (hx : x ∈ U) :
    word ws (dir v (dir w f)) x = dir v (dir w (word ws f)) x := by
  rw [← dir_word_comm hU (dir_smoothOn hU hf w) v ws hx]
  exact dir_congr (by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (dir_word_comm hU hf w ws hy).symm) v

lemma word_ofFn_eq {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) (m : ℕ) (v : Fin m → E) {x : E} (hx : x ∈ U) :
    word (List.ofFn v) f x = iteratedFDeriv ℝ m f x v := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
    rw [List.ofFn_succ]
    change dir (v 0) (word (List.ofFn (fun i => v i.succ)) f) x = _
    have he : word (List.ofFn (fun i => v i.succ)) f =ᶠ[𝓝 x]
        (fun y => iteratedFDeriv ℝ m f y (fun i => v i.succ)) := by
      filter_upwards [hU.mem_nhds hx] with y hy using ih _ hy
    rw [dir_congr he]
    exact (DifferentiableAt.iteratedFDeriv_succ_apply_left'
      (((hf.contDiffAt (hU.mem_nhds hx)).iteratedFDeriv_right
        (m := ∞) (i := m) (by exact WithTop.coe_le_coe.mpr le_top)).differentiableAt (by simp))).symm

lemma norm_word_ofFn_le {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) (m : ℕ) (v : Fin m → E) {x : E} (hx : x ∈ U) :
    ‖word (List.ofFn v) f x‖ ≤ ‖iteratedFDeriv ℝ m f x‖*∏ i, ‖v i‖ := by
  rw [word_ofFn_eq hU hf m v hx]
  exact (iteratedFDeriv ℝ m f x).le_opNorm v
end HigherJet

end
end

end OAI
