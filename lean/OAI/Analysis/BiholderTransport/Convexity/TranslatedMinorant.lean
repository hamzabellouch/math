import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.QuadraticTest

namespace OAI

section
section
noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
section TranslatedMinorant
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma HasLowerSecondTaylor.exists_smooth_minorant_at {f : E → ℝ} {x : E}
    {l : E →L[ℝ] ℝ} {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hf : HasLowerSecondTaylor (fun h => f (x+h)) l B) {ε : ℝ} (hε : 0<ε) :
    ∃ q:E → ℝ,ContDiffAt ℝ 2 q x ∧ q x=f x ∧ fderiv ℝ q x=l ∧
      (∀ᶠ y in 𝓝 x,q y≤f y) ∧
      ∀ d:E,fderiv ℝ (fderiv ℝ q) x d d=B d d-ε*‖d‖^2 := by
  obtain ⟨q,hq,hval,hd,hlo,hH⟩ := hf.exists_smooth_minorant hε
  let Q : E → ℝ := fun y => q (y-x)
  have hQ : ContDiffAt ℝ 2 Q x :=
    (show ContDiffAt ℝ 2 q (x-x) by simpa only [sub_self] using hq).comp (f := fun y:E => y-x) x
      (contDiffAt_id.sub contDiffAt_const)
  have hshift : ∀ y:E,fderiv ℝ Q y=fderiv ℝ q (y-x) := by
    intro y
    simpa only [Q,sub_eq_add_neg] using (fderiv_comp_add_right (-x) (f := q) (x := y))
  refine ⟨Q,hQ,?_,?_,?_,?_⟩
  · simpa only [Q,sub_self,add_zero] using hval
  · rw [hshift,sub_self,hd]
  · have ht : Tendsto (fun y:E => y-x) (𝓝 x) (𝓝 (0:E)) := by
      convert! ((tendsto_id : Tendsto (fun y:E => y) (𝓝 x) (𝓝 x)).sub
        (tendsto_const_nhds (x := x))) using 1
      simp only [sub_self]
    filter_upwards [ht.eventually hlo] with y hy
    simpa only [Q,add_sub_cancel] using hy
  · intro d
    rw [show fderiv ℝ Q=(fun y => fderiv ℝ q (y-x)) from funext hshift]
    have HH := fderiv_comp_add_right (𝕜 := ℝ) (-x) (f := fderiv ℝ q) (x := x)
    simp only [←sub_eq_add_neg,sub_self] at HH
    rw [HH]
    exact hH d

end TranslatedMinorant
end WeakMTWTransport

end

end

end

end OAI
