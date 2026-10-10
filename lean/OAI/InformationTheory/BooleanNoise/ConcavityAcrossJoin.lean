import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.Linarith

namespace OAI

noncomputable section

open Set

namespace LeanBlast.CourtadeKumar

theorem antitoneOn_Ioi_of_hasDerivAt_nonpos_except
    (f f' : ℝ → ℝ) (a c : ℝ)
    (hf : ContinuousOn f (Ioi a))
    (hd : ∀ x, a < x → x ≠ c → HasDerivAt f (f' x) x)
    (hneg : ∀ x, a < x → x ≠ c → f' x ≤ 0) :
    AntitoneOn f (Ioi a) := by
  have hsegment (l r : ℝ) (hal : a < l) (hlr : l ≤ r)
      (hc : c ∉ Ioo l r) : f r ≤ f l := by
    have hanti : AntitoneOn f (Icc l r) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (f' := f') (convex_Icc l r)
      · exact hf.mono (fun _ hz => hal.trans_le hz.1)
      · intro z hz
        rw [interior_Icc] at hz
        have hzc : z ≠ c := by
          rintro rfl
          exact hc hz
        exact (hd z (hal.trans hz.1) hzc).hasDerivWithinAt
      · intro z hz
        rw [interior_Icc] at hz
        have hzc : z ≠ c := by
          rintro rfl
          exact hc hz
        exact hneg z (hal.trans hz.1) hzc
    exact hanti ⟨le_rfl, hlr⟩ ⟨hlr, le_rfl⟩ hlr
  intro x hx y hy hxy
  by_cases hc : c ∈ Ioo x y
  · exact (hsegment c y (hx.trans hc.1) hc.2.le (by simp)).trans
      (hsegment x c hx hc.1.le (by simp))
  · exact hsegment x y hx hxy hc

theorem concaveOn_Ioi_of_hasDerivAt2_nonpos_except
    (f f' f'' : ℝ → ℝ) (a c : ℝ)
    (hd : ∀ x, a < x → HasDerivAt f (f' x) x)
    (hcf' : ContinuousOn f' (Ioi a))
    (hd' : ∀ x, a < x → x ≠ c → HasDerivAt f' (f'' x) x)
    (hneg : ∀ x, a < x → x ≠ c → f'' x ≤ 0) :
    ConcaveOn ℝ (Ioi a) f := by
  have hanti := antitoneOn_Ioi_of_hasDerivAt_nonpos_except f' f'' a c hcf' hd' hneg
  apply AntitoneOn.concaveOn_of_deriv (convex_Ioi a)
  · intro x hx
    exact (hd x hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    exact (hd x hx).differentiableAt.differentiableWithinAt
  · intro x hx y hy hxy
    rw [interior_Ioi] at hx hy
    rw [(hd x hx).deriv, (hd y hy).deriv]
    exact hanti hx hy hxy

end LeanBlast.CourtadeKumar

end

end OAI
