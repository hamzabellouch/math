import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Topology.Order.OrderClosed

namespace OAI

/-! Matching real derivatives across the two interfaces of a radial barrier. -/

open Set Filter Topology
namespace DefocusingNLS

noncomputable def radialSplice (c : ℝ) (f g : ℝ → ℝ) (x : ℝ) : ℝ := if x ≤ c then f x else g x

theorem hasDerivAt_radialSplice_left (c x d : ℝ) (f g : ℝ → ℝ)
    (hx : x < c) (hf : HasDerivAt f d x) : HasDerivAt (radialSplice c f g) d x := by
  apply hf.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hx] with t ht
  exact ite_eq_left ht.le

theorem hasDerivAt_radialSplice_right (c x d : ℝ) (f g : ℝ → ℝ)
    (hx : c < x) (hg : HasDerivAt g d x) : HasDerivAt (radialSplice c f g) d x := by
  apply hg.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with t ht
  exact ite_eq_right ht.not_ge

theorem hasDerivAt_radialSplice_at (c d : ℝ) (f g : ℝ → ℝ)
    (hf : HasDerivAt f d c) (hg : HasDerivAt g d c) (hfg : f c=g c) :
    HasDerivAt (radialSplice c f g) d c := by
  have hl : HasDerivWithinAt (radialSplice c f g) d (Iic c) c := by
    apply hf.hasDerivWithinAt.congr
    · intro t ht
      exact ite_eq_left ht
    · exact ite_eq_left le_rfl
  have hr : HasDerivWithinAt (radialSplice c f g) d (Ici c) c := by
    apply hg.hasDerivWithinAt.congr
    · intro t ht
      change c ≤ t at ht
      rcases ht.eq_or_lt with he | he
      · subst t
        simpa only [radialSplice,ite_eq_left le_rfl] using hfg
      · exact ite_eq_right he.not_ge
    · simpa only [radialSplice,ite_eq_left le_rfl] using hfg
  have h := hl.union hr
  rw [Iic_union_Ici] at h
  exact h.hasDerivAt (by simp)

theorem hasDerivAt_radialSplice (c : ℝ) (f g df dg : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (df x) x) (hg : ∀ x, HasDerivAt g (dg x) x)
    (hv : f c=g c) (hd : df c=dg c) (x : ℝ) :
    HasDerivAt (radialSplice c f g) (radialSplice c df dg x) x := by
  rcases lt_trichotomy x c with hx | hxc | hx
  · simpa only [radialSplice,ite_eq_left hx.le] using hasDerivAt_radialSplice_left c x (df x) f g hx (hf x)
  · subst x
    simp only [radialSplice,ite_eq_left le_rfl]
    exact hasDerivAt_radialSplice_at c (df c) f g (hf c) (hd.symm ▸ hg c) hv
  · simpa only [radialSplice,ite_eq_right hx.not_ge] using hasDerivAt_radialSplice_right c x (dg x) f g hx (hg x)

end DefocusingNLS

end OAI
