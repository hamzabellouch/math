import Mathlib.Analysis.Calculus.FDeriv.Extend

namespace OAI

/-! Joining two actual ODE solutions at a regular positive radius. -/

open Set Filter Topology
namespace DefocusingNLS

theorem radial_ode_join {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F G : ℝ → E) (V : ℝ → E → E) (b : ℝ) (hb : 0 < b)
    (hFc : ContinuousOn F (Icc 0 b))
    (hF : ∀ r ∈ Ioo 0 b, HasDerivAt F (V r (F r)) r)
    (hG : ∀ r, b ≤ r → HasDerivAt G (V r (G r)) r)
    (hmatch : F b=G b) (hV : ContinuousAt (Function.uncurry V) (b,F b)) :
    ∀ r, 0 < r →
      HasDerivAt (fun t => if t ≤ b then F t else G t)
        (V r (if r ≤ b then F r else G r)) r := by
  intro r hr
  rcases lt_trichotomy r b with hlt | heq | hgt
  · rw [ite_eq_left hlt.le]
    apply (hF r ⟨hr,hlt⟩).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hlt] with t ht
    exact ite_eq_left ht.le
  · subst r
    rw [ite_eq_left le_rfl]
    have hFc' : ContinuousWithinAt F (Iio b) b :=
      (hFc b ⟨hb.le,le_rfl⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsLT hb)
    have hlim : Tendsto (fun t => V t (F t)) (nhdsWithin b (Iio b)) (nhds (V b (F b))) :=
      hV.tendsto.comp (continuousWithinAt_id.prodMk hFc')
    have hlim' : Tendsto (deriv F) (nhdsWithin b (Iio b)) (nhds (V b (F b))) := by
      apply hlim.congr'
      filter_upwards [Ioo_mem_nhdsLT hb] with t ht
      exact (hF t ht).deriv.symm
    have hleft := hasDerivWithinAt_Iic_of_tendsto_deriv
      (fun t ht => (hF t ht).differentiableAt.differentiableWithinAt)
      (hFc'.mono Ioo_subset_Iio_self) (Ioo_mem_nhdsLT hb) hlim'
    have hleft' : HasDerivWithinAt (fun t => if t ≤ b then F t else G t)
        (V b (F b)) (Iic b) b := by
      apply hleft.congr
      · intro t ht
        exact ite_eq_left ht
      · exact ite_eq_left le_rfl
    have hright := hG b le_rfl
    rw [← hmatch] at hright
    have hright' : HasDerivWithinAt (fun t => if t ≤ b then F t else G t)
        (V b (F b)) (Ici b) b := by
      apply hright.hasDerivWithinAt.congr
      · intro t ht
        rcases (show b ≤ t from ht).eq_or_lt with rfl | hlt
        · simpa only [ite_eq_left le_rfl] using hmatch
        · exact ite_eq_right hlt.not_ge
      · simpa only [ite_eq_left le_rfl] using hmatch
    have hh := hleft'.union hright'
    rw [Iic_union_Ici] at hh
    exact hh.hasDerivAt (by simp)
  · rw [ite_eq_right hgt.not_ge]
    apply (hG r hgt.le).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hgt] with t ht
    exact ite_eq_right ht.not_ge

end DefocusingNLS

end OAI
