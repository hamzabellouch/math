import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMinimumPrinciple

namespace OAI

/-! A positive limiting free amplitude cannot leave and then return to its unit plateau. -/

open Set Filter Topology
namespace DefocusingNLS

theorem radial_subunit_no_return (R : ℝ) (A D V : ℝ → ℝ) (hA : Continuous A)
    (hAI : ∀ r ∈ Icc 0 R, A r ∈ Ioc 0 1)
    (hAD : ∀ r ∈ Ioo 0 R, HasDerivAt A (D r) r)
    (hDE : ∀ r ∈ Ioo 0 R, A r < 1 → HasDerivAt D (-11/r*D r-V r*A r) r)
    (hV : ∀ r ∈ Ioo 0 R, 0 < V r)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ R)
    (hAa : A a=1) (hAb : A b=1) : ∀ r ∈ Icc a b, A r=1 := by
  intro r hr
  have hrR : r ∈ Icc 0 R := ⟨ha.trans hr.1,hr.2.trans hb⟩
  by_contra hne
  have hr1 : A r < 1 := lt_of_le_of_ne (hAI r hrR).2 hne
  obtain ⟨c,hc,hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab.le) hA.continuousOn
  have hc1 : A c < 1 := (hmin hr).trans_lt hr1
  have hac : a < c := lt_of_le_of_ne hc.1 (by intro he; subst c; linarith)
  have hcb : c < b := lt_of_le_of_ne hc.2 (by intro he; subst c; linarith)
  have hcR : c ∈ Ioo 0 R := ⟨ha.trans_lt hac,hcb.trans_le hb⟩
  have hlocal : IsLocalMin A c := hmin.isLocalMin (Icc_mem_nhds hac hcb)
  have hD0 : D c=0 := by rw [← (hAD c hcR).deriv]; exact hlocal.deriv_eq_zero
  have he : deriv A =ᶠ[𝓝 c] D := by
    filter_upwards [Ioo_mem_nhds hcR.1 hcR.2] with t ht
    exact (hAD t ht).deriv
  have hsecond := radial_local_min_second_nonneg A c hA.continuousAt hlocal
  rw [he.deriv_eq,(hDE c hcR hc1).deriv,hD0] at hsecond
  have hprod := mul_pos (hV c hcR) (hAI c ⟨hcR.1.le,hcR.2.le⟩).1
  nlinarith

end DefocusingNLS

end OAI
