import Mathlib

namespace OAI

open Set Filter
open scoped Topology

namespace CylinderCovering.LevelCrossing

theorem nonneg_of_left_minimum {f : ℝ → ℝ} {a b d : ℝ}
    (hab : a < b) (hd : HasDerivWithinAt f d (Icc a b) a)
    (hmin : ∀ x ∈ Icc a b, f a ≤ f x) : 0 ≤ d := by
  have hacc : AccPt a (𝓟 (Icc a b)) :=
    uniqueDiffWithinAt_iff_accPt.mp ((uniqueDiffOn_Icc hab) a ⟨le_rfl, hab.le⟩)
  have : (𝓝[Icc a b \ {a}] a).NeBot :=
    accPt_principal_iff_nhdsWithin.mp hacc
  apply ge_of_tendsto (hasDerivWithinAt_iff_tendsto_slope.mp hd)
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [slope_def_field]
  exact div_nonneg (sub_nonneg.mpr (hmin x hx.1)) (sub_nonneg.mpr hx.1.1)

theorem nonneg_of_right_maximum {f : ℝ → ℝ} {a b d : ℝ}
    (hab : a < b) (hd : HasDerivWithinAt f d (Icc a b) b)
    (hmax : ∀ x ∈ Icc a b, f x ≤ f b) : 0 ≤ d := by
  have hacc : AccPt b (𝓟 (Icc a b)) :=
    uniqueDiffWithinAt_iff_accPt.mp ((uniqueDiffOn_Icc hab) b ⟨hab.le, le_rfl⟩)
  have : (𝓝[Icc a b \ {b}] b).NeBot :=
    accPt_principal_iff_nhdsWithin.mp hacc
  apply ge_of_tendsto (hasDerivWithinAt_iff_tendsto_slope.mp hd)
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [slope_def_field]
  exact div_nonneg_of_nonpos (sub_nonpos.mpr (hmax x hx.1)) (sub_nonpos.mpr hx.1.2)

theorem first_level_on_Icc {f : ℝ → ℝ} {a b z : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (ha : f a < z) (hb : z ≤ f b) :
    ∃ r ∈ Ioc a b, f r = z ∧ ∀ x ∈ Icc a r, f x ≤ z := by
  let S : Set ℝ := Icc a b ∩ f ⁻¹' {z}
  have hSclosed : IsClosed S :=
    hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hScompact : IsCompact S :=
    isCompact_Icc.of_isClosed_subset hSclosed inter_subset_left
  obtain ⟨u, hu, hfu⟩ := intermediate_value_Icc hab hf ⟨ha.le, hb⟩
  have hSne : S.Nonempty := ⟨u, hu, hfu⟩
  obtain ⟨r, hr⟩ := hScompact.exists_isLeast hSne
  have hrI : r ∈ Icc a b := hr.1.1
  have hfr : f r = z := hr.1.2
  have har : a < r := by
    apply lt_of_le_of_ne hrI.1
    intro heq
    have : f a = z := heq ▸ hfr
    exact (ne_of_lt ha) this
  refine ⟨r, ⟨har, hrI.2⟩, hfr, ?_⟩
  intro x hx
  by_contra hnot
  have hzx : z < f x := lt_of_not_ge hnot
  have hxb : x ≤ b := hx.2.trans hrI.2
  obtain ⟨v, hv, hfv⟩ := intermediate_value_Icc hx.1
    (hf.mono (Icc_subset_Icc le_rfl hxb)) ⟨ha.le, hzx.le⟩
  have hrv : r ≤ v := hr.2 ⟨⟨hv.1, hv.2.trans hxb⟩, hfv⟩
  have hxr : x = r := le_antisymm hx.2 (hrv.trans hv.2)
  rw [hxr, hfr] at hzx
  exact lt_irrefl z hzx

theorem exists_level_nonneg_derivative {f d : ℝ → ℝ} {a b z : ℝ}
    (hab : a < b) (hf : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Icc a b, HasDerivWithinAt f (d x) (Icc a b) x)
    (ha : f a ≤ z) (hb : z ≤ f b) :
    ∃ r ∈ Icc a b, f r = z ∧ 0 ≤ d r := by
  by_cases hlow : ∀ x ∈ Icc a b, z ≤ f x
  · have haa : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
    have hfa : f a = z := le_antisymm ha (hlow a haa)
    refine ⟨a, haa, hfa, nonneg_of_left_minimum hab (hd a haa) ?_⟩
    intro x hx
    exact ha.trans (hlow x hx)
  · push Not at hlow
    obtain ⟨c, hc, hfc⟩ := hlow
    have hcb : c ≤ b := hc.2
    obtain ⟨r, hr, hfr, hbefore⟩ := first_level_on_Icc hcb
      (hf.mono (Icc_subset_Icc hc.1 le_rfl)) hfc hb
    have hrI : r ∈ Icc a b := ⟨hc.1.trans hr.1.le, hr.2⟩
    refine ⟨r, hrI, hfr, nonneg_of_right_maximum (f := f) hr.1 ?_ ?_⟩
    · exact (hd r hrI).mono (Icc_subset_Icc hc.1 hr.2)
    · intro x hx
      rw [hfr]
      exact hbefore x hx

theorem exists_level_nonneg_derivWithin {f : ℝ → ℝ} {a b z : ℝ}
    (hab : a < b) (hf : DifferentiableOn ℝ f (Icc a b))
    (ha : f a ≤ z) (hb : z ≤ f b) :
    ∃ r ∈ Icc a b, f r = z ∧ 0 ≤ derivWithin f (Icc a b) r :=
  exists_level_nonneg_derivative hab hf.continuousOn
    (fun x hx => (hf x hx).hasDerivWithinAt) ha hb

theorem c1_level_crossing {f : ℝ → ℝ} {a b z : ℝ}
    (hab : a < b) (hf : ContDiffOn ℝ 1 f (Icc a b))
    (ha : f a ≤ z) (hb : z ≤ f b) :
    ∃ r ∈ Icc a b, f r = z ∧ 0 ≤ derivWithin f (Icc a b) r :=
  exists_level_nonneg_derivWithin hab hf.differentiableOn_one ha hb

end CylinderCovering.LevelCrossing

end OAI
