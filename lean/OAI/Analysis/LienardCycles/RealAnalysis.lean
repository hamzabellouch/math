import OAI.Analysis.LienardCycles.EndpointAlgebra

namespace OAI

open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology

namespace QuinticLienard.RealAnalysis

def IsIsolatedZeroOn (f : ℝ → ℝ) (J : Set ℝ) (x : ℝ) : Prop :=
  x ∈ J ∧ f x = 0 ∧ ∃ ε > 0, ∀ y ∈ Ioo (x-ε) (x+ε), y ∈ J → f y = 0 → y = x

lemma encard_le_two_of_no_three {s : Set ℝ}
    (h : ∀ x ∈ s, ∀ y ∈ s, ∀ z ∈ s, x < y → y < z → False) : s.encard ≤ 2 := by
  by_cases hs : s.Subsingleton
  · exact (encard_le_one_iff_subsingleton.mpr hs).trans (by norm_num)
  obtain ⟨a, ha, b, hb, hab⟩ := Set.not_subsingleton_iff.mp hs
  wlog hablt : a < b generalizing a b
  · exact this b hb a ha hab.symm (lt_of_le_of_ne (le_of_not_gt hablt) hab.symm)
  have hsub : s ⊆ {a,b} := by
    intro x hx
    by_cases hxa : x = a
    · simp [hxa]
    by_cases hxb : x = b
    · simp [hxb]
    exfalso
    rcases lt_or_gt_of_ne hxa with hxa | hxa
    · exact h x hx a ha b hb hxa hablt
    · rcases lt_or_gt_of_ne hxb with hxb | hxb
      · exact h a ha x hx b hb hxa hxb
      · exact h a ha b hb x hx hablt hxb
  exact (encard_mono hsub).trans_eq (encard_pair hab)

lemma middle_zero_not_isolated {f b q : ℝ → ℝ} {J : Set ℝ}
    (hJ : OrdConnected J)
    (hf : ∀ x ∈ J, HasDerivAt f (b x*q x) x)
    (hb : ∀ x ∈ J, 0 < b x) (hq : MonotoneOn q J)
    {x y z : ℝ} (hx : x ∈ J) (hy : y ∈ J) (hz : z ∈ J)
    (hxy : x < y) (hyz : y < z) (hfx : f x = 0) (hfy : f y = 0) (hfz : f z = 0) :
    ¬ IsIsolatedZeroOn f J y := by
  have hfc : ContinuousOn f J := fun t ht ↦ (hf t ht).continuousAt.continuousWithinAt
  have hxyJ := hJ.out hx hy
  have hyzJ := hJ.out hy hz
  obtain ⟨c, hc, hc0⟩ := exists_hasDerivAt_eq_zero hxy (hfc.mono hxyJ)
    (hfx.trans hfy.symm) (fun t ht ↦ hf t (hxyJ (Ioo_subset_Icc_self ht)))
  obtain ⟨d, hd, hd0⟩ := exists_hasDerivAt_eq_zero hyz (hfc.mono hyzJ)
    (hfy.trans hfz.symm) (fun t ht ↦ hf t (hyzJ (Ioo_subset_Icc_self ht)))
  have hcJ : c ∈ J := hxyJ (Ioo_subset_Icc_self hc)
  have hdJ : d ∈ J := hyzJ (Ioo_subset_Icc_self hd)
  have hqc : q c = 0 := (mul_eq_zero.mp hc0).resolve_left (ne_of_gt (hb c hcJ))
  have hqd : q d = 0 := (mul_eq_zero.mp hd0).resolve_left (ne_of_gt (hb d hdJ))
  have hq0 : ∀ t ∈ Ioo c d, q t = 0 := by
    intro t ht
    have htJ := hJ.out hcJ hdJ (Ioo_subset_Icc_self ht)
    exact le_antisymm (hqd ▸ hq htJ hdJ ht.2.le) (hqc ▸ hq hcJ htJ ht.1.le)
  have hconst : ∀ t ∈ Ioo c d, f t = 0 := by
    intro t ht
    have heq : f t = f y := isOpen_Ioo.is_const_of_deriv_eq_zero
      (convex_Ioo c d).isPreconnected
      (fun u hu ↦ (hf u (hJ.out hcJ hdJ (Ioo_subset_Icc_self hu))).differentiableAt.differentiableWithinAt)
      (fun u hu ↦ by rw [(hf u (hJ.out hcJ hdJ (Ioo_subset_Icc_self hu))).deriv, hq0 u hu]; simp)
      ht ⟨hc.2, hd.1⟩
    exact heq.trans hfy
  rintro ⟨_, _, ε, hε, heps⟩
  have hupper : y < min d (y+ε) := lt_min hd.1 (by linarith)
  obtain ⟨v, hyv, hv⟩ := exists_between hupper
  have hvd : v < d := hv.trans_le (min_le_left _ _)
  have hver : v < y+ε := hv.trans_le (min_le_right _ _)
  have hvc : c < v := hc.2.trans hyv
  have hvJ : v ∈ J := hJ.out hcJ hdJ ⟨hvc.le,hvd.le⟩
  have heq := heps v ⟨by linarith, hver⟩ hvJ (hconst v ⟨hvc,hvd⟩)
  exact (ne_of_gt hyv) heq

theorem isolated_zero_count {f b q : ℝ → ℝ} {J : Set ℝ}
    (hJ : OrdConnected J)
    (hf : ∀ x ∈ J, HasDerivAt f (b x*q x) x)
    (hb : ∀ x ∈ J, 0 < b x) (hq : MonotoneOn q J) :
    {x | IsIsolatedZeroOn f J x}.encard ≤ 2 := by
  apply encard_le_two_of_no_three
  intro x hx y hy z hz hxy hyz
  exact middle_zero_not_isolated hJ hf hb hq hx.1 hy.1 hz.1 hxy hyz hx.2.1 hy.2.1 hz.2.1 hy

lemma deriv_nonpos_of_left_min {f : ℝ → ℝ} {a c v : ℝ} (hac : a < c)
    (hd : HasDerivAt f v c) (hmin : ∀ x ∈ Icc a c, f c ≤ f x) : v ≤ 0 := by
  have ht : Tendsto (slope f c) (𝓝[<] c) (𝓝 v) :=
    (hasDerivAt_iff_tendsto_slope.mp hd).mono_left
      (nhdsWithin_mono c (by intro x hx; exact ne_of_lt hx))
  apply le_of_tendsto ht
  filter_upwards [Ioo_mem_nhdsLT hac] with x hx
  rw [slope_def_field]
  exact div_nonpos_of_nonneg_of_nonpos
    (sub_nonneg.mpr (hmin x (Ioo_subset_Icc_self hx))) (sub_nonpos.mpr hx.2.le)

lemma positive_of_deriv_pos_at_zero {f f' : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (ha : 0 ≤ f a) (hzero : ∀ x ∈ Icc a b, f x = 0 → 0 < f' x) : 0 < f b := by
  have hnonneg : ∀ x ∈ Icc a b, 0 ≤ f x := by
    apply image_le_of_deriv_right_lt_deriv_boundary' continuousOn_const
      (fun x _ ↦ (hasDerivAt_const x (0:ℝ)).hasDerivWithinAt) ha hf
      (fun x hx ↦ (hf' x (Ico_subset_Icc_self hx)).hasDerivWithinAt)
    intro x hx heq
    exact hzero x (Ico_subset_Icc_self hx) heq.symm
  have hn := hnonneg b ⟨hab.le, le_rfl⟩
  by_contra! hh
  have hb0 : f b = 0 := le_antisymm hh hn
  have hd := deriv_nonpos_of_left_min hab (hf' b ⟨hab.le, le_rfl⟩)
    (fun x hx ↦ hb0 ▸ hnonneg x hx)
  exact (not_lt_of_ge hd) (hzero b ⟨hab.le, le_rfl⟩ hb0)

theorem at_most_one_zero_of_deriv_pos {f f' : ℝ → ℝ} {J : Set ℝ}
    (hJ : OrdConnected J) (hf : ∀ x ∈ J, HasDerivAt f (f' x) x)
    (hzero : ∀ x ∈ J, f x = 0 → 0 < f' x) :
    {x ∈ J | f x = 0}.encard ≤ 1 := by
  rw [encard_le_one_iff]
  intro a b ha hb
  by_contra hn
  wlog hab : a < b generalizing a b
  · exact this b a hb ha (Ne.symm hn) (lt_of_le_of_ne (le_of_not_gt hab) (Ne.symm hn))
  have hsub := hJ.out ha.1 hb.1
  have hpos := positive_of_deriv_pos_at_zero hab
    (fun x hx ↦ (hf x (hsub hx)).continuousAt.continuousWithinAt)
    (fun x hx ↦ hf x (hsub hx)) (by simp [ha.2])
    (fun x hx ↦ hzero x (hsub hx))
  simp [hb.2] at hpos

end QuinticLienard.RealAnalysis

end OAI
