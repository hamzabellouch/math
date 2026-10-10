import OAI.GroupTheory.PolycyclicRecognition.Geometry.FlowLineLabels
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Instances.Rat

namespace OAI

/-! # A countable interval cover of admissible flow segments -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter Metric

theorem exists_rational_interval_in_open
    {U : Set ℝ} (hU : IsOpen U) {s t : ℝ} (hseg : Icc (min s t) (max s t) ⊆ U) :
    ∃ a b : ℚ, s ∈ Ioo (a : ℝ) b ∧ t ∈ Ioo (a : ℝ) b ∧ Icc (a : ℝ) b ⊆ U := by
  obtain ⟨δ, hδ, hthick⟩ := isCompact_Icc.exists_cthickening_subset_open hU hseg
  obtain ⟨a, ha₀, ha₁⟩ := exists_rat_btwn (show min s t - δ < min s t by linarith)
  obtain ⟨b, hb₀, hb₁⟩ := exists_rat_btwn (show max s t < max s t + δ by linarith)
  refine ⟨a, b, ⟨ha₁.trans_le (min_le_left _ _), (le_max_left _ _).trans_lt hb₀⟩,
    ⟨ha₁.trans_le (min_le_right _ _), (le_max_right _ _).trans_lt hb₀⟩, ?_⟩
  intro u hu
  apply hthick
  by_cases hlow : u < min s t
  · apply mem_cthickening_of_dist_le u (min s t) δ (Icc (min s t) (max s t))
      ⟨le_rfl, min_le_max⟩
    rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hlow)]
    linarith [hu.1]
  · by_cases hhigh : max s t < u
    · apply mem_cthickening_of_dist_le u (max s t) δ (Icc (min s t) (max s t))
        ⟨min_le_max, le_rfl⟩
      rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hhigh)]
      linarith [hu.2]
    · exact self_subset_cthickening (Icc (min s t) (max s t)) ⟨le_of_not_gt hlow, le_of_not_gt hhigh⟩

def rationalFlowBox
    {G V : Type*} [Group G] [SMul ℝ V]
    (U : Set G) (Exp : V → G) (v : V) (q : ℚ × ℚ) : Set ((ℝ × ℝ) × G) :=
  {z | z.1.1 ∈ Ioo (q.1 : ℝ) q.2 ∧ z.1.2 ∈ Ioo (q.1 : ℝ) q.2 ∧
    ∀ a ∈ Icc (q.1 : ℝ) q.2, z.2 * Exp (a • v) ∈ U}

theorem flowSegmentDomain_eq_iUnion_rationalFlowBox
    {G V : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (U : Set G) (hU : IsOpen U) (Exp : V → G) (hExp : Continuous Exp) (v : V) :
    flowSegmentDomain U Exp v = ⋃ q : ℚ × ℚ, rationalFlowBox U Exp v q := by
  ext z
  constructor
  · intro hz
    have ho : IsOpen {t : ℝ | z.2 * Exp (t • v) ∈ U} := hU.preimage (by fun_prop)
    have hs : Icc (min z.1.1 z.1.2) (max z.1.1 z.1.2) ⊆
        {t : ℝ | z.2 * Exp (t • v) ∈ U} := by
      intro t ht
      have ht' : t ∈ segment ℝ z.1.1 z.1.2 := by rwa [segment_eq_Icc']
      rw [segment_eq_image] at ht'
      obtain ⟨r, hr, rfl⟩ := ht'
      change z.2 * Exp (((1 - r) • z.1.1 + r • z.1.2) • v) ∈ U
      simpa only [flowSegmentPoint, smul_eq_mul] using hz r hr
    obtain ⟨a, b, hs, ht, hab⟩ := exists_rational_interval_in_open ho hs
    exact mem_iUnion.mpr ⟨(a, b), hs, ht, hab⟩
  · intro hz
    obtain ⟨q, hs, ht, hab⟩ := mem_iUnion.mp hz
    intro r hr
    apply hab
    have hh := (convex_Icc (q.1 : ℝ) q.2) ⟨hs.1.le, hs.2.le⟩ ⟨ht.1.le, ht.2.le⟩
      (sub_nonneg.mpr hr.2) hr.1 (show (1 - r) + r = 1 by ring)
    simpa only [smul_eq_mul] using hh

end PolycyclicRecognition

end

end OAI
