import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos

namespace OAI

/-! # Removing countably many times from a uniformly Lipschitz cylinder

The spatial estimates persist under the unique continuous time extension.
Only scalar Lipschitz extension and density of the good times are used.
-/

open Set Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates

theorem remove_countable_times {Y : Type*} [PseudoMetricSpace Y]
    {δ : ℝ} (N : Set ℝ) (hN : N.Countable) (G : ℝ → Y → ℝ) (C L : ℝ≥0)
    (htime : ∀ x, LipschitzOnWith C (fun t => G t x) (Ioo δ 1 \ N))
    (hspace : ∀ t ∈ Ioo δ 1, t ∉ N → LipschitzWith L (G t)) :
    ∃ U : ℝ → Y → ℝ,
      (∀ x, LipschitzWith C (fun t => U t x)) ∧
      (∀ t ∈ Ioo δ 1, LipschitzWith L (U t)) ∧
      (∀ t ∈ Ioo δ 1, t ∉ N → ∀ x, U t x = G t x) ∧
      LipschitzOnWith (C+L) (Function.uncurry U) (Ioo δ 1 ×ˢ univ) := by
  classical
  choose V hV he using fun x => (htime x).extend_real
  let U := fun t x => V x t
  have hgood (t : ℝ) (ht : t ∈ Ioo δ 1) (htN : t ∉ N) (x : Y) : U t x = G t x :=
    (he x ⟨ht,htN⟩).symm
  have hcl (t : ℝ) (ht : t ∈ Ioo δ 1) : t ∈ closure (Ioo δ 1 \ N) := by
    have hd : Dense Nᶜ := volume.dense_of_ae (hN.ae_notMem volume)
    have hh := isOpen_Ioo.inter_closure (t := Nᶜ) ⟨ht,hd t⟩
    simpa only [sdiff_eq] using hh
  have hsp (t : ℝ) (ht : t ∈ Ioo δ 1) : LipschitzWith L (U t) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hc : IsClosed {u : ℝ | dist (V x u) (V y u) ≤ L * dist x y} :=
      isClosed_le ((hV x).continuous.dist (hV y).continuous) continuous_const
    have hs : Ioo δ 1 \ N ⊆ {u : ℝ | dist (V x u) (V y u) ≤ L * dist x y} := by
      intro u hu
      change dist (U u x) (U u y) ≤ _
      rw [hgood u hu.1 hu.2 x,hgood u hu.1 hu.2 y]
      exact (hspace u hu.1 hu.2).dist_le_mul x y
    exact (hc.closure_subset_iff.mpr hs) (hcl t ht)
  refine ⟨U,hV,hsp,hgood,?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro q hq q' hq'
  change dist (U q.1 q.2) (U q'.1 q'.2) ≤ _
  have hdt : dist q.1 q'.1 ≤ dist q q' := by simp only [Prod.dist_eq]; exact le_max_left _ _
  have hdx : dist q.2 q'.2 ≤ dist q q' := by simp only [Prod.dist_eq]; exact le_max_right _ _
  calc
    _ ≤ dist (U q.1 q.2) (U q'.1 q.2) + dist (U q'.1 q.2) (U q'.1 q'.2) := dist_triangle _ _ _
    _ ≤ C * dist q.1 q'.1 + L * dist q.2 q'.2 :=
      add_le_add ((hV q.2).dist_le_mul q.1 q'.1) ((hsp q'.1 hq'.1).dist_le_mul q.2 q'.2)
    _ ≤ C * dist q q' + L * dist q q' :=
      add_le_add (mul_le_mul_of_nonneg_left hdt C.coe_nonneg)
        (mul_le_mul_of_nonneg_left hdx L.coe_nonneg)
    _ = _ := by push_cast; ring

end RegularPointCoordinates

end

end OAI
