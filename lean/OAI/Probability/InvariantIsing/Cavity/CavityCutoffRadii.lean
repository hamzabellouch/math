import OAI.Probability.InvariantIsing.Cavity.CavityBoundaryCutoff
import Mathlib.MeasureTheory.Measure.Portmanteau

namespace OAI

/-! One sequence of increasing cutoff radii can avoid every boundary
atom of a countable family of limiting replica laws. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace InvariantIsing

lemma cavity_radius_atoms_countable {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] (R : X → ℝ) (hR : Measurable R) :
    Set.Countable {B : ℝ | μ {x | R x=B} ≠ 0} := by
  have hm B : MeasurableSet {x | R x=B} := measurableSet_eq_fun hR measurable_const
  have hd : Pairwise (fun B C : ℝ => Disjoint {x | R x=B} {x | R x=C}) := by
    intro B C hBC
    exact Set.disjoint_left.mpr (fun x hx hy => hBC (hx.symm.trans hy))
  simpa only [pos_iff_ne_zero] using Measure.countable_meas_pos_of_disjoint_iUnion hm hd

theorem cavity_common_null_cutoff_radii {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (μ : (n : ℕ) → Measure (X n)) [∀ n, SFinite (μ n)]
    (R : (n : ℕ) → X n → ℝ) (hR : ∀ n, Measurable (R n)) :
    ∃ B : ℕ → ℝ, Tendsto B atTop atTop ∧
      ∀ j : ℕ, (j : ℝ)+1 < B j ∧ B j < (j : ℝ)+2 ∧
        ∀ n, μ n {x | R n x=B j}=0 := by
  let S : Set ℝ := ⋃ n, {B : ℝ | μ n {x | R n x=B} ≠ 0}
  have hS : S.Countable := Set.countable_iUnion (fun n => cavity_radius_atoms_countable (μ n) (R n) (hR n))
  have hex (j : ℕ) : ∃ B ∈ Set.Ioo ((j : ℝ)+1) ((j : ℝ)+2), B ∉ S := by
    have he := measure_sdiff_null (s := Set.Ioo ((j : ℝ)+1) ((j : ℝ)+2)) (hS.measure_zero volume)
    have hp : 0 < volume (Set.Ioo ((j : ℝ)+1) ((j : ℝ)+2) \ S) := by
      rw [he,Real.volume_Ioo]
      exact ENNReal.ofReal_pos.mpr (by linarith)
    obtain ⟨B,hB⟩ := nonempty_of_measure_ne_zero hp.ne'
    exact ⟨B,hB.1,hB.2⟩
  choose B hB hBS using hex
  refine ⟨B, ?_, fun j => ⟨(hB j).1,(hB j).2,?_⟩⟩
  · apply tendsto_atTop.mpr
    intro b
    obtain ⟨n,hn⟩ := exists_nat_gt b
    filter_upwards [eventually_ge_atTop n] with j hj
    have hnj : (n : ℝ) ≤ j := Nat.cast_le.mpr hj
    linarith [(hB j).1]
  · intro n
    by_contra hn
    exact hBS j (Set.mem_iUnion_of_mem n hn)

end InvariantIsing

end

end OAI
