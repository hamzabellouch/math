import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Separation.Basic

namespace OAI

/-! Square-summable dust tolls are upper semicontinuous in every T1
topology. Consequently, the supremum toll on shrinking jump neighborhoods
has limit superior at most the toll at the limiting dust point. -/

open Set Filter
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [TopologicalSpace X] [T1Space X]

omit [TopologicalSpace X] [T1Space X] in
theorem finite_toll_superlevel {m : X → ℝ≥0∞} (hm : (∑' x, m x ^ 2) ≠ ∞)
    {a : ℝ≥0∞} (ha : a ≠ 0) : {x | a ≤ m x}.Finite := by
  apply (ENNReal.finite_const_le_of_tsum_ne_top hm (pow_ne_zero 2 ha)).subset
  intro x hx
  change a ≤ m x at hx
  exact pow_le_pow_left' hx 2

theorem square_summable_toll_upperSemicontinuous {m : X → ℝ≥0∞}
    (hm : (∑' x, m x ^ 2) ≠ ∞) : UpperSemicontinuous m := by
  apply upperSemicontinuous_iff_isClosed_preimage.mpr
  intro a
  by_cases ha : a = 0
  · simp [ha]
  · exact (finite_toll_superlevel hm ha).isClosed

def neighborhoodTollSup (m : X → ℝ≥0∞) (U : Set X) : ℝ≥0∞ := ⨆ x ∈ U, m x

omit [T1Space X] in
theorem eventually_neighborhoodTollSup_le {m : X → ℝ≥0∞}
    (hm : UpperSemicontinuous m) {s : X} {U : ℕ → Set X}
    (hU : ∀ V ∈ 𝓝 s, ∀ᶠ j in atTop, U j ⊆ V)
    {a : ℝ≥0∞} (ha : m s < a) :
    ∀ᶠ j in atTop, neighborhoodTollSup m (U j) ≤ a := by
  have hv : {x | m x < a} ∈ 𝓝 s := hm s a ha
  filter_upwards [hU _ hv] with j hj
  exact iSup_le fun x => iSup_le fun hx => (hj hx).le

theorem shrinking_jump_toll_limsup {m : X → ℝ≥0∞}
    (hm : (∑' x, m x ^ 2) ≠ ∞) {s : X} {U : ℕ → Set X}
    (hU : ∀ V ∈ 𝓝 s, ∀ᶠ j in atTop, U j ⊆ V)
    {ρ : ℕ → ℝ≥0∞} (hρ : Tendsto ρ atTop (𝓝 0)) :
    limsup (fun j => max (ρ j) (neighborhoodTollSup m (U j))) atTop ≤ m s := by
  apply le_of_forall_gt
  intro a ha
  obtain ⟨b, hb, hba⟩ := exists_between ha
  have ht := eventually_neighborhoodTollSup_le
    (square_summable_toll_upperSemicontinuous hm) hU hb
  have hr : ∀ᶠ j in atTop, ρ j < b := hρ.eventually (gt_mem_nhds (lt_of_le_of_lt bot_le hb))
  apply lt_of_le_of_lt (limsup_le_of_le (a := b) (h := ?_)) hba
  filter_upwards [ht, hr] with j hj hρj
  exact max_le hρj.le hj

end CircleDomainRigidity

end

end OAI
