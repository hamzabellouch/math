import OAI.GroupTheory.PolycyclicRecognition.Algebra.UniformUnitNetBound
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteCutoffPartition
import Mathlib.Algebra.BigOperators.Finsupp.Basic

namespace OAI

/-! # Finitely supported cutoff weights on the infinite unit net -/

noncomputable section
namespace PolycyclicRecognition

open Set Metric
open scoped BigOperators

variable {X : Type*} [MetricSpace X] [ProperSpace X]
  {V : Set X} (hV : V.Pairwise (fun x y => 1 < dist x y))

include hV in
theorem finite_subtype_unit_net_ball (x : X) (R : ℝ) :
    {v : V | dist x v ≤ R}.Finite := by
  have h := (finite_unit_net_ball hV x R).preimage_embedding (Function.Embedding.subtype V)
  apply h.subset
  intro v hv
  change dist x v.val ≤ R at hv
  refine ⟨v.property, ?_⟩
  change dist v.val x ≤ R
  simpa only [dist_comm] using hv

def unitNetMass (x : X) : V →₀ ℝ :=
  Finsupp.ofSupportFinite (fun v => max 0 (2 - dist x v)) (by
    apply (finite_subtype_unit_net_ball hV x 2).subset
    intro v hv
    change max 0 (2 - dist x v) ≠ 0 at hv
    change dist x v ≤ 2
    by_contra hn
    apply hv
    exact max_eq_left (by linarith))

@[simp] theorem unitNetMass_apply (x : X) (v : V) :
    unitNetMass hV x v = max 0 (2 - dist x v) := rfl

theorem mem_support_unitNetMass_iff (x : X) (v : V) :
    v ∈ (unitNetMass hV x).support ↔ dist x v < 2 := by
  rw [Finsupp.mem_support_iff, unitNetMass_apply]
  constructor
  · intro h
    by_contra hn
    exact h (max_eq_left (by linarith))
  · intro h he
    have := le_max_right (0 : ℝ) (2 - dist x v)
    rw [he] at this
    linarith

def unitNetTotal (x : X) : ℝ := (unitNetMass hV x).sum (fun _ a => a)

def unitNetPartition (x : X) : V →₀ ℝ :=
  (unitNetTotal hV x)⁻¹ • unitNetMass hV x

theorem unitNetMass_nonneg (x : X) (v : V) : 0 ≤ unitNetMass hV x v :=
  le_max_left _ _

theorem one_le_unitNetTotal (hcover : ∀ x : X, ∃ v ∈ V, dist x v ≤ 1) (x : X) :
    1 ≤ unitNetTotal hV x := by
  obtain ⟨v, hv, hd⟩ := hcover x
  have hp : 1 ≤ unitNetMass hV x ⟨v, hv⟩ := by
    exact (by linarith : 1 ≤ 2 - dist x v).trans (le_max_right _ _)
  have hm : (⟨v, hv⟩ : V) ∈ (unitNetMass hV x).support := by
    apply Finsupp.mem_support_iff.mpr
    linarith
  exact hp.trans (Finset.single_le_sum (fun i _ => unitNetMass_nonneg hV x i) hm)

theorem unitNetPartition_nonneg (x : X) (v : V) : 0 ≤ unitNetPartition hV x v :=
  mul_nonneg (inv_nonneg.mpr (Finset.sum_nonneg (fun i _ => unitNetMass_nonneg hV x i)))
    (unitNetMass_nonneg hV x v)

theorem unitNetPartition_total (hcover : ∀ x : X, ∃ v ∈ V, dist x v ≤ 1) (x : X) :
    (unitNetPartition hV x).sum (fun _ a => a) = 1 := by
  have ht : unitNetTotal hV x ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_unitNetTotal hV hcover x))
  rw [unitNetPartition, Finsupp.sum_smul_index' (by simp)]
  change (∑ i ∈ (unitNetMass hV x).support, (unitNetTotal hV x)⁻¹ * unitNetMass hV x i) = 1
  rw [← Finset.mul_sum]
  change (unitNetTotal hV x)⁻¹ * unitNetTotal hV x = 1
  exact inv_mul_cancel₀ ht

theorem unitNetTotal_eq_sum (x : X) (s : Finset V)
    (hs : (unitNetMass hV x).support ⊆ s) :
    unitNetTotal hV x = ∑ v ∈ s, max 0 (2 - dist x v) := by
  exact Finsupp.sum_of_support_subset _ hs _ (by simp)

/-- On any finite set containing the support, the global partition agrees
with the finite-dimensional cutoff partition. -/
theorem cutoffPartition_eq_unitNetPartition (x : X) (s : Finset V)
    (hs : (unitNetMass hV x).support ⊆ s) (v : s) :
    cutoffPartition (fun u : s => (u.val : X)) x v = unitNetPartition hV x v.val := by
  have he : ‖cutoffMass (fun u : s => (u.val : X)) x‖ = unitNetTotal hV x := by
    rw [PiLp.norm_eq_of_L1, unitNetTotal_eq_sum hV x s hs]
    change (∑ u : s, ‖max 0 (2 - dist x (u.val : X))‖) = _
    simp only [Real.norm_of_nonneg (le_max_left (0 : ℝ) _)]
    exact Finset.sum_coe_sort s (fun u : V => max 0 (2 - dist x u))
  change ‖cutoffMass (fun u : s => (u.val : X)) x‖⁻¹ * max 0 (2 - dist x (v.val : X)) = _
  rw [he]
  rfl

theorem unitNetPartition_variation_on_finset
    (hcover : ∀ x : X, ∃ v ∈ V, dist x v ≤ 1) (x y : X) (s : Finset V)
    (hx : (unitNetMass hV x).support ⊆ s)
    (hy : (unitNetMass hV y).support ⊆ s) :
    (∑ v ∈ s, |unitNetPartition hV x v - unitNetPartition hV y v|) ≤
      2 * (s.card : ℝ) * dist x y := by
  have cover (z : X) (hz : (unitNetMass hV z).support ⊆ s) :
      ∃ u : s, dist z (u.val : X) ≤ 1 := by
    obtain ⟨v, hv, hd⟩ := hcover z
    have hm := (mem_support_unitNetMass_iff hV z ⟨v, hv⟩).mpr (by linarith)
    exact ⟨⟨⟨v, hv⟩, hz hm⟩, hd⟩
  have h := norm_cutoffPartition_sub_le (fun u : s => (u.val : X)) x y (cover x hx) (cover y hy)
  rw [PiLp.norm_eq_of_L1] at h
  simp only [PiLp.sub_apply, Real.norm_eq_abs, cutoffPartition_eq_unitNetPartition hV x s hx,
    cutoffPartition_eq_unitNetPartition hV y s hy, Fintype.card_coe] at h
  calc
    _ = ∑ v : s, |unitNetPartition hV x v.val - unitNetPartition hV y v.val| :=
      (Finset.sum_coe_sort s (fun v : V => |unitNetPartition hV x v - unitNetPartition hV y v|)).symm
    _ ≤ _ := h

theorem unitNetMass_support_card_le {M : ℕ}
    (hM : ∀ x : X, (V ∩ closedBall x 2).ncard ≤ M) (x : X) :
    (unitNetMass hV x).support.card ≤ M := by
  classical
  let B := V ∩ closedBall x 2
  let : Finite B := (finite_unit_net_ball hV x 2).to_subtype
  let j : (unitNetMass hV x).support → B := fun v =>
    ⟨v.val.val, v.val.property, by
      rw [mem_closedBall, dist_comm]
      exact ((mem_support_unitNetMass_iff hV x v.val).mp v.property).le⟩
  have hj : Function.Injective j := by
    intro v w he
    have he' : v.val.val = w.val.val := congrArg (fun z : B => z.val) he
    exact Subtype.ext (Subtype.ext he')
  have h := Nat.card_le_card_of_injective j hj
  simp only [Nat.card_eq_finsetCard, Nat.card_coe_set_eq] at h
  exact h.trans (hM x)

/-- The infinite partition obeys the same sum-norm estimate as its finite
restrictions. Only the two finite supports participate in the comparison. -/
theorem unitNetPartition_variation_le
    (hcover : ∀ x : X, ∃ v ∈ V, dist x v ≤ 1) {M : ℕ}
    (hM : ∀ x : X, (V ∩ closedBall x 2).ncard ≤ M) (x y : X) :
    (unitNetPartition hV x - unitNetPartition hV y).sum (fun _ a => |a|) ≤
      4 * (M : ℝ) * dist x y := by
  classical
  let s := (unitNetMass hV x).support ∪ (unitNetMass hV y).support
  have hx : (unitNetMass hV x).support ⊆ s := Finset.subset_union_left
  have hy : (unitNetMass hV y).support ⊆ s := Finset.subset_union_right
  have hpsx : (unitNetPartition hV x).support ⊆ s :=
    Finset.Subset.trans Finsupp.support_smul hx
  have hpsy : (unitNetPartition hV y).support ⊆ s :=
    Finset.Subset.trans Finsupp.support_smul hy
  have hs : (unitNetPartition hV x - unitNetPartition hV y).support ⊆ s :=
    Finset.Subset.trans Finsupp.support_sub (Finset.union_subset hpsx hpsy)
  rw [Finsupp.sum_of_support_subset _ hs _ (by simp)]
  simp only [Finsupp.sub_apply]
  have hcard : s.card ≤ M + M := (Finset.card_union_le _ _).trans
    (Nat.add_le_add (unitNetMass_support_card_le hV hM x) (unitNetMass_support_card_le hV hM y))
  have hcardR : (s.card : ℝ) ≤ (M : ℝ) + M := by exact_mod_cast hcard
  exact (unitNetPartition_variation_on_finset hV hcover x y s hx hy).trans
    (by nlinarith only [mul_le_mul_of_nonneg_right hcardR (dist_nonneg (x := x) (y := y))])

end PolycyclicRecognition

end

end OAI
