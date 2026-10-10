import OAI.Probability.DilutedSpin.ReservoirTrees

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree

@[simp] lemma leaves_heightCast {n m : ℕ} (h : n=m) (S : PrescribedTree n) :
    leaves (heightCast h S)=leaves S := by cases h; rfl

@[simp] lemma canonicalMatrixTail_length (t : ℕ) : (canonicalMatrixTail t).length=t := by
  simp [canonicalMatrixTail]

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.ReducedTopology
open PrescribedTree
open scoped BigOperators

/-- A grid-independent budget for all leaves and history colors used in the
aligned two-copy experiment of a fixed topology. -/
def nodeHistoryBudget (k : ℕ+) (hk : 2≤(k:ℕ)) (C : Fin k → ReducedTopology) : ℕ :=
  4*Fintype.card (ReducedTopology.node k hk C).Leaf

noncomputable def nodeChargeConstant (k : ℕ+) (hk : 2≤(k:ℕ))
    (C : Fin k → ReducedTopology) (η : ℝ) : ℝ :=
  let R := nodeHistoryBudget k hk C
  (((2+(R:ℝ))*(R:ℝ))^(2*Fintype.card (ReducedTopology.node k hk C).Leaf-2+1)) /
    (min η 1)^R

lemma nodeChargeConstant_nonneg (k : ℕ+) (hk : 2≤(k:ℕ))
    (C : Fin k → ReducedTopology) {η : ℝ} (hη : 0<η) :
    0≤nodeChargeConstant k hk C η := by
  unfold nodeChargeConstant
  exact div_nonneg (pow_nonneg (by positivity) _) (pow_nonneg (le_min hη.le zero_le_one) _)

lemma node_realize_leaves (H lo : ℕ) (k : ℕ+) (hk : 2≤(k:ℕ))
    (C : Fin k → ReducedTopology) (q : (j : Fin k) → (C j).Vertex → ℕ)
    (had : ∀ j, Admissible (C j) (q j) lo (lo+H)) :
    leaves (PrescribedTree.node k (fun j => realize H lo (C j) (q j))) =
      Fintype.card (ReducedTopology.node k hk C).Leaf := by
  change (∑ j, leaves (realize H lo (C j) (q j))) = Fintype.card ((j : Fin k) × (C j).Leaf)
  rw [Fintype.card_sigma]
  exact Finset.sum_congr rfl (fun j _ => realize_leaves H lo (C j) (q j) (had j))

lemma node_old_realize_leaves (H lo : ℕ) (k : ℕ+) (hk : 2≤(k:ℕ))
    (C : Fin k → ReducedTopology) (q : (j : Fin k) → (C j).Vertex → ℕ)
    (had : ∀ j, Admissible (C j) (q j) lo (lo+H)) :
    leaves (PrescribedTree.node k (fun j => realize (H+1) lo (C j) (q j))) =
      Fintype.card (ReducedTopology.node k hk C).Leaf := by
  change (∑ j, leaves (realize (H+1) lo (C j) (q j))) = Fintype.card ((j : Fin k) × (C j).Leaf)
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro j _
  rw [realize_bottom H lo (C j) (q j) (had j),leaves_bottom,
    realize_leaves H lo (C j) (q j) (had j)]

variable {α I : Type} [Fintype α] [DecidableEq α] [Fintype I] [DecidableEq I]

omit [Fintype α] [DecidableEq α] in
/-- The actual frame charging cost is bounded only by the reduced topology
and the separation parameter. The canonical ratio and vertex multiplicities
are retained; no maximization over a grid-dependent majorant is used. -/
theorem node_frame_charge_uniform (H r d : ℕ) (k : ℕ+) (hk : 2≤(k:ℕ)) (a : α)
    (C : Fin k → ReducedTopology) (e : (j : Fin k) → (C j).Vertex → {j : α // j≠a})
    (Q : α → Fin (H+1+1+r+1+d))
    (had : ∀ j, Admissible (C j) (fun v => (Q (e j v)).val) (r+1+d+1) (r+1+d+1+H))
    {η : ℝ} (hη : 0<η)
    (heval : η≤((d+r+2:ℕ):ℝ)/((H+1+1+r+1+d:ℕ):ℝ)) :
    let Base := PrescribedTree.node k (fun j => realize H (r+1+d+1) (C j) (fun v => (Q (e j v)).val))
    let Old := PrescribedTree.node k (fun j => realize (H+1) (r+1+d+1) (C j) (fun v => (Q (e j v)).val))
    let New := PrescribedTree.node k (fun j => realize H (r+1+1+d+1) (C j) (fun v => (Q (e j v)).val+1))
    let Target := heightCast (shiftedFrameHeight H r d) (splitFrame New (r+1) d)
    let S := splitFrame Old r d
    let B := shiftedPrefixDepths (stem Base r) d
    let t := 2*Fintype.card (ReducedTopology.node k hk C).Leaf-2
    ∀ (q : I → Target.Leaf), Function.Bijective q → ∀ (u v : I), u≠v →
    shiftedCharge B Target S (t+1) /
      |partialKappa Target (grid (H+1+1+r+1+d) 0 (H+1+1+r+1+d)) (Finset.univ.image q)/
        partialKappa Target (grid (H+1+1+r+1+d) 0 (H+1+1+r+1+d)) ((insert v ({u}:Finset I)).image q)| ≤
      nodeChargeConstant k hk C η := by
  dsimp only
  intro q hq u v huv
  rw [partialKappa_ratio_bijective _ q hq]
  have hbase := node_realize_leaves H (r+1+d+1) k hk C (fun j v => (Q (e j v)).val) had
  have hold := node_old_realize_leaves H (r+1+d+1) k hk C (fun j v => (Q (e j v)).val) had
  have hnew := delayed_node_leaves H (r+1+d+1) k hk C (fun j v => (Q (e j v)).val) had
  rw [show r+1+d+1+1=r+1+1+d+1 by omega] at hnew
  have hpos := leaf_card_pos (ReducedTopology.node k hk C)
  apply shiftedCharge_relative_uniform (by omega) _ _ _ _ (nodeHistoryBudget k hk C)
  · apply (shiftedPrefixDepths_card_le _ _).trans
    rw [leaves_stem,hbase]
    unfold nodeHistoryBudget
    omega
  · rw [leaves_splitFrame,hold]
    unfold nodeHistoryBudget
    omega
  · rw [leaves_heightCast,leaves_splitFrame,hnew]
    unfold nodeHistoryBudget
    omega
  · exact fun h => huv (hq.1 h)
  · exact hη
  · exact scheduled_frame_target_regular H r d k a C e Q η heval
  · exact scheduled_frame_target_total H r d k a C e Q

end DilutedSpinGlass.ReducedTopology

end

end OAI
