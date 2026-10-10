import OAI.Probability.DilutedSpin.ScheduledContinuity

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators
noncomputable local instance scheduledGeometryPropDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition

lemma vertex_card_add_one_le_leaf_card (S : ReducedTopology) :
    Fintype.card S.Vertex+1 ≤ Fintype.card S.Leaf := by
  induction S with
  | leaf => exact le_rfl
  | node k hk C ih =>
    change Fintype.card (Option ((i : Fin k) × (C i).Vertex))+1 ≤
      Fintype.card ((i : Fin k) × (C i).Leaf)
    rw [Fintype.card_option,Fintype.card_sigma,Fintype.card_sigma]
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => ih i)
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      smul_eq_mul,mul_one] at hs
    omega

lemma branching_depth_assigned (L : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ)
    (hq : Admissible S q 0 L) (a : ℕ)
    (ha : a ∈ PrescribedTree.branchingDepths (realize L 0 S q)) : ∃ v, q v=a := by
  classical
  by_contra! h
  have hz : PrescribedTree.branchingCount (realize L 0 S q) (fun d => d=a)=0 := by
    have he := realize_branchingCount L 0 S q (by simpa using hq) (fun d => d=a)
    simpa only [Nat.zero_add,h,ite_false,Finset.sum_const_zero] using he
  exact ((PrescribedTree.branchingCount_eq_zero_iff _ _).mp hz a ha) rfl

/-- Exact geometric justification of the shifted charging hypothesis for
all admissible regular assignments of any reduced topology. -/
theorem realize_no_adjacent {L : ℕ} [NeZero L] (S : ReducedTopology)
    (q : S.Vertex → Fin L) (hq : Admissible S (fun v => (q v).val) 0 L)
    {η : ℝ} (hlarge : 1<η*(L:ℝ)) (hr : DepthAverage.Regular η q) :
    PrescribedTree.NoAdjacentBranchDepths (realize L 0 S (fun v => (q v).val)) := by
  intro a ha b hb he
  obtain ⟨u,hu⟩ := branching_depth_assigned L S (fun v => (q v).val) hq a ha
  obtain ⟨v,hv⟩ := branching_depth_assigned L S (fun v => (q v).val) hq b hb
  have huv : u ≠ v := by intro hh; subst v; omega
  have hsep := hr.2 u v huv
  have hL : (0:ℝ)<L := Nat.cast_pos.mpr (NeZero.pos L)
  have hval : (q u).val+1=(q v).val := by omega
  have hval' : ((q u).val:ℝ)+1=((q v).val:ℝ) := by exact_mod_cast hval
  have habs : |DepthAverage.normalized (q u)-DepthAverage.normalized (q v)|=1/(L:ℝ) := by
    unfold DepthAverage.normalized
    rw [← sub_div,abs_div,abs_of_pos hL]
    have heq : ((q u).val:ℝ)-((q v).val:ℝ) = -1 := by linarith
    rw [heq]
    norm_num
  rw [habs] at hsep
  have hlt : 1/(L:ℝ)<η := (div_lt_iff₀ hL).mpr hlarge
  linarith

/-- The two aligned target copies contribute two occurrences of EVERY
branching vertex. The old tree has none at the shifted depths. -/
theorem scheduled_shifted_counts {L : ℕ} [NeZero L] (S : ReducedTopology)
    (q : S.Vertex → Fin L) (hq : Admissible S (fun v => (q v).val) 0 L)
    {η : ℝ} (hlarge : 1<η*(L:ℝ)) (hr : DepthAverage.Regular η q) :
    let T := realize L 0 S (fun v => (q v).val)
    PrescribedTree.branchingCount (PrescribedTree.doubled (PrescribedTree.bottomUnary T))
      (· ∈ PrescribedTree.shiftedTwinDepths T) = 0 ∧
    PrescribedTree.branchingCount (PrescribedTree.doubled (PrescribedTree.unary T))
      (· ∈ PrescribedTree.shiftedTwinDepths T) = 2*Fintype.card S.Vertex := by
  dsimp only
  constructor
  · exact PrescribedTree.shifted_twin_old_count _ (realize_no_adjacent S q hq hlarge hr)
  · rw [PrescribedTree.shifted_twin_target_count]
    congr 1
    have he := realize_branchingCount L 0 S (fun v => (q v).val) (by simpa using hq) (fun _ => True)
    simpa only [ite_true,Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one] using he

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
