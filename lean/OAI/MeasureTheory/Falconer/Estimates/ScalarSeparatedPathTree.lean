import OAI.MeasureTheory.Falconer.Estimates.ScalarPathNodes
import OAI.MeasureTheory.Falconer.Estimates.ScalarSeparatedTree

namespace OAI

/-! The regularized scalar paths give the actual finite separated tree
 used by the porous projection argument. -/
namespace Falconer.Regularization

noncomputable def scalarSeparatedPathTree {N K : ℕ} (Q : Finset (CellPath 1))
    (hQ : Q ⊆ cubePaths 1 N) (d branch level : ℕ → ℕ)
    (hd0 : d 0 = N) (hd : ∀ i ≤ K, d i ≤ N)
    (hstep : ∀ i < K, d (i+1) ≤ d i)
    (hlevel : ∀ i < K, ScalarBranchingLevel Q (d (i+1)) (d i) (branch i) (level i)) :
    ScalarSeparatedTree ((1/2:ℝ)^N) K := by
  classical
  refine {
    nodes := fun i => (Q.image (List.take (d i))).image scalarPathCenter
    children := fun i x => scalarPrefixChildren Q (d (i+1)) (d i) x
    points := fun i x => scalarPrefixPoints Q (d i) x
    branching := fun i => 2^(branch i)
    radius := fun i => (1/2:ℝ)^(d i)
    gap := fun i => 8*(1/2:ℝ)^(level i)
    branch_pos := fun _ _ => by positivity
    radius_ge := fun i hi => pow_le_pow_of_le_one (by norm_num) (by norm_num) (hd i hi.le)
    gap_pos := fun _ _ => by positivity
    gap_gt := ?_
    child_subset := ?_
    child_card := ?_
    child_sep := ?_
    child_bound := ?_
    parent_eq := ?_
    leaf_card := ?_
  }
  · intro i hi
    have hh : (1/2:ℝ)^(d i) ≤ (1/2:ℝ)^(level i) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (hlevel i hi).level_hi
    have hp : 0 < (1/2:ℝ)^(level i) := by positivity
    linarith
  · intro i hi x hx y hy
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    rw [scalar_prefix_children_eq hQ (hd (i+1) (by omega)) hp] at hy
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image_of_mem _ (prefixChildren_mem_image hc)
  · intro i hi x hx
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    rw [scalar_prefix_children_eq hQ (hd (i+1) (by omega)) hp]
    rw [Finset.card_image_of_injOn (scalarPathCenter_injOn _
      (scalar_prefix_children_length (a := d (i+1)) hQ (hd i hi.le) p))]
    exact (hlevel i hi).children_card p hp
  · intro i hi x hx y hy z hz hyz
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    rw [scalar_prefix_children_eq hQ (hd (i+1) (by omega)) hp] at hy hz
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hz
    exact (hlevel i hi).separated hp c hc e he (fun hce => hyz (congrArg scalarPathCenter hce))
  · intro i hi x hx y hy z hz
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    rw [scalar_prefix_children_eq hQ (hd (i+1) (by omega)) hp] at hy
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hy
    rw [scalar_prefix_points_eq hQ (hd i hi.le) (prefixChildren_mem_image hc)] at hz
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hz
    exact scalar_prefix_leaf_center_dist hQ (hd i hi.le) hu
  · intro i hi x _
    exact scalar_prefix_points_children hQ (hstep i hi) (hd i hi.le) x
  · intro x hx
    rw [hd0] at hx ⊢
    rw [scalar_prefix_points_leaf hQ hx]
    simp

end Falconer.Regularization

end OAI
