import OAI.MeasureTheory.Falconer.Estimates.ScalarClusterGain
import OAI.MeasureTheory.Falconer.Estimates.ScalarBunchTree

namespace OAI

/-! The cluster tree formed by actual path fibers. Terminal fibers retain
 their full uniform cardinality and original fine-scale separation. -/
namespace Falconer.Regularization

 theorem scalar_prefix_points_separated {N : ℕ} {Q : Finset (CellPath 1)}
    (hQ : Q ⊆ cubePaths 1 N) (a : ℕ) (x : ℝ) :
    ∀ u ∈ scalarPrefixPoints Q a x, ∀ v ∈ scalarPrefixPoints Q a x,
      u ≠ v → (1/2:ℝ)^N ≤ |u-v| := by
  classical
  intro u hu v hv huv
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hv
  have hpN := (mem_cubePaths 1 N p).mp (hQ (Finset.mem_filter.mp hp).1)
  have hqN := (mem_cubePaths 1 N q).mp (hQ (Finset.mem_filter.mp hq).1)
  exact scalarPathCenter_separated hpN hqN (fun he => huv (congrArg scalarPathCenter he))

noncomputable def scalarClusterPathTreeOfLevels {N K m : ℕ} (Q : Finset (CellPath 1))
    (hQ : Q ⊆ cubePaths 1 N) (d branch : ℕ → ℕ) (gap : ℕ → ℝ)
    (hd : ∀ i ≤ K, d i ≤ N) (hm : 0 < m)
    (hbranch : ∀ i < K, 0 < branch i)
    (hlevel : ∀ i < K, ScalarPathLevel Q (d (i+1)) (d i) (branch i) (gap i))
    (hgap : ∀ i < K, 5*(1/2:ℝ)^(d i) < gap i)
    (hleaf : ∀ p ∈ Q.image (List.take (d 0)), (prefixFiber Q (d 0) p).card = m) :
    ScalarClusterTree ((1/2:ℝ)^N) K := by
  classical
  refine {
    nodes := fun i => (Q.image (List.take (d i))).image scalarPathCenter
    children := fun i x => scalarPrefixChildren Q (d (i+1)) (d i) x
    points := fun i x => scalarPrefixPoints Q (d i) x
    branching := branch
    radius := fun i => (1/2:ℝ)^(d i)
    gap := gap
    branch_pos := hbranch
    radius_ge := fun i hi => pow_le_pow_of_le_one (by norm_num) (by norm_num) (hd i hi.le)
    gap_pos := fun i hi => lt_trans (by positivity) (hgap i hi)
    gap_gt := hgap
    child_subset := ?_
    child_card := ?_
    child_sep := ?_
    child_bound := ?_
    parent_eq := ?_
    leaf_size := m
    leaf_pos := hm
    leaf_card := ?_
    leaf_sep := fun x _ => scalar_prefix_points_separated hQ (d 0) x
  }
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
    exact (hlevel i hi).card p hp
  · intro i hi x hx y hy z hz hyz
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    rw [scalar_prefix_children_eq hQ (hd (i+1) (by omega)) hp] at hy hz
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hz
    exact (hlevel i hi).separated p hp c hc e he (fun hce => hyz (congrArg scalarPathCenter hce))
  · intro i hi x hx y hy z hz
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    rw [scalar_prefix_children_eq hQ (hd (i+1) (by omega)) hp] at hy
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hy
    rw [scalar_prefix_points_eq hQ (hd i hi.le) (prefixChildren_mem_image hc)] at hz
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hz
    exact scalar_prefix_leaf_center_dist hQ (hd i hi.le) hu
  · intro i hi x _
    exact scalar_prefix_points_children hQ (hlevel i hi).order (hd i hi.le) x
  · intro x hx
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    rw [scalar_prefix_points_eq hQ (hd 0 (Nat.zero_le K)) hp]
    rw [Finset.card_image_of_injOn (scalarPathCenter_injOn (prefixFiber Q (d 0) p) (fun q hq =>
      (mem_cubePaths 1 N q).mp (hQ (Finset.mem_filter.mp hq).1)))]
    exact hleaf p hp

end Falconer.Regularization

end OAI
