import OAI.MeasureTheory.Falconer.Measures.ScalarSingleChildPruning
import OAI.MeasureTheory.Falconer.Estimates.ScalarSeparatedPathTree

namespace OAI

/-! Separated levels retain only the information used by the projection
 argument. They allow bunching without requiring a new closest-pair witness. -/
namespace Falconer.Regularization

structure ScalarPathLevel (Q : Finset (CellPath 1)) (a b K : ℕ) (g : ℝ) : Prop where
  order : a ≤ b
  card : ∀ p ∈ Q.image (List.take a), (prefixChildren Q a b p).card = K
  separated : ∀ p ∈ Q.image (List.take a), ∀ u ∈ prefixChildren Q a b p,
    ∀ v ∈ prefixChildren Q a b p, u ≠ v → g ≤ |scalarPathCenter u-scalarPathCenter v|

 theorem ScalarPathLevel.prune_lower {L : Finset (CellPath 1)} {a b K c d : ℕ} {g : ℝ}
    (h : ScalarPathLevel L a b K g) (hcd : c ≤ d) (hda : d ≤ a)
    (F : CellPath 1 → Finset (CellPath 1)) :
    ScalarPathLevel (scalarPruneLeaves L c d F) a b K g := by
  classical
  refine ⟨h.order,?_,?_⟩
  · intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    rw [scalarPruneLeaves_lower_children L hcd hda F hq]
    exact h.card _ (Finset.mem_image_of_mem _ (scalarPruneLeaves_subset L c d F hq))
  · intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    rw [scalarPruneLeaves_lower_children L hcd hda F hq]
    exact h.separated _ (Finset.mem_image_of_mem _ (scalarPruneLeaves_subset L c d F hq))

 theorem ScalarPathLevel.prune_upper {L : Finset (CellPath 1)} {a b K c d : ℕ} {g : ℝ}
    (h : ScalarPathLevel L a b K g) (hbc : b ≤ c)
    (F : CellPath 1 → Finset (CellPath 1))
    (hF : ∀ p ∈ L.image (List.take c), (F p).Nonempty ∧ F p ⊆ prefixChildren L c d p) :
    ScalarPathLevel (scalarPruneLeaves L c d F) a b K g := by
  classical
  refine ⟨h.order,?_,?_⟩
  · intro p hp
    rw [scalarPruneLeaves_upper_children L h.order hbc F hF]
    exact h.card p (Finset.image_subset_image (scalarPruneLeaves_subset L c d F) hp)
  · intro p hp
    rw [scalarPruneLeaves_upper_children L h.order hbc F hF]
    exact h.separated p (Finset.image_subset_image (scalarPruneLeaves_subset L c d F) hp)

 theorem ScalarPathLevel.of_branching {Q : Finset (CellPath 1)} {a b k n : ℕ}
    (hab : a ≤ b) (h : ScalarBranchingLevel Q a b k n) :
    ScalarPathLevel Q a b (2^k) (8*(1/2:ℝ)^n) :=
  ⟨hab,h.children_card,fun _ hp => h.separated hp⟩

 theorem ScalarPathLevel.trim {N : ℕ} {L : Finset (CellPath 1)}
    (hL : L ⊆ cubePaths 1 N) {a c b K : ℕ} {g : ℝ}
    (h : ScalarPathLevel L a c K g) (hcb : c ≤ b) (hb : b ≤ N)
    (F : CellPath 1 → Finset (CellPath 1))
    (hF : ∀ p ∈ L.image (List.take c), F p ⊆ prefixChildren L c b p ∧ (F p).card = 1) :
    ScalarPathLevel (scalarPruneLeaves L c b F) a b K (g-2*(1/2:ℝ)^c) := by
  classical
  refine ⟨h.order.trans hcb,?_,?_⟩
  · intro p hp
    rw [scalar_single_child_group_card L h.order hcb F hF]
    exact h.card p (Finset.image_subset_image (scalarPruneLeaves_subset L c b F) hp)
  · intro p hp
    exact scalar_single_child_group_separated hL h.order hcb hb F hF g p
      (h.separated p (Finset.image_subset_image (scalarPruneLeaves_subset L c b F) hp))

noncomputable def scalarSeparatedPathTreeOfLeafFibers {N K : ℕ} (Q : Finset (CellPath 1))
    (hQ : Q ⊆ cubePaths 1 N) (d branch : ℕ → ℕ) (gap : ℕ → ℝ)
    (hd : ∀ i ≤ K, d i ≤ N)
    (hbranch : ∀ i < K, 0 < branch i)
    (hlevel : ∀ i < K, ScalarPathLevel Q (d (i+1)) (d i) (branch i) (gap i))
    (hgap : ∀ i < K, 5*(1/2:ℝ)^(d i) < gap i)
    (hleaf : ∀ p ∈ Q.image (List.take (d 0)), (prefixFiber Q (d 0) p).card = 1) :
    ScalarSeparatedTree ((1/2:ℝ)^N) K := by
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
    leaf_card := ?_
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
    obtain ⟨q,hq⟩ := Finset.card_eq_one.mp (hleaf p hp)
    rw [hq]
    simp

noncomputable def scalarSeparatedPathTreeOfLevels {N K : ℕ} (Q : Finset (CellPath 1))
    (hQ : Q ⊆ cubePaths 1 N) (d branch : ℕ → ℕ) (gap : ℕ → ℝ)
    (hd0 : d 0 = N) (hd : ∀ i ≤ K, d i ≤ N)
    (hbranch : ∀ i < K, 0 < branch i)
    (hlevel : ∀ i < K, ScalarPathLevel Q (d (i+1)) (d i) (branch i) (gap i))
    (hgap : ∀ i < K, 5*(1/2:ℝ)^(d i) < gap i) :
    ScalarSeparatedTree ((1/2:ℝ)^N) K := by
  apply scalarSeparatedPathTreeOfLeafFibers Q hQ d branch gap hd hbranch hlevel hgap
  rw [hd0]
  intro p hp
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
  have hlen := (mem_cubePaths 1 N q).mp (hQ hq)
  have htake : q.take N = q := by rw [← hlen,List.take_length]
  rw [htake,prefixFiber_leaf hQ hq]
  simp

end Falconer.Regularization

end OAI
