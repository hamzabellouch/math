import OAI.MeasureTheory.Falconer.Estimates.PrefixCounting

namespace OAI

/-! Whole-child pruning in the scalar dyadic tree. Lower completed levels
 retain their exact fibers, which makes bottom-up regularization stable. -/
namespace Falconer.Regularization

noncomputable def scalarPruneLeaves (L : Finset (CellPath 1)) (a b : ℕ)
    (K : CellPath 1 → Finset (CellPath 1)) : Finset (CellPath 1) := by
  classical
  exact L.filter fun q => q.take b ∈ K (q.take a)

 theorem scalarPruneLeaves_subset (L : Finset (CellPath 1)) (a b : ℕ)
    (K : CellPath 1 → Finset (CellPath 1)) : scalarPruneLeaves L a b K ⊆ L := by
  classical
  exact Finset.filter_subset _ _

 theorem scalarPruneLeaves_children (L : Finset (CellPath 1)) (a b : ℕ)
    (K : CellPath 1 → Finset (CellPath 1)) (p : CellPath 1)
    (hK : K p ⊆ prefixChildren L a b p) :
    prefixChildren (scalarPruneLeaves L a b K) a b p = K p := by
  classical
  ext c
  constructor
  · intro hc
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hc
    have hqa := (Finset.mem_filter.mp hq).2
    have hqK := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2
    rwa [hqa] at hqK
  · intro hc
    obtain ⟨q,hq,hqc⟩ := Finset.mem_image.mp (hK hc)
    have hqa := (Finset.mem_filter.mp hq).2
    apply Finset.mem_image.mpr
    refine ⟨q,?_,hqc⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_,hqa⟩
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hq).1,by rw [hqa,hqc]; exact hc⟩

 theorem scalarPruneLeaves_fiber (L : Finset (CellPath 1)) {a b c : ℕ}
    (hab : a ≤ b) (hbc : b ≤ c) (K : CellPath 1 → Finset (CellPath 1))
    {q : CellPath 1} (hq : q ∈ scalarPruneLeaves L a b K) :
    prefixFiber (scalarPruneLeaves L a b K) c (q.take c) = prefixFiber L c (q.take c) := by
  classical
  ext r
  simp only [prefixFiber,Finset.mem_filter]
  constructor
  · rintro ⟨hr,he⟩
    exact ⟨scalarPruneLeaves_subset L a b K hr,he⟩
  · rintro ⟨hr,he⟩
    have ha : r.take a = q.take a := take_eq_of_take_eq (hab.trans hbc) he
    have hb : r.take b = q.take b := take_eq_of_take_eq hbc he
    have hqK := (Finset.mem_filter.mp hq).2
    exact ⟨Finset.mem_filter.mpr ⟨hr,by rw [ha,hb]; exact hqK⟩,he⟩

 theorem scalarPruneLeaves_lower_children (L : Finset (CellPath 1)) {a b c d : ℕ}
    (hab : a ≤ b) (hbc : b ≤ c) (K : CellPath 1 → Finset (CellPath 1))
    {q : CellPath 1} (hq : q ∈ scalarPruneLeaves L a b K) :
    prefixChildren (scalarPruneLeaves L a b K) c d (q.take c) = prefixChildren L c d (q.take c) := by
  unfold prefixChildren
  rw [scalarPruneLeaves_fiber L hab hbc K hq]

 theorem scalarPruneLeaves_fiber_card (L : Finset (CellPath 1)) {a b : ℕ}
    (hab : a ≤ b) (K : CellPath 1 → Finset (CellPath 1)) (p : CellPath 1)
    (hK : K p ⊆ prefixChildren L a b p) :
    (prefixFiber (scalarPruneLeaves L a b K) a p).card =
      ∑ c ∈ K p, (prefixFiber L b c).card := by
  classical
  rw [prefixFiber_card_sum hab,scalarPruneLeaves_children L a b K p hK]
  apply Finset.sum_congr rfl
  intro c hc
  obtain ⟨q,hq,hqc⟩ := Finset.mem_image.mp (hK hc)
  have hqa := (Finset.mem_filter.mp hq).2
  have hq' : q ∈ scalarPruneLeaves L a b K :=
    Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hq).1,by rw [hqa,hqc]; exact hc⟩
  rw [← hqc,scalarPruneLeaves_fiber L hab le_rfl K hq']

 theorem scalar_prefix_children_card_le {N a b : ℕ} {L : Finset (CellPath 1)}
    (hL : L ⊆ cubePaths 1 N) (hab : a ≤ b) (hb : b ≤ N) (p : CellPath 1) :
    (prefixChildren L a b p).card ≤ 2^(b-a) := by
  classical
  have hsub : prefixChildren L a b p ⊆
      (cubePaths 1 (b-a)).image (fun q => p ++ q) := by
    intro c hc
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hc
    have hqa := (Finset.mem_filter.mp hq).2
    have hlen := (mem_cubePaths 1 N q).mp (hL (Finset.mem_filter.mp hq).1)
    refine Finset.mem_image.mpr ⟨(q.take b).drop a,?_,?_⟩
    · simp only [mem_cubePaths,List.length_drop,List.length_take,hlen,min_eq_left hb]
    · have hh := List.take_append_drop a (q.take b)
      simpa only [List.take_take,min_eq_left hab,hqa] using hh
  calc
    _ ≤ ((cubePaths 1 (b-a)).image (fun q => p ++ q)).card := Finset.card_le_card hsub
    _ ≤ (cubePaths 1 (b-a)).card := Finset.card_image_le
    _ = _ := by simp only [card_cubePaths,one_mul]

end Falconer.Regularization

end OAI
