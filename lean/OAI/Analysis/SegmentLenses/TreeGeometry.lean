import OAI.Analysis.SegmentLenses.Basic

namespace OAI

/-!
# Ancestry, segment splitting, and opposite crossings
-/

noncomputable section

open scoped BigOperators
open Finset

namespace SegmentLenses





class TreeOrder (V : Type*) [PartialOrder V] : Prop where
  lower_chain : ∀ {a b c : V}, a ≤ c → b ≤ c → a ≤ b ∨ b ≤ a


class IntervalSegments (V : Type*) [PartialOrder V] [SegmentSystem V] : Prop where
  iff_interval : ∀ S : Finset V, SegmentSystem.isSegment S ↔ IsInterval (· ≤ ·) S

instance infiniteOrder : PartialOrder InfiniteVertex where
  le := List.IsPrefix
  lt := fun a b => a.IsPrefix b ∧ ¬b.IsPrefix a
  le_refl := List.prefix_refl
  le_trans := fun _ _ _ => List.IsPrefix.trans
  le_antisymm := fun _ _ => prefix_antisymm

instance infiniteTreeOrder : TreeOrder InfiniteVertex where
  lower_chain := List.prefix_or_prefix_of_prefix

instance infiniteIntervalSegments : IntervalSegments InfiniteVertex where
  iff_interval _ := Iff.rfl

instance infiniteLocallyFinite : LocallyFiniteOrder InfiniteVertex := by
  classical
  exact LocallyFiniteOrder.ofIcc InfiniteVertex
    (fun a b => b.inits.toFinset.filter (fun v => a.IsPrefix v))
    (fun a b v => by simp [List.mem_inits, and_comm, LE.le])

instance forestOrder : PartialOrder ForestVertex where
  le := ForestAncestor
  lt := fun a b => ForestAncestor a b ∧ ¬ForestAncestor b a
  le_refl := forestAncestor_refl
  le_trans := fun _ _ _ hab hbc => ⟨hab.1.trans hbc.1, hab.2.trans hbc.2⟩
  le_antisymm := fun _ _ => forestAncestor_antisymm

instance forestTreeOrder : TreeOrder ForestVertex where
  lower_chain := by
    intro a b c hac hbc
    rcases List.prefix_or_prefix_of_prefix hac.2 hbc.2 with hab | hba
    · exact Or.inl ⟨hac.1.trans hbc.1.symm, hab⟩
    · exact Or.inr ⟨hbc.1.trans hac.1.symm, hba⟩

instance forestIntervalSegments : IntervalSegments ForestVertex where
  iff_interval _ := Iff.rfl

instance forestLocallyFinite : LocallyFiniteOrder ForestVertex :=
  LocallyFiniteOrder.ofFiniteIcc (by
    intro a b
    apply Set.Finite.of_injOn (f := fun v : ForestVertex => v.val.2)
      (t := {w : List ℕ | w.IsPrefix b.val.2})
    · intro v hv
      exact hv.2.2
    · intro v hv w hw he
      apply Subtype.ext
      exact Prod.ext (hv.2.1.trans hw.2.1.symm) he
    · exact b.val.2.inits.finite_toSet.subset (by
        intro w hw
        exact (List.mem_inits w b.val.2).mpr hw))

section TreeGeometry
variable {V : Type*} [decidableEqV : DecidableEq V] [partialOrderV : PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V] [treeOrderV : TreeOrder V]
  [segmentSystemV : SegmentSystem V] [intervalSegmentsV : IntervalSegments V]

theorem interval_isSegment {a b : V} (hab : a ≤ b) :
    SegmentSystem.isSegment (Finset.Icc a b) := by
  have _ := decidableEqV
  have _ := treeOrderV
  apply (IntervalSegments.iff_interval _).mpr
  exact ⟨a, b, hab, fun v => Finset.mem_Icc⟩



theorem halfOpen_isSegment (a c : V) :
    Finset.Ico a c = ∅ ∨ SegmentSystem.isSegment (Finset.Ico a c) := by
  classical
  by_cases hac : a < c
  · right
    have hne : (Finset.Ico a c).Nonempty := ⟨a, Finset.mem_Ico.mpr ⟨le_rfl, hac⟩⟩
    obtain ⟨z, hz⟩ := Finset.exists_maximal hne
    have hzac := Finset.mem_Ico.mp hz.1
    have hmax : ∀ v ∈ Finset.Ico a c, v ≤ z := by
      intro v hv
      have hvac := Finset.mem_Ico.mp hv
      rcases TreeOrder.lower_chain hvac.2.le hzac.2.le with hvz | hzv
      · exact hvz
      · exact hz.2 hv hzv
    have he : Finset.Ico a c = Finset.Icc a z := by
      ext v
      constructor
      · intro hv
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Ico.mp hv).1, hmax v hv⟩
      · intro hv
        have hh := Finset.mem_Icc.mp hv
        exact Finset.mem_Ico.mpr ⟨hh.1, lt_of_le_of_lt hh.2 hzac.2⟩
    rw [he]
    exact interval_isSegment hzac.1
  · left
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have hh := Finset.mem_Ico.mp hv
    exact hac (lt_of_le_of_lt hh.1 hh.2)


theorem split_interval {a c b : V} (hac : a ≤ c) (hcb : c ≤ b) :
    Finset.Ico a c ∪ Finset.Icc c b = Finset.Icc a b := by
  have _ := segmentSystemV
  have _ := intervalSegmentsV
  classical
  ext v
  simp only [Finset.mem_union, Finset.mem_Ico, Finset.mem_Icc]
  constructor
  · rintro (⟨hav, hvc⟩ | ⟨hcv, hvb⟩)
    · exact ⟨hav, le_trans hvc.le hcb⟩
    · exact ⟨le_trans hac hcv, hvb⟩
  · rintro ⟨hav, hvb⟩
    rcases TreeOrder.lower_chain hvb hcb with hvc | hcv
    · rcases lt_or_eq_of_le hvc with hlt | rfl
      · exact Or.inl ⟨hav, hlt⟩
      · exact Or.inr ⟨le_rfl, hcb⟩
    · exact Or.inr ⟨hcv, hvb⟩

theorem split_disjoint (a c b : V) : Disjoint (Finset.Ico a c) (Finset.Icc c b) := by
  have _ := decidableEqV
  have _ := treeOrderV
  have _ := segmentSystemV
  have _ := intervalSegmentsV
  refine Finset.disjoint_left.mpr ?_
  intro v hv hv'
  exact (not_lt_of_ge (Finset.mem_Icc.mp hv').1) (Finset.mem_Ico.mp hv).2


theorem head_zero_above {H : Finset V} (hH : Ancestral (· ≤ ·) H)
    {p : V →₀ ℝ} (hp : p.support ⊆ H) {g v : V} (hg : g ∉ H) (hgv : g ≤ v) :
    p v = 0 := by
  have _ := decidableEqV
  have _ := locallyFiniteOrderV
  have _ := treeOrderV
  have _ := segmentSystemV
  have _ := intervalSegmentsV
  apply Finsupp.notMem_support_iff.mp
  intro hv
  exact hg (hH (hp hv) hgv)



theorem segment_sum_eq_head {H : Finset V} (hH : Ancestral (· ≤ ·) H)
    {p : V →₀ ℝ} (hp : p.support ⊆ H) {a g b : V}
    (hag : a ≤ g) (hgb : g ≤ b) (hg : g ∉ H) :
    (∑ v ∈ Finset.Icc a b, p v) = ∑ v ∈ Finset.Ico a g, p v := by
  classical
  rw [← split_interval hag hgb, Finset.sum_union (split_disjoint _ _ _)]
  have hz : (∑ v ∈ Finset.Icc g b, p v) = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    exact head_zero_above hH hp hg (Finset.mem_Icc.mp hv).1
  rw [hz, add_zero]



theorem split_suffix_sum {H : Finset V} (hH : Ancestral (· ≤ ·) H)
    {p : V →₀ ℝ} (hp : p.support ⊆ H) {c g b b' : V}
    (hcg : c ≤ g) (hgb : g ≤ b) (hgb' : g ≤ b') (hg : g ∉ H) :
    (∑ v ∈ Finset.Icc c b, p v) = ∑ v ∈ Finset.Icc c b', p v := by
  rw [segment_sum_eq_head hH hp hcg hgb hg,
    segment_sum_eq_head hH hp hcg hgb' hg]



theorem opposite_split_gain {H : Finset V} (hH : Ancestral (· ≤ ·) H)
    {p : V →₀ ℝ} (hp : p.support ⊆ H) {a c g b b' : V}
    (hac : a ≤ c) (hcg : c ≤ g) (hgb : g ≤ b) (hgb' : g ≤ b')
    (hg : g ∉ H)
    (hop : (∑ v ∈ Finset.Icc a b, p v) * (∑ v ∈ Finset.Icc c b', p v) < 0) :
    2 * |(∑ v ∈ Finset.Icc a b, p v) * (∑ v ∈ Finset.Icc c b', p v)| ≤
      (∑ v ∈ Finset.Ico a c, p v) ^ 2 + (∑ v ∈ Finset.Icc c b, p v) ^ 2 -
        (∑ v ∈ Finset.Icc a b, p v) ^ 2 := by
  classical
  have he := split_suffix_sum hH hp hcg hgb hgb' hg
  have hsum : (∑ v ∈ Finset.Icc a b, p v) =
      (∑ v ∈ Finset.Ico a c, p v) + (∑ v ∈ Finset.Icc c b, p v) := by
    rw [← split_interval hac (le_trans hcg hgb),
      Finset.sum_union (split_disjoint _ _ _)]
  rw [abs_of_neg hop, ← he, hsum]
  nlinarith [sq_nonneg (∑ v ∈ Finset.Icc c b, p v)]



theorem selected_split_budget {ι Γ : Type*} [Fintype ι] [Fintype Γ]
    (p : V →₀ ℝ) (a b : ι → V) (hab : ∀ i, a i ≤ b i)
    (hd : Pairwise fun i j => Disjoint (Finset.Icc (a i) (b i)) (Finset.Icc (a j) (b j)))
    (select : Γ → ι) (hinj : Function.Injective select) (cut : Γ → V)
    (hcut : ∀ g, a (select g) ≤ cut g ∧ cut g ≤ b (select g))
    (cost : Γ → ℝ) (hcost : ∀ g, 0 ≤ cost g)
    (hgain : ∀ g, cost g ≤
      (∑ v ∈ Finset.Ico (a (select g)) (cut g), p v) ^ 2 +
      (∑ v ∈ Finset.Icc (cut g) (b (select g)), p v) ^ 2 -
      (∑ v ∈ Finset.Icc (a (select g)) (b (select g)), p v) ^ 2) :
    ∑ g, cost g ≤ segmentSeminorm V p ^ 2 -
      ∑ i, (∑ v ∈ Finset.Icc (a i) (b i), p v) ^ 2 := by
  classical
  let c := Function.extend select cut a
  have hc : ∀ i, a i ≤ c i ∧ c i ≤ b i := by
    intro i
    by_cases hi : ∃ g, select g = i
    · obtain ⟨g, rfl⟩ := hi
      rw [show c (select g) = cut g from hinj.extend_apply cut a g]
      exact hcut g
    · rw [show c i = a i from Function.extend_apply' cut a i hi]
      exact ⟨le_rfl, hab i⟩
  let gain : ι → ℝ := fun i =>
    (∑ v ∈ Finset.Ico (a i) (c i), p v) ^ 2 +
    (∑ v ∈ Finset.Icc (c i) (b i), p v) ^ 2 -
    (∑ v ∈ Finset.Icc (a i) (b i), p v) ^ 2
  have hgselect : ∀ g, cost g ≤ gain (select g) := by
    intro g
    dsimp [gain]
    rw [show c (select g) = cut g from hinj.extend_apply cut a g]
    exact hgain g
  have hgn : ∀ i, 0 ≤ gain i := by
    intro i
    by_cases hi : ∃ g, select g = i
    · obtain ⟨g, rfl⟩ := hi
      exact (hcost g).trans (hgselect g)
    · dsimp [gain]
      rw [show c i = a i from Function.extend_apply' cut a i hi]
      simp
  have hs : ∑ g, cost g ≤ ∑ i, gain i := by
    calc
      ∑ g, cost g ≤ ∑ g, gain (select g) := Finset.sum_le_sum fun g _ => hgselect g
      _ = ∑ i ∈ Finset.univ.image select, gain i :=
        (Finset.sum_image hinj.injOn).symm
      _ ≤ ∑ i, gain i := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun i _ _ => hgn i)
  have he := refinement_test_bound p
    (fun i => Finset.Icc (a i) (b i))
    (fun i => Finset.Ico (a i) (c i)) (fun i => Finset.Icc (c i) (b i)) hd
    (fun i => by
      intro v hv
      have hh := Finset.mem_Ico.mp hv
      exact Finset.mem_Icc.mpr ⟨hh.1, le_trans hh.2.le (hc i).2⟩)
    (fun i => by
      intro v hv
      have hh := Finset.mem_Icc.mp hv
      exact Finset.mem_Icc.mpr ⟨le_trans (hc i).1 hh.1, hh.2⟩)
    (fun i => split_disjoint _ _ _)
    (fun i => halfOpen_isSegment _ _)
    (fun i => Or.inr (interval_isSegment (hc i).2))
  have hsum : (∑ i, gain i) =
      (∑ i, ((∑ v ∈ Finset.Ico (a i) (c i), p v) ^ 2 +
        (∑ v ∈ Finset.Icc (c i) (b i), p v) ^ 2)) -
      ∑ i, (∑ v ∈ Finset.Icc (a i) (b i), p v) ^ 2 := by
    simp [gain, Finset.sum_sub_distrib]
  rw [hsum] at hs
  linarith




theorem matched_opposite_crossing {ι κ Γ : Type*} [Fintype ι] [Fintype κ] [Fintype Γ]
    {H : Finset V} (hH : Ancestral (· ≤ ·) H)
    (p : V →₀ ℝ) (hp : p.support ⊆ H)
    (a b : ι → V) (a' b' : κ → V)
    (hab : ∀ i, a i ≤ b i) (hab' : ∀ j, a' j ≤ b' j)
    (hd : Pairwise fun i j => Disjoint (Finset.Icc (a i) (b i)) (Finset.Icc (a j) (b j)))
    (hd' : Pairwise fun i j => Disjoint (Finset.Icc (a' i) (b' i)) (Finset.Icc (a' j) (b' j)))
    (gate : Γ → V) (left : Γ → ι) (right : Γ → κ)
    (hl : Function.Injective left) (hr : Function.Injective right)
    (hgate : ∀ g, gate g ∉ H)
    (hmem : ∀ g, a (left g) ≤ gate g ∧ gate g ≤ b (left g))
    (hmem' : ∀ g, a' (right g) ≤ gate g ∧ gate g ≤ b' (right g))
    (hop : ∀ g, (∑ v ∈ Finset.Icc (a (left g)) (b (left g)), p v) *
      (∑ v ∈ Finset.Icc (a' (right g)) (b' (right g)), p v) < 0) :
    2 * ∑ g, |(∑ v ∈ Finset.Icc (a (left g)) (b (left g)), p v) *
        (∑ v ∈ Finset.Icc (a' (right g)) (b' (right g)), p v)| ≤
      (segmentSeminorm V p ^ 2 - ∑ i, (∑ v ∈ Finset.Icc (a i) (b i), p v) ^ 2) +
      (segmentSeminorm V p ^ 2 - ∑ j, (∑ v ∈ Finset.Icc (a' j) (b' j), p v) ^ 2) := by
  classical
  let longer : Γ → Prop := fun g => a (left g) ≤ a' (right g)
  let cost : Γ → ℝ := fun g => 2 *
    |(∑ v ∈ Finset.Icc (a (left g)) (b (left g)), p v) *
      (∑ v ∈ Finset.Icc (a' (right g)) (b' (right g)), p v)|
  have hc : ∀ g, 0 ≤ cost g := fun g => mul_nonneg (by norm_num) (abs_nonneg _)
  have h₁ := selected_split_budget p a b hab hd
    (fun g : {g // longer g} => left g.val) (hl.comp Subtype.val_injective)
    (fun g => a' (right g.val))
    (fun g => ⟨g.property, le_trans (hmem' g.val).1 (hmem g.val).2⟩)
    (fun g => cost g.val) (fun g => hc g.val)
    (fun g => opposite_split_gain hH hp g.property (hmem' g.val).1
      (hmem g.val).2 (hmem' g.val).2 (hgate g.val) (hop g.val))
  have h₂ := selected_split_budget p a' b' hab' hd'
    (fun g : {g // ¬longer g} => right g.val) (hr.comp Subtype.val_injective)
    (fun g => a (left g.val))
    (fun g => ⟨(TreeOrder.lower_chain (hmem g.val).1 (hmem' g.val).1).resolve_left g.property,
      le_trans (hmem g.val).1 (hmem' g.val).2⟩)
    (fun g => cost g.val) (fun g => hc g.val) (fun g => by
      have hstart := (TreeOrder.lower_chain (hmem g.val).1 (hmem' g.val).1).resolve_left g.property
      have ho : (∑ v ∈ Finset.Icc (a' (right g.val)) (b' (right g.val)), p v) *
          (∑ v ∈ Finset.Icc (a (left g.val)) (b (left g.val)), p v) < 0 := by
        simpa [mul_comm] using hop g.val
      simpa only [cost, mul_comm] using opposite_split_gain hH hp hstart
        (hmem g.val).1 (hmem' g.val).2 (hmem g.val).2 (hgate g.val) ho)
  have hs := Fintype.sum_subtype_add_sum_subtype longer cost
  have he : (∑ g, cost g) =
      2 * ∑ g, |(∑ v ∈ Finset.Icc (a (left g)) (b (left g)), p v) *
        (∑ v ∈ Finset.Icc (a' (right g)) (b' (right g)), p v)| := by
    simp [cost, Finset.mul_sum]
  linarith



def Gate (H : Finset V) (g : V) : Prop :=
  g ∉ H ∧ ∀ v, v < g → v ∈ H

theorem gates_incomparable {H : Finset V} {g g' : V}
    (hg : Gate H g) (hg' : Gate H g') (h : g ≤ g') : g = g' := by
  have _ := locallyFiniteOrderV
  have _ := treeOrderV
  have _ := segmentSystemV
  have _ := intervalSegmentsV
  by_contra hne
  exact hg.1 (hg'.2 g (lt_of_le_of_ne h hne))

theorem gate_unique_in_interval {H : Finset V} {g g' a b : V}
    (hg : Gate H g) (hg' : Gate H g')
    (hm : g ∈ Finset.Icc a b) (hm' : g' ∈ Finset.Icc a b) : g = g' := by
  rcases TreeOrder.lower_chain (Finset.mem_Icc.mp hm).2 (Finset.mem_Icc.mp hm').2 with h | h
  · exact gates_incomparable hg hg' h
  · exact (gates_incomparable hg' hg h).symm

namespace SegmentFamily


def presentation (F : SegmentFamily V) (S : F.sets) :
    {q : V × V // q.1 ≤ q.2 ∧ S.val = Finset.Icc q.1 q.2} := by
  classical
  have hs := (IntervalSegments.iff_interval S.val).mp (F.segment S.val S.property)
  apply Classical.choice
  obtain ⟨a, b, hab, hs⟩ := hs
  exact ⟨⟨(a, b), hab, Finset.ext (fun v => by simpa only [Finset.mem_Icc] using hs v)⟩⟩

def first (F : SegmentFamily V) (S : F.sets) : V := (F.presentation S).val.1

def last (F : SegmentFamily V) (S : F.sets) : V := (F.presentation S).val.2

theorem first_le_last (F : SegmentFamily V) (S : F.sets) : F.first S ≤ F.last S := by
  have _ := decidableEqV
  have _ := treeOrderV
  exact
    (F.presentation S).property.1

theorem repr (F : SegmentFamily V) (S : F.sets) :
    S.val = Finset.Icc (F.first S) (F.last S) := by
  have _ := decidableEqV
  have _ := treeOrderV
  exact (F.presentation S).property.2

theorem repr_disjoint (F : SegmentFamily V) :
    Pairwise fun S T : F.sets =>
      Disjoint (Finset.Icc (F.first S) (F.last S)) (Finset.Icc (F.first T) (F.last T)) := by
  intro S T hne
  rw [← F.repr S, ← F.repr T]
  exact F.disjoint S.property T.property (fun h => hne (Subtype.ext h))



def boundary (F : SegmentFamily V) (p : V →₀ ℝ) (g : V) : ℝ :=
  ∑ S ∈ F.sets, if g ∈ S then ∑ v ∈ S, p v else 0

theorem boundary_of_mem (F : SegmentFamily V) (p : V →₀ ℝ)
    {g : V} (S : F.sets) (hg : g ∈ S.val) :
    F.boundary p g = ∑ v ∈ S.val, p v := by
  have _ := partialOrderV
  have _ := locallyFiniteOrderV
  have _ := treeOrderV
  have _ := intervalSegmentsV
  classical
  unfold boundary
  rw [Finset.sum_eq_single S.val]
  · simp [hg]
  · intro T hT hne
    have hn : g ∉ T := fun h =>
      Finset.disjoint_left.mp (F.disjoint hT S.property hne) h hg
    simp [hn]
  · intro hn
    exact False.elim (hn S.property)

theorem boundary_nonzero (F : SegmentFamily V) (p : V →₀ ℝ)
    {g : V} (hne : F.boundary p g ≠ 0) : ∃ S : F.sets, g ∈ S.val := by
  have _ := partialOrderV
  have _ := locallyFiniteOrderV
  have _ := treeOrderV
  have _ := intervalSegmentsV
  classical
  by_contra h
  apply hne
  apply Finset.sum_eq_zero
  intro S hS
  have hn : g ∉ S := fun hs => h ⟨⟨S, hS⟩, hs⟩
  simp [hn]

theorem gate_unique {H : Finset V} (F : SegmentFamily V) (S : F.sets)
    {g g' : V} (hg : Gate H g) (hg' : Gate H g') (hm : g ∈ S.val) (hm' : g' ∈ S.val) :
    g = g' := by
  rw [F.repr S] at hm hm'
  exact gate_unique_in_interval hg hg' hm hm'

end SegmentFamily



theorem opposite_crossing (F F' : SegmentFamily V) {H : Finset V}
    (hH : Ancestral (· ≤ ·) H) (p : V →₀ ℝ) (hp : p.support ⊆ H)
    (G : Finset V) (hG : ∀ g ∈ G, Gate H g) :
    (∑ g : G, (|F.boundary p g.val * F'.boundary p g.val| -
      F.boundary p g.val * F'.boundary p g.val)) ≤
      (segmentSeminorm V p ^ 2 - F.seminorm p ^ 2) +
      (segmentSeminorm V p ^ 2 - F'.seminorm p ^ 2) := by
  classical
  let opposite : G → Prop := fun g => F.boundary p g.val * F'.boundary p g.val < 0
  let Γ := {g : G // opposite g}
  have hleft : ∀ g : Γ, ∃ S : F.sets, g.val.val ∈ S.val := by
    intro g
    apply F.boundary_nonzero p
    intro hz
    have ho := g.property
    change F.boundary p g.val.val * F'.boundary p g.val.val < 0 at ho
    rw [hz, zero_mul] at ho
    exact lt_irrefl _ ho
  have hright : ∀ g : Γ, ∃ S : F'.sets, g.val.val ∈ S.val := by
    intro g
    apply F'.boundary_nonzero p
    intro hz
    have ho := g.property
    change F.boundary p g.val.val * F'.boundary p g.val.val < 0 at ho
    rw [hz, mul_zero] at ho
    exact lt_irrefl _ ho
  let left : Γ → F.sets := fun g => Classical.choose (hleft g)
  let right : Γ → F'.sets := fun g => Classical.choose (hright g)
  have hlmem : ∀ g : Γ, g.val.val ∈ (left g).val := fun g => Classical.choose_spec (hleft g)
  have hrmem : ∀ g : Γ, g.val.val ∈ (right g).val := fun g => Classical.choose_spec (hright g)
  have hl : Function.Injective left := by
    intro g g' he
    apply Subtype.ext
    apply Subtype.ext
    have hg' := hlmem g'
    rw [← he] at hg'
    exact F.gate_unique (left g) (hG _ g.val.property) (hG _ g'.val.property) (hlmem g) hg'
  have hr : Function.Injective right := by
    intro g g' he
    apply Subtype.ext
    apply Subtype.ext
    have hg' := hrmem g'
    rw [← he] at hg'
    exact F'.gate_unique (right g) (hG _ g.val.property) (hG _ g'.val.property) (hrmem g) hg'
  have heL : ∀ g : Γ, (∑ v ∈ Finset.Icc (F.first (left g)) (F.last (left g)), p v) =
      F.boundary p g.val.val := by
    intro g
    rw [← F.repr (left g)]
    exact (F.boundary_of_mem p (left g) (hlmem g)).symm
  have heR : ∀ g : Γ, (∑ v ∈ Finset.Icc (F'.first (right g)) (F'.last (right g)), p v) =
      F'.boundary p g.val.val := by
    intro g
    rw [← F'.repr (right g)]
    exact (F'.boundary_of_mem p (right g) (hrmem g)).symm
  have h := matched_opposite_crossing hH p hp F.first F.last F'.first F'.last
    F.first_le_last F'.first_le_last F.repr_disjoint F'.repr_disjoint
    (fun g : Γ => g.val.val) left right hl hr
    (fun g => (hG _ g.val.property).1)
    (fun g => Finset.mem_Icc.mp ((F.repr (left g)) ▸ hlmem g))
    (fun g => Finset.mem_Icc.mp ((F'.repr (right g)) ▸ hrmem g))
    (fun g => by rw [heL, heR]; exact g.property)
  simp_rw [heL, heR, ← F.repr, ← F'.repr] at h
  rw [← F.seminorm_sq p, ← F'.seminorm_sq p] at h
  have hsum : (∑ g : G, (|F.boundary p g.val * F'.boundary p g.val| -
        F.boundary p g.val * F'.boundary p g.val)) =
      2 * ∑ g : Γ, |F.boundary p g.val.val * F'.boundary p g.val.val| := by
    have he : ∀ z : ℝ, |z| - z = if z < 0 then 2 * |z| else 0 := by
      intro z
      by_cases hz : z < 0
      · simp [hz, abs_of_neg hz]; ring
      · simp [hz, abs_of_nonneg (le_of_not_gt hz)]
    simp_rw [he]
    rw [← Finset.sum_filter]
    rw [Finset.sum_subtype (p := opposite) _ (fun g => by simp [opposite])]
    rw [← Finset.mul_sum]
  rw [hsum]
  exact h

end TreeGeometry

end SegmentLenses

end

end OAI
