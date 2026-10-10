import OAI.Analysis.DiamondDistortion.SegmentNorm

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

/-- A finite interval in an ancestral order.  This keeps the root in every tree. -/
def intervalSystem {ι : Type*} (r : ι → ι → Prop)
    (hrefl : ∀ a, r a a) (hanti : ∀ a b, r a b → r b a → a = b) : SegmentSystem ι where
  IsSegment s := ∃ a b, r a b ∧ ∀ v, v ∈ s ↔ r a v ∧ r v b
  singleton v := by
    refine ⟨v, v, hrefl v, ?_⟩
    intro w
    simp only [Finset.mem_singleton]
    constructor
    · rintro rfl
      exact ⟨hrefl _, hrefl _⟩
    · intro h
      exact hanti w v h.2 h.1

/-- An ancestral partial order: the predecessors of any vertex form a chain. -/
class Ancestry (ι : Type*) extends PartialOrder ι where
  predecessors_total : ∀ {a b c : ι}, le a c → le b c → le a b ∨ le b a

namespace Ancestry
open scoped Classical
variable {ι : Type*} [A : Ancestry ι]
local instance : PartialOrder ι := A.toPartialOrder

/-- Nonempty finite intervals for an ancestral order. -/
def segments : SegmentSystem ι :=
  intervalSystem (· ≤ ·) (fun _ => le_rfl) (fun _ _ => le_antisymm)

/-- Downward closed sets are precisely ancestral heads. -/
def Ancestral (H : Set ι) : Prop := ∀ ⦃a b : ι⦄, a ≤ b → b ∈ H → a ∈ H

lemma ancestral_not_above (c : ι) : A.Ancestral {v | ¬ c ≤ v} := by
  intro a b hab hb ha
  exact hb (ha.trans hab)

lemma interval_chain {S : Finset ι} (hS : A.segments.IsSegment S) :
    ∀ a ∈ S, ∀ b ∈ S, a ≤ b ∨ b ≤ a := by
  obtain ⟨l, r, _, hmem⟩ := hS
  intro a ha b hb
  exact A.predecessors_total ((hmem a).mp ha).2 ((hmem b).mp hb).2

lemma segment_filter_head {S : Finset ι} (hS : A.segments.IsSegment S)
    {H : Set ι} (hH : A.Ancestral H) :
    (S.filter (· ∈ H)).Nonempty → A.segments.IsSegment (S.filter (· ∈ H)) := by
  classical
  intro hne
  obtain ⟨c, hc, hmax⟩ := Finset.exists_maximal hne
  have hcS : c ∈ S := (Finset.mem_filter.mp hc).1
  have hcH : c ∈ H := (Finset.mem_filter.mp hc).2
  have hgreat : ∀ v ∈ S.filter (· ∈ H), v ≤ c := by
    intro v hv
    rcases A.interval_chain hS c hcS v (Finset.mem_filter.mp hv).1 with h | h
    · exact hmax hv h
    · exact h
  obtain ⟨a, b, hab, hmem⟩ := hS
  refine ⟨a, c, ((hmem c).mp hcS).1, ?_⟩
  intro v
  simp only [Finset.mem_filter]
  constructor
  · intro hv
    exact ⟨((hmem v).mp hv.1).1, hgreat v (Finset.mem_filter.mpr hv)⟩
  · intro hv
    exact ⟨(hmem v).mpr ⟨hv.1, hv.2.trans ((hmem c).mp hcS).2⟩, hH hv.2 hcH⟩

lemma segment_filter_tail {S : Finset ι} (hS : A.segments.IsSegment S)
    {H : Set ι} (hH : A.Ancestral H) :
    (S.filter (· ∉ H)).Nonempty → A.segments.IsSegment (S.filter (· ∉ H)) := by
  classical
  intro hne
  obtain ⟨c, hc, hmin⟩ := Finset.exists_minimal hne
  have hcS : c ∈ S := (Finset.mem_filter.mp hc).1
  have hcH : c ∉ H := (Finset.mem_filter.mp hc).2
  have hleast : ∀ v ∈ S.filter (· ∉ H), c ≤ v := by
    intro v hv
    rcases A.interval_chain hS c hcS v (Finset.mem_filter.mp hv).1 with h | h
    · exact h
    · exact hmin hv h
  obtain ⟨a, b, hab, hmem⟩ := hS
  refine ⟨c, b, ((hmem c).mp hcS).2, ?_⟩
  intro v
  simp only [Finset.mem_filter]
  constructor
  · intro hv
    exact ⟨hleast v (Finset.mem_filter.mpr hv), ((hmem v).mp hv.1).2⟩
  · intro hv
    refine ⟨(hmem v).mpr ⟨((hmem c).mp hcS).1.trans hv.1, hv.2⟩, ?_⟩
    exact fun hvH => hcH (hH hv.1 hvH)

/-- Splitting each member of a disjoint family at its own ancestral cut preserves
    the testing budget. This is the simultaneous, not one-gate-at-a-time, estimate. -/
lemma split_energy_le (F : A.segments.Family) (H : Fin F.n → Set ι)
    (hH : ∀ i, A.Ancestral (H i)) (u : ι →₀ ℝ) :
    (∑ i, ((∑ v ∈ (F.seg i).filter (· ∈ H i), u v) ^ 2 +
      (∑ v ∈ (F.seg i).filter (· ∉ H i), u v) ^ 2)) ≤
      (A.segments.primalSeminorm u) ^ 2 := by
  classical
  let P : Fin F.n × Bool → Finset ι := fun z =>
    if z.2 then (F.seg z.1).filter (· ∉ H z.1) else (F.seg z.1).filter (· ∈ H z.1)
  have hp : ∀ z, (P z).Nonempty → A.segments.IsSegment (P z) := by
    rintro ⟨i, b⟩
    cases b
    · exact A.segment_filter_head (F.allowed i) (hH i)
    · exact A.segment_filter_tail (F.allowed i) (hH i)
  have hs : ∀ z, P z ⊆ F.seg z.1 := by
    rintro ⟨i, b⟩
    cases b <;> exact Finset.filter_subset _ _
  have hd : Pairwise (fun z w => Disjoint (P z) (P w)) := by
    intro z w hzw
    by_cases h : z.1 = w.1
    · obtain ⟨i, b⟩ := z
      obtain ⟨j, c⟩ := w
      dsimp at h
      subst j
      apply Finset.disjoint_left.mpr
      intro v hv hw
      cases b <;> cases c
      · exact hzw rfl
      · simp only [P, Bool.false_eq_true, ↓reduceIte, Finset.mem_filter] at hv hw
        exact hw.2 hv.2
      · simp only [P, Bool.false_eq_true, ↓reduceIte, Finset.mem_filter] at hv hw
        exact hv.2 hw.2
      · exact hzw rfl
    · exact (F.disjoint h).mono (hs z) (hs w)
  have he := A.segments.test_energy_le_allow_empty P hp hd u
  simpa only [Fintype.sum_prod_type, Fintype.sum_bool, P, Bool.false_eq_true, ↓reduceIte,
    add_comm] using he

/-- The explicit increase in the squared test after simultaneous splitting. -/
lemma split_gain_le (F : A.segments.Family) (H : Fin F.n → Set ι)
    (hH : ∀ i, A.Ancestral (H i)) (u : ι →₀ ℝ) :
    (∑ i, (∑ v ∈ F.seg i, u v) ^ 2) +
      2 * (∑ i : Fin F.n, ((∑ v ∈ (F.seg i).filter (· ∉ H i), u v) ^ 2 -
        (∑ v ∈ F.seg i, u v) * (∑ v ∈ (F.seg i).filter (· ∉ H i), u v))) ≤
        (A.segments.primalSeminorm u) ^ 2 := by
  classical
  have he := A.split_energy_le F H hH u
  have hp (i : Fin F.n) :
      (∑ v ∈ (F.seg i).filter (· ∈ H i), u v) +
      (∑ v ∈ (F.seg i).filter (· ∉ H i), u v) = ∑ v ∈ F.seg i, u v := by
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    by_cases h : v ∈ H i <;> simp [h]
  convert he using 1
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← hp i]
  ring

/-- A minimal vertex outside a head. Gates in a tree form an antichain. -/
def Gate (H : Set ι) (g : ι) : Prop :=
  g ∉ H ∧ ∀ v, v < g → v ∈ H

lemma gates_eq_of_le {H : Set ι} {g h : ι} (hg : A.Gate H g)
    (hh : A.Gate H h) (hgh : g ≤ h) : g = h := by
  by_contra hne
  exact hg.1 (hh.2 g (lt_of_le_of_ne hgh hne))

lemma gates_eq_of_common_upper {H : Set ι} {g h v : ι} (hg : A.Gate H g)
    (hh : A.Gate H h) (hgv : g ≤ v) (hhv : h ≤ v) : g = h := by
  rcases A.predecessors_total hgv hhv with h | h
  · exact A.gates_eq_of_le hg hh h
  · exact (A.gates_eq_of_le hh hg h).symm

lemma gate_unique_in_segment {H : Set ι} {S : Finset ι}
    (hS : A.segments.IsSegment S) {g h : ι} (hg : A.Gate H g)
    (hh : A.Gate H h) (hgS : g ∈ S) (hhS : h ∈ S) : g = h := by
  rcases A.interval_chain hS g hgS h hhS with h | h
  · exact A.gates_eq_of_le hg hh h
  · exact (A.gates_eq_of_le hh hg h).symm

lemma exists_gate_le {H : Set ι} {K : Finset ι} (hK : A.Ancestral (K : Set ι))
    {v : ι} (hvK : v ∈ K) (hvH : v ∉ H) :
    ∃ g ∈ K, A.Gate H g ∧ g ≤ v := by
  classical
  let S := K.filter (fun a => a ≤ v ∧ a ∉ H)
  have hvS : v ∈ S := by simp [S, hvK, hvH]
  obtain ⟨g, hg, hmin⟩ := Finset.exists_minimal ⟨v, hvS⟩
  have hgK := (Finset.mem_filter.mp hg).1
  have hgv := (Finset.mem_filter.mp hg).2.1
  have hgH := (Finset.mem_filter.mp hg).2.2
  refine ⟨g, hgK, ⟨hgH, ?_⟩, hgv⟩
  intro a hag
  by_contra haH
  have haS : a ∈ S := by
    exact Finset.mem_filter.mpr ⟨hK hag.le hgK, hag.le.trans hgv, haH⟩
  exact (not_le_of_gt hag) (hmin haS hag.le)

/-- Canonical lower endpoint; no ordering is imposed on segment families. -/
def first (F : A.segments.Family) (i : Fin F.n) : ι :=
  Classical.choose (F.allowed i)

lemma first_spec (F : A.segments.Family) (i : Fin F.n) :
    ∃ b, A.first F i ≤ b ∧ ∀ v, v ∈ F.seg i ↔ A.first F i ≤ v ∧ v ≤ b :=
  Classical.choose_spec (F.allowed i)

lemma first_le_of_mem (F : A.segments.Family) (i : Fin F.n) {v : ι}
    (hv : v ∈ F.seg i) : A.first F i ≤ v := by
  obtain ⟨b, _, hm⟩ := A.first_spec F i
  exact ((hm v).mp hv).1

lemma first_mem (F : A.segments.Family) (i : Fin F.n) : A.first F i ∈ F.seg i := by
  obtain ⟨b, hb, hm⟩ := A.first_spec F i
  exact (hm _).mpr ⟨le_rfl, hb⟩

/-- Two heads through a common exterior vertex are nested; cutting the longer
    at the shorter's first vertex preserves exactly the shorter head sum. -/
lemma crossing_cut_sum {H : Set ι} (hH : A.Ancestral H) (p : ι →₀ ℝ)
    (hp : ∀ v, v ∉ H → p v = 0) (F G : A.segments.Family)
    (i : Fin F.n) (j : Fin G.n) {g : ι} (hg : g ∉ H)
    (hgF : g ∈ F.seg i) (hgG : g ∈ G.seg j)
    (hfirst : A.first F i ≤ A.first G j) :
    (∑ v ∈ (F.seg i).filter (fun v => A.first G j ≤ v), p v) =
      ∑ v ∈ G.seg j, p v := by
  classical
  obtain ⟨b, hfb, hFm⟩ := A.first_spec F i
  obtain ⟨d, hgd, hGm⟩ := A.first_spec G j
  have hhead : ∀ S, A.segments.IsSegment S → g ∈ S → ∀ v ∈ S, v ∈ H → v ≤ g := by
    intro S hS hgS v hv hvH
    rcases A.interval_chain hS v hv g hgS with h | h
    · exact h
    · exact False.elim (hg (hH h hvH))
  have he : ((F.seg i).filter (fun v => A.first G j ≤ v)).filter (· ∈ H) =
      (G.seg j).filter (· ∈ H) := by
    ext v
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hvF, hvfirst⟩, hvH⟩
      refine ⟨(hGm v).mpr ⟨hvfirst, ?_⟩, hvH⟩
      exact (hhead _ (F.allowed i) hgF v hvF hvH).trans ((hGm g).mp hgG).2
    · rintro ⟨hvG, hvH⟩
      have hvg := hhead _ (G.allowed j) hgG v hvG hvH
      exact ⟨⟨(hFm v).mpr ⟨hfirst.trans ((hGm v).mp hvG).1,
        hvg.trans ((hFm g).mp hgF).2⟩, ((hGm v).mp hvG).1⟩, hvH⟩
  have hf (S : Finset ι) : (∑ v ∈ S.filter (· ∈ H), p v) = ∑ v ∈ S, p v := by
    apply Finset.sum_filter_of_ne
    intro v _ hpv
    by_contra hvH
    exact hpv (hp v hvH)
  rw [← hf ((F.seg i).filter (fun v => A.first G j ≤ v)), he, hf]

/-- Zero-extension along a finite injection preserves the finite sum. -/
lemma sum_extend_zero {κ ν : Type*} [Fintype κ] [Fintype ν]
    (e : κ ↪ ν) (f : κ → ℝ) :
    (∑ i, Function.extend e f (fun _ => 0) i) = ∑ a, f a := by
  classical
  let I := Finset.univ.image e
  have hz : ∀ i ∈ Finset.univ, i ∉ I → Function.extend e f (fun _ => 0) i = 0 := by
    intro i _ hi
    apply Function.extend_apply'
    simpa [I] using hi
  rw [← Finset.sum_subset (Finset.subset_univ I) hz,
    Finset.sum_image (fun _ _ _ _ h => e.injective h)]
  apply Finset.sum_congr rfl
  intro a _
  exact e.injective.extend_apply _ _ _

/-- Simultaneous splitting restricted to any injected list of original segments. -/
lemma matched_split_gain_le {κ : Type*} [Fintype κ]
    (F : A.segments.Family) (e : κ ↪ Fin F.n) (c : κ → ι) (p : ι →₀ ℝ) :
    (∑ i, (∑ v ∈ F.seg i, p v) ^ 2) +
      2 * (∑ a, ((∑ v ∈ (F.seg (e a)).filter (fun v => c a ≤ v), p v) ^ 2 -
        (∑ v ∈ F.seg (e a), p v) *
          (∑ v ∈ (F.seg (e a)).filter (fun v => c a ≤ v), p v))) ≤
      (A.segments.primalSeminorm p) ^ 2 := by
  classical
  let H : Fin F.n → Set ι := Function.extend e (fun a => {v | ¬ c a ≤ v}) (fun _ => Set.univ)
  have he (a : κ) : H (e a) = {v | ¬ c a ≤ v} := e.injective.extend_apply _ _ _
  have hout (i : Fin F.n) (hi : ¬ ∃ a, e a = i) : H i = Set.univ :=
    Function.extend_apply' _ _ _ hi
  have hH : ∀ i, A.Ancestral (H i) := by
    intro i
    by_cases hi : ∃ a, e a = i
    · obtain ⟨a, rfl⟩ := hi
      rw [he]
      exact A.ancestral_not_above (c a)
    · rw [hout i hi]
      intro a b _ _
      trivial
  have hb := A.split_gain_le F H hH p
  let q : κ → ℝ := fun a =>
    (∑ v ∈ (F.seg (e a)).filter (fun v => c a ≤ v), p v) ^ 2 -
      (∑ v ∈ F.seg (e a), p v) *
        (∑ v ∈ (F.seg (e a)).filter (fun v => c a ≤ v), p v)
  have hid : (fun i => (∑ v ∈ (F.seg i).filter (· ∉ H i), p v) ^ 2 -
      (∑ v ∈ F.seg i, p v) * (∑ v ∈ (F.seg i).filter (· ∉ H i), p v)) =
        Function.extend e q (fun _ => 0) := by
    funext i
    by_cases hi : ∃ a, e a = i
    · obtain ⟨a, rfl⟩ := hi
      rw [he, e.injective.extend_apply]
      simp [q]
    · rw [hout i hi, Function.extend_apply' _ _ _ hi]
      simp
  rw [hid, sum_extend_zero] at hb
  exact hb

/-- Opposite head sums, matched injectively in both families, spend only the
    combined testing deficits. This is the simultaneous boundary cancellation. -/
lemma opposite_matching_le {κ : Type*} [Fintype κ]
    {H : Set ι} (hH : A.Ancestral H) (p : ι →₀ ℝ)
    (hp : ∀ v, v ∉ H → p v = 0) (F G : A.segments.Family)
    (eF : κ ↪ Fin F.n) (eG : κ ↪ Fin G.n) (g : κ → ι)
    (hgH : ∀ a, g a ∉ H) (hgF : ∀ a, g a ∈ F.seg (eF a))
    (hgG : ∀ a, g a ∈ G.seg (eG a))
    (hopp : ∀ a, (∑ v ∈ F.seg (eF a), p v) * (∑ v ∈ G.seg (eG a), p v) < 0) :
    2 * (∑ a, |(∑ v ∈ F.seg (eF a), p v) * (∑ v ∈ G.seg (eG a), p v)|) ≤
      ((A.segments.primalSeminorm p) ^ 2 - ∑ i, (∑ v ∈ F.seg i, p v) ^ 2) +
      ((A.segments.primalSeminorm p) ^ 2 - ∑ j, (∑ v ∈ G.seg j, p v) ^ 2) := by
  classical
  let P : κ → Prop := fun a => A.first F (eF a) ≤ A.first G (eG a)
  let L := {a : κ // P a}
  let U := {a : κ // ¬ P a}
  let eL : L ↪ Fin F.n := ⟨fun a => eF a.val,
    fun a b h => Subtype.ext (eF.injective h)⟩
  let eU : U ↪ Fin G.n := ⟨fun a => eG a.val,
    fun a b h => Subtype.ext (eG.injective h)⟩
  have hcutL (a : L) :
      (∑ v ∈ (F.seg (eL a)).filter (fun v => A.first G (eG a.val) ≤ v), p v) =
        ∑ v ∈ G.seg (eG a.val), p v :=
    A.crossing_cut_sum hH p hp F G (eF a.val) (eG a.val)
      (hgH a.val) (hgF a.val) (hgG a.val) a.property
  have hcutU (a : U) :
      (∑ v ∈ (G.seg (eU a)).filter (fun v => A.first F (eF a.val) ≤ v), p v) =
        ∑ v ∈ F.seg (eF a.val), p v := by
    have hfirst : A.first G (eG a.val) ≤ A.first F (eF a.val) := by
      rcases A.predecessors_total (A.first_le_of_mem F _ (hgF a.val))
        (A.first_le_of_mem G _ (hgG a.val)) with h | h
      · exact False.elim (a.property h)
      · exact h
    exact A.crossing_cut_sum hH p hp G F (eG a.val) (eF a.val)
      (hgH a.val) (hgG a.val) (hgF a.val) hfirst
  have hF := A.matched_split_gain_le F eL (fun a => A.first G (eG a.val)) p
  have hG := A.matched_split_gain_le G eU (fun a => A.first F (eF a.val)) p
  simp_rw [hcutL] at hF
  simp_rw [hcutU] at hG
  have hL : (∑ a : L, |(∑ v ∈ F.seg (eF a.val), p v) *
      (∑ v ∈ G.seg (eG a.val), p v)|) ≤
      ∑ a : L, ((∑ v ∈ G.seg (eG a.val), p v) ^ 2 -
        (∑ v ∈ F.seg (eL a), p v) * (∑ v ∈ G.seg (eG a.val), p v)) := by
    apply Finset.sum_le_sum
    intro a _
    rw [abs_of_neg (hopp a.val)]
    change -( (∑ v ∈ F.seg (eF a.val), p v) * (∑ v ∈ G.seg (eG a.val), p v)) ≤
      (∑ v ∈ G.seg (eG a.val), p v) ^ 2 -
        (∑ v ∈ F.seg (eF a.val), p v) * (∑ v ∈ G.seg (eG a.val), p v)
    nlinarith [sq_nonneg (∑ v ∈ G.seg (eG a.val), p v)]
  have hU : (∑ a : U, |(∑ v ∈ F.seg (eF a.val), p v) *
      (∑ v ∈ G.seg (eG a.val), p v)|) ≤
      ∑ a : U, ((∑ v ∈ F.seg (eF a.val), p v) ^ 2 -
        (∑ v ∈ G.seg (eU a), p v) * (∑ v ∈ F.seg (eF a.val), p v)) := by
    apply Finset.sum_le_sum
    intro a _
    rw [abs_of_neg (hopp a.val)]
    change -( (∑ v ∈ F.seg (eF a.val), p v) * (∑ v ∈ G.seg (eG a.val), p v)) ≤
      (∑ v ∈ F.seg (eF a.val), p v) ^ 2 -
        (∑ v ∈ G.seg (eG a.val), p v) * (∑ v ∈ F.seg (eF a.val), p v)
    nlinarith [sq_nonneg (∑ v ∈ F.seg (eF a.val), p v)]
  have hsum := Fintype.sum_subtype_add_sum_subtype P (fun a =>
    |(∑ v ∈ F.seg (eF a), p v) * (∑ v ∈ G.seg (eG a), p v)|)
  change (∑ a : L, _) + (∑ a : U, _) = _ at hsum
  linarith

/-- The (possibly zero) head sum carried by the unique segment at a gate. -/
def boundaryCoeff (F : A.segments.Family) (p : ι →₀ ℝ) (g : ι) : ℝ :=
  ∑ i : Fin F.n, if g ∈ F.seg i then (∑ v ∈ F.seg i, p v) else 0

lemma boundaryCoeff_eq (F : A.segments.Family) (p : ι →₀ ℝ)
    (i : Fin F.n) {g : ι} (hg : g ∈ F.seg i) :
    A.boundaryCoeff F p g = ∑ v ∈ F.seg i, p v := by
  classical
  rw [boundaryCoeff, Finset.sum_eq_single i]
  · simp [hg]
  · intro j _ hji
    have hj : g ∉ F.seg j := fun h => Finset.disjoint_left.mp (F.disjoint hji) h hg
    simp [hj]
  · simp

lemma boundaryCoeff_nonzero_mem (F : A.segments.Family) (p : ι →₀ ℝ)
    {g : ι} (h : A.boundaryCoeff F p g ≠ 0) : ∃ i, g ∈ F.seg i := by
  classical
  by_contra hn
  have hm : ∀ i, g ∉ F.seg i := by simpa using hn
  exact h (by simp [boundaryCoeff, hm])

/-- Exact two-family opposite-crossing estimate, written without a sign-filter
    so that it can be averaged over independent finite endpoint laws. -/
lemma opposite_crossing_le {κ : Type*} [Fintype κ]
    {H : Set ι} (hH : A.Ancestral H) (p : ι →₀ ℝ)
    (hp : ∀ v, v ∉ H → p v = 0) (F G : A.segments.Family)
    (gate : κ ↪ ι) (hgate : ∀ a, A.Gate H (gate a)) :
    (∑ a, (|A.boundaryCoeff F p (gate a)| * |A.boundaryCoeff G p (gate a)| -
      A.boundaryCoeff F p (gate a) * A.boundaryCoeff G p (gate a))) ≤
      ((A.segments.primalSeminorm p) ^ 2 - ∑ i, (∑ v ∈ F.seg i, p v) ^ 2) +
      ((A.segments.primalSeminorm p) ^ 2 - ∑ j, (∑ v ∈ G.seg j, p v) ^ 2) := by
  classical
  let P : κ → Prop := fun a => A.boundaryCoeff F p (gate a) *
    A.boundaryCoeff G p (gate a) < 0
  let M := {a : κ // P a}
  have hnF (a : M) : A.boundaryCoeff F p (gate a.val) ≠ 0 := by
    intro he
    have := a.property
    change A.boundaryCoeff F p (gate a.val) * A.boundaryCoeff G p (gate a.val) < 0 at this
    simp [he] at this
  have hnG (a : M) : A.boundaryCoeff G p (gate a.val) ≠ 0 := by
    intro he
    have := a.property
    change A.boundaryCoeff F p (gate a.val) * A.boundaryCoeff G p (gate a.val) < 0 at this
    simp [he] at this
  choose iF hiF using fun a : M => A.boundaryCoeff_nonzero_mem F p (hnF a)
  choose iG hiG using fun a : M => A.boundaryCoeff_nonzero_mem G p (hnG a)
  have hiFinj : Function.Injective iF := by
    intro a b hab
    apply Subtype.ext
    apply gate.injective
    exact A.gate_unique_in_segment (F.allowed (iF a)) (hgate a.val) (hgate b.val)
      (hiF a) (by rw [hab]; exact hiF b)
  have hiGinj : Function.Injective iG := by
    intro a b hab
    apply Subtype.ext
    apply gate.injective
    exact A.gate_unique_in_segment (G.allowed (iG a)) (hgate a.val) (hgate b.val)
      (hiG a) (by rw [hab]; exact hiG b)
  have hbF (a : M) := A.boundaryCoeff_eq F p (iF a) (hiF a)
  have hbG (a : M) := A.boundaryCoeff_eq G p (iG a) (hiG a)
  have hb := A.opposite_matching_le hH p hp F G ⟨iF, hiFinj⟩ ⟨iG, hiGinj⟩
    (fun a => gate a.val) (fun a => (hgate a.val).1) hiF hiG (by
      intro a
      change (∑ v ∈ F.seg (iF a), p v) * (∑ v ∈ G.seg (iG a), p v) < 0
      rw [← hbF, ← hbG]
      exact a.property)
  simp only [Function.Embedding.coeFn_mk, ← hbF, ← hbG] at hb
  let f : κ → ℝ := fun a => |A.boundaryCoeff F p (gate a)| *
    |A.boundaryCoeff G p (gate a)| - A.boundaryCoeff F p (gate a) * A.boundaryCoeff G p (gate a)
  have hzero : (∑ a : {a : κ // ¬ P a}, f a.val) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    dsimp [f]
    rw [← abs_mul, abs_of_nonneg (le_of_not_gt a.property), sub_self]
  have heq : (∑ a : M, f a.val) =
      2 * ∑ a : M, |A.boundaryCoeff F p (gate a.val) * A.boundaryCoeff G p (gate a.val)| := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    dsimp [f]
    rw [← abs_mul, abs_of_neg a.property]
    ring
  have hs := Fintype.sum_subtype_add_sum_subtype P f
  rw [hzero, add_zero, heq] at hs
  simpa only [hs] using hb

lemma gate_coefficient_energy {κ : Type*} [Fintype κ] {H : Set ι}
    (F : A.segments.Family) (a : Fin F.n → ℝ)
    (gate : κ ↪ ι) (hg : ∀ g, A.Gate H (gate g)) :
    (∑ g, (A.segments.combine F.seg a (A.segments.unitVector (gate g))) ^ 2) ≤
      ∑ i, a i ^ 2 := by
  classical
  let P : κ → Prop := fun g => ∃ i, gate g ∈ F.seg i
  let M := {g : κ // P g}
  choose idx hidx using fun g : M => g.property
  have hinj : Function.Injective idx := by
    intro g h he
    apply Subtype.ext
    apply gate.injective
    exact A.gate_unique_in_segment (F.allowed (idx g)) (hg g.val) (hg h.val)
      (hidx g) (by rw [he]; exact hidx h)
  have hz : (∑ g : {g : κ // ¬ P g},
      (A.segments.combine F.seg a (A.segments.unitVector (gate g.val))) ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro g _
    rw [SegmentSystem.combine_unit]
    have hgn : ∀ i, gate g.val ∉ F.seg i := by simpa only [P, not_exists] using g.property
    simp only [hgn, ↓reduceIte, Finset.sum_const_zero, zero_pow (by norm_num : 2 ≠ 0)]
  have he := Fintype.sum_subtype_add_sum_subtype P
    (fun g => (A.segments.combine F.seg a (A.segments.unitVector (gate g))) ^ 2)
  rw [hz, add_zero] at he
  rw [← he]
  calc
    _ = ∑ g : M, a (idx g) ^ 2 := by
      apply Finset.sum_congr rfl
      intro g _
      rw [A.segments.combine_unit_of_mem F a (idx g) (hidx g)]
    _ = ∑ i ∈ Finset.univ.image idx, a i ^ 2 :=
      (Finset.sum_image (s := Finset.univ) (f := fun i : Fin F.n => a i ^ 2)
        (fun _ _ _ _ h => hinj h)).symm
    _ ≤ _ := Finset.sum_le_univ_sum_of_nonneg (fun i => sq_nonneg _)

/-- The tail from the unique segment through g, or the empty segment if absent. -/
def tailAt (F : A.segments.Family) (H : Finset ι) (g : ι) : Finset ι :=
  if h : ∃ i, g ∈ F.seg i then (F.seg h.choose).filter (· ∉ H) else ∅

lemma tailAt_eq (F : A.segments.Family) (H : Finset ι)
    (i : Fin F.n) {g : ι} (hg : g ∈ F.seg i) :
    A.tailAt F H g = (F.seg i).filter (· ∉ H) := by
  classical
  have h : ∃ i, g ∈ F.seg i := ⟨i,hg⟩
  have he : h.choose = i := by
    by_contra hn
    exact Finset.disjoint_left.mp (F.disjoint hn) h.choose_spec hg
  simp only [tailAt, dite_eq_left h]
  rw [he]

lemma tailAt_mem {F : A.segments.Family} {H : Finset ι} {g v : ι}
    (hv : v ∈ A.tailAt F H g) : ∃ i, g ∈ F.seg i ∧ v ∈ F.seg i ∧ v ∉ H := by
  classical
  unfold tailAt at hv
  split_ifs at hv with h
  · exact ⟨h.choose, h.choose_spec, (Finset.mem_filter.mp hv).1, (Finset.mem_filter.mp hv).2⟩
  · simp at hv

lemma tailAt_outside {F : A.segments.Family} {H : Finset ι} {g v : ι}
    (hv : v ∈ A.tailAt F H g) : v ∉ H := (A.tailAt_mem hv).choose_spec.2.2

lemma tailAt_allowed (F : A.segments.Family) {H : Finset ι}
    (hH : A.Ancestral (H : Set ι)) (g : ι) (hne : (A.tailAt F H g).Nonempty) :
    A.segments.IsSegment (A.tailAt F H g) := by
  classical
  obtain ⟨v,hv⟩ := hne
  obtain ⟨i, hgi, _, _⟩ := A.tailAt_mem hv
  rw [A.tailAt_eq F H i hgi] at hv ⊢
  convert A.segment_filter_tail (F.allowed i) hH ?_ using 1
  · ext w
    simp only [Finset.mem_filter, Finset.mem_coe]
  · simpa only [Finset.filter_nonempty_iff, Finset.mem_coe] using
      (show ((F.seg i).filter (· ∉ H)).Nonempty from ⟨v,hv⟩)

lemma tailAt_cone {F : A.segments.Family} {H : Finset ι} {g v : ι}
    (hg : A.Gate (H : Set ι) g) (hv : v ∈ A.tailAt F H g) : g ≤ v := by
  obtain ⟨i,hgi,hvi,hvH⟩ := A.tailAt_mem hv
  rcases A.interval_chain (F.allowed i) g hgi v hvi with h | h
  · exact h
  · by_contra hn
    have hvne : v ≠ g := fun he => hn (he ▸ le_rfl)
    exact hvH (hg.2 v (lt_of_le_of_ne h hvne))

lemma tailAt_pairwise {κ : Type*} (F : κ → A.segments.Family) {H : Finset ι}
    (gate : κ ↪ ι) (hg : ∀ a, A.Gate (H : Set ι) (gate a)) :
    Pairwise (fun a b => Disjoint (A.tailAt (F a) H (gate a)) (A.tailAt (F b) H (gate b))) := by
  intro a b hab
  apply Finset.disjoint_left.mpr
  intro v hva hvb
  exact hab (gate.injective (A.gates_eq_of_common_upper (hg a) (hg b)
    (A.tailAt_cone (hg a) hva) (A.tailAt_cone (hg b) hvb)))

lemma gate_on_nonzero_segment {H K : Finset ι} (hH : A.Ancestral (H : Set ι))
    (hK : A.Ancestral (K : Set ι)) (F : A.segments.Family)
    (hFK : ∀ i, F.seg i ⊆ K) (p : ι →₀ ℝ) (hp : ∀ v, v ∉ H → p v = 0)
    (i : Fin F.n) (hi : (∑ v ∈ F.seg i, p v) ≠ 0) {v : ι}
    (hvi : v ∈ F.seg i) (hvH : v ∉ H) :
    ∃ g ∈ K, A.Gate (H : Set ι) g ∧ g ∈ F.seg i := by
  classical
  obtain ⟨w, hwi, hpw⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
  have hwH : w ∈ H := by by_contra hn; exact hpw (hp w hn)
  have hfH : A.first F i ∈ H := hH (A.first_le_of_mem F i hwi) hwH
  obtain ⟨g,hgK,hg,hgv⟩ := A.exists_gate_le hK (hFK i hvi) hvH
  obtain ⟨b,hfb,hm⟩ := A.first_spec F i
  have hfg : A.first F i ≤ g := by
    rcases A.predecessors_total (A.first_le_of_mem F i hvi) hgv with h | h
    · exact h
    · exact False.elim (hg.1 (hH h hfH))
  exact ⟨g,hgK,hg,(hm g).mpr ⟨hfg,hgv.trans ((hm v).mp hvi).2⟩⟩

/-- The represented finite set of all gates of H in K. -/
def gateSet (H K : Finset ι) : Finset ι := K.filter (A.Gate (H : Set ι))

lemma mem_gateSet {H K : Finset ι} {g : ι} :
    g ∈ A.gateSet H K ↔ g ∈ K ∧ A.Gate (H : Set ι) g := Finset.mem_filter

/-- Replacement coefficients have no wholly exterior contribution. Their entire
    tail is the sum of their crossing tails at the finitely represented gates. -/
lemma replaced_tail_eq {H K : Finset ι} (hH : A.Ancestral (H : Set ι))
    (hK : A.Ancestral (K : Set ι)) (F : A.segments.Family)
    (hFK : ∀ i, F.seg i ⊆ K) (p : ι →₀ ℝ) (hp : ∀ v, v ∉ H → p v = 0) :
    A.segments.tailDual H (A.segments.combine F.seg (fun i => ∑ v ∈ F.seg i, p v)) =
      A.segments.combine (fun g : A.gateSet H K => A.tailAt F H g.val)
        (fun g : A.gateSet H K => A.boundaryCoeff F p g.val) := by
  classical
  apply A.segments.dual_ext
  intro v
  rw [SegmentSystem.tailDual_apply, sub_apply, SegmentSystem.headDual_unit]
  by_cases hvH : v ∈ H
  · rw [ite_eq_left hvH, sub_self, SegmentSystem.combine_unit]
    symm
    apply Finset.sum_eq_zero
    intro g _
    rw [ite_eq_right (fun hv => A.tailAt_outside hv hvH)]
  rw [ite_eq_right hvH, sub_zero]
  by_cases hhas : ∃ i, v ∈ F.seg i
  · obtain ⟨i,hvi⟩ := hhas
    rw [A.segments.combine_unit_of_mem F _ i hvi, SegmentSystem.combine_unit]
    by_cases hi : (∑ w ∈ F.seg i, p w) = 0
    · rw [hi]
      symm
      apply Finset.sum_eq_zero
      intro g _
      split_ifs with hv
      · obtain ⟨j,hgj,hvj,_⟩ := A.tailAt_mem hv
        have hji : j = i := by
          by_contra hn
          exact Finset.disjoint_left.mp (F.disjoint hn) hvj hvi
        subst j
        rwa [A.boundaryCoeff_eq F p i hgj]
      · rfl
    obtain ⟨g,hgK,hg,hgi⟩ := A.gate_on_nonzero_segment hH hK F hFK p hp i hi hvi hvH
    let g' : A.gateSet H K := ⟨g, A.mem_gateSet.mpr ⟨hgK,hg⟩⟩
    have hvJ : v ∈ A.tailAt F H g := by
      rw [A.tailAt_eq F H i hgi]
      exact Finset.mem_filter.mpr ⟨hvi,hvH⟩
    rw [Finset.sum_eq_single g']
    · rw [ite_eq_left hvJ, A.boundaryCoeff_eq F p i hgi]
    · intro h _ hh
      rw [ite_eq_right]
      intro hv
      have he : h.val = g := A.gates_eq_of_common_upper
        (A.mem_gateSet.mp h.property).2 hg
        (A.tailAt_cone (A.mem_gateSet.mp h.property).2 hv) (A.tailAt_cone hg hvJ)
      exact hh (Subtype.ext he)
    · simp
  · have hn : ∀ i, v ∉ F.seg i := by simpa only [not_exists] using hhas
    rw [SegmentSystem.combine_unit, SegmentSystem.combine_unit]
    have hz : (∑ i, if v ∈ F.seg i then (∑ w ∈ F.seg i,p w) else 0) = 0 := by simp [hn]
    rw [hz]
    symm
    apply Finset.sum_eq_zero
    intro g _
    rw [ite_eq_right]
    intro hv
    obtain ⟨i,_,hvi,_⟩ := A.tailAt_mem hv
    exact hn i hvi

lemma primal_filter_le {H : Set ι} (hH : A.Ancestral H) (u : ι →₀ ℝ) :
    A.segments.primalSeminorm (u.filter (· ∈ H)) ≤ A.segments.primalSeminorm u := by
  classical
  rw [SegmentSystem.primalSeminorm,
    Seminorm.iSup_apply A.segments.families_bddAbove]
  apply ciSup_le
  intro F
  have h := A.segments.test_energy_le_allow_empty
    (fun i => (F.seg i).filter (· ∈ H))
    (fun i hne => A.segment_filter_head (F.allowed i) hH hne)
    (fun i j hij => (F.disjoint hij).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)) u
  have he : ‖F.test (u.filter (· ∈ H))‖ ^ 2 =
      ∑ i, (∑ v ∈ (F.seg i).filter (· ∈ H), u v) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [SegmentSystem.Family.test, LinearMap.coe_mk, AddHom.coe_mk,
      WithLp.ofLp_toLp, Real.norm_eq_abs, sq_abs]
    congr 1
    simp [Finsupp.filter_apply, Finset.sum_filter]
  rw [← he] at h
  exact (sq_le_sq₀ (norm_nonneg _) (apply_nonneg _ _)).mp h

lemma primal_filter_tail_le {H : Set ι} (hH : A.Ancestral H) (u : ι →₀ ℝ) :
    A.segments.primalSeminorm (u.filter (· ∉ H)) ≤ A.segments.primalSeminorm u := by
  classical
  rw [SegmentSystem.primalSeminorm,
    Seminorm.iSup_apply A.segments.families_bddAbove]
  apply ciSup_le
  intro F
  have h := A.segments.test_energy_le_allow_empty
    (fun i => (F.seg i).filter (· ∉ H))
    (fun i hne => A.segment_filter_tail (F.allowed i) hH hne)
    (fun i j hij => (F.disjoint hij).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)) u
  have he : ‖F.test (u.filter (· ∉ H))‖ ^ 2 =
      ∑ i, (∑ v ∈ (F.seg i).filter (· ∉ H), u v) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [SegmentSystem.Family.test, LinearMap.coe_mk, AddHom.coe_mk,
      WithLp.ofLp_toLp, Real.norm_eq_abs, sq_abs]
    congr 1
    simp [Finsupp.filter_apply, Finset.sum_filter]
  rw [← he] at h
  exact (sq_le_sq₀ (norm_nonneg _) (apply_nonneg _ _)).mp h

/-- Restricting any test family to a finite ancestral set gives one of the
    finitely many local families, with exactly the same energy for supported tests. -/
lemma localize_family_energy {K : Finset ι} (hK : A.Ancestral (K : Set ι))
    (F : A.segments.Family) (p : ι →₀ ℝ) (hp : ∀ v, v ∉ K → p v = 0) :
    ∃ G : A.segments.LocalFamily K,
      (∑ i, (∑ v ∈ F.seg i, p v) ^ 2) =
        ∑ S : A.segments.LocalIndex G, (∑ v ∈ S.val, p v) ^ 2 := by
  classical
  let P : Fin F.n → Prop := fun i => ((F.seg i).filter (· ∈ K)).Nonempty
  let I := {i : Fin F.n // P i}
  let f : I → Finset ι := fun i => (F.seg i.val).filter (· ∈ K)
  have hf : Function.Injective f := by
    intro i j he
    apply Subtype.ext
    by_contra hne
    obtain ⟨v, hv⟩ := i.property
    have hvj : v ∈ f j := by rw [← he]; exact hv
    exact Finset.disjoint_left.mp (F.disjoint hne)
      (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hvj).1
  let Gset := Finset.univ.image f
  have hGK : Gset ∈ K.powerset.powerset := by
    apply Finset.mem_powerset.mpr
    intro S hS
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hS
    apply Finset.mem_powerset.mpr
    intro v hv
    exact (Finset.mem_filter.mp hv).2
  have hGa : ∀ S ∈ Gset, A.segments.IsSegment S := by
    intro S hS
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hS
    convert A.segment_filter_head (F.allowed i.val) hK (by
      have hi := i.property
      change ((F.seg i.val).filter (fun v => v ∈ K)).Nonempty at hi
      simpa only [Finset.filter_nonempty_iff, Finset.mem_coe] using hi) using 1
    ext v
    simp only [f, Finset.mem_filter, Finset.mem_coe]

  have hGd : (Gset : Set (Finset ι)).Pairwise Disjoint := by
    intro S hS U hU hSU
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hU
    have hij : i.val ≠ j.val := fun h => hSU (congrArg f (Subtype.ext h))
    exact (F.disjoint hij).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  let G : A.segments.LocalFamily K := ⟨Gset, hGK, hGa, hGd⟩
  refine ⟨G, ?_⟩
  have hsum (i : Fin F.n) : (∑ v ∈ F.seg i, p v) =
      ∑ v ∈ (F.seg i).filter (· ∈ K), p v := by
    symm
    apply Finset.sum_filter_of_ne
    intro v _ hv
    by_contra hn
    exact hv (hp v hn)
  have hzero : (∑ i : {i : Fin F.n // ¬ P i},
      (∑ v ∈ (F.seg i.val).filter (· ∈ K), p v) ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hi : (F.seg i.val).filter (· ∈ K) = ∅ := Finset.not_nonempty_iff_eq_empty.mp i.property
    rw [hi]
    simp
  have he := Fintype.sum_subtype_add_sum_subtype P
    (fun i => (∑ v ∈ (F.seg i).filter (· ∈ K), p v) ^ 2)
  rw [hzero, add_zero] at he
  simp_rw [hsum]
  rw [← he]
  change (∑ i : I, (∑ v ∈ f i, p v) ^ 2) =
    ∑ S : ↥Gset, (∑ v ∈ S.val, p v) ^ 2
  calc
    _ = ∑ S ∈ Gset, (∑ v ∈ S, p v) ^ 2 :=
      (Finset.sum_image (fun _ _ _ _ h => hf h)).symm
    _ = _ := (Finset.sum_coe_sort Gset (fun S => (∑ v ∈ S, p v) ^ 2)).symm

lemma primal_le_of_local_energies {K : Finset ι} (hK : A.Ancestral (K : Set ι))
    (p : ι →₀ ℝ) (hp : ∀ v, v ∉ K → p v = 0) {M : ℝ} (hM : 0 ≤ M)
    (hlocal : ∀ G : A.segments.LocalFamily K,
      (∑ S : A.segments.LocalIndex G, (∑ v ∈ S.val, p v) ^ 2) ≤ M ^ 2) :
    A.segments.primalSeminorm p ≤ M := by
  rw [SegmentSystem.primalSeminorm, Seminorm.iSup_apply A.segments.families_bddAbove]
  apply ciSup_le
  intro F
  obtain ⟨G, he⟩ := A.localize_family_energy hK F p hp
  have h := hlocal G
  rw [← he] at h
  have hnorm : ‖F.test p‖ ^ 2 = ∑ i, (∑ v ∈ F.seg i, p v) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [SegmentSystem.Family.test_apply, Real.norm_eq_abs, sq_abs]
  rw [← hnorm] at h
  exact (sq_le_sq₀ (norm_nonneg _) hM).mp h

/-- Finite atomic-ball formula: exact inherited dual restrictions, derived by
    finite-dimensional separation rather than assumed as model data. -/
lemma finite_atomic_representation {K : Finset ι} (hK : A.Ancestral (K : Set ι))
    (x : A.segments.Dual) (hx : ‖x‖ ≤ 1) :
    ∃ c ∈ A.segments.coefficientBall K 1,
      A.segments.totalMap K c = fun v : K => x (A.segments.unitVector v.val) := by
  classical
  let C := A.segments.totalMap K '' A.segments.coefficientBall K 1
  let z : A.segments.Coordinates K := fun v => x (A.segments.unitVector v.val)
  suffices z ∈ C by exact this
  by_contra hn
  have hCc : Convex ℝ C := (A.segments.coefficientBall_convex K 1).linear_image _
  have hCk : IsCompact C := (A.segments.coefficientBall_compact K (by norm_num : (0:ℝ) ≤ 1)).image
    (A.segments.totalMap K).continuous_of_finiteDimensional
  obtain ⟨f, u, hfu, huz⟩ := geometric_hahn_banach_closed_point hCc hCk.isClosed hn
  have hzC : (0 : A.segments.Coordinates K) ∈ C := by
    refine ⟨0, ?_, map_zero _⟩
    change (∑ F : A.segments.LocalFamily K, ‖(0 : A.segments.Coefficients K) F‖) ≤ 1
    simp
  have hu : 0 < u := by simpa only [map_zero] using hfu 0 hzC
  let p := A.segments.coordinateTest K (fun w => f (Pi.single w 1))
  have hp : ∀ v, v ∉ K → p v = 0 := by
    intro v hv
    exact A.segments.coordinateTest_not_mem K _ hv
  have hpbound : A.segments.primalSeminorm p ≤ u := by
    apply A.primal_le_of_local_energies hK p hp hu.le
    intro F
    apply A.segments.local_energy_le_of_functional_bound F f hu.le
    intro a ha
    apply (hfu _ ?_).le
    refine ⟨Pi.single F a, A.segments.single_mem_coefficientBall K F a ha, ?_⟩
    exact A.segments.totalMap_single K F a
  have he : f z = x (A.segments.finiteEmbedding p) := by
    rw [A.segments.functional_pi_formula, A.segments.coordinateTest_pairing]
    apply Finset.sum_congr rfl
    intro v _
    exact mul_comm _ _
  have hle : f z ≤ u := by
    rw [he]
    calc
      x (A.segments.finiteEmbedding p) ≤ ‖x (A.segments.finiteEmbedding p)‖ := Real.le_norm_self _
      _ ≤ ‖x‖ * ‖A.segments.finiteEmbedding p‖ := x.le_opNorm _
      _ ≤ 1 * A.segments.primalSeminorm p := by
        rw [A.segments.finiteEmbedding_norm]
        exact mul_le_mul_of_nonneg_right hx (apply_nonneg _ _)
      _ ≤ u := by simpa using hpbound
  exact (not_lt_of_ge hle) huz

lemma finite_atomic_representation_radius {K : Finset ι} (hK : A.Ancestral (K : Set ι))
    (x : A.segments.Dual) {R : ℝ} (hR : 0 ≤ R) (hx : ‖x‖ ≤ R) :
    ∃ c ∈ A.segments.coefficientBall K R,
      A.segments.totalMap K c = fun v : K => x (A.segments.unitVector v.val) := by
  classical
  rcases eq_or_lt_of_le hR with hR0 | hRpos
  · have hx0 : x = 0 := norm_eq_zero.mp (le_antisymm (by simpa [← hR0] using hx) (norm_nonneg _))
    refine ⟨0, ?_, ?_⟩
    · simp [SegmentSystem.coefficientBall, ← hR0]
    · rw [map_zero]
      ext v
      simp [hx0]
  have hxn : ‖R⁻¹ • x‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hRpos)]
    exact (inv_mul_le_iff₀ hRpos).mpr (by simpa using hx)
  obtain ⟨c, hc, hce⟩ := A.finite_atomic_representation hK (R⁻¹ • x) hxn
  refine ⟨R • c, ?_, ?_⟩
  · change (∑ F, ‖R • c F‖) ≤ R
    simp_rw [norm_smul, Real.norm_eq_abs, abs_of_pos hRpos]
    rw [← Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left hc hRpos.le).trans_eq (mul_one _)
  · rw [map_smul, hce]
    ext v
    simp only [Pi.smul_apply, smul_apply, smul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ hRpos.ne', one_mul]

lemma headPrimal_norm_le {H : Finset ι} (hH : A.Ancestral (H : Set ι))
    (u : A.segments.JamesSpace) : ‖A.segments.headPrimal H u‖ ≤ ‖u‖ := by
  induction u using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih u =>
    rw [SegmentSystem.headPrimal_coe, UniformSpace.Completion.norm_coe,
      UniformSpace.Completion.norm_coe]
    exact A.primal_filter_le hH u

lemma tailPrimal_norm_le {H : Finset ι} (hH : A.Ancestral (H : Set ι))
    (u : A.segments.JamesSpace) : ‖u - A.segments.headPrimal H u‖ ≤ ‖u‖ := by
  induction u using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih u =>
    rw [SegmentSystem.headPrimal_coe, ← UniformSpace.Completion.coe_sub,
      UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe]
    rw [SegmentSystem.sub_filterPrimal, SegmentSystem.norm_eq_primal,
      SegmentSystem.norm_eq_primal, SegmentSystem.ofPrimal_filter]
    convert A.primal_filter_tail_le hH (A.segments.ofPrimal u) using 1
    congr 2

lemma headDual_norm_le {H : Finset ι} (hH : A.Ancestral (H : Set ι))
    (x : A.segments.Dual) : ‖A.segments.headDual H x‖ ≤ ‖x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro u
  rw [SegmentSystem.headDual_apply_apply]
  exact (x.le_opNorm _).trans (mul_le_mul_of_nonneg_left (A.headPrimal_norm_le hH u)
    (norm_nonneg _))

lemma tailDual_norm_le {H : Finset ι} (hH : A.Ancestral (H : Set ι))
    (x : A.segments.Dual) : ‖A.segments.tailDual H x‖ ≤ ‖x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro u
  rw [SegmentSystem.tailDual_apply_apply]
  exact (x.le_opNorm _).trans (mul_le_mul_of_nonneg_left (A.tailPrimal_norm_le hH u)
    (norm_nonneg _))

lemma replacement_error_le {H : Finset ι} (hH : A.Ancestral (H : Set ι))
    (F : A.segments.Family) (a b : Fin F.n → ℝ) :
    ‖A.segments.tailDual H (A.segments.combine F.seg a - A.segments.combine F.seg b)‖ ^ 2 ≤
      ∑ i, (a i - b i) ^ 2 := by
  have hV : 0 ≤ ∑ i,(a i-b i)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hc := A.tailDual_norm_le hH (A.segments.combine F.seg a - A.segments.combine F.seg b)
  rw [← SegmentSystem.combine_sub] at hc
  have ha := A.segments.norm_combine_le F.seg (a-b) (fun i _ => F.allowed i) F.disjoint
  have h := (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).2 (hc.trans ha)
  simpa only [Pi.sub_apply, Real.sq_sqrt hV, SegmentSystem.combine_sub] using h

lemma replacement_error_gate {H : Finset ι} (F : A.segments.Family)
    (a : Fin F.n → ℝ) (q : ι →₀ ℝ) {g : ι} (hg : g ∉ H) :
    A.segments.tailDual H (A.segments.combine F.seg a -
      A.segments.combine F.seg (fun i => ∑ v ∈ F.seg i,q v)) (A.segments.unitVector g) =
      A.segments.combine F.seg a (A.segments.unitVector g) - A.boundaryCoeff F q g := by
  rw [SegmentSystem.tailDual_apply, sub_apply, SegmentSystem.headDual_unit, ite_eq_right hg,
    sub_zero, sub_apply]
  simp only [SegmentSystem.combine_unit, boundaryCoeff]

lemma replacement_cross (F : A.segments.Family) (a : Fin F.n → ℝ) (p : ι →₀ ℝ) (r : ℝ) :
    (∑ i, a i * (∑ v ∈ F.seg i,(r • p) v)) =
      r * A.segments.combine F.seg a (A.segments.finiteEmbedding p) := by
  rw [SegmentSystem.finiteEmbedding_apply, SegmentSystem.combine_coe]
  change (∑ i,a i*(∑ v ∈ F.seg i,(r • p) v)) = r*(∑ i,a i*(∑ v ∈ F.seg i,p v))
  simp_rw [Finsupp.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma replacement_mass_norm {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {H K : Finset ι} (hH : A.Ancestral (H : Set ι)) (hK : A.Ancestral (K : Set ι))
    (F : Ω → A.segments.Family) (hFK : ∀ ω i, (F ω).seg i ⊆ K)
    (q : ι →₀ ℝ) (hq : ∀ v,v ∉ H → q v=0)
    (w σ : Ω → ℝ) (hw : ∀ ω,0 ≤ w ω) (hσ : ∀ ω,|σ ω|=1) :
    ‖∑ ω,w ω • (σ ω • A.segments.tailDual H
      (A.segments.combine (F ω).seg (fun i => ∑ v ∈ (F ω).seg i,q v)))‖ ≤
      Real.sqrt (∑ g : A.gateSet H K, (∑ ω,w ω * |A.boundaryCoeff (F ω) q g.val|)^2) := by
  classical
  let gate : A.gateSet H K ↪ ι := ⟨Subtype.val, Subtype.val_injective⟩
  have hg (g : A.gateSet H K) : A.Gate (H : Set ι) (gate g) :=
    (A.mem_gateSet.mp g.property).2
  have h := A.segments.norm_cone_mean_le
    (fun ω (g : A.gateSet H K) => A.tailAt (F ω) H g.val)
    (fun ω g => σ ω * A.boundaryCoeff (F ω) q g.val) w hw
    (fun ω g => A.tailAt_allowed (F ω) hH g.val) (by
      intro g h hgh ω ν
      apply Finset.disjoint_left.mpr
      intro v hvg hvh
      exact hgh (gate.injective (A.gates_eq_of_common_upper (hg g) (hg h)
        (A.tailAt_cone (hg g) hvg) (A.tailAt_cone (hg h) hvh))))
  simp only [abs_mul, hσ, one_mul] at h
  convert h using 1
  congr 1
  apply Finset.sum_congr rfl
  intro ω _
  rw [A.replaced_tail_eq hH hK (F ω) (hFK ω) q hq, SegmentSystem.combine_smul]

/-- The finite pooled coefficient/slack bound, before taking the supremum over
    head tests. No lens or convexity modulus is postulated for the space. -/
lemma pooled_tail_test {Ω : Type*} [Fintype Ω] {H K : Finset ι}
    (hH : A.Ancestral (H : Set ι)) (hK : A.Ancestral (K : Set ι))
    {R : ℝ} {x y : A.segments.Dual} (law : A.segments.BipolarLaw Ω R x y)
    (hFK : ∀ ω i,(law.atom ω).family.seg i ⊆ K)
    (hx : ∀ v,v ∉ H → x (A.segments.unitVector v)=0)
    (p : ι →₀ ℝ) (hp : ∀ v,v ∉ H → p v=0) (hpn : A.segments.primalSeminorm p ≤ 1) :
    ‖A.segments.tailDual H y‖ ≤
      2*Real.sqrt (R^2 - (x (A.segments.finiteEmbedding p))^2) := by
  classical
  have : Nonempty Ω := by
    by_contra hn
    have : IsEmpty Ω := not_nonempty_iff.mp hn
    have h := law.sum_one
    simp at h
  let r : ℝ := x (A.segments.finiteEmbedding p)
  let q : ι →₀ ℝ := r • p
  let F : Ω → A.segments.Family := fun ω => (law.atom ω).family
  let a : (ω : Ω) → Fin (F ω).n → ℝ := fun ω => (law.atom ω).coeff
  let β : (ω : Ω) → Fin (F ω).n → ℝ := fun ω i => ∑ v ∈ (F ω).seg i,q v
  let Ac : Ω → A.segments.Dual := fun ω => A.segments.combine (F ω).seg (β ω)
  let W : Ω → A.segments.Dual := fun ω =>
    A.segments.tailDual H ((law.atom ω).value - Ac ω)
  let V : Ω → ℝ := fun ω => ∑ i,(a ω i-β ω i)^2
  let L : Ω → ℝ := fun ω => r^2-∑ i,β ω i^2
  let η : ℝ := ∑ ω,law.weight ω*V ω
  let θ : ℝ := ∑ ω,law.weight ω*L ω
  have hq (v : ι) (hv : v ∉ H) : q v = 0 := by simp only [q,Finsupp.smul_apply,hp v hv,smul_zero]
  have hqn : A.segments.primalSeminorm q ≤ |r| := by
    dsimp [q]
    rw [map_smul_eq_mul, Real.norm_eq_abs]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hpn (abs_nonneg r)
  have hqn2 : (A.segments.primalSeminorm q)^2 ≤ r^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (apply_nonneg _ _) (abs_nonneg r)).2 hqn
  have hV (ω : Ω) : 0 ≤ V ω := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hL (ω : Ω) : 0 ≤ L ω := by
    apply sub_nonneg.mpr
    exact (A.segments.test_energy_le_allow_empty (F ω).seg
      (fun i _ => (F ω).allowed i) (F ω).disjoint q).trans hqn2
  have hη : 0 ≤ η := Finset.sum_nonneg (fun ω _ => mul_nonneg (law.nonneg ω) (hV ω))
  have hθ : 0 ≤ θ := Finset.sum_nonneg (fun ω _ => mul_nonneg (law.nonneg ω) (hL ω))
  have hcross : (∑ ω,law.weight ω*(∑ i,a ω i*β ω i)) = r^2 := by
    have hm := congrArg (fun z : A.segments.Dual => z (A.segments.finiteEmbedding p)) law.mean
    simp only [sum_apply, smul_apply, smul_eq_mul] at hm
    calc
      _ = r*(∑ ω,law.weight ω*(law.atom ω).value (A.segments.finiteEmbedding p)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ω _
        have hr := A.replacement_cross (F ω) (a ω) p r
        change (∑ i,a ω i*β ω i) = r*(law.atom ω).value (A.segments.finiteEmbedding p) at hr
        rw [hr]
        ring
      _ = r^2 := by rw [hm]; dsimp [r]; ring
  have hbudget : η+θ ≤ R^2-r^2 :=
    FiniteAverage.joint_budget law.weight law.nonneg law.sum_one (fun ω => Fin (F ω).n)
      a β (fun ω => (law.atom ω).energy_le) hcross
  have hWnorm (ω : Ω) : ‖W ω‖^2 ≤ V ω :=
    A.replacement_error_le hH (F ω) (a ω) (β ω)
  let gate : A.gateSet H K ↪ ι := ⟨Subtype.val,Subtype.val_injective⟩
  have hg (g : A.gateSet H K) : A.Gate (H : Set ι) (gate g) :=
    (A.mem_gateSet.mp g.property).2
  let b : Ω → A.gateSet H K → ℝ := fun ω g => A.boundaryCoeff (F ω) q g.val
  let e : Ω → A.gateSet H K → ℝ := fun ω g => W ω (A.segments.unitVector g.val)
  have he (ω : Ω) (g : A.gateSet H K) :
      e ω g = (law.atom ω).value (A.segments.unitVector g.val) - b ω g :=
    A.replacement_error_gate (F ω) (a ω) q (hg g).1
  have hgateEnergy (ω : Ω) : (∑ g,e ω g^2) ≤ V ω := by
    have heq (g : A.gateSet H K) : e ω g =
        A.segments.combine (F ω).seg (a ω-β ω) (A.segments.unitVector g.val) := by
      rw [SegmentSystem.combine_sub]
      rw [sub_apply]
      simpa only [SegmentSystem.Atom.value, SegmentSystem.combine_unit, b, β,
        boundaryCoeff, F, a] using he ω g
    simp_rw [heq]
    exact A.gate_coefficient_energy (F ω) (a ω-β ω) gate hg
  have hmean (g : A.gateSet H K) :
      (∑ ω,law.weight ω*b ω g) = -(∑ ω,law.weight ω*e ω g) := by
    have hm := congrArg (fun z : A.segments.Dual => z (A.segments.unitVector g.val)) law.mean
    simp only [sum_apply,smul_apply,smul_eq_mul,hx g.val (hg g).1] at hm
    have heq : (∑ ω,law.weight ω*b ω g)+(∑ ω,law.weight ω*e ω g) =
        ∑ ω,law.weight ω*(law.atom ω).value (A.segments.unitVector g.val) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro ω _
      rw [he]
      ring
    rw [hm] at heq
    linarith
  have hopp (ω ν : Ω) : (∑ g,(|b ω g| * |b ν g|-b ω g*b ν g)) ≤ L ω+L ν := by
    have h := A.opposite_crossing_le hH q hq (F ω) (F ν) gate hg
    change (∑ g,(|b ω g| * |b ν g|-b ω g*b ν g)) ≤
      ((A.segments.primalSeminorm q)^2 - ∑ i,β ω i^2) +
      ((A.segments.primalSeminorm q)^2 - ∑ i,β ν i^2) at h
    exact h.trans (add_le_add (sub_le_sub_right hqn2 _) (sub_le_sub_right hqn2 _))
  have hmass : (∑ g,(∑ ω,law.weight ω* |b ω g|)^2) ≤ η+2*θ :=
    FiniteAverage.pooled_mass law.weight law.nonneg law.sum_one b e V L hmean hgateEnergy hopp
  have herr : ‖∑ ω,law.weight ω • (law.sign ω • W ω)‖ ≤ Real.sqrt η := by
    apply FiniteAverage.norm_mean_le_sqrt law.weight law.nonneg law.sum_one _ hη
    apply Finset.sum_le_sum
    intro ω _
    rw [norm_smul,Real.norm_eq_abs,law.abs_sign,one_mul]
    exact mul_le_mul_of_nonneg_left (hWnorm ω) (law.nonneg ω)
  have hrec : ‖∑ ω,law.weight ω • (law.sign ω • A.segments.tailDual H (Ac ω))‖ ≤
      Real.sqrt (η+2*θ) := by
    exact (A.replacement_mass_norm hH hK F hFK q hq law.weight law.sign law.nonneg law.abs_sign).trans
      (Real.sqrt_le_sqrt hmass)
  have hdec : A.segments.tailDual H y =
      (∑ ω,law.weight ω • (law.sign ω • W ω)) +
      (∑ ω,law.weight ω • (law.sign ω • A.segments.tailDual H (Ac ω))) := by
    conv_lhs => rw [← law.signed_mean]
    rw [map_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ω _
    simp only [map_smul, W, map_sub, smul_sub]
    module
  calc
    ‖A.segments.tailDual H y‖ ≤ Real.sqrt η+Real.sqrt (η+2*θ) := by
      rw [hdec]
      exact (norm_add_le _ _).trans (add_le_add herr hrec)
    _ ≤ 2*Real.sqrt (η+θ) := FiniteAverage.sqrt_pooled hη hθ
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hbudget) (by norm_num)

/-- Pair the two exact finite atomic representations, retaining their common
    ancestral support and their actual endpoints. -/
lemma finite_lens_test {H K : Finset ι}
    (hH : A.Ancestral (H : Set ι)) (hK : A.Ancestral (K : Set ι)) (hHK : H ⊆ K)
    {R : ℝ} (hR : 0 < R) {x y : A.segments.Dual}
    (hx : ∀ v, v ∉ H → x (A.segments.unitVector v) = 0)
    (hplus : ‖x+y‖ ≤ R) (hminus : ‖x-y‖ ≤ R)
    (p : ι →₀ ℝ) (hp : ∀ v, v ∉ H → p v = 0) (hpn : A.segments.primalSeminorm p ≤ 1) :
    ‖A.segments.tailDual H (A.segments.headDual K y)‖ ≤
      2*Real.sqrt (R^2 - (x (A.segments.finiteEmbedding p))^2) := by
  classical
  obtain ⟨cp,hcp,hcep⟩ := A.finite_atomic_representation_radius hK (x+y) hR.le hplus
  obtain ⟨cm,hcm,hcem⟩ := A.finite_atomic_representation_radius hK (x-y) hR.le hminus
  have hxK : A.segments.headDual K x = x :=
    A.segments.headDual_eq_self (fun v hv => hx v (fun h => hv (hHK h)))
  let Lp0 := A.segments.lawOfCoefficients (x+y) hR cp hcp hcep
  let Lm0 := A.segments.lawOfCoefficients (x-y) hR cm hcm hcem
  let Lp : A.segments.AtomLaw (Option (A.segments.LocalFamily K)) R
      (x+A.segments.headDual K y) :=
    { Lp0 with mean := by rw [Lp0.mean, map_add, hxK] }
  let Lm : A.segments.AtomLaw (Option (A.segments.LocalFamily K)) R
      (x-A.segments.headDual K y) :=
    { Lm0 with mean := by rw [Lm0.mean, map_sub, hxK] }
  apply A.pooled_tail_test hH hK (A.segments.pairLaws Lp Lm) _ hx p hp hpn
  apply A.segments.pairLaws_subset Lp Lm K
  · exact A.segments.lawOfCoefficients_subset (x+y) hR cp hcp hcep
  · exact A.segments.lawOfCoefficients_subset (x-y) hR cm hcm hcem

/-- Finite restrictions suffice for the full dual estimate: no shrinking or
    reflexivity hypothesis is needed for this intrinsic finite-head bound. -/
lemma intrinsic_tail_test
    (hfin : ∀ S : Finset ι, ∃ K : Finset ι, S ⊆ K ∧ A.Ancestral (K : Set ι))
    {H : Finset ι} (hH : A.Ancestral (H : Set ι)) {R : ℝ} (hR : 0 < R)
    {x y : A.segments.Dual} (hx : ∀ v, v ∉ H → x (A.segments.unitVector v) = 0)
    (hplus : ‖x+y‖ ≤ R) (hminus : ‖x-y‖ ≤ R)
    (p : ι →₀ ℝ) (hp : ∀ v, v ∉ H → p v = 0) (hpn : A.segments.primalSeminorm p ≤ 1) :
    ‖A.segments.tailDual H y‖ ≤
      2*Real.sqrt (R^2 - (x (A.segments.finiteEmbedding p))^2) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
  intro u
  induction u using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih u =>
    obtain ⟨K,hsub,hK⟩ := hfin (H ∪ (A.segments.ofPrimal u).support)
    have hHK : H ⊆ K := Finset.Subset.trans Finset.subset_union_left hsub
    have huK : (A.segments.ofPrimal u).support ⊆ K :=
      Finset.Subset.trans Finset.subset_union_right hsub
    have ht := A.finite_lens_test hH hK hHK hR hx hplus hminus p hp hpn
    calc
      _ = ‖A.segments.tailDual H (A.segments.headDual K y) (u : A.segments.JamesSpace)‖ := by
        rw [SegmentSystem.tailDual_headDual, A.segments.headDual_finite_apply _ u huK]
      _ ≤ ‖A.segments.tailDual H (A.segments.headDual K y)‖ * ‖(u : A.segments.JamesSpace)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right ht (norm_nonneg _)

lemma norm_center_le {x y : A.segments.Dual} {R : ℝ}
    (hplus : ‖x+y‖ ≤ R) (hminus : ‖x-y‖ ≤ R) : ‖x‖ ≤ R := by
  have h := (norm_add_le (x+y) (x-y)).trans (add_le_add hplus hminus)
  have he : (x+y)+(x-y) = (2:ℝ) • x := by module
  rw [he, norm_smul, Real.norm_eq_abs] at h
  norm_num at h
  linarith

lemma intrinsic_tail_sq
    (hfin : ∀ S : Finset ι, ∃ K : Finset ι, S ⊆ K ∧ A.Ancestral (K : Set ι))
    {H : Finset ι} (hH : A.Ancestral (H : Set ι)) {R : ℝ} (hR : 0 ≤ R)
    {x y : A.segments.Dual} (hx : ∀ v, v ∉ H → x (A.segments.unitVector v) = 0)
    (hplus : ‖x+y‖ ≤ R) (hminus : ‖x-y‖ ≤ R) :
    ‖A.segments.tailDual H y‖^2 + 4*‖x‖^2 ≤ 4*R^2 := by
  have hxr := A.norm_center_le hplus hminus
  rcases eq_or_lt_of_le hR with hR0 | hRpos
  · have hx0 : x=0 := norm_eq_zero.mp (le_antisymm (by simpa [← hR0] using hxr) (norm_nonneg _))
    have hy0 : y=0 := norm_eq_zero.mp (le_antisymm (by simpa [← hR0,hx0] using hplus) (norm_nonneg _))
    simp [hx0,hy0,← hR0]
  let t := ‖A.segments.tailDual H y‖
  have ht : 0 ≤ t := norm_nonneg _
  have htn : t ≤ 2*R := by
    have h := A.intrinsic_tail_test hfin hH hRpos hx hplus hminus 0 (by simp) (by simp)
    simpa only [map_zero, zero_pow (by decide : 2 ≠ 0), sub_zero,
      Real.sqrt_sq_eq_abs, abs_of_nonneg hR] using h
  have ht2 : t^2 ≤ (2*R)^2 := (sq_le_sq₀ ht (by positivity)).2 htn
  have hrad : 0 ≤ R^2-t^2/4 := by nlinarith
  have hxn : ‖x‖ ≤ Real.sqrt (R^2-t^2/4) := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (Real.sqrt_nonneg _)
    intro u hu
    let p := A.segments.headArray H u
    have hp : ∀ v, v ∉ H → p v=0 := fun v hv => A.segments.headArray_outside H u hv
    have hpn : A.segments.primalSeminorm p ≤ 1 := by
      rw [← SegmentSystem.finiteEmbedding_norm, SegmentSystem.finiteEmbedding_headArray]
      exact (A.headPrimal_norm_le hH u).trans hu.le
    have he : x (A.segments.finiteEmbedding p) = x u := by
      rw [SegmentSystem.finiteEmbedding_headArray, ← SegmentSystem.headDual_apply_apply,
        A.segments.headDual_eq_self hx]
    have hval : |x u| ≤ R := by
      have h := x.le_opNorm u
      rw [Real.norm_eq_abs, hu, mul_one] at h
      exact h.trans hxr
    have hval2 : (x u)^2 ≤ R^2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hR).2 hval
    have h := A.intrinsic_tail_test hfin hH hRpos hx hplus hminus p hp hpn
    rw [he] at h
    have hsq : t^2 ≤ (2*Real.sqrt (R^2-(x u)^2))^2 :=
      (sq_le_sq₀ ht (by positivity)).2 h
    have hs := Real.sq_sqrt (sub_nonneg.mpr hval2)
    have hv2 : (x u)^2 ≤ R^2-t^2/4 := by nlinarith
    rw [Real.norm_eq_abs]
    apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [sq_abs, Real.sq_sqrt hrad]
    exact hv2
  have hxn2 := (sq_le_sq₀ (norm_nonneg x) (Real.sqrt_nonneg _)).2 hxn
  rw [Real.sq_sqrt hrad] at hxn2
  change t^2+4*‖x‖^2 ≤ 4*R^2
  nlinarith

lemma finite_heads_of_predecessors
    (hpred : ∀ b : ι, ({a : ι | a ≤ b} : Set ι).Finite) :
    ∀ S : Finset ι, ∃ K : Finset ι, S ⊆ K ∧ A.Ancestral (K : Set ι) := by
  classical
  intro S
  let U : Set ι := ⋃ b ∈ (S : Set ι), {a : ι | a ≤ b}
  have hU : U.Finite := S.finite_toSet.biUnion (fun b _ => hpred b)
  refine ⟨hU.toFinset, ?_, ?_⟩
  · intro b hb
    rw [Set.Finite.mem_toFinset]
    exact Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨hb, le_rfl⟩⟩
  · intro a b hab hb
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hb ⊢
    obtain ⟨c,hc,hbc⟩ := Set.mem_iUnion₂.mp hb
    exact Set.mem_iUnion₂.mpr ⟨c,hc,hab.trans hbc⟩

lemma coordinate_predual_approximation
    (hfin : ∀ S : Finset ι, ∃ K : Finset ι, S ⊆ K ∧ A.Ancestral (K : Set ι))
    {x : A.segments.Dual} (hx : x ∈ A.segments.CoordinatePredual)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ H : Finset ι, A.Ancestral (H : Set ι) ∧ ‖A.segments.tailDual H x‖ < ε := by
  have hxcl : x ∈ closure (Submodule.span ℝ (Set.range A.segments.coordinate) : Set A.segments.Dual) := hx
  obtain ⟨z,hz,hclose⟩ := Metric.mem_closure_iff.mp hxcl ε hε
  obtain ⟨S,hS⟩ := A.segments.span_coordinates_finite_support hz
  obtain ⟨H,hSH,hH⟩ := hfin S
  have hPH : A.segments.headDual H z = z :=
    A.segments.headDual_eq_self (fun v hv => hS v (fun h => hv (hSH h)))
  refine ⟨H,hH,?_⟩
  have he : A.segments.tailDual H x = A.segments.tailDual H (x-z) := by
    simp only [map_sub, SegmentSystem.tailDual_apply, hPH, sub_self, sub_zero]
  rw [he]
  exact lt_of_le_of_lt (A.tailDual_norm_le hH (x-z)) (by simpa only [dist_eq_norm] using hclose)

/-- Finite-dimensional compactness compares distinct members of any bounded
    sequence; no maximum over the infinitely many children is asserted. -/
lemma finite_head_pair {H : Finset ι} (hH : A.Ancestral (H : Set ι))
    (z : ℕ → A.segments.Dual) {R η : ℝ} (hz : ∀ i, ‖z i‖ ≤ R) (hη : 0 < η) :
    ∃ i j : ℕ, i ≠ j ∧ ‖A.segments.headDual H ((1/2:ℝ) • (z i-z j))‖ < η := by
  classical
  let M := Submodule.span ℝ (A.segments.coordinate '' (H : Set ι))
  have : FiniteDimensional ℝ M :=
    FiniteDimensional.span_of_finite ℝ (H.finite_toSet.image A.segments.coordinate)
  have hm (w : A.segments.Dual) : A.segments.headDual H w ∈ M := by
    rw [SegmentSystem.headDual_apply]
    apply Submodule.sum_mem
    intro v hv
    exact Submodule.smul_mem M _ (Submodule.subset_span ⟨v,hv,rfl⟩)
  let Z : ℕ → M := fun i => ⟨A.segments.headDual H (z i),hm (z i)⟩
  have hZ (i : ℕ) : Z i ∈ Metric.closedBall (0 : M) R := by
    rw [Metric.mem_closedBall]
    change dist (A.segments.headDual H (z i)) 0 ≤ R
    rw [dist_zero_right]
    exact (A.headDual_norm_le hH (z i)).trans (hz i)
  obtain ⟨a,_,φ,hφ,hconv⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hZ
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hconv.cauchySeq (2*η) (by positivity)
  have hd := hN N le_rfl (N+1) (by omega)
  change dist (Z (φ N)) (Z (φ (N+1))) < 2*η at hd
  change dist (A.segments.headDual H (z (φ N))) (A.segments.headDual H (z (φ (N+1)))) < 2*η at hd
  rw [dist_eq_norm] at hd
  change ‖A.segments.headDual H (z (φ N)) - A.segments.headDual H (z (φ (N+1)))‖ < 2*η at hd
  refine ⟨φ N, φ (N+1), hφ.injective.ne (by omega), ?_⟩
  rw [map_smul,norm_smul,map_sub,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
  linarith

lemma average_lens {x : A.segments.Dual} (z : ℕ → A.segments.Dual) {R : ℝ}
    (hplus : ∀ i, ‖x+z i‖ ≤ R) (hminus : ∀ i, ‖x-z i‖ ≤ R) (i j : ℕ) :
    ‖x+(1/2:ℝ) • (z i-z j)‖ ≤ R ∧ ‖x-(1/2:ℝ) • (z i-z j)‖ ≤ R := by
  have hp : x+(1/2:ℝ) • (z i-z j) = (1/2:ℝ) • ((x+z i)+(x-z j)) := by module
  have hm : x-(1/2:ℝ) • (z i-z j) = (1/2:ℝ) • ((x-z i)+(x+z j)) := by module
  constructor
  · rw [hp,norm_smul,Real.norm_eq_abs]
    norm_num
    have h := (norm_add_le (x+z i) (x-z j)).trans (add_le_add (hplus i) (hminus j))
    linarith
  · rw [hm,norm_smul,Real.norm_eq_abs]
    norm_num
    have h := (norm_add_le (x-z i) (x+z j)).trans (add_le_add (hminus i) (hplus j))
    linarith

/-- Exact separated-lens consequence of the intrinsic estimate. Its only
    approximation input is explicitly proved for each target model below. -/
lemma separated_lens
    (hfin : ∀ S : Finset ι, ∃ K : Finset ι, S ⊆ K ∧ A.Ancestral (K : Set ι))
    {x : A.segments.Dual}
    (happrox : ∀ η > 0, ∃ H : Finset ι, A.Ancestral (H : Set ι) ∧ ‖A.segments.tailDual H x‖ < η)
    (z : ℕ → A.segments.Dual) {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    (hplus : ∀ i, ‖x+z i‖ ≤ R) (hminus : ∀ i, ‖x-z i‖ ≤ R)
    (hsep : ∀ i j, i ≠ j → ε ≤ ‖z i-z j‖) :
    ‖x‖^2+ε^2/16 ≤ R^2 := by
  have hxr : ‖x‖ ≤ R := A.norm_center_le (hplus 0) (hminus 0)
  have hz (i : ℕ) : ‖z i‖ ≤ R := by
    apply A.norm_center_le (x := z i) (y := x)
    · simpa only [add_comm] using hplus i
    · simpa only [norm_sub_rev] using hminus i
  apply le_of_forall_pos_le_add
  intro δ hδ
  let C : ℝ := 8*R+8*‖x‖+ε+4
  have hC : 0 < C := by dsimp [C]; positivity
  let η : ℝ := min (ε/4) (min 1 (δ/C))
  have hη : 0 < η := lt_min (by positivity) (lt_min (by norm_num) (div_pos hδ hC))
  have hηε : η < ε/2 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hη1 : η ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hηδ : C*η ≤ δ := by
    have hh : η ≤ δ/C := (min_le_right _ _).trans (min_le_right _ _)
    nlinarith [(le_div_iff₀ hC).mp hh]
  obtain ⟨H,hH,hclose⟩ := happrox η hη
  let p := A.segments.headDual H x
  have hp : ∀ v, v ∉ H → p (A.segments.unitVector v)=0 := by
    intro v hv
    exact (A.segments.headDual_unit H x v).trans (ite_eq_right hv)
  have hpn : ‖p‖ ≤ ‖x‖ := A.headDual_norm_le hH x
  have hsmall : ‖x-p‖ < η := hclose
  have hplower : ‖x‖-η ≤ ‖p‖ := by
    have h := norm_sub_norm_le x p
    linarith
  obtain ⟨i,j,hij,hhead⟩ := A.finite_head_pair hH z hz hη
  let w := (1/2:ℝ) • (z i-z j)
  have hw : ε/2 ≤ ‖w‖ := by
    dsimp [w]
    rw [norm_smul,Real.norm_eq_abs]
    norm_num
    linarith [hsep i j hij]
  have hwl : ε/2-η ≤ ‖A.segments.tailDual H w‖ := by
    have h := norm_sub_norm_le w (A.segments.headDual H w)
    change ‖w‖-‖A.segments.headDual H w‖ ≤ ‖A.segments.tailDual H w‖ at h
    linarith
  obtain ⟨hwp,hwm⟩ := A.average_lens z hplus hminus i j
  have hpp : ‖p+w‖ ≤ R+η := by
    have he : p+w = (x+w)-(x-p) := by module
    rw [he]
    exact (norm_sub_le _ _).trans (add_le_add hwp hsmall.le)
  have hpm : ‖p-w‖ ≤ R+η := by
    have he : p-w = (x-w)-(x-p) := by module
    rw [he]
    exact (norm_sub_le _ _).trans (add_le_add hwm hsmall.le)
  have hbudget := A.intrinsic_tail_sq hfin hH (add_nonneg hR hη.le) hp hpp hpm
  have hpsq : ‖x‖^2 - 2*‖x‖*η ≤ ‖p‖^2 := by
    nlinarith [sq_nonneg (‖x‖-‖p‖),mul_nonneg (norm_nonneg x) (sub_nonneg.mpr hplower)]
  have hw2 : (ε/2)^2-ε*η ≤ ‖A.segments.tailDual H w‖^2 := by
    have hh := (sq_le_sq₀ (by linarith : 0 ≤ ε/2-η) (norm_nonneg _)).2 hwl
    nlinarith
  have hη2 : η^2 ≤ η := by nlinarith
  dsimp [C] at hηδ
  nlinarith

end Ancestry

end DiamondDistortion

end

end OAI
