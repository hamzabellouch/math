import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.Interval.Set.Disjoint
import OAI.Computability.BinPacking.Packing.FiniteHall
import OAI.Computability.BinPacking.Packing.PackingScalar
import OAI.Computability.BinPacking.Trees.CompletionGeometry

namespace OAI

noncomputable section

namespace BinPackingGap
namespace CoverageCounts

section FiniteCounts

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β]

theorem interval_prefix_card [LinearOrder γ] (s : Finset α) (h b : α → γ)
    (hle : ∀ i ∈ s, h i ≤ b i) (a : γ) :
    (s.filter fun i => h i ≤ a).card =
      (s.filter fun i => b i ≤ a).card +
        (s.filter fun i => h i ≤ a ∧ a < b i).card := by
  classical
  have hunion : (s.filter fun i => h i ≤ a) =
      (s.filter fun i => b i ≤ a) ∪
        (s.filter fun i => h i ≤ a ∧ a < b i) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨his, hia⟩
      by_cases hba : b i ≤ a
      · exact Or.inl ⟨his, hba⟩
      · exact Or.inr ⟨his, hia, lt_of_not_ge hba⟩
    · rintro (⟨his, hba⟩ | ⟨his, hia, _⟩)
      · exact ⟨his, (hle i his).trans hba⟩
      · exact ⟨his, hia⟩
  have hdis : Disjoint (s.filter fun i => b i ≤ a)
      (s.filter fun i => h i ≤ a ∧ a < b i) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (not_lt_of_ge (Finset.mem_filter.mp hi).2)
      (Finset.mem_filter.mp hj).2.2
  rw [hunion, Finset.card_union_of_disjoint hdis]

omit [DecidableEq α] in
theorem ordered_short_long_partition [LinearOrder γ]
    (s : Finset α) (position : α → γ) (current : γ) (short : α → Prop)
    [DecidablePred short] (horder : ∀ i ∈ s, position i ≤ current) :
    s.card = (s.filter fun i => position i < current).card +
      (s.filter fun i => position i = current ∧ short i).card +
      (s.filter fun i => position i = current ∧ ¬ short i).card := by
  classical
  have hexact : (s.filter fun i => ¬ position i < current) =
      (s.filter fun i => position i = current) := by
    ext i
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨his, hi⟩
      exact ⟨his, le_antisymm (horder i his) (le_of_not_gt hi)⟩
    · rintro ⟨his, hi⟩
      exact ⟨his, by rw [hi]; exact lt_irrefl _⟩
  have hpositions := Finset.card_filter_add_card_filter_not
    (s := s) (fun i => position i < current)
  rw [hexact] at hpositions
  have hlengths := Finset.card_filter_add_card_filter_not
    (s := s.filter fun i => position i = current) short
  simp only [Finset.filter_filter] at hlengths
  omega

theorem card_le_good_card_add {s bad : Finset α} {K : ℕ}
    (hbad : bad.card ≤ K) : s.card ≤ (s \ bad).card + K := by
  have hinter : (s ∩ bad).card ≤ K :=
    (Finset.card_le_card Finset.inter_subset_right).trans hbad
  have hsplit := Finset.card_sdiff_add_card_inter s bad
  omega

omit [DecidableEq β] in
theorem card_le_target_add_loss {s bad : Finset α} {t : Finset β} {K : ℕ}
    (f : α → β) (hbad : bad.card ≤ K)
    (hmap : ∀ i ∈ s \ bad, f i ∈ t)
    (hinj : Set.InjOn f (↑(s \ bad : Finset α) : Set α)) : s.card ≤ t.card + K := by
  have hgood := Finset.card_le_card_of_injOn f hmap hinj
  have htotal := card_le_good_card_add (s := s) hbad
  omega

omit [DecidableEq β] in
theorem card_add_card_le_of_disjoint_injections
    (s t : Finset α) (resources : Finset β) (row : α → β)
    (hdis : Disjoint s t)
    (hmap : ∀ i ∈ s ∪ t, row i ∈ resources)
    (hinj : Set.InjOn row (↑(s ∪ t : Finset α) : Set α)) : s.card + t.card ≤ resources.card := by
  rw [← Finset.card_union_of_disjoint hdis]
  exact Finset.card_le_card_of_injOn row hmap hinj

omit [DecidableEq β] in
theorem card_three_le_of_disjoint_injections
    (s t u : Finset α) (resources : Finset β) (row : α → β)
    (hst : Disjoint s t) (hsu : Disjoint s u) (htu : Disjoint t u)
    (hmap : ∀ i ∈ (s ∪ t) ∪ u, row i ∈ resources)
    (hinj : Set.InjOn row (↑((s ∪ t) ∪ u : Finset α) : Set α)) :
    s.card + t.card + u.card ≤ resources.card := by
  have hdis : Disjoint (s ∪ t) u := by
    apply Finset.disjoint_left.mpr
    intro i hi hu
    rcases Finset.mem_union.mp hi with hs | ht
    · exact Finset.disjoint_left.mp hsu hs hu
    · exact Finset.disjoint_left.mp htu ht hu
  have hcount := card_add_card_le_of_disjoint_injections
    (s ∪ t) u resources row hdis hmap hinj
  rwa [Finset.card_union_of_disjoint hst] at hcount

theorem card_le_add_of_subset_union (s t u : Finset α) (h : s ⊆ t ∪ u) :
    s.card ≤ t.card + u.card :=
  (Finset.card_le_card h).trans (Finset.card_union_le _ _)

end FiniteCounts

theorem displaced_baseline_bound {A B tree jobs used goodEarlier ξ K : ℕ}
    (hA : A ≤ tree + used) (hB : B = tree + jobs)
    (hrows : used + goodEarlier + ξ ≤ 2 * jobs)
    (hkeys : jobs ≤ goodEarlier + 3 * K) : A + ξ ≤ B + 3 * K := by
  omega

theorem coverage_lower_bound {A B C I d K : ℕ}
    (hpartition : C = A + I) (hdeadline : B + d ≤ C + 3 * K)
    (hbaseline : A ≤ B + 3 * K) : d ≤ I + 6 * K := by
  omega

theorem displaced_short_correction {A B C I d K ξ xplus shortM : ℕ}
    (hpartition : C = A + I) (hdeadline : B + d ≤ C + 3 * K)
    (hbaseline : A + ξ ≤ B + 3 * K) (hcoverage : I ≤ xplus + shortM) :
    d + ξ ≤ xplus + shortM + 6 * K := by
  omega

theorem short_le_displaced_add_long {d K ξ goodCurrent shortM shortG longG : ℕ}
    (hkeys : d ≤ goodCurrent + 3 * K)
    (hpartition : goodCurrent = ξ + shortG + longG)
    (hshort : shortM + shortG ≤ d) : shortM ≤ ξ + longG + 3 * K := by
  omega

theorem long_match_lower_bound {d K ξ xplus shortM longG : ℕ}
    (hcorrection : d + ξ ≤ xplus + shortM + 6 * K)
    (hshort : shortM ≤ ξ + longG + 3 * K) :
    d ≤ longG + xplus + 9 * K := by
  omega

end CoverageCounts
end BinPackingGap

namespace BinPackingGap.IntervalCoverage

variable {ι κ τ α : Type*} [LinearOrder α]

def prefixSet [Fintype ι] (f : ι → α) (a : α) : Finset ι := by
  classical
  exact Finset.univ.filter fun i => f i ≤ a

def prefixCount [Fintype ι] (f : ι → α) (a : α) : ℕ := (prefixSet f a).card

def coverageSet [Fintype ι] (h b : ι → α) (a : α) : Finset ι := by
  classical
  exact Finset.univ.filter fun i => h i ≤ a ∧ a < b i

def coverageCount [Fintype ι] (h b : ι → α) (a : α) : ℕ :=
  (coverageSet h b a).card

@[simp] theorem mem_prefixSet [Fintype ι] (f : ι → α) (a : α) (i : ι) :
    i ∈ prefixSet f a ↔ f i ≤ a := by
  classical
  simp [prefixSet]

@[simp] theorem mem_coverageSet [Fintype ι] (h b : ι → α) (a : α) (i : ι) :
    i ∈ coverageSet h b a ↔ h i ≤ a ∧ a < b i := by
  classical
  simp [coverageSet]

theorem completion_prefix_identity [Fintype ι] (h b : ι → α)
    (hle : ∀ i, h i ≤ b i) (a : α) :
    prefixCount h a = prefixCount b a + coverageCount h b a := by
  classical
  simpa only [prefixCount, coverageCount, prefixSet, coverageSet] using
    CoverageCounts.interval_prefix_card Finset.univ h b (fun i _ => hle i) a

structure ShiftData (Copy Test : Type*) (d : ℕ) (Coordinate : Type*)
    [LinearOrder Coordinate] where
  baseline : Copy → Coordinate
  left : Test → Coordinate
  right : Test → Coordinate
  designated : (Test × Fin d) ↪ Copy
  baseline_designated : ∀ q, baseline (designated q) = right q.1
  left_le_right : ∀ t, left t ≤ right t

namespace ShiftData

variable {d : ℕ} (D : ShiftData ι τ d α)

local instance : DecidableEq ι := Classical.decEq ι

def deadline (i : ι) : α := by
  classical
  exact if hi : ∃ q, D.designated q = i then D.left (Classical.choose hi).1
    else D.baseline i

@[simp] theorem deadline_designated (q : τ × Fin d) :
    D.deadline (D.designated q) = D.left q.1 := by
  classical
  have hi : ∃ q', D.designated q' = D.designated q := ⟨q, rfl⟩
  have heq : Classical.choose hi = q := D.designated.injective (Classical.choose_spec hi)
  simp only [deadline, dite_eq_left hi, heq]

theorem deadline_undesignated (i : ι) (hi : ∀ q, D.designated q ≠ i) :
    D.deadline i = D.baseline i := by
  classical
  have hn : ¬ ∃ q, D.designated q = i := by
    rintro ⟨q, hq⟩
    exact hi q hq
  simp only [deadline, dite_eq_right hn]

theorem designated_block_card (t : τ) :
    ((Finset.univ : Finset (Fin d)).image (fun j => D.designated (t, j))).card = d := by
  classical
  rw [Finset.card_image_of_injective]
  · exact Fintype.card_fin d
  · intro j k hjk
    exact congrArg Prod.snd (D.designated.injective hjk)

def activeTests [Fintype τ] (a : α) : Finset τ := by
  classical
  exact Finset.univ.filter fun t => D.left t ≤ a ∧ a < D.right t

@[simp] theorem mem_activeTests [Fintype τ] (a : α) (t : τ) :
    t ∈ D.activeTests a ↔ D.left t ≤ a ∧ a < D.right t := by
  classical
  simp [activeTests]

theorem deadline_prefix_of_agrees [Fintype ι] [Fintype τ]
    (z : ι → α)
    (hdesignated : ∀ q, z (D.designated q) = D.left q.1)
    (hother : ∀ i, (∀ q, D.designated q ≠ i) → z i = D.baseline i)
    (a : α) :
    prefixCount z a = prefixCount D.baseline a + d * (D.activeTests a).card := by
  classical
  have hle : ∀ i, z i ≤ D.baseline i := by
    intro i
    by_cases hi : ∃ q, D.designated q = i
    · obtain ⟨q, rfl⟩ := hi
      rw [hdesignated, D.baseline_designated]
      exact D.left_le_right q.1
    · rw [hother i (by simpa only [not_exists] using hi)]
  have hset : coverageSet z D.baseline a =
      ((D.activeTests a).product (Finset.univ : Finset (Fin d))).map D.designated := by
    ext i
    simp only [mem_coverageSet, Finset.mem_map, Finset.product_eq_sprod, Finset.mem_product,
      mem_activeTests, Finset.mem_univ, and_true]
    constructor
    · intro hi
      have hex : ∃ q, D.designated q = i := by
        by_contra hn
        have he := hother i (by simpa only [not_exists] using hn)
        exact (not_lt_of_ge (he ▸ hi.1)) hi.2
      obtain ⟨q, rfl⟩ := hex
      exact ⟨q, by simpa only [hdesignated, D.baseline_designated] using hi, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      simpa only [hdesignated, D.baseline_designated] using hq
  rw [completion_prefix_identity z D.baseline hle a]
  unfold coverageCount
  rw [hset, Finset.card_map, Finset.product_eq_sprod, Finset.card_product,
    Finset.card_univ, Fintype.card_fin]
  rw [Nat.mul_comm]

theorem deadline_prefix [Fintype ι] [Fintype τ] (a : α) :
    prefixCount D.deadline a = prefixCount D.baseline a + d * (D.activeTests a).card :=
  D.deadline_prefix_of_agrees D.deadline D.deadline_designated D.deadline_undesignated a

theorem activeTests_card [Fintype τ]
    (hdisjoint : ∀ s t, s ≠ t →
      Disjoint (Set.Ico (D.left s) (D.right s)) (Set.Ico (D.left t) (D.right t)))
    (a : α) :
    (D.activeTests a).card = if ∃ t, D.left t ≤ a ∧ a < D.right t then 1 else 0 := by
  classical
  have hle : (D.activeTests a).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro s hs t ht
    by_contra hst
    exact Set.disjoint_left.mp (hdisjoint s t hst)
      (D.mem_activeTests a s |>.mp hs) (D.mem_activeTests a t |>.mp ht)
  split_ifs with hex
  · obtain ⟨t, ht⟩ := hex
    have hpos := Finset.card_pos.mpr ⟨t, (D.mem_activeTests a t).mpr ht⟩
    omega
  · apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro t ht
    exact hex ⟨t, (D.mem_activeTests a t).mp ht⟩

theorem deadline_prefix_disjoint_of_agrees [Fintype ι] [Fintype τ]
    (z : ι → α)
    (hdesignated : ∀ q, z (D.designated q) = D.left q.1)
    (hother : ∀ i, (∀ q, D.designated q ≠ i) → z i = D.baseline i)
    (hdisjoint : ∀ s t, s ≠ t →
      Disjoint (Set.Ico (D.left s) (D.right s)) (Set.Ico (D.left t) (D.right t)))
    (a : α) :
    prefixCount z a = prefixCount D.baseline a +
      d * (if ∃ t, D.left t ≤ a ∧ a < D.right t then 1 else 0) := by
  rw [D.deadline_prefix_of_agrees z hdesignated hother, D.activeTests_card hdisjoint]

theorem deadline_prefix_disjoint [Fintype ι] [Fintype τ]
    (hdisjoint : ∀ s t, s ≠ t →
      Disjoint (Set.Ico (D.left s) (D.right s)) (Set.Ico (D.left t) (D.right t)))
    (a : α) :
    prefixCount D.deadline a = prefixCount D.baseline a +
      d * (if ∃ t, D.left t ≤ a ∧ a < D.right t then 1 else 0) :=
  D.deadline_prefix_disjoint_of_agrees D.deadline D.deadline_designated
    D.deadline_undesignated hdisjoint a

end ShiftData

theorem exists_equiv_of_prefix_dominance [Fintype ι] [Fintype κ]
    (h : ι → α) (z : κ → α) (hcard : Fintype.card ι = Fintype.card κ)
    (hprefix : ∀ a, prefixCount z a ≤ prefixCount h a) :
    ∃ e : ι ≃ κ, ∀ i, h i ≤ z (e i) := by
  classical
  let neighbors : ι → Finset κ := fun i => Finset.univ.filter fun j => h i ≤ z j
  have hall : ∀ s : Finset ι, s.card ≤ (s.biUnion neighbors).card := by
    intro s
    let N := s.biUnion neighbors
    let bad := (Finset.univ : Finset κ) \ N
    have hpartition : bad.card + N.card = Fintype.card κ := by
      simpa only [bad, Finset.card_univ] using
        Finset.card_sdiff_add_card_eq_card (Finset.subset_univ N)
    by_cases hbad : bad.Nonempty
    · obtain ⟨j, hj, hmax⟩ := bad.exists_max_image z hbad
      have hN : j ∉ N := (Finset.mem_sdiff.mp hj).2
      have hd : Disjoint s (prefixSet h (z j)) := by
        apply Finset.disjoint_left.mpr
        intro i hi hip
        apply hN
        exact Finset.mem_biUnion.mpr ⟨i, hi, by
          simpa only [neighbors, Finset.mem_filter, Finset.mem_univ, true_and,
            mem_prefixSet] using hip⟩
      have hsum : s.card + prefixCount h (z j) ≤ Fintype.card ι := by
        rw [prefixCount, ← Finset.card_union_of_disjoint hd]
        exact Finset.card_le_univ _
      have hb : bad.card ≤ prefixCount z (z j) := by
        apply Finset.card_le_card
        intro k hk
        exact (mem_prefixSet z (z j) k).mpr (hmax k hk)
      have hp := hprefix (z j)
      change s.card ≤ N.card
      omega
    · have hb : bad.card = 0 := Finset.card_eq_zero.mpr
        (Finset.not_nonempty_iff_eq_empty.mp hbad)
      have hs := Finset.card_le_univ s
      change s.card ≤ N.card
      omega
  obtain ⟨f, hf, hmatch⟩ :=
    (FiniteHall.all_card_le_biUnion_card_iff_existsInjective neighbors).mp hall
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, hcard⟩
  refine ⟨Equiv.ofBijective f hbij, ?_⟩
  intro i
  change h i ≤ z (f i)
  have hi := hmatch i
  simpa only [neighbors, Finset.mem_filter, Finset.mem_univ, true_and] using hi

end BinPackingGap.IntervalCoverage

namespace BinPackingGap
namespace Coverage

variable {I : Instance} {b n : ℕ}

def goodTuplesAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n) : Finset (p.TableBin cls) := by
  classical
  exact Finset.univ.filter fun t => p.IsGoodTableBin cls label t ∧
    label (p.itemAtRole cls t .anchor) = some v

def mainTuplesAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n) : Finset (p.TableBin cls) := by
  classical
  exact (goodTuplesAt p cls label v).filter fun t => p.tablePattern cls t ≠ .edgeJob

def edgeTuplesAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n) : Finset (p.TableBin cls) := by
  classical
  exact (goodTuplesAt p cls label v).filter fun t => p.tablePattern cls t = .edgeJob

@[simp] theorem mem_goodTuplesAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n) (t : p.TableBin cls) :
    t ∈ goodTuplesAt p cls label v ↔ p.IsGoodTableBin cls label t ∧
      label (p.itemAtRole cls t .anchor) = some v := by
  classical
  simp [goodTuplesAt]

@[simp] theorem mem_mainTuplesAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n) (t : p.TableBin cls) :
    t ∈ mainTuplesAt p cls label v ↔ p.IsGoodTableBin cls label t ∧
      label (p.itemAtRole cls t .anchor) = some v ∧
        p.tablePattern cls t ≠ .edgeJob := by
  classical
  simp [mainTuplesAt, and_assoc]

@[simp] theorem mem_edgeTuplesAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n) (t : p.TableBin cls) :
    t ∈ edgeTuplesAt p cls label v ↔ p.IsGoodTableBin cls label t ∧
      label (p.itemAtRole cls t .anchor) = some v ∧
        p.tablePattern cls t = .edgeJob := by
  classical
  simp [edgeTuplesAt, and_assoc]

theorem mainTuplesAt_subset_good (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n) :
    mainTuplesAt p cls label v ⊆ goodTuplesAt p cls label v := by
  classical
  exact Finset.filter_subset _ _

theorem edgeTuplesAt_subset_good (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n) :
    edgeTuplesAt p cls label v ⊆ goodTuplesAt p cls label v := by
  classical
  exact Finset.filter_subset _ _

theorem goodTuplesAt_eq_union (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n) :
    goodTuplesAt p cls label v =
      mainTuplesAt p cls label v ∪ edgeTuplesAt p cls label v := by
  classical
  ext t
  by_cases h : p.tablePattern cls t = .edgeJob <;>
    simp [mainTuplesAt, edgeTuplesAt, h]

theorem mainTuplesAt_disjoint_edge (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v w : Fin n) :
    Disjoint (mainTuplesAt p cls label v) (edgeTuplesAt p cls label w) := by
  apply Finset.disjoint_left.mpr
  intro t ht hu
  exact ((mem_mainTuplesAt p cls label v t).mp ht).2.2
    (((mem_edgeTuplesAt p cls label w t).mp hu).2.2)

theorem goodTuplesAt_disjoint_label (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) {v w : Fin n} (hvw : v ≠ w) :
    Disjoint (goodTuplesAt p cls label v) (goodTuplesAt p cls label w) := by
  apply Finset.disjoint_left.mpr
  intro t ht hu
  have hv := ((mem_goodTuplesAt p cls label v t).mp ht).2
  have hw := ((mem_goodTuplesAt p cls label w t).mp hu).2
  exact hvw (Option.some.inj (hv.symm.trans hw))

theorem mainTuplesAt_disjoint_label (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) {v w : Fin n} (hvw : v ≠ w) :
    Disjoint (mainTuplesAt p cls label v) (mainTuplesAt p cls label w) :=
  (goodTuplesAt_disjoint_label p cls label hvw).mono
    (mainTuplesAt_subset_good p cls label v) (mainTuplesAt_subset_good p cls label w)

theorem edgeTuplesAt_disjoint_label (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) {v w : Fin n} (hvw : v ≠ w) :
    Disjoint (edgeTuplesAt p cls label v) (edgeTuplesAt p cls label w) :=
  (goodTuplesAt_disjoint_label p cls label hvw).mono
    (edgeTuplesAt_subset_good p cls label v) (edgeTuplesAt_subset_good p cls label w)

def roleItems (p : Packing I b) (cls : I.Item → Subclass)
    (s : Finset (p.TableBin cls)) (role : Role) : Finset I.Item :=
  s.image fun t => p.itemAtRole cls t role

@[simp] theorem roleItems_card (p : Packing I b) (cls : I.Item → Subclass)
    (s : Finset (p.TableBin cls)) (role : Role) : (roleItems p cls s role).card = s.card :=
  Finset.card_image_of_injective s (p.itemAtRole_injective cls role)

def anchorItemsAt (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n) : Finset I.Item := by
  classical
  exact Finset.univ.filter fun i => (cls i).role = .anchor ∧ label i = some v

@[simp] theorem mem_anchorItemsAt (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n) (i : I.Item) :
    i ∈ anchorItemsAt (I := I) cls label v ↔
      (cls i).role = .anchor ∧ label i = some v := by
  classical
  simp [anchorItemsAt]

def badAnchorsAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n) : Finset I.Item :=
  anchorItemsAt (I := I) cls label v \
    roleItems p cls (goodTuplesAt p cls label v) .anchor

@[simp] theorem mem_badAnchorsAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n) (i : I.Item) :
    i ∈ badAnchorsAt p cls label v ↔
      i ∈ anchorItemsAt (I := I) cls label v ∧
        i ∉ roleItems p cls (goodTuplesAt p cls label v) .anchor := by
  simp only [badAnchorsAt, Finset.mem_sdiff]

theorem good_anchorItems_subset (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n) :
    roleItems p cls (goodTuplesAt p cls label v) .anchor ⊆
      anchorItemsAt (I := I) cls label v := by
  intro i hi
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hi
  exact (mem_anchorItemsAt cls label v _).mpr
    ⟨p.itemAtRole_role cls t .anchor, ((mem_goodTuplesAt p cls label v t).mp ht).2⟩

theorem card_le_role_resources (p : Packing I b) (cls : I.Item → Subclass)
    (s : Finset (p.TableBin cls)) (role : Role) (resources : Finset I.Item)
    (hmap : ∀ t ∈ s, p.itemAtRole cls t role ∈ resources) : s.card ≤ resources.card :=
  Finset.card_le_card_of_injOn (fun t => p.itemAtRole cls t role) hmap
    (p.itemAtRole_injective cls role).injOn

theorem card_three_le_row_resources (p : Packing I b) (cls : I.Item → Subclass)
    (s t u : Finset (p.TableBin cls)) (resources : Finset I.Item)
    (hst : Disjoint s t) (hsu : Disjoint s u) (htu : Disjoint t u)
    (hmap : ∀ x ∈ (s ∪ t) ∪ u, p.itemAtRole cls x .x ∈ resources) :
    s.card + t.card + u.card ≤ resources.card :=
  CoverageCounts.card_three_le_of_disjoint_injections s t u resources
    (fun x => p.itemAtRole cls x .x) hst hsu htu hmap
    (p.itemAtRole_injective cls .x).injOn

def tupleCompletion (p : Packing I b) (cls : I.Item → Subclass)
    (baseline : I.Item → ℚ) (short : I.Item → Bool)
    (globalLen localLen : I.Item → ℚ) (delta : ℚ) (t : p.TableBin cls) : ℚ :=
  completion (baseline (p.itemAtRole cls t .x)) (short (p.itemAtRole cls t .x))
    (globalLen (p.itemAtRole cls t .«global»))
    (localLen (p.itemAtRole cls t .«local»)) delta

theorem tupleCompletion_le_baseline (p : Packing I b) (cls : I.Item → Subclass)
    (baseline : I.Item → ℚ) (short : I.Item → Bool)
    (globalLen localLen : I.Item → ℚ) (delta : ℚ)
    (hglobal : ∀ i, 0 ≤ globalLen i) (hlocal : ∀ i, 0 ≤ localLen i)
    (hdelta : 0 ≤ delta) (t : p.TableBin cls) :
    tupleCompletion p cls baseline short globalLen localLen delta t ≤
      baseline (p.itemAtRole cls t .x) :=
  completion_le_baseline _ _ _ _ _ (hglobal _) (hlocal _) hdelta

def baselinePrefixAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (baseline : I.Item → ℚ) (a : ℚ) : Finset (p.TableBin cls) :=
  (mainTuplesAt p cls label v).filter fun t => baseline (p.itemAtRole cls t .x) ≤ a

def completionPrefixAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (finish : p.TableBin cls → ℚ) (a : ℚ) : Finset (p.TableBin cls) :=
  (mainTuplesAt p cls label v).filter fun t => finish t ≤ a

def coveringTuplesAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (baseline : I.Item → ℚ) (finish : p.TableBin cls → ℚ) (a : ℚ) :
    Finset (p.TableBin cls) :=
  (mainTuplesAt p cls label v).filter fun t =>
    finish t ≤ a ∧ a < baseline (p.itemAtRole cls t .x)

theorem completion_prefix_decomposition (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (baseline : I.Item → ℚ) (finish : p.TableBin cls → ℚ)
    (hle : ∀ t ∈ mainTuplesAt p cls label v, finish t ≤ baseline (p.itemAtRole cls t .x))
    (a : ℚ) :
    (completionPrefixAt p cls label v finish a).card =
      (baselinePrefixAt p cls label v baseline a).card +
        (coveringTuplesAt p cls label v baseline finish a).card :=
  CoverageCounts.interval_prefix_card (mainTuplesAt p cls label v) finish
    (fun t => baseline (p.itemAtRole cls t .x)) hle a

theorem literal_completion_prefix_decomposition
    (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (baseline : I.Item → ℚ) (short : I.Item → Bool)
    (globalLen localLen : I.Item → ℚ) (delta a : ℚ)
    (hglobal : ∀ i, 0 ≤ globalLen i) (hlocal : ∀ i, 0 ≤ localLen i)
    (hdelta : 0 ≤ delta) :
    (completionPrefixAt p cls label v
      (tupleCompletion p cls baseline short globalLen localLen delta) a).card =
      (baselinePrefixAt p cls label v baseline a).card +
        (coveringTuplesAt p cls label v baseline
          (tupleCompletion p cls baseline short globalLen localLen delta) a).card :=
  completion_prefix_decomposition p cls label v baseline _
    (fun t _ => tupleCompletion_le_baseline p cls baseline short globalLen localLen delta
      hglobal hlocal hdelta t) a

def deadlinePrefixAt (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (deadline : I.Item → ℚ) (a : ℚ) : Finset I.Item := by
  classical
  exact Finset.univ.filter fun i => cls i = .z ∧ label i = some v ∧ deadline i ≤ a

@[simp] theorem mem_deadlinePrefixAt (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (deadline : I.Item → ℚ) (a : ℚ) (i : I.Item) :
    i ∈ deadlinePrefixAt (I := I) cls label v deadline a ↔
      cls i = .z ∧ label i = some v ∧ deadline i ≤ a := by
  classical
  simp [deadlinePrefixAt]

theorem good_deadline_subset_completed_anchor_image
    (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (deadline : I.Item → ℚ) (finish : p.TableBin cls → ℚ) (a : ℚ)
    (hfeasible : ∀ t ∈ mainTuplesAt p cls label v,
      finish t ≤ deadline (p.itemAtRole cls t .anchor)) :
    deadlinePrefixAt (I := I) cls label v deadline a \ badAnchorsAt p cls label v ⊆
      roleItems p cls (completionPrefixAt p cls label v finish a) .anchor := by
  classical
  intro i hi
  obtain ⟨hi, hnotbad⟩ := Finset.mem_sdiff.mp hi
  obtain ⟨hcls, hlabel, hdeadline⟩ :=
    (mem_deadlinePrefixAt cls label v deadline a i).mp hi
  have hanchor : i ∈ anchorItemsAt (I := I) cls label v := by
    apply (mem_anchorItemsAt cls label v i).mpr
    exact ⟨by rw [hcls]; rfl, hlabel⟩
  have hused : i ∈ roleItems p cls (goodTuplesAt p cls label v) .anchor := by
    by_contra h
    exact hnotbad ((mem_badAnchorsAt p cls label v i).mpr ⟨hanchor, h⟩)
  obtain ⟨t, ht, hti⟩ := Finset.mem_image.mp hused
  have hM : t ∈ mainTuplesAt p cls label v := by
    have htgood := (mem_goodTuplesAt p cls label v t).mp ht
    refine (mem_mainTuplesAt p cls label v t).mpr ⟨htgood.1, htgood.2, ?_⟩
    intro hedge
    have hsub := p.itemAtRole_subclass cls t .anchor
    rw [hedge] at hsub
    have hnot : (Subclass.z : Subclass) = .y := by
      calc
        Subclass.z = cls i := hcls.symm
        _ = cls (p.itemAtRole cls t .anchor) := congrArg cls hti.symm
        _ = Subclass.y := hsub
    cases hnot
  apply Finset.mem_image.mpr
  refine ⟨t, ?_, hti⟩
  apply Finset.mem_filter.mpr
  refine ⟨hM, (hfeasible t hM).trans ?_⟩
  simpa only [hti] using hdeadline

theorem deadline_prefix_le_completion_add_loss
    (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (deadline : I.Item → ℚ) (finish : p.TableBin cls → ℚ) (a : ℚ) (K : ℕ)
    (hbad : (badAnchorsAt p cls label v).card ≤ 3 * K)
    (hfeasible : ∀ t ∈ mainTuplesAt p cls label v,
      finish t ≤ deadline (p.itemAtRole cls t .anchor)) :
    (deadlinePrefixAt (I := I) cls label v deadline a).card ≤
      (completionPrefixAt p cls label v finish a).card + 3 * K := by
  have hcount := Finset.card_le_card
    (good_deadline_subset_completed_anchor_image p cls label v deadline finish a hfeasible)
  rw [roleItems_card] at hcount
  have hloss := CoverageCounts.card_le_good_card_add
    (s := deadlinePrefixAt (I := I) cls label v deadline a) hbad
  omega

def jobRowPrefixAt (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (baseline : I.Item → ℚ) (a : ℚ) : Finset I.Item := by
  classical
  exact Finset.univ.filter fun i => cls i = .s ∧ label i = some v ∧ baseline i ≤ a

def treeRowPrefixAt (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (baseline : I.Item → ℚ) (a : ℚ) : Finset I.Item := by
  classical
  exact Finset.univ.filter fun i =>
    (cls i = .tp ∨ cls i = .tm) ∧ label i = some v ∧ baseline i ≤ a

def keyPrefixAt (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (keyBaseline : I.Item → ℚ) (a : ℚ) : Finset I.Item := by
  classical
  exact Finset.univ.filter fun i => cls i = .y ∧ label i = some v ∧ keyBaseline i ≤ a

def edgePrefixAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (keyBaseline : I.Item → ℚ) (a : ℚ) : Finset (p.TableBin cls) :=
  (edgeTuplesAt p cls label v).filter fun t => keyBaseline (p.itemAtRole cls t .anchor) ≤ a

def mainJobPrefixAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (baseline : I.Item → ℚ) (a : ℚ) : Finset (p.TableBin cls) := by
  classical
  exact (baselinePrefixAt p cls label v baseline a).filter fun t =>
    cls (p.itemAtRole cls t .x) = .s

def mainTreePrefixAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (baseline : I.Item → ℚ) (a : ℚ) : Finset (p.TableBin cls) := by
  classical
  exact (baselinePrefixAt p cls label v baseline a).filter fun t =>
    cls (p.itemAtRole cls t .x) ≠ .s

theorem baseline_prefix_row_partition
    (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n) (baseline : I.Item → ℚ) (a : ℚ) :
    (baselinePrefixAt p cls label v baseline a).card =
      (mainTreePrefixAt p cls label v baseline a).card +
        (mainJobPrefixAt p cls label v baseline a).card := by
  classical
  have h := Finset.card_filter_add_card_filter_not
    (s := baselinePrefixAt p cls label v baseline a)
    (fun t => cls (p.itemAtRole cls t .x) = .s)
  simpa only [mainTreePrefixAt, mainJobPrefixAt, Nat.add_comm] using h.symm

theorem main_tree_prefix_le_inventory
    (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n) (baseline : I.Item → ℚ) (a : ℚ) :
    (mainTreePrefixAt p cls label v baseline a).card ≤
      (treeRowPrefixAt (I := I) cls label v baseline a).card := by
  classical
  apply card_le_role_resources p cls _ .x _
  intro t ht
  obtain ⟨ht, hnots⟩ := Finset.mem_filter.mp ht
  obtain ⟨ht, hbase⟩ := Finset.mem_filter.mp ht
  obtain ⟨hgood, hlabel, _⟩ := (mem_mainTuplesAt p cls label v t).mp ht
  have hrole := (role_eq_x_iff (cls (p.itemAtRole cls t .x))).mp
    (p.itemAtRole_role cls t .x)
  have htree : cls (p.itemAtRole cls t .x) = .tp ∨
      cls (p.itemAtRole cls t .x) = .tm := by
    rcases hrole with hp | hm | hs
    · exact Or.inl hp
    · exact Or.inr hm
    · exact False.elim (hnots hs)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, htree, hgood.1.trans hlabel, hbase⟩

theorem good_key_subset_edge_anchor_image
    (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (keyBaseline : I.Item → ℚ) (a : ℚ) :
    keyPrefixAt (I := I) cls label v keyBaseline a \ badAnchorsAt p cls label v ⊆
      roleItems p cls (edgePrefixAt p cls label v keyBaseline a) .anchor := by
  classical
  intro i hi
  obtain ⟨hi, hnotbad⟩ := Finset.mem_sdiff.mp hi
  obtain ⟨_, hcls, hlabel, hbase⟩ := Finset.mem_filter.mp hi
  have hanchor : i ∈ anchorItemsAt (I := I) cls label v :=
    (mem_anchorItemsAt cls label v i).mpr ⟨by rw [hcls]; rfl, hlabel⟩
  have hused : i ∈ roleItems p cls (goodTuplesAt p cls label v) .anchor := by
    by_contra h
    exact hnotbad ((mem_badAnchorsAt p cls label v i).mpr ⟨hanchor, h⟩)
  obtain ⟨t, ht, hti⟩ := Finset.mem_image.mp hused
  have hpattern : p.tablePattern cls t = .edgeJob := by
    have hsub : patternSubclass (p.tablePattern cls t) .anchor = .y :=
      (p.itemAtRole_subclass cls t .anchor).symm.trans ((congrArg cls hti).trans hcls)
    cases hp : p.tablePattern cls t <;> simp_all [patternSubclass]
  have htgood := (mem_goodTuplesAt p cls label v t).mp ht
  have hG : t ∈ edgeTuplesAt p cls label v :=
    (mem_edgeTuplesAt p cls label v t).mpr ⟨htgood.1, htgood.2, hpattern⟩
  apply Finset.mem_image.mpr
  refine ⟨t, Finset.mem_filter.mpr ⟨hG, ?_⟩, hti⟩
  simpa only [hti] using hbase

theorem key_prefix_le_edge_prefix_add_loss
    (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (keyBaseline : I.Item → ℚ) (a : ℚ) (K : ℕ)
    (hbad : (badAnchorsAt p cls label v).card ≤ 3 * K) :
    (keyPrefixAt (I := I) cls label v keyBaseline a).card ≤
      (edgePrefixAt p cls label v keyBaseline a).card + 3 * K := by
  have hcount := Finset.card_le_card
    (good_key_subset_edge_anchor_image p cls label v keyBaseline a)
  rw [roleItems_card] at hcount
  have hloss := CoverageCounts.card_le_good_card_add
    (s := keyPrefixAt (I := I) cls label v keyBaseline a) hbad
  omega

theorem edge_row_mem_job_prefix
    (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n) (baseline : I.Item → ℚ) (a : ℚ)
    {t : p.TableBin cls} (ht : t ∈ edgeTuplesAt p cls label v)
    (hbase : baseline (p.itemAtRole cls t .x) ≤ a) :
    p.itemAtRole cls t .x ∈ jobRowPrefixAt (I := I) cls label v baseline a := by
  obtain ⟨hgood, hlabel, hpattern⟩ := (mem_edgeTuplesAt p cls label v t).mp ht
  have hcls : cls (p.itemAtRole cls t .x) = .s := by
    rw [p.itemAtRole_subclass cls t .x, hpattern]
    rfl
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcls, hgood.1.trans hlabel, hbase⟩

theorem displaced_baseline_prefix_le
    (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (baseline keyBaseline : I.Item → ℚ) (a : ℚ)
    (extra : Finset (p.TableBin cls)) (B jobs K : ℕ)
    (hbad : (badAnchorsAt p cls label v).card ≤ 3 * K)
    (horder : ∀ t ∈ edgeTuplesAt p cls label v,
      baseline (p.itemAtRole cls t .x) ≤ keyBaseline (p.itemAtRole cls t .anchor))
    (hextra : extra ⊆ edgeTuplesAt p cls label v)
    (hextraRows : ∀ t ∈ extra, baseline (p.itemAtRole cls t .x) ≤ a)
    (hextraDis : Disjoint (edgePrefixAt p cls label v keyBaseline a) extra)
    (hjobStock : (jobRowPrefixAt (I := I) cls label v baseline a).card = 2 * jobs)
    (hkeyStock : (keyPrefixAt (I := I) cls label v keyBaseline a).card = jobs)
    (hbaselineStock : B = (treeRowPrefixAt (I := I) cls label v baseline a).card + jobs) :
    (baselinePrefixAt p cls label v baseline a).card + extra.card ≤ B + 3 * K := by
  classical
  let M := mainJobPrefixAt p cls label v baseline a
  let E := edgePrefixAt p cls label v keyBaseline a
  have hMsub : M ⊆ mainTuplesAt p cls label v := by
    intro t ht
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).1
  have hEsub : E ⊆ edgeTuplesAt p cls label v := Finset.filter_subset _ _
  have hME : Disjoint M E :=
    (mainTuplesAt_disjoint_edge p cls label v v).mono hMsub hEsub
  have hMX : Disjoint M extra :=
    (mainTuplesAt_disjoint_edge p cls label v v).mono hMsub hextra
  have hmap : ∀ t ∈ (M ∪ E) ∪ extra,
      p.itemAtRole cls t .x ∈ jobRowPrefixAt (I := I) cls label v baseline a := by
    intro t ht
    rcases Finset.mem_union.mp ht with ht | ht
    · rcases Finset.mem_union.mp ht with ht | ht
      · obtain ⟨hprefix, hcls⟩ := Finset.mem_filter.mp ht
        obtain ⟨htM, hbase⟩ := Finset.mem_filter.mp hprefix
        obtain ⟨hgood, hlabel, _⟩ := (mem_mainTuplesAt p cls label v t).mp htM
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hcls, hgood.1.trans hlabel, hbase⟩
      · obtain ⟨htG, hbase⟩ := Finset.mem_filter.mp ht
        exact edge_row_mem_job_prefix p cls label v baseline a htG
          ((horder t htG).trans hbase)
    · exact edge_row_mem_job_prefix p cls label v baseline a (hextra ht)
        (hextraRows t ht)
  have hrows := card_three_le_row_resources p cls M E extra
    (jobRowPrefixAt (I := I) cls label v baseline a) hME hMX hextraDis hmap
  rw [hjobStock] at hrows
  have hkeys := key_prefix_le_edge_prefix_add_loss p cls label v keyBaseline a K hbad
  rw [hkeyStock] at hkeys
  have hsplit := baseline_prefix_row_partition p cls label v baseline a
  have htrees := main_tree_prefix_le_inventory p cls label v baseline a
  have hmain : (baselinePrefixAt p cls label v baseline a).card ≤
      (treeRowPrefixAt (I := I) cls label v baseline a).card + M.card := by
    dsimp only [M]
    omega
  exact CoverageCounts.displaced_baseline_bound hmain hbaselineStock hrows hkeys

def currentKeyItemsAt (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (keyBaseline : I.Item → ℚ) (current : ℚ) : Finset I.Item := by
  classical
  exact Finset.univ.filter fun i =>
    cls i = .y ∧ label i = some v ∧ keyBaseline i = current

def currentEdgeTuplesAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (keyBaseline : I.Item → ℚ) (current : ℚ) : Finset (p.TableBin cls) :=
  (edgeTuplesAt p cls label v).filter fun t =>
    keyBaseline (p.itemAtRole cls t .anchor) = current

def displacedTuplesAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (baseline keyBaseline : I.Item → ℚ) (current : ℚ) : Finset (p.TableBin cls) :=
  (currentEdgeTuplesAt p cls label v keyBaseline current).filter fun t =>
    baseline (p.itemAtRole cls t .x) < current

def currentShortMainAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (baseline : I.Item → ℚ) (short : I.Item → Bool) (current : ℚ) :
    Finset (p.TableBin cls) :=
  (mainTuplesAt p cls label v).filter fun t =>
    baseline (p.itemAtRole cls t .x) = current ∧ short (p.itemAtRole cls t .x) = true

def currentShortEdgeAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (baseline keyBaseline : I.Item → ℚ) (short : I.Item → Bool) (current : ℚ) :
    Finset (p.TableBin cls) :=
  (currentEdgeTuplesAt p cls label v keyBaseline current).filter fun t =>
    baseline (p.itemAtRole cls t .x) = current ∧ short (p.itemAtRole cls t .x) = true

def currentLongEdgeAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (baseline keyBaseline : I.Item → ℚ) (short : I.Item → Bool) (current : ℚ) :
    Finset (p.TableBin cls) :=
  (currentEdgeTuplesAt p cls label v keyBaseline current).filter fun t =>
    baseline (p.itemAtRole cls t .x) = current ∧ short (p.itemAtRole cls t .x) ≠ true

def currentShortItemsAt (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (baseline : I.Item → ℚ) (short : I.Item → Bool) (current : ℚ) : Finset I.Item := by
  classical
  exact Finset.univ.filter fun i => cls i = .s ∧ label i = some v ∧
    baseline i = current ∧ short i = true

theorem key_subset_le_matching_add_loss
    (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (keys : Finset I.Item) (matchedTuples : Finset (p.TableBin cls)) (K : ℕ)
    (hkeys : ∀ i ∈ keys, cls i = .y ∧ label i = some v)
    (hselect : ∀ t ∈ edgeTuplesAt p cls label v,
      p.itemAtRole cls t .anchor ∈ keys → t ∈ matchedTuples)
    (hbad : (badAnchorsAt p cls label v).card ≤ 3 * K) :
    keys.card ≤ matchedTuples.card + 3 * K := by
  classical
  have hsubset : keys \ badAnchorsAt p cls label v ⊆ roleItems p cls matchedTuples .anchor := by
    intro i hi
    obtain ⟨hi, hnotbad⟩ := Finset.mem_sdiff.mp hi
    obtain ⟨hcls, hlabel⟩ := hkeys i hi
    have hanchor : i ∈ anchorItemsAt (I := I) cls label v :=
      (mem_anchorItemsAt cls label v i).mpr ⟨by rw [hcls]; rfl, hlabel⟩
    have hused : i ∈ roleItems p cls (goodTuplesAt p cls label v) .anchor := by
      by_contra h
      exact hnotbad ((mem_badAnchorsAt p cls label v i).mpr ⟨hanchor, h⟩)
    obtain ⟨t, ht, hti⟩ := Finset.mem_image.mp hused
    have hpattern : p.tablePattern cls t = .edgeJob := by
      have hsub : patternSubclass (p.tablePattern cls t) .anchor = .y :=
        (p.itemAtRole_subclass cls t .anchor).symm.trans ((congrArg cls hti).trans hcls)
      cases hp : p.tablePattern cls t <;> simp_all [patternSubclass]
    have htgood := (mem_goodTuplesAt p cls label v t).mp ht
    have hG : t ∈ edgeTuplesAt p cls label v :=
      (mem_edgeTuplesAt p cls label v t).mpr ⟨htgood.1, htgood.2, hpattern⟩
    refine Finset.mem_image.mpr ⟨t, hselect t hG ?_, hti⟩
    simpa only [hti] using hi
  have hcount := Finset.card_le_card hsubset
  rw [roleItems_card] at hcount
  have hloss := CoverageCounts.card_le_good_card_add (s := keys) hbad
  omega

theorem current_key_count_le_matches_add_loss
    (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (keyBaseline : I.Item → ℚ) (current : ℚ) (K : ℕ)
    (hbad : (badAnchorsAt p cls label v).card ≤ 3 * K) :
    (currentKeyItemsAt (I := I) cls label v keyBaseline current).card ≤
      (currentEdgeTuplesAt p cls label v keyBaseline current).card + 3 * K := by
  apply key_subset_le_matching_add_loss p cls label v _ _ K _ _ hbad
  · intro i hi
    obtain ⟨_, hcls, hlabel, _⟩ := Finset.mem_filter.mp hi
    exact ⟨hcls, hlabel⟩
  · intro t ht hi
    exact Finset.mem_filter.mpr ⟨ht, (Finset.mem_filter.mp hi).2.2.2⟩

theorem current_match_partition
    (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (baseline keyBaseline : I.Item → ℚ) (short : I.Item → Bool) (current : ℚ)
    (horder : ∀ t ∈ edgeTuplesAt p cls label v,
      baseline (p.itemAtRole cls t .x) ≤ keyBaseline (p.itemAtRole cls t .anchor)) :
    (currentEdgeTuplesAt p cls label v keyBaseline current).card =
      (displacedTuplesAt p cls label v baseline keyBaseline current).card +
      (currentShortEdgeAt p cls label v baseline keyBaseline short current).card +
      (currentLongEdgeAt p cls label v baseline keyBaseline short current).card := by
  apply CoverageCounts.ordered_short_long_partition
    (currentEdgeTuplesAt p cls label v keyBaseline current)
    (fun t => baseline (p.itemAtRole cls t .x)) current
    (fun t => short (p.itemAtRole cls t .x) = true)
  intro t ht
  obtain ⟨ht, hcurrent⟩ := Finset.mem_filter.mp ht
  exact (horder t ht).trans_eq hcurrent

theorem current_short_consumption_le_stock
    (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (baseline keyBaseline : I.Item → ℚ) (short : I.Item → Bool) (current : ℚ)
    (hshortJob : ∀ i, short i = true → cls i = .s) :
    (currentShortMainAt p cls label v baseline short current).card +
      (currentShortEdgeAt p cls label v baseline keyBaseline short current).card ≤
        (currentShortItemsAt (I := I) cls label v baseline short current).card := by
  classical
  let M := currentShortMainAt p cls label v baseline short current
  let G := currentShortEdgeAt p cls label v baseline keyBaseline short current
  have hMsub : M ⊆ mainTuplesAt p cls label v := Finset.filter_subset _ _
  have hGsub : G ⊆ edgeTuplesAt p cls label v := by
    intro t ht
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).1
  apply CoverageCounts.card_add_card_le_of_disjoint_injections M G
    (currentShortItemsAt (I := I) cls label v baseline short current)
    (fun t => p.itemAtRole cls t .x)
    ((mainTuplesAt_disjoint_edge p cls label v v).mono hMsub hGsub)
    _ (p.itemAtRole_injective cls .x).injOn
  intro t ht
  rcases Finset.mem_union.mp ht with ht | ht
  · obtain ⟨ht, hbase, hshort⟩ := Finset.mem_filter.mp ht
    obtain ⟨hgood, hlabel, _⟩ := (mem_mainTuplesAt p cls label v t).mp ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hshortJob _ hshort,
      hgood.1.trans hlabel, hbase, hshort⟩
  · obtain ⟨ht, hbase, hshort⟩ := Finset.mem_filter.mp ht
    obtain ⟨ht, _⟩ := Finset.mem_filter.mp ht
    obtain ⟨hgood, hlabel, _⟩ := (mem_edgeTuplesAt p cls label v t).mp ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hshortJob _ hshort,
      hgood.1.trans hlabel, hbase, hshort⟩

theorem current_long_matches_from_correction
    (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (baseline keyBaseline : I.Item → ℚ) (short : I.Item → Bool) (current : ℚ)
    (d K xplus : ℕ)
    (hbad : (badAnchorsAt p cls label v).card ≤ 3 * K)
    (horder : ∀ t ∈ edgeTuplesAt p cls label v,
      baseline (p.itemAtRole cls t .x) ≤ keyBaseline (p.itemAtRole cls t .anchor))
    (hshortJob : ∀ i, short i = true → cls i = .s)
    (hkeys : (currentKeyItemsAt (I := I) cls label v keyBaseline current).card = d)
    (hshortStock : (currentShortItemsAt (I := I) cls label v baseline short current).card = d)
    (hcorrection : d + (displacedTuplesAt p cls label v baseline keyBaseline current).card ≤
      xplus + (currentShortMainAt p cls label v baseline short current).card + 6 * K) :
    d ≤ (currentLongEdgeAt p cls label v baseline keyBaseline short current).card +
      xplus + 9 * K := by
  have hgood := current_key_count_le_matches_add_loss p cls label v keyBaseline current K hbad
  rw [hkeys] at hgood
  have hpartition := current_match_partition p cls label v baseline keyBaseline short current horder
  have hshort := current_short_consumption_le_stock p cls label v baseline keyBaseline
    short current hshortJob
  rw [hshortStock] at hshort
  exact CoverageCounts.long_match_lower_bound hcorrection
    (CoverageCounts.short_le_displaced_add_long hgood hpartition hshort)

end Coverage
end BinPackingGap

end

end OAI
