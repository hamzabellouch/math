import OAI.Computability.WLIdentification.LocalImages

namespace OAI

namespace WLIdentification

namespace RingLayout
variable {r : ℕ} {T L : Type} (R : RingLayout r T L)

theorem wrapping_row_inj (hr : 3 ≤ r) {U : Finset R.Block}
    (h : R.Wrapping (by omega) U) (hu : U.card ≤ r) : Set.InjOn R.blockRow U := by
  classical
  apply Finset.card_image_iff.mp
  have he : U.image R.blockRow = Finset.univ := Finset.eq_univ_of_forall (R.wrapping_rows hr h)
  rw [he, Finset.card_univ, Fintype.card_fin]
  exact Nat.le_antisymm (R.wrapping_card hr h) hu

def blockRepresentative : R.Block → R.Corner
  | .inl h => R.nameFirst (.inl h)
  | .inr b => R.nameFirst (.inl (R.leftH b))

theorem name_present {U : Finset R.Block} {b : R.Block} (hb : b ∈ U)
    {n : R.Name} (hn : n ∈ R.blockNames b) : n ∈ R.names U := by
  classical
  exact Finset.mem_biUnion.mpr ⟨b, hb, hn⟩

theorem name_reachable (hr : 2 ≤ r) {U : Finset R.Block} {n : R.Name}
    (hn : n ∈ R.names U) :
    (R.cornerGraph hr U).Reachable (R.nameFirst n) (R.nameSecond n) :=
  SimpleGraph.Adj.reachable ⟨n, hn, Or.inl ⟨rfl, rfl⟩⟩

/-- Every name of a block belongs to the block's unique corner component. -/
theorem block_reachable (hr : 2 ≤ r) {U : Finset R.Block} {b : R.Block} (hb : b ∈ U)
    {n : R.Name} (hn : n ∈ R.blockNames b) :
    (R.cornerGraph hr U).Reachable (R.blockRepresentative b) (R.nameFirst n) ∧
    (R.cornerGraph hr U).Reachable (R.blockRepresentative b) (R.nameSecond n) := by
  classical
  cases b with
  | inl b =>
    have he : n = Sum.inl b := Finset.mem_singleton.mp hn
    subst n
    exact ⟨SimpleGraph.Reachable.refl _, R.name_reachable hr (R.name_present hb hn)⟩
  | inr b =>
    have hl := R.name_reachable hr (R.name_present hb
      (show Sum.inl (R.leftH b) ∈ R.blockNames (.inr b) by simp [blockNames]))
    have hr' := R.name_reachable hr (R.name_present hb
      (show Sum.inl (R.rightH b) ∈ R.blockNames (.inr b) by simp [blockNames]))
    have ht := R.name_reachable hr (R.name_present hb
      (show Sum.inr (R.topV b) ∈ R.blockNames (.inr b) by simp [blockNames]))
    have hb' := R.name_reachable hr (R.name_present hb
      (show Sum.inr (R.bottomV b) ∈ R.blockNames (.inr b) by simp [blockNames]))
    simp only [blockNames, Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl | rfl
    · exact ⟨SimpleGraph.Reachable.refl _, hl⟩
    · exact ⟨ht, ht.trans hr'⟩
    · exact ⟨SimpleGraph.Reachable.refl _, ht⟩
    · exact ⟨hl, hl.trans hb'⟩

noncomputable def componentBlocks (hr : 2 ≤ r) (U : Finset R.Block) (u : R.Corner) : Finset R.Block := by
  classical
  exact U.filter (fun b => (R.cornerGraph hr U).Reachable u (R.blockRepresentative b))

theorem componentBlocks_subset (hr : 2 ≤ r) (U : Finset R.Block) (u : R.Corner) :
    R.componentBlocks hr U u ⊆ U := by
  classical
  exact Finset.filter_subset _ _

theorem component_edge (hr : 2 ≤ r) {U : Finset R.Block} {root u v : R.Corner}
    (hu : (R.cornerGraph hr U).Reachable root u) (h : (R.cornerGraph hr U).Adj u v) :
    (R.cornerGraph hr (R.componentBlocks hr U root)).Adj u v := by
  classical
  obtain ⟨n, hn, h⟩ := h
  obtain ⟨b, hb, hbn⟩ := Finset.mem_biUnion.mp hn
  have hb' : b ∈ R.componentBlocks hr U root := by
    apply Finset.mem_filter.mpr
    refine ⟨hb, ?_⟩
    obtain ⟨hfirst, hsecond⟩ := R.block_reachable hr hb hbn
    rcases h with ⟨hf, _⟩ | ⟨_, hs⟩
    · exact hu.trans (hf ▸ hfirst).symm
    · exact hu.trans (hs ▸ hsecond).symm
  exact ⟨n, R.name_present hb' hbn, h⟩

theorem component_walk (hr : 2 ≤ r) {U : Finset R.Block} (root : R.Corner)
    {u v : R.Corner} (p : (R.cornerGraph hr U).Walk u v) :
    (R.cornerGraph hr U).Reachable root u →
    ∃ q : (R.cornerGraph hr (R.componentBlocks hr U root)).Walk u v,
      Marker.walkSum R.cornerMarker q = Marker.walkSum R.cornerMarker p := by
  induction p with
  | nil => exact fun _ => ⟨.nil, rfl⟩
  | cons h p ih =>
    intro hu
    obtain ⟨q, hq⟩ := ih (hu.trans h.reachable)
    exact ⟨.cons (R.component_edge hr hu h) q, congrArg (fun x => R.cornerMarker _ _ + x) hq⟩

/-- A wrapping collection of at most r blocks is entirely in the component of
its odd closed walk. This also rules out two independent old wrapping choices. -/
theorem wrapping_component (hr : 3 ≤ r) {U : Finset R.Block} (hu : U.card ≤ r)
    {u : R.Corner} (p : (R.cornerGraph (by omega) U).Walk u u)
    (hp : Marker.walkSum R.cornerMarker p = 1) :
    R.componentBlocks (by omega) U u = U := by
  obtain ⟨q, hq⟩ := R.component_walk (by omega) u p (SimpleGraph.Reachable.refl _)
  have hw : R.Wrapping (by omega) (R.componentBlocks (by omega) U u) := ⟨u, q, hq.trans hp⟩
  exact Finset.eq_of_subset_of_card_le (R.componentBlocks_subset _ U u)
    (hu.trans (R.wrapping_card hr hw))

end RingLayout

namespace Marker

/-- Label separation at a boundary cuts every winding walk. The parity
incidence argument is expressed as a coboundary. -/
theorem closed_zero_of_mismatched_labels {r : ℕ} (hr : 2 ≤ r)
    {V : Type} {G : SimpleGraph V} (row : V → Fin r) (label : V → Bool)
    (start finish : Fin r → Bool) (j : Fin r) (hj : finish j ≠ start (finRotate r j))
    (m : V → V → Bit)
    (he : ∀ u v, G.Adj u v →
      (row u = row v ∧ label u = label v ∧ m u v = 0) ∨
      ∃ i, m u v = delta i ∧
        ((row u = i ∧ row v = finRotate r i ∧ label u = start i ∧ label v = finish i) ∨
         (row v = i ∧ row u = finRotate r i ∧ label v = start i ∧ label u = finish i))) :
    ∀ u (p : G.Walk u u), walkSum m p = 0 := by
  let mark (i : Fin r) (a : Bool) : Bit := if i = finRotate r j ∧ a = finish j then 1 else 0
  have hmark (i : Fin r) : mark i (start i) + mark (finRotate r i) (finish i) =
      if i = j then 1 else 0 := by
    by_cases hi : i = j
    · subst i
      have hne := CycleRows.rotate_ne_self hr j
      dsimp only [mark]
      rw [ite_eq_right (fun h => hne h.1.symm), ite_eq_left ⟨rfl, rfl⟩, ite_eq_left rfl, zero_add]
    · by_cases hi' : i = finRotate r j
      · subst i
        have hne := CycleRows.rotate_ne_self hr (finRotate r j)
        dsimp only [mark]
        rw [ite_eq_right (fun h => hj h.2.symm), ite_eq_right (fun h => hne h.1), ite_eq_right hi, add_zero]
      · have hrot : finRotate r i ≠ finRotate r j := fun h => hi ((finRotate r).injective h)
        dsimp only [mark]
        rw [ite_eq_right (fun h => hi' h.1), ite_eq_right (fun h => hrot h.1), ite_eq_right hi, add_zero]
  let pot (v : V) : Bit := cut j (row v) + mark (row v) (label v)
  have hm : ∀ u v, G.Adj u v → m u v = pot u + pot v := by
    intro u v huv
    rcases he u v huv with ⟨hrow, hlab, hz⟩ | ⟨i, hval, hh⟩
    · dsimp only [pot]
      rw [hrow, hlab, CharTwo.add_self_eq_zero, hz]
    · have hcalc : delta i =
          (cut j i + mark i (start i)) + (cut j (finRotate r i) + mark (finRotate r i) (finish i)) := by
        calc
          _ = (cut j i + cut j (finRotate r i)) +
              (mark i (start i) + mark (finRotate r i) (finish i)) := by
            rw [cut_toggle, hmark, add_assoc, CharTwo.add_self_eq_zero, add_zero]
          _ = _ := by abel
      dsimp only [pot]
      rcases hh with ⟨hu, hv, hlu, hlv⟩ | ⟨hv, hu, hlv, hlu⟩
      · rw [hu, hv, hlu, hlv, hval, hcalc]
      · rw [hu, hv, hlu, hlv, hval, add_comm]
        exact hcalc
  intro u p
  rw [walkSum_of_exact pot m hm p, CharTwo.add_self_eq_zero]

end Marker

namespace RingLayout
variable {r : ℕ} {T L : Type} (R : RingLayout r T L)

/-- An alignment is only required to respect actual vertical readout names.
No assertion is made that ambient labels inhabit every product factor. -/
def Aligned (U : Finset R.Block) (a : R.Corner → Bool) : Prop :=
  ∀ v : R.VName, Sum.inr v ∈ R.names U → a (R.nameFirst (.inr v)) = a (R.nameSecond (.inr v))

def blockStart (a : R.Corner → Bool) : R.Block → Bool
  | .inl h => a (R.nameFirst (.inl h))
  | .inr b => a (R.nameFirst (.inl (R.leftH b)))

def blockFinish (a : R.Corner → Bool) : R.Block → Bool
  | .inl h => a (R.nameSecond (.inl h))
  | .inr b => a (R.nameSecond (.inl (R.leftH b)))

theorem horizontal_labels {U : Finset R.Block} {a : R.Corner → Bool} (ha : R.Aligned U a)
    {h : R.HName} (hh : Sum.inl h ∈ R.names U) :
    ∃ b ∈ U, R.blockRow b = h.2.1 ∧
      a (R.nameFirst (.inl h)) = R.blockStart a b ∧
      a (R.nameSecond (.inl h)) = R.blockFinish a b := by
  classical
  obtain ⟨b, hb, hm⟩ := Finset.mem_biUnion.mp hh
  refine ⟨b, hb, ?_⟩
  cases b with
  | inl b =>
    have he : h = b := Sum.inl.inj (Finset.mem_singleton.mp hm)
    subst h
    exact ⟨rfl, rfl, rfl⟩
  | inr b =>
    have ht := ha (R.topV b) (R.name_present hb (by simp [blockNames]))
    have hb' := ha (R.bottomV b) (R.name_present hb (by simp [blockNames]))
    simp only [blockNames, Finset.mem_insert, Finset.mem_singleton, Sum.inl.injEq,
      Sum.inl_ne_inr, or_false] at hm
    rcases hm with rfl | rfl
    · exact ⟨rfl, rfl, rfl⟩
    · exact ⟨rfl, ht.symm, hb'.symm⟩

def IsWrappingAddress (U : Finset R.Block) (a : R.Corner → Bool) (address : Fin r → Bool) : Prop :=
  ∀ b ∈ U, R.blockStart a b = address (R.blockRow b) ∧
    R.blockFinish a b = address (finRotate r (R.blockRow b))

/-- Exactly r wrapping blocks prescribe one genuine aligned address. -/
theorem wrapping_address (hr : 3 ≤ r) {U : Finset R.Block}
    (h : R.Wrapping (by omega) U) (hu : U.card ≤ r)
    {a : R.Corner → Bool} (ha : R.Aligned U a) :
    ∃! address : Fin r → Bool, R.IsWrappingAddress U a address := by
  classical
  have hex (i : Fin r) : ∃ b ∈ U, R.blockRow b = i := Finset.mem_image.mp (R.wrapping_rows hr h i)
  choose blocks hb hrow using hex
  have huniq {b : R.Block} (hb' : b ∈ U) : blocks (R.blockRow b) = b :=
    R.wrapping_row_inj hr h hu (hb _) hb' (hrow _)
  let start (i : Fin r) := R.blockStart a (blocks i)
  let finish (i : Fin r) := R.blockFinish a (blocks i)
  have hmatch (j : Fin r) : finish j = start (finRotate r j) := by
    by_contra hj
    have hz := Marker.closed_zero_of_mismatched_labels (show 2 ≤ r by omega)
      (G := R.cornerGraph (by omega) U) (fun c : R.Corner => c.2.1) a start finish j hj
      R.cornerMarker ?_
    · obtain ⟨u, p, hp⟩ := h
      have := hz u p
      rw [hp] at this
      exact one_ne_zero this
    · intro u v huv
      obtain ⟨n, hn, hh⟩ := huv
      cases n with
      | inl n =>
        obtain ⟨b, hb', hr', hl, ht⟩ := R.horizontal_labels ha hn
        have hs : a (R.nameFirst (.inl n)) = start n.2.1 := by
          rw [hl, ← hr']; dsimp only [start]; rw [huniq hb']
        have hf : a (R.nameSecond (.inl n)) = finish n.2.1 := by
          rw [ht, ← hr']; dsimp only [finish]; rw [huniq hb']
        refine Or.inr ⟨n.2.1, ?_⟩
        rcases hh with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨(R.cornerMarker_horizontal hr n).1, Or.inl ⟨rfl, rfl, hs, hf⟩⟩
        · exact ⟨(R.cornerMarker_horizontal hr n).2, Or.inr ⟨rfl, rfl, hs, hf⟩⟩
      | inr n =>
        have he := ha n hn
        rcases hh with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl ⟨rfl, he, (R.cornerMarker_vertical n).1⟩
        · exact Or.inl ⟨rfl, he.symm, (R.cornerMarker_vertical n).2⟩
  refine ⟨start, ?_, ?_⟩
  · intro b hb'
    constructor
    · dsimp only [start]; rw [huniq hb']
    · rw [← hmatch]
      dsimp only [finish]; rw [huniq hb']
  · intro other ho
    funext i
    have hi := (ho (blocks i) (hb i)).1
    rw [hrow i] at hi
    exact hi.symm

end RingLayout

namespace RingLayout
variable {r : ℕ} {T L : Type} (R : RingLayout r T L)

theorem names_mono {V U : Finset R.Block} (h : V ⊆ U) : R.names V ⊆ R.names U := by
  classical
  intro n hn
  obtain ⟨b, hb, hn⟩ := Finset.mem_biUnion.mp hn
  exact R.name_present (h hb) hn

theorem cornerGraph_mono (hr : 2 ≤ r) {V U : Finset R.Block} (h : V ⊆ U) :
    R.cornerGraph hr V ≤ R.cornerGraph hr U := by
  rintro u v ⟨n, hn, hh⟩
  exact ⟨n, R.names_mono h hn, hh⟩

theorem aligned_mono {V U : Finset R.Block} (h : V ⊆ U) {a : R.Corner → Bool}
    (ha : R.Aligned U a) : R.Aligned V a :=
  fun v hv => ha v (R.names_mono h hv)

theorem wrapping_blocks_reachable (hr : 3 ≤ r) {U : Finset R.Block}
    (hu : U.card ≤ r) (hw : R.Wrapping (by omega) U) {b c : R.Block} (hb : b ∈ U) (hc : c ∈ U) :
    (R.cornerGraph (by omega) U).Reachable (R.blockRepresentative b) (R.blockRepresentative c) := by
  classical
  obtain ⟨u, p, hp⟩ := hw
  have he := R.wrapping_component hr hu p hp
  have hb' : b ∈ R.componentBlocks (by omega) U u := by rw [he]; exact hb
  have hc' : c ∈ R.componentBlocks (by omega) U u := by rw [he]; exact hc
  exact (Finset.mem_filter.mp hb').2.symm.trans (Finset.mem_filter.mp hc').2

/-- Two r-element subcollections of r+1 blocks differ by at most one block. -/
theorem small_sdiff {U V W : Finset R.Block} (hV : V ⊆ U) (hW : W ⊆ U)
    (hu : U.card ≤ r + 1) (hw : r ≤ W.card) : (V \ W).card ≤ 1 := by
  classical
  have hs : V \ W ⊆ U \ W := by
    intro b hb
    exact Finset.mem_sdiff.mpr ⟨hV (Finset.mem_sdiff.mp hb).1, (Finset.mem_sdiff.mp hb).2⟩
  have hc := Finset.card_sdiff_add_card_inter U W
  rw [Finset.inter_eq_right.mpr hW] at hc
  have hd := Finset.card_le_card hs
  omega

/-- The common rows of two wrapping r-subcollections touch every boundary.
This is exactly where r≥3 is used for address compatibility. -/
theorem shared_incident (hr : 3 ≤ r) {U V W : Finset R.Block}
    (hV : V ⊆ U) (hW : W ⊆ U) (hu : U.card ≤ r + 1)
    (hv : R.Wrapping (by omega) V) (hw : R.Wrapping (by omega) W) (i : Fin r) :
    ∃ b ∈ V ∩ W, R.blockRow b = i ∨ finRotate r (R.blockRow b) = i := by
  classical
  obtain ⟨b, hb, hbi⟩ := Finset.mem_image.mp (R.wrapping_rows hr hv i)
  obtain ⟨c, hc, hci⟩ := Finset.mem_image.mp (R.wrapping_rows hr hv ((finRotate r).symm i))
  by_cases hbW : b ∈ W
  · exact ⟨b, Finset.mem_inter.mpr ⟨hb, hbW⟩, Or.inl hbi⟩
  by_cases hcW : c ∈ W
  · refine ⟨c, Finset.mem_inter.mpr ⟨hc, hcW⟩, Or.inr ?_⟩
    rw [hci, Equiv.apply_symm_apply]
  have hd := R.small_sdiff hV hW hu (R.wrapping_card hr hw)
  have he := Finset.card_le_one.mp hd b (Finset.mem_sdiff.mpr ⟨hb, hbW⟩)
    c (Finset.mem_sdiff.mpr ⟨hc, hcW⟩)
  have hi : finRotate r i = i := calc
    _ = finRotate r (R.blockRow b) := congrArg (finRotate r) hbi.symm
    _ = finRotate r (R.blockRow c) := congrArg (fun b => finRotate r (R.blockRow b)) he
    _ = i := by rw [hci, Equiv.apply_symm_apply]
  exact (CycleRows.rotate_ne_self (by omega) i hi).elim

/-- All wrapping r-subcollections of r+1 blocks have the same address in a
single ambient alignment; no address is imposed by an arbitrary r+1-cycle. -/
theorem wrapping_addresses_agree (hr : 3 ≤ r) {U V W : Finset R.Block}
    (hV : V ⊆ U) (hW : W ⊆ U) (hu : U.card ≤ r + 1)
    (hv : R.Wrapping (by omega) V) (hw : R.Wrapping (by omega) W)
    {a : R.Corner → Bool} {v w : Fin r → Bool}
    (hvaddr : R.IsWrappingAddress V a v) (hwaddr : R.IsWrappingAddress W a w) : v = w := by
  funext i
  obtain ⟨b, hb, hi⟩ := R.shared_incident hr hV hW hu hv hw i
  obtain ⟨hbV, hbW⟩ := Finset.mem_inter.mp hb
  rcases hi with hi | hi
  · rw [← hi, ← (hvaddr b hbV).1, ← (hwaddr b hbW).1]
  · rw [← hi, ← (hvaddr b hbV).2, ← (hwaddr b hbW).2]

/-- Wrapping r-subcollections also belong to one corner component, even if
other nonwrapping covers appear elsewhere in U. -/
theorem wrapping_subcollections_connected (hr : 3 ≤ r) {U V W : Finset R.Block}
    (hV : V ⊆ U) (hW : W ⊆ U) (hu : U.card ≤ r + 1)
    (hvcard : V.card ≤ r) (hwcard : W.card ≤ r)
    (hv : R.Wrapping (by omega) V) (hw : R.Wrapping (by omega) W)
    {b c : R.Block} (hb : b ∈ V) (hc : c ∈ W) :
    (R.cornerGraph (by omega) U).Reachable (R.blockRepresentative b) (R.blockRepresentative c) := by
  obtain ⟨d, hd, _⟩ := R.shared_incident hr hV hW hu hv hw ⟨0, by omega⟩
  obtain ⟨hdV, hdW⟩ := Finset.mem_inter.mp hd
  have hbd := (R.wrapping_blocks_reachable hr hvcard hv hb hdV).mono (R.cornerGraph_mono _ hV)
  have hdc := (R.wrapping_blocks_reachable hr hwcard hw hdW hc).mono (R.cornerGraph_mono _ hW)
  exact hbd.trans hdc

end RingLayout

namespace RingLayout
variable {r : ℕ} {T L : Type} (R : RingLayout r T L)

noncomputable def usedLinks (U : Finset R.Block) : Finset L := by
  classical
  exact U.biUnion (fun b => match b with | .inl _ => ∅ | .inr q => {q.1})

theorem mem_usedLinks {U : Finset R.Block} {l : L} : l ∈ R.usedLinks U ↔
    ∃ q : R.Square, Sum.inr q ∈ U ∧ q.1 = l := by
  classical
  constructor
  · intro h
    obtain ⟨b, hb, hm⟩ := Finset.mem_biUnion.mp h
    cases b with
    | inl b => exact (Finset.notMem_empty _ hm).elim
    | inr b => exact ⟨b, hb, (Finset.mem_singleton.mp hm).symm⟩
  · rintro ⟨q, hq, rfl⟩
    exact Finset.mem_biUnion.mpr ⟨.inr q, hq, Finset.mem_singleton_self _⟩

theorem usedLinks_card (U : Finset R.Block) : (R.usedLinks U).card ≤ U.card := by
  classical
  calc
    _ ≤ ∑ b ∈ U, (match b with | .inl _ => (∅ : Finset L) | .inr q => {q.1}).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _b ∈ U, 1 := by
      apply Finset.sum_le_sum
      intro b _
      cases b <;> simp
    _ = _ := by simp

end RingLayout

end WLIdentification

end OAI
