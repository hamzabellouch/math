import Mathlib
import OAI.Algebra.GroupRing.IntervalSelfLinks

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.LinkComponents
open scoped Classical BigOperators
open EntropyStages
variable {I : Type*} [Fintype I] (m : I → ℕ)
abbrev Occurrence := (i : I) × Fin (m i)
variable (P : Pairing (Occurrence m))

def graph : SimpleGraph I where
  Adj i j := i ≠ j ∧ ∃ o : Occurrence m, o.1 = i ∧ (P.partner o).1 = j
  symm := ⟨by
    rintro i j ⟨hne,o,hi,hj⟩
    exact ⟨hne.symm,P.partner o,hj,by rw [P.involutive]; exact hi⟩⟩
  loopless := ⟨fun i h => h.1 rfl⟩

abbrev Component := (graph m P).ConnectedComponent

def HasSelf (c : Component m P) : Prop :=
  ∃ o : Occurrence m, (graph m P).connectedComponentMk o.1 = c ∧
    P.partner o ≠ o ∧ (P.partner o).1 = o.1

omit [Fintype I] in
/-- Matched block occurrences always stay in their link component. -/
theorem partner_component (o : Occurrence m) :
    (graph m P).connectedComponentMk (P.partner o).1 = (graph m P).connectedComponentMk o.1 := by
  by_cases he : (P.partner o).1 = o.1
  · rw [he]
  · apply SimpleGraph.ConnectedComponent.sound
    apply SimpleGraph.Adj.reachable
    exact ⟨he,P.partner o,rfl,by rw [P.involutive]⟩

abbrev ComponentOccurrence (c : Component m P) :=
  {o : Occurrence m // (graph m P).connectedComponentMk o.1 = c}

def restrict (c : Component m P) : Pairing (ComponentOccurrence m P c) where
  partner o := ⟨P.partner o.val,(partner_component m P o.val).trans o.property⟩
  involutive o := Subtype.ext (P.involutive o.val)

def unmatched (c : Component m P) : ℕ := Fintype.card (restrict m P c).Unmatched

/-- Counting actual occurrences, including repeats, gives the sum of block
multiplicities in the component. -/
theorem card_occurrences (c : Component m P) :
    Fintype.card (ComponentOccurrence m P c) = ∑ i : c, m i.val := by
  let e : ComponentOccurrence m P c ≃ (i : c) × Fin (m i.val) :=
    { toFun := fun o => ⟨⟨o.val.1,o.property⟩,o.val.2⟩
      invFun := fun o => ⟨⟨o.1.val,o.2⟩,o.1.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e,Fintype.card_sigma]
  simp only [Fintype.card_fin]

theorem card_block_occurrences (c : Component m P) (i : c) :
    Fintype.card {o : ComponentOccurrence m P c // o.val.1 = i.val} = m i.val := by
  let e : {o : ComponentOccurrence m P c // o.val.1 = i.val} ≃ Fin (m i.val) :=
    { toFun := fun o => ⟨o.val.val.2.val,by simpa only [o.property] using o.val.val.2.isLt⟩
      invFun := fun k => ⟨⟨⟨i.val,k⟩,i.property⟩,rfl⟩
      left_inv := by
        intro ⟨⟨⟨j,k⟩,hj⟩,hi⟩
        dsimp at hi
        subst j
        rfl
      right_inv := fun _ => rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_fin _)

/-- Literal link balance in a component without a self-link. -/
theorem balance (c : Component m P) (hn : ¬HasSelf m P c) (i : c) :
    2*m i.val ≤ (∑ j : c, m j.val) + unmatched m P c := by
  have hc : ∀ o : ComponentOccurrence m P c,
      (restrict m P c).partner o ≠ o →
        ((restrict m P c).partner o).val.1 ≠ o.val.1 := by
    intro o hne he
    apply hn
    exact ⟨o.val,o.property,fun ho => hne (Subtype.ext ho),he⟩
  have hh := (restrict m P c).color_balance (fun o => o.val.1) i.val hc
  rw [card_block_occurrences m P c i,card_occurrences m P c] at hh
  exact hh

/-- The maximum multiplicity is present exactly in the active components. -/
def maximum (c : Component m P) : ℕ :=
  (Finset.univ.image (fun i : c => m i.val)).max'
    (by obtain ⟨i⟩ := c.connected_toSimpleGraph.nonempty; exact ⟨m i.val,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩)

theorem le_maximum (c : Component m P) (i : c) : m i.val ≤ maximum m P c :=
  by
    unfold maximum
    exact Finset.le_max' (Finset.univ.image (fun j : c => m j.val)) (m i.val) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)

theorem maximum_mem (c : Component m P) : ∃ i : c, m i.val = maximum m P c := by
  have hh := Finset.max'_mem (Finset.univ.image (fun i : c => m i.val))
    (by obtain ⟨i⟩ := c.connected_toSimpleGraph.nonempty; exact ⟨m i.val,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩)
  rcases Finset.mem_image.mp hh with ⟨i,_,hi⟩
  exact ⟨i,hi⟩

theorem maximum_balance (c : Component m P) (hn : ¬HasSelf m P c) :
    2*maximum m P c ≤ (∑ j : c, m j.val) + unmatched m P c := by
  obtain ⟨i,hi⟩ := maximum_mem m P c
  rw [← hi]
  exact balance m P c hn i

theorem active_iff (c : Component m P) (j : ℕ) :
    (∃ i : c, j < m i.val) ↔ j < maximum m P c := by
  constructor
  · rintro ⟨i,hi⟩
    exact hi.trans_le (le_maximum m P c i)
  · intro hj
    obtain ⟨i,hi⟩ := maximum_mem m P c
    exact ⟨i,hi ▸ hj⟩

/-- Components partition the underlying blocks, including the isolated ones. -/
theorem sum_components {R : Type*} [AddCommMonoid R] (a : I → R) :
    (∑ c : Component m P, ∑ i : c, a i.val) = ∑ i, a i := by
  let e := Equiv.sigmaFiberEquiv (graph m P).connectedComponentMk
  calc
    _ = ∑ x : (c : Component m P) × c, a x.2.val :=
      (Fintype.sum_sigma (fun x : (c : Component m P) × c => a x.2.val)).symm
    _ = _ := Fintype.sum_equiv e _ _ (fun _ => rfl)

/-- Fixed occurrences are partitioned by precisely the same components. -/
theorem sum_unmatched :
    (∑ c : Component m P, unmatched m P c) = Fintype.card P.Unmatched := by
  let f : P.Unmatched → Component m P := fun o => (graph m P).connectedComponentMk o.val.1
  have hc (c : Component m P) :
      unmatched m P c = Fintype.card {o : P.Unmatched // f o = c} := by
    let e : (restrict m P c).Unmatched ≃ {o : P.Unmatched // f o = c} :=
      { toFun := fun o => ⟨⟨o.val.val, congrArg Subtype.val o.property⟩, o.val.property⟩
        invFun := fun o => ⟨⟨o.val.val, o.property⟩, Subtype.ext o.val.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact Fintype.card_congr e
  simp_rw [hc]
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.sigmaFiberEquiv f)

/-- The bin-minimizing root need not be present at a given stage. -/
def minimumRoot (d : I → ℝ) (c : Component m P) : c :=
  Classical.choose (Finset.exists_min_image Finset.univ (fun i : c => d i.val)
    (by obtain ⟨i⟩ := c.connected_toSimpleGraph.nonempty; exact ⟨i, Finset.mem_univ _⟩))

theorem minimumRoot_le (d : I → ℝ) (c : Component m P) (i : c) :
    d (minimumRoot m P d c).val ≤ d i.val :=
  (Classical.choose_spec (Finset.exists_min_image Finset.univ (fun i : c => d i.val)
    (by obtain ⟨i⟩ := c.connected_toSimpleGraph.nonempty; exact ⟨i, Finset.mem_univ _⟩))).2 i (Finset.mem_univ _)

def componentLabelCost (d : I → ℝ) (δ s : ℝ) (c : Component m P) : ℝ :=
  if HasSelf m P c then 0 else 2*d (minimumRoot m P d c).val-δ*s

/-- The actual label/block part of the stage exponent, before embedding and
uniform error terms are added. Stages are indexed from zero. -/
def stageCost (M : ℕ) (d : I → ℝ) (δ s : ℝ) (j : Fin M) : ℝ :=
  -(∑ i, if j.val < m i then d i else 0) +
    ∑ c : Component m P, if j.val < maximum m P c then componentLabelCost m P d δ s c else 0

/-- Summing the actual link-component exponents gives decay and
only the globally counted unmatched correction. No coverage identity is assumed. -/
theorem sum_stageCost (M : ℕ) (hm : ∀ i, m i ≤ M) (d : I → ℝ) (δ s a : ℝ)
    (hδ : 0 ≤ δ) (hs : 0 ≤ s) (ha : 0 ≤ a)
    (hlow : ∀ i, δ*s/2 ≤ d i) (hhigh : ∀ i, d i ≤ a*s) :
    (∑ j : Fin M, stageCost m P M d δ s j) ≤
      a*s*(Fintype.card P.Unmatched : ℝ) - δ/2*s*(∑ i, (m i : ℝ)) := by
  have hz : ∀ c : Component m P, maximum m P c ≤ M := by
    intro c
    obtain ⟨i,hi⟩ := maximum_mem m P c
    rw [← hi]
    exact hm i.val
  have hi : (∑ j : Fin M, ∑ i, if j.val < m i then d i else 0) =
      ∑ i, (m i : ℝ)*d i := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => StageFusion.layers M (m i) (hm i) (d i))
  have hc : (∑ j : Fin M, ∑ c : Component m P,
      if j.val < maximum m P c then componentLabelCost m P d δ s c else 0) =
      ∑ c : Component m P, (maximum m P c : ℝ)*componentLabelCost m P d δ s c := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun c _ => StageFusion.layers M (maximum m P c) (hz c) _)
  have hid : (∑ j : Fin M, stageCost m P M d δ s j) =
      ∑ c : Component m P, StageFusion.componentCost (HasSelf m P)
        (fun (c : Component m P) (i : c) => m i.val) (fun (c : Component m P) (i : c) => d i.val) (maximum m P)
        (fun c => d (minimumRoot m P d c).val) δ s c := by
    simp only [stageCost,Finset.sum_add_distrib,Finset.sum_neg_distrib]
    rw [hi,hc,← sum_components m P (fun i => (m i : ℝ)*d i)]
    simp only [StageFusion.componentCost,Finset.sum_add_distrib,Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro c _
    unfold componentLabelCost
    split_ifs <;> ring
  rw [hid]
  have htotal := StageFusion.total_component_cost (HasSelf m P)
    (fun (c : Component m P) (i : c) => m i.val) (fun (c : Component m P) (i : c) => d i.val) (maximum m P)
    (fun c => d (minimumRoot m P d c).val) (fun c => (unmatched m P c : ℝ)) δ s a
    hδ hs ha (fun _ => Nat.cast_nonneg _)
    (fun _ i => hlow i.val) (fun c _ i => minimumRoot_le m P d c i)
    (fun c _ => hlow (minimumRoot m P d c).val)
    (fun c _ => hhigh (minimumRoot m P d c).val)
    (fun c hc => by exact_mod_cast maximum_balance m P c hc)
  have hu : (∑ c : Component m P, (unmatched m P c : ℝ)) = Fintype.card P.Unmatched := by
    exact_mod_cast sum_unmatched m P
  rw [hu,sum_components m P (fun i => (m i : ℝ))] at htotal
  exact htotal

/-- A numerical bound for actual stages: the Euler terms need only have
nonpositive total, exactly as supplied by the immersed traversal argument. -/
theorem sum_stageBound (M : ℕ) (hm : ∀ i, m i ≤ M) (d : I → ℝ) (δ s a logn : ℝ)
    (power err : Fin M → ℝ)
    (hδ : 0 ≤ δ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hn : 0 ≤ logn)
    (hlow : ∀ i, δ*s/2 ≤ d i) (hhigh : ∀ i, d i ≤ a*s)
    (hpower : (∑ j : Fin M, power j) ≤ 0) :
    (Finset.univ.sum (fun j : Fin M => power j*logn + stageCost m P M d δ s j + err j)) ≤
      a*s*(Fintype.card P.Unmatched : ℝ) - δ/2*s*(∑ i, (m i : ℝ)) + (∑ j : Fin M, err j) := by
  have hc := sum_stageCost m P M hm d δ s a hδ hs ha hlow hhigh
  have hp := mul_nonpos_of_nonpos_of_nonneg hpower hn
  simp only [Finset.sum_add_distrib,← Finset.sum_mul]
  linarith

end TorsionFreeZeroDivisors.LinkComponents

namespace TorsionFreeZeroDivisors.OccurrenceMatching.Data
open scoped Classical
variable {Ω B B' E : Type*} (D : OccurrenceMatching.Data (Ω := Ω) (B := B) (E := E))

def transport (r : B' ≃ B) : OccurrenceMatching.Data (Ω := Ω) (B := B') (E := E) where
  error := D.error
  positions b := D.positions (r b)
  disjoint h := D.disjoint (r.injective.ne h)
  pairing := D.pairing
  side := D.side
  flip := D.flip
  flip_inv := D.flip_inv
  flip_ne := D.flip_ne
  side_partner := D.side_partner

theorem transport_joined (r : B' ≃ B) (o p : B') :
    (D.transport r).Joined o p ↔ D.Joined (r o) (r p) := Iff.rfl

theorem transport_partner (r : B' ≃ B) (o : B') :
    r ((D.transport r).matching.partner o) = D.matching.partner (r o) := by
  by_cases h : D.matching.partner (r o) = r o
  · have hh : (D.transport r).matching.partner o = o := by
      apply ((D.transport r).unmatched_iff o).mpr
      intro p hp
      exact (D.unmatched_iff (r o)).mp h (r p) hp
    rw [hh,h]
  · obtain ⟨p,hp⟩ := (D.matched_iff (r o)).mp h
    have hp' : (D.transport r).Joined o (r.symm p) := by
      rw [transport_joined,r.apply_symm_apply]
      exact hp
    have he := (D.transport r).partner_spec hp'
    have he' := D.partner_spec hp
    change (D.transport r).matching.partner o = r.symm p at he
    change D.matching.partner (r o) = p at he'
    rw [he,he',r.apply_symm_apply]

end TorsionFreeZeroDivisors.OccurrenceMatching.Data

namespace TorsionFreeZeroDivisors.RepeatedBlocks
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks
variable {C E : Type*} (s : ℝ) (hs : 0 < s) (len m : C → ℕ)

abbrev Traversal := (c : C) × Fin (m c)
abbrev traversalLength : Traversal m → ℕ := fun t => len t.1
abbrev Underlying := ComparedBlocks.Block s len
abbrev Occurrence := ComparedBlocks.Block s (traversalLength len m)
abbrev multiplicity (i : Underlying s len) : ℕ := m i.1

/-- The occurrence index is retained separately from the common chain grid. -/
def occurrenceEquiv : Occurrence s len m ≃ LinkComponents.Occurrence (multiplicity s len m) where
  toFun b := ⟨⟨b.1.1,b.2⟩,b.1.2⟩
  invFun b := ⟨⟨b.1.1,b.2⟩,b.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def color (b : Occurrence s len m) : Underlying s len := (occurrenceEquiv s len m b).1

def height (i : Underlying s len) : ℕ := (block s i.2.val).card

def lower (i : Underlying s len) : ℤ := ⌈(i.2.val : ℝ)*s-1/2⌉
def upper (i : Underlying s len) : ℤ := ⌈((i.2.val : ℝ)+1)*s-1/2⌉

theorem block_interval (i : Underlying s len) : block s i.2.val = Finset.Ico (lower s len i) (upper s len i) := by
  simp only [block,positions,lower,upper,Int.cast_natCast]

/-- Literal increasing edge coordinates shared by every repetition. -/
def wordCoordinate (i : Underlying s len) : block s i.2.val ≃ Fin (height s len i) :=
  (Set.equivOfEq (congrArg (fun positions : Finset ℤ => (positions : Set ℤ)) (block_interval s len i))).trans
    ((IntervalSelfLinks.coordinate (lower s len i) (upper s len i)).trans
      (finCongr (by rw [height,block_interval,Int.card_Ico])))

theorem wordCoordinate_val (i : Underlying s len) (q : block s i.2.val) :
    ((wordCoordinate s len i q).val : ℤ) = q.val-lower s len i := by
  exact IntervalSelfLinks.coordinate_val ⟨q.val,by rw [← block_interval]; exact q.property⟩

def blockPositionEquiv (b : Occurrence s len m) :
    blockPositions s hs (traversalLength len m) b ≃ block s b.2.val where
  toFun x := ⟨x.val.2.val,((mem_blockPositions s hs (traversalLength len m)).mp x.property).2⟩
  invFun q := ⟨includeBlock s hs (traversalLength len m) b q,
    Finset.mem_map.mpr ⟨q,Finset.mem_attach _ _,rfl⟩⟩
  left_inv x := by
    apply Subtype.ext
    have hh := ((mem_blockPositions s hs (traversalLength len m)).mp x.property).1
    cases b with
    | mk t k =>
      rcases x with ⟨⟨u,q⟩,hx⟩
      dsimp at hh
      subst u
      rfl
  right_inv _ := rfl

def coordinate (b : Occurrence s len m) :
    blockPositions s hs (traversalLength len m) b ≃ Fin (height s len (color s len m b)) :=
  (blockPositionEquiv s hs len m b).trans (wordCoordinate s len (color s len m b))

theorem coordinate_val (b : Occurrence s len m)
    (x : blockPositions s hs (traversalLength len m) b) :
    ((coordinate s hs len m b x).val : ℤ) = x.val.2.val-lower s len (color s len m b) :=
  wordCoordinate_val s len (color s len m b) (blockPositionEquiv s hs len m b x)

variable (cmp : Comparisons (E := E) (traversalLength len m)) (err : ℕ)

def data : OccurrenceMatching.Data (Ω := Position (traversalLength len m))
    (B := LinkComponents.Occurrence (multiplicity s len m)) (E := E) :=
  (cmp.matchingData s hs (traversalLength len m) err).transport (occurrenceEquiv s len m).symm

def repeatedCoordinate (b : LinkComponents.Occurrence (multiplicity s len m)) :
    (data s hs len m cmp err).positions b ≃ Fin (height s len b.1) :=
  coordinate s hs len m ((occurrenceEquiv s len m).symm b)

variable {A : Type*} (symbol : E → (A ≃ A))

def links : StageLabels.Links (T := A) (height s len) :=
  MatchedLabels.links (data s hs len m cmp err) Sigma.fst (height s len)
    (repeatedCoordinate s hs len m cmp err) symbol

theorem links_graph : (links s hs len m cmp err symbol).graph =
    LinkComponents.graph (multiplicity s len m) (data s hs len m cmp err).matching := rfl

theorem links_deficit (i j : Underlying s len)
    (hadj : (links s hs len m cmp err symbol).graph.Adj i j) :
    height s len i - ((links s hs len m cmp err symbol).known i j).card ≤ err :=
  MatchedLabels.links_deficit _ _ _ _ _ hadj

theorem links_consistent (letters : Position (traversalLength len m) → A)
    (words : (i : Underlying s len) → Fin (height s len i) → A)
    (hcompare : ∀ x e, cmp.side x = some e →
      letters x = symbol e (letters (cmp.pairing.partner x)))
    (hwords : ∀ b (x : blockPositions s hs (traversalLength len m) b),
      words (color s len m b) (coordinate s hs len m b x) = letters x.val) :
    (links s hs len m cmp err symbol).Consistent words := by
  apply MatchedLabels.links_consistent _ _ _ _ _ letters words hcompare
  intro b x
  exact hwords ((occurrenceEquiv s len m).symm b) x

theorem integerSlice_self (i : Underlying s len) (k t : Fin (m i.1)) (e : E) :
    cmp.integerSlice s (traversalLength len m) e
      ((occurrenceEquiv s len m).symm ⟨i,k⟩) ((occurrenceEquiv s len m).symm ⟨i,t⟩) =
    IntervalSelfLinks.selfSlice (lower s len i) (upper s len i)
      ⌈cmp.lo e-1/2⌉ ⌈cmp.hi e-1/2⌉ (cmp.reverse e) (cmp.offset e) := by
  unfold Comparisons.integerSlice
  change (block s i.2.val ∩ positions (cmp.lo e) (cmp.hi e)).filter
    (fun q => affine (cmp.reverse e) (cmp.offset e) q ∈ block s i.2.val) = _
  rw [block_interval s len i]
  rfl

 theorem self_slice_card (i : Underlying s len) (k t : Fin (m i.1)) (e : E)
    (hsource : (⟨i.1,k⟩ : Traversal m) = cmp.source e)
    (htarget : (⟨i.1,t⟩ : Traversal m) = cmp.source (cmp.flip e)) :
    ((data s hs len m cmp err).slice e ⟨i,k⟩ ⟨i,t⟩).card =
      (IntervalSelfLinks.selfSlice (lower s len i) (upper s len i)
        ⌈cmp.lo e-1/2⌉ ⌈cmp.hi e-1/2⌉ (cmp.reverse e) (cmp.offset e)).card := by
  change ((cmp.matchingData s hs (traversalLength len m) err).slice e
    ((occurrenceEquiv s len m).symm ⟨i,k⟩) ((occurrenceEquiv s len m).symm ⟨i,t⟩)).card = _
  rw [cmp.slice_integer_card s hs (traversalLength len m) err hsource htarget,
    integerSlice_self]

include hs in
/-- The original letter comparison restricts to precisely this integer slice. -/
theorem self_comparison {A : Type*} (bar : A → A) (w : C → ℤ → A)
    (hcompare : ∀ x e, cmp.side x = some e →
      w x.1.1 x.2.val = if cmp.reverse e then
        bar (w (cmp.pairing.partner x).1.1 (cmp.pairing.partner x).2.val)
      else w (cmp.pairing.partner x).1.1 (cmp.pairing.partner x).2.val)
    (i : Underlying s len) (k t : Fin (m i.1)) (e : E)
    (hsource : (⟨i.1,k⟩ : Traversal m) = cmp.source e)
    (htarget : (⟨i.1,t⟩ : Traversal m) = cmp.source (cmp.flip e))
    (q : ℤ) (hq : q ∈ IntervalSelfLinks.selfSlice (lower s len i) (upper s len i)
      ⌈cmp.lo e-1/2⌉ ⌈cmp.hi e-1/2⌉ (cmp.reverse e) (cmp.offset e)) :
    w i.1 q = if cmp.reverse e then bar (w i.1 (affine (cmp.reverse e) (cmp.offset e) q))
      else w i.1 (affine (cmp.reverse e) (cmp.offset e) q) := by
  have hh := (Finset.mem_inter.mp (Finset.mem_filter.mp hq).1)
  have hb : q ∈ block s i.2.val := by rw [block_interval]; exact hh.1
  let x : Position (traversalLength len m) :=
    ⟨⟨i.1,k⟩,⟨q,full_subset s hs (len i.1) i.2 hb⟩⟩
  have hx : cmp.side x = some e := (cmp.side_iff x e).mpr ⟨hsource,hh.2⟩
  have hy : (cmp.pairing.partner x).1.1 = i.1 :=
    congrArg Sigma.fst ((cmp.partner_source x e hx).trans htarget.symm)
  have hc := hcompare x e hx
  rw [hy,cmp.partner_coordinate x e hx] at hc
  exact hc

/-- Literal edge reduction rules out zero shift, rather than assuming that
self-links are nontrivial translations. -/
theorem self_shift_ne_zero
    (hreduced : ∀ x e, cmp.side x = some e →
      (x.1.1,x.2.val) ≠ ((cmp.pairing.partner x).1.1,(cmp.pairing.partner x).2.val))
    (i : Underlying s len) (k t : Fin (m i.1)) (e : E)
    (hne : ((data s hs len m cmp err).slice e ⟨i,k⟩ ⟨i,t⟩).Nonempty)
    (hrev : cmp.reverse e = false) : cmp.offset e ≠ 0 := by
  intro hz
  obtain ⟨x,hx⟩ := hne
  obtain ⟨hb,he,hp⟩ := (OccurrenceMatching.Data.slice_mem _).mp hx
  have hb' := ((mem_blockPositions s hs (traversalLength len m)).mp hb).1
  have hp' := ((mem_blockPositions s hs (traversalLength len m)).mp hp).1
  apply hreduced x e he
  apply Prod.ext
  · exact (congrArg Sigma.fst hb').trans (congrArg Sigma.fst hp').symm
  · rw [cmp.partner_coordinate x e he]
    simp [affine,hrev,hz]

/-- A near-full actual self-link is a nonzero translation. Reversed self-links
are infeasible for an immersed block, by the midpoint obstruction. -/
theorem self_link_translation {A : Type*} (bar : A → A)
    (hbar : Function.Involutive bar) (hfree : ∀ a, bar a ≠ a)
    (w : C → ℤ → A)
    (hcompare : ∀ x e, cmp.side x = some e →
      w x.1.1 x.2.val = if cmp.reverse e then
        bar (w (cmp.pairing.partner x).1.1 (cmp.pairing.partner x).2.val)
      else w (cmp.pairing.partner x).1.1 (cmp.pairing.partner x).2.val)
    (hwordred : ∀ (i : Underlying s len) q,
      lower s len i ≤ q → q+1 < upper s len i → w i.1 (q+1) ≠ bar (w i.1 q))
    (hreduced : ∀ x e, cmp.side x = some e →
      (x.1.1,x.2.val) ≠ ((cmp.pairing.partner x).1.1,(cmp.pairing.partner x).2.val))
    (i : Underlying s len) (k t : Fin (m i.1)) (e : E)
    (hmass : height s len i < 2*((data s hs len m cmp err).slice e ⟨i,k⟩ ⟨i,t⟩).card) :
    cmp.reverse e = false ∧ cmp.offset e ≠ 0 := by
  have hne : ((data s hs len m cmp err).slice e ⟨i,k⟩ ⟨i,t⟩).Nonempty :=
    Finset.card_pos.mp (by omega)
  have hne' : ((cmp.matchingData s hs (traversalLength len m) err).slice e
    ((occurrenceEquiv s len m).symm ⟨i,k⟩) ((occurrenceEquiv s len m).symm ⟨i,t⟩)).Nonempty := hne
  obtain ⟨hsrc,htgt⟩ := cmp.slice_sources s hs (traversalLength len m) err hne'
  have hrev : cmp.reverse e = false := by
    cases hr : cmp.reverse e with
    | false => rfl
    | true =>
      have hh := IntervalSelfLinks.reflection_not_large bar hbar hfree (w i.1)
        (lower s len i) (upper s len i) ⌈cmp.lo e-1/2⌉ ⌈cmp.hi e-1/2⌉ (cmp.offset e)
        (hwordred i) (by
          intro q hq
          have hc := self_comparison s hs len m cmp bar w hcompare i k t e hsrc htgt q (by rwa [hr])
          simpa [hr,affine] using hc)
      rw [self_slice_card s hs len m cmp err i k t e hsrc htgt,hr] at hmass
      change (block s i.2.val).card < _ at hmass
      rw [block_interval] at hmass
      omega
  exact ⟨hrev,self_shift_ne_zero s hs len m cmp err hreduced i k t e hne hrev⟩

theorem height_eq (i : Underlying s len) :
    height s len i = (upper s len i-lower s len i).toNat := by
  rw [height,block_interval,Int.card_Ico]

/-- The actual word on an underlying block, in its chain orientation. -/
def word (w : C → ℤ → A) (i : Underlying s len) (k : Fin (height s len i)) : A :=
  w i.1 ((k.val : ℤ)+lower s len i)

theorem word_at_coordinateN (w : C → ℤ → A) (i : Underlying s len)
    (q : Finset.Ico (lower s len i) (upper s len i)) :
    word s len w i (IntervalSelfLinks.coordinateN (lower s len i) (upper s len i)
      (height s len i) (height_eq s len i) q) = w i.1 q.val := by
  unfold word
  rw [IntervalSelfLinks.coordinateN_val,sub_add_cancel]

/-- A chosen literal self-comparison yields a fixed translation forest that
works for all compatible words. Its cardinality is the original slice's, not
an unrelated proxy for the number of constraints. -/
theorem self_translation_constraints
    (i : Underlying s len) (k t : Fin (m i.1)) (e : E)
    (hsource : (⟨i.1,k⟩ : Traversal m) = cmp.source e)
    (htarget : (⟨i.1,t⟩ : Traversal m) = cmp.source (cmp.flip e))
    (hrev : cmp.reverse e = false) (hz : cmp.offset e ≠ 0) :
    ∃ tr : BlockConstraints.Translation (height s len i),
      tr.domain.card = ((data s hs len m cmp err).slice e ⟨i,k⟩ ⟨i,t⟩).card ∧
      ∀ (A : Type*) (bar : A → A) (w : C → ℤ → A),
        (∀ x e, cmp.side x = some e →
          w x.1.1 x.2.val = if cmp.reverse e then
            bar (w (cmp.pairing.partner x).1.1 (cmp.pairing.partner x).2.val)
          else w (cmp.pairing.partner x).1.1 (cmp.pairing.partner x).2.val) →
        ∀ q : tr.domain, word s len w i (tr.target q) = word s len w i q.val := by
  obtain ⟨tr,hcard,htr⟩ := IntervalSelfLinks.translation_from_slice_at
    (lower s len i) (upper s len i) ⌈cmp.lo e-1/2⌉ ⌈cmp.hi e-1/2⌉ (cmp.offset e) hz
    (height s len i) (height_eq s len i)
  refine ⟨tr,?_,?_⟩
  · rw [hcard,self_slice_card s hs len m cmp err i k t e hsource htarget,hrev]
  · intro A bar w hcompare
    apply htr A (word s len w i)
    intro q hq
    rw [word_at_coordinateN,word_at_coordinateN]
    have hc := self_comparison s hs len m cmp bar w hcompare i k t e hsource htarget q (by rwa [hrev])
    simpa [hrev,affine] using hc.symm

theorem positions_height (o : LinkComponents.Occurrence (multiplicity s len m)) :
    ((data s hs len m cmp err).positions o).card = height s len o.1 := by
  have hh := Fintype.card_congr (repeatedCoordinate s hs len m cmp err o)
  simpa only [Fintype.card_coe,Fintype.card_fin] using hh

/-- Every literal self-linked component has a root and a translation forest
of the prescribed deficit. A single feasible immersed labeling rules out the
reflection case; the resulting forest then constrains every feasible labeling. -/
theorem self_component_translation [Fintype C]
    {A : Type*} (bar : A → A) (hbar : Function.Involutive bar) (hfree : ∀ a, bar a ≠ a)
    (w₀ : C → ℤ → A)
    (hcompare₀ : ∀ x e, cmp.side x = some e →
      w₀ x.1.1 x.2.val = if cmp.reverse e then
        bar (w₀ (cmp.pairing.partner x).1.1 (cmp.pairing.partner x).2.val)
      else w₀ (cmp.pairing.partner x).1.1 (cmp.pairing.partner x).2.val)
    (hwordred : ∀ (i : Underlying s len) q,
      lower s len i ≤ q → q+1 < upper s len i → w₀ i.1 (q+1) ≠ bar (w₀ i.1 q))
    (hreduced : ∀ x e, cmp.side x = some e →
      (x.1.1,x.2.val) ≠ ((cmp.pairing.partner x).1.1,(cmp.pairing.partner x).2.val))
    (c : LinkComponents.Component (multiplicity s len m) (data s hs len m cmp err).matching)
    (hc : LinkComponents.HasSelf (multiplicity s len m) (data s hs len m cmp err).matching c) :
    ∃ (i : c) (tr : BlockConstraints.Translation (height s len i.val)),
      height s len i.val-tr.domain.card ≤ err ∧
      ∀ (A : Type*) (bar : A → A) (w : C → ℤ → A),
        (∀ x e, cmp.side x = some e →
          w x.1.1 x.2.val = if cmp.reverse e then
            bar (w (cmp.pairing.partner x).1.1 (cmp.pairing.partner x).2.val)
          else w (cmp.pairing.partner x).1.1 (cmp.pairing.partner x).2.val) →
        ∀ q : tr.domain, word s len w i.val (tr.target q) = word s len w i.val q.val := by
  obtain ⟨o,ho,hmatched,hself⟩ := hc
  obtain ⟨p,hjoin⟩ := ((data s hs len m cmp err).matched_iff o).mp hmatched
  have hp := (data s hs len m cmp err).partner_spec hjoin
  change (data s hs len m cmp err).partner o = p at hp
  change ((data s hs len m cmp err).partner o).1 = o.1 at hself
  rw [hp] at hself
  rcases o with ⟨i,k⟩
  rcases p with ⟨j,t⟩
  dsimp at hself
  subst j
  obtain ⟨e,hmass,_,hdef,_⟩ := hjoin
  rw [positions_height] at hmass hdef
  obtain ⟨hr,hz⟩ := self_link_translation s hs len m cmp err bar hbar hfree w₀
    hcompare₀ hwordred hreduced i k t e hmass
  have hne : ((cmp.matchingData s hs (traversalLength len m) err).slice e
    ((occurrenceEquiv s len m).symm ⟨i,k⟩) ((occurrenceEquiv s len m).symm ⟨i,t⟩)).Nonempty :=
    Finset.card_pos.mp (by change 0 < ((data s hs len m cmp err).slice e ⟨i,k⟩ ⟨i,t⟩).card; omega)
  obtain ⟨hsrc,htgt⟩ := cmp.slice_sources s hs (traversalLength len m) err hne
  obtain ⟨tr,hcard,htr⟩ := self_translation_constraints s hs len m cmp err i k t e hsrc htgt hr hz
  refine ⟨⟨i,ho⟩,tr,?_,htr⟩
  rw [hcard]
  change height s len i ≤ ((data s hs len m cmp err).slice e ⟨i,k⟩ ⟨i,t⟩).card+err at hdef
  exact Nat.sub_le_iff_le_add.mpr (by simpa only [Nat.add_comm] using hdef)

end TorsionFreeZeroDivisors.RepeatedBlocks

end

end OAI
