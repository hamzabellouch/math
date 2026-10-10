import OAI.Computability.WLIdentification.StableColors

namespace OAI

namespace WLIdentification

namespace AffineBlocks
variable {C B : Type} [Fintype C] [DecidableEq C] [Fintype B] (D : AffineBlocks C B)

abbrev Response (beta : B → Bit) := Σ b, {v // D.Legal beta b v}

def zeroVertex (b : B) : D.Vertex 0 := .inr ⟨b, 0, D.legal_zero b⟩

def BlockWinning {k : ℕ} {beta : B → Bit} (p : Fin k → D.Response beta) : Prop :=
  TagStable (D.baseGraph 0) (D.baseGraph beta) D.colorNat D.colorNat
    (fun i => D.zeroVertex (p i).1) (fun i => .inr (p i))

/-- Stable block responses agree on every shared bit. The probe retains all
current responses and asks one zero bit through the stable extension bijection. -/
theorem blockWinning_consistent {k : ℕ} (hk : 2 ≤ k) {beta : B → Bit}
    {p : Fin k → D.Response beta} (hp : D.BlockWinning p) (i j : Fin k)
    (c : C) (hi : c ∈ D.coordinates (p i).1) (hj : c ∈ D.coordinates (p j).1) :
    (p i).2.val ⟨c, hi⟩ = (p j).2.val ⟨c, hj⟩ := by
  obtain ⟨e, _, hc, ha⟩ := TagStable.extension hk D.colorNat_pos (D.vertex_card 0 beta) hp
  have he := (D.colorNat_eq_iff (.inl (c, 0)) (e (.inl (c, 0)))).mp (hc (.inl (c, 0)))
  obtain ⟨a, heq⟩ := D.exists_bit_of_color (e (.inl (c, 0))) c he.symm
  have h1 := (ha (.inl (c, 0)) i).mp (by exact ⟨hi, rfl⟩)
  have h2 := (ha (.inl (c, 0)) j).mp (by exact ⟨hj, rfl⟩)
  rw [heq] at h1 h2
  obtain ⟨_, h1⟩ := h1
  obtain ⟨_, h2⟩ := h2
  exact h1.trans h2.symm

theorem blockWinning_exists {k : ℕ} (hk : 2 ≤ k) {beta : B → Bit}
    (h : Equivalent k (D.graph 0) (D.graph beta)) (b : Fin k → B) :
    ∃ p : Fin k → D.Response beta, D.BlockWinning p ∧ ∀ i, (p i).1 = b i := by
  classical
  obtain ⟨w, hw⟩ := TagStable.exists_of_equivalent hk D.colorNat_pos h (fun i => D.zeroVertex (b i))
  have hc (i : Fin k) : D.colorName (w i) = .inr (b i) := by
    exact ((D.colorNat_eq_iff _ _).mp (TagStable.colors hk (D.vertex_card 0 beta) hw i)).symm
  choose q hq using fun i => D.exists_valuation_of_color (w i) (b i) (hc i)
  refine ⟨fun i => ⟨b i, q i⟩, ?_, fun _ => rfl⟩
  have hh : w = fun i => .inr ⟨b i, q i⟩ := funext hq
  rw [hh] at hw
  exact hw

/-- One response extends simultaneously in every replacement slot, and agrees
with all old responses, even the one to be discarded. This is the literal
place-before-discard property needed for ring transfers. -/
theorem blockWinning_extend {k : ℕ} (hk : 2 ≤ k) {beta : B → Bit}
    {p : Fin k → D.Response beta} (hp : D.BlockWinning p) (b : B) :
    ∃ q : {v // D.Legal beta b v},
      (∀ i, D.BlockWinning (Function.update p i ⟨b, q⟩)) ∧
      (∀ i c (hi : c ∈ D.coordinates (p i).1) (hb : c ∈ D.coordinates b),
        (p i).2.val ⟨c, hi⟩ = q.val ⟨c, hb⟩) := by
  classical
  obtain ⟨e, he, hc, _⟩ := TagStable.extension hk D.colorNat_pos (D.vertex_card 0 beta) hp
  have hn := ((D.colorNat_eq_iff _ _).mp (hc (D.zeroVertex b))).symm
  obtain ⟨q, hq⟩ := D.exists_valuation_of_color (e (D.zeroVertex b)) b hn
  have hh (i : Fin k) : D.BlockWinning (Function.update p i ⟨b, q⟩) := by
    have ht := he (D.zeroVertex b) i
    rw [hq] at ht
    have h1 : Function.update (fun j => D.zeroVertex (p j).1) i (D.zeroVertex b) =
        fun j => D.zeroVertex (Function.update p i ⟨b, q⟩ j).1 := by
      funext j; by_cases hji : j = i <;> simp [hji]
    have h2 : Function.update (fun j => Sum.inr (p j) : Fin k → D.Vertex beta) i (.inr ⟨b, q⟩) =
        fun j => .inr (Function.update p i ⟨b, q⟩ j) := by
      funext j; by_cases hji : j = i <;> simp [hji]
    rw [h1, h2] at ht
    exact ht
  refine ⟨q, hh, ?_⟩
  intro i c hi hb
  have hj : ∃ j : Fin k, i ≠ j := by
    let a : Fin k := ⟨0, by omega⟩
    let b : Fin k := ⟨1, by omega⟩
    by_cases hia : i = a
    · refine ⟨b, ?_⟩
      intro h
      have := congrArg Fin.val (hia.symm.trans h)
      simp [a, b] at this
    · exact ⟨a, hia⟩
  obtain ⟨j, hij⟩ := hj
  have hcons := D.blockWinning_consistent hk (hh j) i j
  rw [Function.update_of_ne hij, Function.update_self] at hcons
  exact hcons c hi hb

end AffineBlocks

namespace AffineBlocks
variable {C B : Type} [Fintype C] [DecidableEq C] [Fintype B] (D : AffineBlocks C B)

noncomputable def responseValue {beta : B → Bit} (p : D.Response beta) (c : C) : Bit :=
  if h : c ∈ D.coordinates p.1 then p.2.val ⟨c, h⟩ else 0

omit [Fintype B] in
theorem responseValue_of_mem {beta : B → Bit} (p : D.Response beta) (c : C)
    (hc : c ∈ D.coordinates p.1) : D.responseValue p c = p.2.val ⟨c, hc⟩ := by
  simp only [responseValue, dite_eq_left hc]

def Agree {beta : B → Bit} (p q : D.Response beta) : Prop :=
  ∀ c, c ∈ D.coordinates p.1 → c ∈ D.coordinates q.1 →
    D.responseValue p c = D.responseValue q c

omit [Fintype B] in
theorem agree_refl {beta : B → Bit} (p : D.Response beta) : D.Agree p p := fun _ _ _ => rfl

omit [Fintype B] in
theorem agree_symm {beta : B → Bit} {p q : D.Response beta} (h : D.Agree p q) : D.Agree q p :=
  fun c hq hp => (h c hp hq).symm

theorem blockWinning_agree {beta : B → Bit} {k : ℕ} (hk : 2 ≤ k)
    {p : Fin k → D.Response beta} (hp : D.BlockWinning p) (i j : Fin k) : D.Agree (p i) (p j) := by
  intro c hi hj
  rw [D.responseValue_of_mem _ _ hi, D.responseValue_of_mem _ _ hj]
  exact D.blockWinning_consistent hk hp i j c hi hj

/-- Sequentially transfer every slot to its prescribed next block. For every
row the shared-coordinate values of its old block are retained. -/
theorem blockWinning_transfer {beta : B → Bit} {k : ℕ} (hk : 2 ≤ k)
    {p : Fin k → D.Response beta} (hp : D.BlockWinning p) (b : Fin k → B) :
    ∃ q : Fin k → D.Response beta, D.BlockWinning q ∧
      (∀ i, (q i).1 = b i) ∧ (∀ i, D.Agree (p i) (q i)) := by
  classical
  have h (U : Finset (Fin k)) : ∃ q : Fin k → D.Response beta, D.BlockWinning q ∧
      (∀ i ∈ U, (q i).1 = b i ∧ D.Agree (p i) (q i)) ∧
      (∀ i ∉ U, q i = p i) := by
    induction U using Finset.induction_on with
    | empty => exact ⟨p, hp, by simp, fun _ _ => rfl⟩
    | @insert i U hi ih =>
      obtain ⟨q, hq, hdone, hold⟩ := ih
      obtain ⟨v, hv, ha⟩ := D.blockWinning_extend hk hq (b i)
      refine ⟨Function.update q i ⟨b i, v⟩, hv i, ?_, ?_⟩
      · intro j hj
        rcases Finset.mem_insert.mp hj with hji | hj
        · subst j
          refine ⟨by simp, ?_⟩
          simp only [Function.update_self]
          intro c hc hc'
          have hh := ha i
          rw [hold i hi] at hh
          rw [D.responseValue_of_mem _ _ hc, D.responseValue_of_mem _ _ hc']
          exact hh c hc hc'
        · have hji : j ≠ i := fun h => hi (h ▸ hj)
          simpa only [Function.update_of_ne hji] using hdone j hj
      · intro j hj
        have hji : j ≠ i := fun h => hj (h ▸ Finset.mem_insert_self _ _)
        rw [Function.update_of_ne hji]
        exact hold j (fun h => hj (Finset.mem_insert_of_mem h))
  obtain ⟨q, hq, hd, _⟩ := h Finset.univ
  exact ⟨q, hq, fun i => (hd i (Finset.mem_univ _)).1,
    fun i => (hd i (Finset.mem_univ _)).2⟩

end AffineBlocks

namespace AffineBlocks
variable {C B : Type} [Fintype C] [DecidableEq C] [Fintype B] (D : AffineBlocks C B)

omit [Fintype B] in
theorem response_legal {beta : B → Bit} (p : D.Response beta) :
    D.Legal beta p.1 (D.restrict p.1 (D.responseValue p)) := by
  have hh : D.restrict p.1 (D.responseValue p) = p.2.val := by
    funext c
    exact D.responseValue_of_mem p c.val c.property
  rw [hh]
  exact p.2.property

end AffineBlocks

namespace RingLayout
variable {r : ℕ} {T L : Type} [Fintype T] [Fintype L] (R : RingLayout r T L)

abbrev siteRing (t : T) (a : R.Address t) (i : Fin r) : R.HName :=
  ⟨t, i, a i, a (finRotate r i)⟩
abbrev squareRing (e : L) (a : R.MatchAddress e) (i : Fin r) : R.Square :=
  ⟨e, i, a i, a (finRotate r i)⟩

noncomputable def responseRingSum (hr : 2 ≤ r) {beta : R.Block → Bit}
    (p : Fin r → (R.affine hr).Response beta) (t : T) (a : R.Address t) :
    Fin (R.dimension t) → Bit :=
  ∑ i, R.horizontal ((R.affine hr).responseValue (p i)) (R.siteRing t a i)

theorem horizontal_agree (hr : 2 ≤ r) {beta : R.Block → Bit}
    {p q : (R.affine hr).Response beta} (ha : (R.affine hr).Agree p q)
    (h : R.HName)
    (hp : ∀ j, Sum.inl ⟨h, j⟩ ∈ R.coordinates p.1)
    (hq : ∀ j, Sum.inl ⟨h, j⟩ ∈ R.coordinates q.1) :
    R.horizontal ((R.affine hr).responseValue p) h =
      R.horizontal ((R.affine hr).responseValue q) h := by
  funext j
  exact ha _ (hp j) (hq j)

/-- The actual responses of a square ring obey its summed equation. Verticals
cancel because adjacent stable marked squares agree on their shared bit. -/
theorem square_ring_sum (hr : 2 ≤ r) {beta : R.Block → Bit}
    {q : Fin r → (R.affine hr).Response beta} (hq : (R.affine hr).BlockWinning q)
    (e : L) (a : R.MatchAddress e)
    (hn : ∀ i, (q i).1 = .inr (R.squareRing e a i)) :
    R.firstForm e (∑ i, R.horizontal ((R.affine hr).responseValue (q i)) (R.leftH (R.squareRing e a i))) +
      R.secondForm e (∑ i, R.horizontal ((R.affine hr).responseValue (q i)) (R.rightH (R.squareRing e a i))) =
      R.linkShift beta e a := by
  classical
  let z (i : Fin r) := (R.affine hr).responseValue (q i)
  have hsq (i : Fin r) :
      R.firstForm e (R.horizontal (z i) (R.leftH (R.squareRing e a i))) +
      R.secondForm e (R.horizontal (z i) (R.rightH (R.squareRing e a i))) +
      R.vertical (z i) (R.topV (R.squareRing e a i)) +
      R.vertical (z i) (R.bottomV (R.squareRing e a i)) = beta (.inr (R.squareRing e a i)) := by
    have hh := (R.affine hr).response_legal (q i)
    rw [hn i] at hh
    exact hh rfl
  have hv (i : Fin r) : R.vertical (z i) (R.bottomV (R.squareRing e a i)) =
      R.vertical (z (finRotate r i)) (R.topV (R.squareRing e a (finRotate r i))) := by
    apply (R.affine hr).blockWinning_agree hr hq i (finRotate r i)
    · rw [hn i]
      exact R.bottom_mem _
    · rw [hn (finRotate r i)]
      exact R.top_mem _
  have hs := congrArg (fun f : Fin r → Bit => ∑ i, f i) (funext hsq)
  simp only [Finset.sum_add_distrib] at hs
  have hb : (∑ i, R.vertical (z i) (R.bottomV (R.squareRing e a i))) =
      ∑ i, R.vertical (z i) (R.topV (R.squareRing e a i)) := by
    simp_rw [hv]
    exact Equiv.sum_comp (finRotate r) (fun i : Fin r => R.vertical (z i) (R.topV (R.squareRing e a i)))
  rw [hb] at hs
  dsimp only [horizontal, leftH, rightH, squareRing] at hs ⊢
  rw [map_sum, map_sum]
  simpa only [z, add_assoc, CharTwo.add_self_eq_zero, add_zero, linkShift] using hs

/-- Site-ring images are defined by all stable responses, not by a selected
memoryless strategy or by a simultaneous choice of endpoint vectors. -/
def ImageSet (hr : 2 ≤ r) (beta : R.Block → Bit) (t : T) (a : R.Address t) :
    Set (Fin (R.dimension t) → Bit) :=
  {x | ∃ p : Fin r → (R.affine hr).Response beta,
    (R.affine hr).BlockWinning p ∧
    (∀ i, (p i).1 = .inl (R.siteRing t a i)) ∧ R.responseRingSum hr p t a = x}

theorem imageSet_nonempty (hr : 2 ≤ r) {beta : R.Block → Bit}
    (h : Equivalent r ((R.affine hr).graph 0) ((R.affine hr).graph beta)) (t : T) (a : R.Address t) :
    (R.ImageSet hr beta t a).Nonempty := by
  obtain ⟨p, hp, hn⟩ := (R.affine hr).blockWinning_exists hr h (fun i => .inl (R.siteRing t a i))
  exact ⟨_, p, hp, hn, rfl⟩

end RingLayout

namespace RingLayout
variable {r : ℕ} {T L : Type} [Fintype T] [Fintype L] (R : RingLayout r T L)

private theorem transfer_left_sums (hr : 2 ≤ r) {beta : R.Block → Bit}
    {p q : Fin r → (R.affine hr).Response beta} (e : L) (a : R.MatchAddress e)
    (hp : ∀ i, (p i).1 = .inl (R.siteRing (R.first e) (R.leftAddress e a) i))
    (hq : ∀ i, (q i).1 = .inr (R.squareRing e a i))
    (ha : ∀ i, (R.affine hr).Agree (p i) (q i)) :
    R.responseRingSum hr p (R.first e) (R.leftAddress e a) =
      ∑ i, R.horizontal ((R.affine hr).responseValue (q i)) (R.leftH (R.squareRing e a i)) := by
  apply Finset.sum_congr rfl
  intro i _
  apply R.horizontal_agree hr (ha i)
  · intro j
    rw [hp i]
    exact R.hCoord_mem _ j
  · intro j
    rw [hq i]
    exact R.left_mem (R.squareRing e a i) j

private theorem transfer_right_sums (hr : 2 ≤ r) {beta : R.Block → Bit}
    {p q : Fin r → (R.affine hr).Response beta} (e : L) (a : R.MatchAddress e)
    (hp : ∀ i, (p i).1 = .inl (R.siteRing (R.second e) (R.rightAddress e a) i))
    (hq : ∀ i, (q i).1 = .inr (R.squareRing e a i))
    (ha : ∀ i, (R.affine hr).Agree (p i) (q i)) :
    R.responseRingSum hr p (R.second e) (R.rightAddress e a) =
      ∑ i, R.horizontal ((R.affine hr).responseValue (q i)) (R.rightH (R.squareRing e a i)) := by
  apply Finset.sum_congr rfl
  intro i _
  apply R.horizontal_agree hr (ha i)
  · intro j
    rw [hp i]
    exact R.hCoord_mem _ j
  · intro j
    rw [hq i]
    exact R.right_mem (R.squareRing e a i) j

theorem imageSet_left_support (hr : 2 ≤ r) {beta : R.Block → Bit}
    (e : L) (a : R.MatchAddress e) {x : Fin (R.dimension (R.first e)) → Bit}
    (hx : x ∈ R.ImageSet hr beta (R.first e) (R.leftAddress e a)) :
    ∃ y ∈ R.ImageSet hr beta (R.second e) (R.rightAddress e a),
      R.firstForm e x + R.secondForm e y = R.linkShift beta e a := by
  classical
  obtain ⟨p, hp, hpn, hpx⟩ := hx
  obtain ⟨q, hq, hqn, hqa⟩ := (R.affine hr).blockWinning_transfer hr hp
    (fun i => .inr (R.squareRing e a i))
  obtain ⟨s, hs, hsn, hsa⟩ := (R.affine hr).blockWinning_transfer hr hq
    (fun i => .inl (R.siteRing (R.second e) (R.rightAddress e a) i))
  refine ⟨_, ⟨s, hs, hsn, rfl⟩, ?_⟩
  rw [← hpx, R.transfer_left_sums hr e a hpn hqn hqa,
    R.transfer_right_sums hr e a hsn hqn (fun i => (R.affine hr).agree_symm (hsa i))]
  exact R.square_ring_sum hr hq e a hqn

theorem imageSet_right_support (hr : 2 ≤ r) {beta : R.Block → Bit}
    (e : L) (a : R.MatchAddress e) {y : Fin (R.dimension (R.second e)) → Bit}
    (hy : y ∈ R.ImageSet hr beta (R.second e) (R.rightAddress e a)) :
    ∃ x ∈ R.ImageSet hr beta (R.first e) (R.leftAddress e a),
      R.firstForm e x + R.secondForm e y = R.linkShift beta e a := by
  classical
  obtain ⟨p, hp, hpn, hpy⟩ := hy
  obtain ⟨q, hq, hqn, hqa⟩ := (R.affine hr).blockWinning_transfer hr hp
    (fun i => .inr (R.squareRing e a i))
  obtain ⟨s, hs, hsn, hsa⟩ := (R.affine hr).blockWinning_transfer hr hq
    (fun i => .inl (R.siteRing (R.first e) (R.leftAddress e a) i))
  refine ⟨_, ⟨s, hs, hsn, rfl⟩, ?_⟩
  rw [← hpy, R.transfer_right_sums hr e a hpn hqn hqa,
    R.transfer_left_sums hr e a hsn hqn (fun i => (R.affine hr).agree_symm (hsa i))]
  exact R.square_ring_sum hr hq e a hqn

end RingLayout

end WLIdentification

end OAI
