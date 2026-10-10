import OAI.Computability.WLIdentification.ScalarExtension

namespace OAI

namespace WLIdentification

namespace ComparisonSchemas
variable {r : ℕ} {P E : Type} (S : ComparisonSchemas r P E)

/-- Cut an unused middle link on each private wire. End links need never be
removed: the private interior alone is longer than any small support. -/
def Avoids (n : ℕ) (U : Finset (S.layout n).Block) (cut : E → Fin n) : Prop :=
  ∀ e, Sum.inr (Sum.inl (e, cut e)) ∉ (S.layout n).usedLinks U

theorem exists_cuts (n : ℕ) (U : Finset (S.layout n).Block) (hu : U.card < n) :
    ∃ cut : E → Fin n, S.Avoids n U cut := by
  classical
  have hex (e : E) : ∃ i : Fin n, Sum.inr (Sum.inl (e, i)) ∉ (S.layout n).usedLinks U := by
    by_contra h
    have hall : ∀ i : Fin n, Sum.inr (Sum.inl (e, i)) ∈ (S.layout n).usedLinks U := by
      simpa only [not_exists, not_not] using h
    have hs : Finset.univ.image (fun i : Fin n => (Sum.inr (Sum.inl (e, i)) : S.Link n)) ⊆
        (S.layout n).usedLinks U := by
      intro l hl
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hl
      exact hall i
    have hinj : Function.Injective (fun i : Fin n => (Sum.inr (Sum.inl (e, i)) : S.Link n)) := by
      intro i j hij
      exact (Prod.mk.inj (Sum.inl.inj (Sum.inr.inj hij))).2
    have hc := Finset.card_le_card hs
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] at hc
    have hb := (S.layout n).usedLinks_card U
    omega
  choose cut hc using hex
  exact ⟨cut, hc⟩

def root (n : ℕ) (cut : E → Fin n) : S.InternalType n → P
  | .inl p => p
  | .inr (e, i) => if i.val ≤ (cut e).val then S.source e else S.target e

def onLeft (_S : ComparisonSchemas r P E) (n : ℕ) (cut : E → Fin n) (e : E) (i : Fin (n + 1)) : Prop :=
  i.val ≤ (cut e).val

instance (n : ℕ) (cut : E → Fin n) (e : E) (i : Fin (n + 1)) :
    Decidable (S.onLeft n cut e i) := inferInstanceAs (Decidable (i.val ≤ (cut e).val))

theorem cut_middle {n : ℕ} {cut : E → Fin n} {e : E} {i : Fin n} (hi : i ≠ cut e) :
    S.onLeft n cut e i.castSucc ↔ S.onLeft n cut e i.succ := by
  have hne : i.val ≠ (cut e).val := fun h => hi (Fin.ext h)
  dsimp only [onLeft, Fin.val_castSucc, Fin.val_succ]
  omega

theorem root_link {n : ℕ} {U : Finset (S.layout n).Block} {cut : E → Fin n}
    (hc : S.Avoids n U cut) {l : S.Link n} (hl : l ∈ (S.layout n).usedLinks U) :
    S.root n cut (S.first n l) = S.root n cut (S.second n l) := by
  cases l with
  | inl e => simp [root, first, second]
  | inr l => cases l with
    | inl ei =>
      obtain ⟨e, i⟩ := ei
      have hi : i ≠ cut e := fun hi => hc e (hi ▸ hl)
      dsimp only [root, first, second]
      have hm := S.cut_middle hi
      dsimp only [onLeft] at hm
      simp only [hm]
    | inr e =>
      have hn := (cut e).isLt
      simp [root, first, second, show ¬n ≤ (cut e).val by omega]

/-- Every injective partial binary coordinate map extends to a permutation.
This lemma preserves singleton domains rather than silently enlarging them. -/
theorem binary_extension (A : Finset Bool) (hA : A.Nonempty)
    (f : {a // a ∈ A} → Bool) (hf : Function.Injective f) :
    ∃ p : Equiv.Perm Bool, ∀ a, p a.val = f a := by
  classical
  obtain ⟨x, hx⟩ := hA
  let a0 : {a // a ∈ A} := ⟨x, hx⟩
  let flip : Equiv.Perm Bool := ⟨Bool.not, Bool.not, Bool.not_not, Bool.not_not⟩
  by_cases he : f a0 = x
  · refine ⟨Equiv.refl Bool, ?_⟩
    intro a
    change a.val = f a
    by_cases ha : a = a0
    · subst a; exact he.symm
    · have hav : a.val ≠ x := fun h => ha (Subtype.ext h)
      have hfa : f a ≠ f a0 := fun h => ha (hf h)
      rw [he] at hfa
      cases hval : a.val <;> cases hfx : f a <;> cases x <;> simp_all
  · refine ⟨flip, ?_⟩
    intro a
    change (!a.val) = f a
    by_cases ha : a = a0
    · subst a
      dsimp only [a0]
      cases hfx : f ⟨x, hx⟩ <;> cases x <;> simp_all [a0]
    · have hav : a.val ≠ x := fun h => ha (Subtype.ext h)
      have hfa : f a ≠ f a0 := fun h => ha (hf h)
      cases hval : a.val <;> cases hfx : f a <;> cases hf0 : f a0 <;> cases x <;> simp_all

noncomputable def permutation (e : E) (i : Fin r) : Equiv.Perm Bool :=
  (binary_extension (S.domain e i) (S.domain_nonempty e i)
    (S.mapping e i) (S.mapping_injective e i)).choose

theorem permutation_apply (e : E) (i : Fin r) (a : {a // a ∈ S.domain e i}) :
    S.permutation e i a.val = S.mapping e i a :=
  (binary_extension (S.domain e i) (S.domain_nonempty e i)
    (S.mapping e i) (S.mapping_injective e i)).choose_spec a

noncomputable def align (n : ℕ) (cut : E → Fin n) : (S.layout n).Corner → Bool
  | ⟨.inl _, _, a⟩ => a.val
  | ⟨.inr (e, j), i, a⟩ => if S.onLeft n cut e j then a.val else S.permutation e i a.val

theorem align_link {n : ℕ} {U : Finset (S.layout n).Block} {cut : E → Fin n}
    (hc : S.Avoids n U cut) {l : S.Link n} (hl : l ∈ (S.layout n).usedLinks U)
    (i : Fin r) (a : (S.layout n).Match l i) :
    S.align n cut ((S.layout n).nameFirst (.inr ⟨l, i, a⟩)) =
    S.align n cut ((S.layout n).nameSecond (.inr ⟨l, i, a⟩)) := by
  cases l with
  | inl e =>
    change a.val = (if 0 ≤ (cut e).val then a.val else S.permutation e i a.val)
    rw [ite_eq_left (Nat.zero_le _)]
  | inr l => cases l with
    | inl ei =>
      obtain ⟨e, j⟩ := ei
      have hj : j ≠ cut e := fun he => hc e (he ▸ hl)
      change (if S.onLeft n cut e j.castSucc then a.val else S.permutation e i a.val) =
        (if S.onLeft n cut e j.succ then a.val else S.permutation e i a.val)
      simp only [S.cut_middle hj]
    | inr e =>
      change (if n ≤ (cut e).val then a.val else S.permutation e i a.val) = S.mapping e i a
      rw [ite_eq_right (Nat.not_le.mpr (cut e).isLt)]
      exact S.permutation_apply e i a

end ComparisonSchemas

namespace RingLayout
variable {r : ℕ} {T L : Type} (R : RingLayout r T L)

theorem vertical_usedLink {U : Finset R.Block} {v : R.VName}
    (hv : Sum.inr v ∈ R.names U) : v.1 ∈ R.usedLinks U := by
  classical
  obtain ⟨b, hb, hn⟩ := Finset.mem_biUnion.mp hv
  cases b with
  | inl b => simp [blockNames] at hn
  | inr b =>
    simp only [blockNames, Finset.mem_insert, Finset.mem_singleton, Sum.inr_ne_inl,
      Sum.inr.injEq, false_or] at hn
    rcases hn with rfl | rfl <;> exact R.mem_usedLinks.mpr ⟨b, hb, rfl⟩

abbrev Shift := (t : T) → Fin (R.dimension t) → Bit
abbrev Potential := (c : R.Corner) → Fin (R.dimension c.1) → Bit

def potentialHorizontal (h : R.Shift) (M : R.Potential) : R.Horizontal :=
  fun x => M ⟨x.1, x.2.1, x.2.2.1⟩ + M ⟨x.1, finRotate r x.2.1, x.2.2.2⟩ + Marker.delta x.2.1 • h x.1

def potentialVertical (M : R.Potential) : R.Vertical :=
  fun x => R.firstForm x.1 (M (R.nameFirst (.inr x))) +
    R.secondForm x.1 (M (R.nameSecond (.inr x)))

def translation (h : R.Shift) (M : R.Potential) : R.Coordinate → Bit :=
  R.pack (R.potentialHorizontal h M) (R.potentialVertical M)

/-- The potential terms cancel on every square, leaving only its row marker
multiplied by the affine link-shift equation. -/
theorem translation_square (h : R.Shift) (M : R.Potential) (b : R.Square) :
    R.firstForm b.1 (R.horizontal (R.translation h M) (R.leftH b)) +
      R.secondForm b.1 (R.horizontal (R.translation h M) (R.rightH b)) +
      R.vertical (R.translation h M) (R.topV b) +
      R.vertical (R.translation h M) (R.bottomV b) =
    Marker.delta b.2.1 * (R.firstForm b.1 (h (R.first b.1)) +
      R.secondForm b.1 (h (R.second b.1))) := by
  have hh : R.horizontal (R.translation h M) = R.potentialHorizontal h M := rfl
  have hv : R.vertical (R.translation h M) = R.potentialVertical M := rfl
  rw [hh, hv]
  dsimp only [potentialHorizontal, potentialVertical, leftH, rightH, topV,
    bottomV, nameFirst, nameSecond]
  simp only [map_add, map_smul, smul_eq_mul]
  ring_nf
  simp only [show (2 : Bit) = 0 by decide, mul_zero, zero_add, add_zero]

end RingLayout

namespace ComparisonSchemas
variable {r : ℕ} {P E : Type} (S : ComparisonSchemas r P E)

theorem align_aligned {n : ℕ} {U : Finset (S.layout n).Block} {cut : E → Fin n}
    (hc : S.Avoids n U cut) : (S.layout n).Aligned U (S.align n cut) := by
  intro v hv
  exact S.align_link hc ((S.layout n).vertical_usedLink hv) v.2.1 v.2.2

theorem root_edge {n : ℕ} {U : Finset (S.layout n).Block} {cut : E → Fin n}
    (hc : S.Avoids n U cut) (hr : 2 ≤ r) {u v : (S.layout n).Corner}
    (huv : ((S.layout n).cornerGraph hr U).Adj u v) :
    S.root n cut u.1 = S.root n cut v.1 := by
  obtain ⟨x, hx, hh⟩ := huv
  cases x with
  | inl x => rcases hh with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  | inr x =>
    have he := S.root_link hc ((S.layout n).vertical_usedLink hx)
    rcases hh with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact he
    · exact he.symm

theorem root_reachable {n : ℕ} {U : Finset (S.layout n).Block} {cut : E → Fin n}
    (hc : S.Avoids n U cut) (hr : 2 ≤ r) {u v : (S.layout n).Corner}
    (huv : ((S.layout n).cornerGraph hr U).Reachable u v) :
    S.root n cut u.1 = S.root n cut v.1 := by
  obtain ⟨p⟩ := huv
  induction p with
  | nil => rfl
  | cons h p ih => exact (S.root_edge hc hr h).trans ih

abbrev RealShift := (p : P) → Fin (S.dimension p) → Bit

def linkConstant (n : ℕ) (b : E → Bit) : S.Link n → Bit
  | .inl _ => 0
  | .inr (.inl _) => 0
  | .inr (.inr e) => b e

def specialTwist (n : ℕ) (b : E → Bit) : (S.layout n).Block → Bit
  | .inl _ => 0
  | .inr q => Marker.delta q.2.1 * S.linkConstant n b q.1

/-- Completing the cut layout to rooted stars gives a uniform affine shift.
The real vectors may be arbitrary; internal values are constant on each arm. -/
def starShift (n : ℕ) (cut : E → Fin n) (b : E → Bit) (q : S.RealShift) : (S.layout n).Shift
  | .inl p => q p
  | .inr (e, i) => fun _ => if S.onLeft n cut e i then S.left e (q (S.source e))
      else b e + S.right e (q (S.target e))

theorem starShift_link {n : ℕ} {U : Finset (S.layout n).Block} {cut : E → Fin n}
    (hc : S.Avoids n U cut) (b : E → Bit) (q : S.RealShift)
    {l : S.Link n} (hl : l ∈ (S.layout n).usedLinks U) :
    (S.layout n).firstForm l (S.starShift n cut b q ((S.layout n).first l)) +
      (S.layout n).secondForm l (S.starShift n cut b q ((S.layout n).second l)) =
      S.linkConstant n b l := by
  cases l with
  | inl e =>
    change S.left e (q (S.source e)) +
      (if 0 ≤ (cut e).val then S.left e (q (S.source e)) else b e + S.right e (q (S.target e))) = 0
    rw [ite_eq_left (Nat.zero_le _), CharTwo.add_self_eq_zero]
  | inr l => cases l with
    | inl ei =>
      obtain ⟨e, i⟩ := ei
      have hi : i ≠ cut e := fun he => hc e (he ▸ hl)
      change (if S.onLeft n cut e i.castSucc then S.left e (q (S.source e)) else b e + S.right e (q (S.target e))) +
        (if S.onLeft n cut e i.succ then S.left e (q (S.source e)) else b e + S.right e (q (S.target e))) = 0
      simp only [S.cut_middle hi, CharTwo.add_self_eq_zero]
    | inr e =>
      change (if n ≤ (cut e).val then S.left e (q (S.source e)) else b e + S.right e (q (S.target e))) +
        S.right e (q (S.target e)) = b e
      rw [ite_eq_right (Nat.not_le.mpr (cut e).isLt), add_assoc, CharTwo.add_self_eq_zero, add_zero]

variable [Fintype P] [Fintype E]

theorem translation_legal {n : ℕ} {U : Finset (S.layout n).Block} {cut : E → Fin n}
    (hc : S.Avoids n U cut) (hr : 2 ≤ r) (b : E → Bit) (q : S.RealShift)
    (M : (S.layout n).Potential) {a : (S.layout n).Block} (ha : a ∈ U) :
    ((S.layout n).affine hr).Legal (S.specialTwist n b) a
      (((S.layout n).affine hr).restrict a ((S.layout n).translation (S.starShift n cut b q) M)) := by
  cases a with
  | inl a => intro hh; cases hh
  | inr a =>
    intro _
    change (S.layout n).squareForm a (fun c => (S.layout n).translation (S.starShift n cut b q) M c.val) = _
    rw [RingLayout.squareForm_apply]
    change (S.layout n).firstForm a.1
      ((S.layout n).horizontal ((S.layout n).translation (S.starShift n cut b q) M) ((S.layout n).leftH a)) +
      (S.layout n).secondForm a.1
      ((S.layout n).horizontal ((S.layout n).translation (S.starShift n cut b q) M) ((S.layout n).rightH a)) +
      (S.layout n).vertical ((S.layout n).translation (S.starShift n cut b q) M) ((S.layout n).topV a) +
      (S.layout n).vertical ((S.layout n).translation (S.starShift n cut b q) M) ((S.layout n).bottomV a) = _
    rw [RingLayout.translation_square, S.starShift_link hc b q ((S.layout n).mem_usedLinks.mpr ⟨a, ha, rfl⟩)]
    rfl

end ComparisonSchemas

namespace RingLayout
variable {r : ℕ} {T L : Type} (R : RingLayout r T L)

def coordinateName : R.Coordinate → R.Name
  | .inl h => .inl h.1
  | .inr v => .inr v

theorem coordinate_name_mem {b : R.Block} {c : R.Coordinate}
    (hc : c ∈ R.coordinates b) : R.coordinateName c ∈ R.blockNames b := by
  classical
  cases b with
  | inl h =>
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_singleton_self _
  | inr b =>
    simp only [coordinates, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with (hh | hh) | hh | hh
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hh
      simp [coordinateName, blockNames]
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hh
      simp [coordinateName, blockNames]
    · subst c
      simp [coordinateName, blockNames]
    · subst c
      simp [coordinateName, blockNames]

theorem cornerMarker_symm (hr : 3 ≤ r) {U : Finset R.Block} {u v : R.Corner}
    (h : (R.cornerGraph (by omega) U).Adj u v) : R.cornerMarker u v = R.cornerMarker v u := by
  obtain ⟨n, _, h⟩ := h
  cases n with
  | inl n =>
    obtain ⟨h1, h2⟩ := R.cornerMarker_horizontal hr n
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h1.trans h2.symm
    · exact h2.trans h1.symm
  | inr n =>
    obtain ⟨h1, h2⟩ := R.cornerMarker_vertical n
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h1.trans h2.symm
    · exact h2.trans h1.symm

theorem nonwrapping_exact (hr : 3 ≤ r) {U : Finset R.Block}
    (hw : ¬R.Wrapping (by omega) U) :
    ∃ s : R.Corner → Bit, ∀ n ∈ R.names U,
      R.cornerMarker (R.nameFirst n) (R.nameSecond n) = s (R.nameFirst n) + s (R.nameSecond n) := by
  have hc : ∀ u (p : (R.cornerGraph (by omega) U).Walk u u), Marker.walkSum R.cornerMarker p = 0 := by
    intro u p
    have hb : ∀ x : Bit, x = 0 ∨ x = 1 := by intro x; fin_cases x <;> (first | exact Or.inl rfl | exact Or.inr rfl)
    rcases hb (Marker.walkSum R.cornerMarker p) with h | h
    · exact h
    · exact (hw ⟨u, p, h⟩).elim
  obtain ⟨s, hs⟩ := Marker.exact_of_closed_zero R.cornerMarker
    (fun _ _ h => R.cornerMarker_symm hr h) hc
  exact ⟨s, fun n hn => hs _ _ ⟨n, hn, Or.inl ⟨rfl, rfl⟩⟩⟩

/-- On a nonwrapping support any two shifts with the same affine link equations
induce the same offset family after a potential adjustment. -/
theorem adjust_potential (hr : 3 ≤ r) {U : Finset R.Block}
    (hw : ¬R.Wrapping (by omega) U) (old new : R.Shift) (M : R.Potential)
    (he : ∀ l ∈ R.usedLinks U,
      R.firstForm l (old (R.first l)) + R.secondForm l (old (R.second l)) =
      R.firstForm l (new (R.first l)) + R.secondForm l (new (R.second l))) :
    ∃ N : R.Potential, ∀ b ∈ U, ∀ c ∈ R.coordinates b,
      R.translation new N c = R.translation old M c := by
  classical
  obtain ⟨s, hs⟩ := R.nonwrapping_exact hr hw
  let N : R.Potential := fun c => M c + s c • (new c.1 + old c.1)
  have hh {h : R.HName} (hh : Sum.inl h ∈ R.names U) :
      R.potentialHorizontal new N h = R.potentialHorizontal old M h := by
    have hm := (R.cornerMarker_horizontal hr h).1.symm.trans (hs (.inl h) hh)
    exact Marker.horizontal_adjust (M (R.nameFirst (.inl h))) (M (R.nameSecond (.inl h)))
      (old h.1) (new h.1) (s (R.nameFirst (.inl h))) (s (R.nameSecond (.inl h)))
      (Marker.delta h.2.1) hm.symm
  have hv {v : R.VName} (hv : Sum.inr v ∈ R.names U) :
      R.potentialVertical N v = R.potentialVertical M v := by
    have hm := (R.cornerMarker_vertical v).1.symm.trans (hs (.inr v) hv)
    have hst : s (R.nameFirst (.inr v)) = s (R.nameSecond (.inr v)) := by
      calc
        _ = s (R.nameFirst (.inr v)) + (s (R.nameFirst (.inr v)) + s (R.nameSecond (.inr v))) := by rw [← hm, add_zero]
        _ = _ := by rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    have hl := he v.1 (R.vertical_usedLink hv)
    have he' : R.firstForm v.1 (new (R.first v.1) + old (R.first v.1)) +
        R.secondForm v.1 (new (R.second v.1) + old (R.second v.1)) = 0 := by
      rw [map_add, map_add]
      calc
        _ = (R.firstForm v.1 (new (R.first v.1)) + R.secondForm v.1 (new (R.second v.1))) +
            (R.firstForm v.1 (old (R.first v.1)) + R.secondForm v.1 (old (R.second v.1))) := by abel
        _ = 0 := by rw [hl, CharTwo.add_self_eq_zero]
    exact Marker.vertical_adjust (R.firstForm v.1) (R.secondForm v.1)
      (M (R.nameFirst (.inr v))) (M (R.nameSecond (.inr v)))
      (new (R.first v.1) + old (R.first v.1)) (new (R.second v.1) + old (R.second v.1))
      (s (R.nameFirst (.inr v))) (s (R.nameSecond (.inr v))) hst he'
  refine ⟨N, ?_⟩
  intro b hb c hc
  have hn := R.name_present hb (R.coordinate_name_mem hc)
  cases c with
  | inl h => exact congrFun (hh hn) h.2
  | inr v => exact hv hn

end RingLayout

namespace ComparisonSchemas
variable {r : ℕ} {P E : Type} (S : ComparisonSchemas r P E)

def GoodAddress (n : ℕ) (hr : 2 ≤ r) (U : Finset (S.layout n).Block)
    (cut : E → Fin n) (a : Fin r → Bool) : Prop :=
  ∀ V ⊆ U, V.card ≤ r → (S.layout n).Wrapping hr V →
    (S.layout n).IsWrappingAddress V (S.align n cut) a

theorem goodAddress_exists (n : ℕ) (hr : 3 ≤ r) {U : Finset (S.layout n).Block}
    (hu : U.card ≤ r + 1) {cut : E → Fin n} (hc : S.Avoids n U cut) :
    ∃ a, S.GoodAddress n (by omega) U cut a := by
  classical
  by_cases hw : ∃ V ⊆ U, V.card ≤ r ∧ (S.layout n).Wrapping (by omega) V
  · obtain ⟨V, hV, hv, hwV⟩ := hw
    obtain ⟨a, ha, _⟩ := (S.layout n).wrapping_address hr hwV hv
      ((S.layout n).aligned_mono hV (S.align_aligned hc))
    refine ⟨a, ?_⟩
    intro W hW hw' hww
    obtain ⟨a', ha', _⟩ := (S.layout n).wrapping_address hr hww hw'
      ((S.layout n).aligned_mono hW (S.align_aligned hc))
    have he := (S.layout n).wrapping_addresses_agree hr hV hW hu hwV hww ha ha'
    exact he ▸ ha'
  · exact ⟨fun _ => false, fun V hV hv hwV => (hw ⟨V, hV, hv, hwV⟩).elim⟩

theorem avoids_mono {n : ℕ} {V U : Finset (S.layout n).Block} (h : V ⊆ U)
    {cut : E → Fin n} (hc : S.Avoids n U cut) : S.Avoids n V cut := by
  intro e he
  obtain ⟨b, hb, hb'⟩ := (S.layout n).mem_usedLinks.mp he
  exact hc e ((S.layout n).mem_usedLinks.mpr ⟨b, h hb, hb'⟩)

theorem goodAddress_mono {n : ℕ} {hr : 2 ≤ r} {V U : Finset (S.layout n).Block}
    (h : V ⊆ U) {cut : E → Fin n} {a : Fin r → Bool}
    (ha : S.GoodAddress n hr U cut a) : S.GoodAddress n hr V cut a :=
  fun W hW => ha W (hW.trans h)

end ComparisonSchemas

end WLIdentification

end OAI
