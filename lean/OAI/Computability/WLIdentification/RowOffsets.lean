import OAI.Computability.WLIdentification.AffineTranslations

namespace OAI

namespace WLIdentification

namespace CycleRows

/-- The row-sum restriction is retained explicitly; pointwise globally consistent
address values alone are not used as a substitute for actual readout offsets. -/
def RowSum {r : ℕ} (A : Fin r → Type) (V : Type) [AddCommMonoid V]
    (h : ((i : Fin r) → A i) → V) : Prop :=
  ∃ f : (i : Fin r) → A i → A (finRotate r i) → V,
    ∀ a, h a = ∑ i, f i (a i) (a (finRotate r i))

namespace RowSum
variable {r : ℕ} {A : Fin r → Type} {V W : Type} [AddCommMonoid V] [AddCommMonoid W]

protected theorem zero : RowSum A V (fun _ => 0) := ⟨fun _ _ _ => 0, by simp⟩

protected theorem add {h g : ((i : Fin r) → A i) → V}
    (hh : RowSum A V h) (hg : RowSum A V g) : RowSum A V (fun a => h a + g a) := by
  obtain ⟨f, hf⟩ := hh
  obtain ⟨g, hg⟩ := hg
  exact ⟨fun i u v => f i u v + g i u v, fun a => by
    dsimp only
    rw [Finset.sum_add_distrib, hf, hg]⟩

protected theorem map {h : ((i : Fin r) → A i) → V}
    (hh : RowSum A V h) (L : V →+ W) : RowSum A W (fun a => L (h a)) := by
  obtain ⟨f, hf⟩ := hh
  exact ⟨fun i u v => L (f i u v), fun a => by dsimp only; rw [hf, map_sum]⟩

protected theorem pullback {A' : Fin r → Type} {h : ((i : Fin r) → A i) → V}
    (hh : RowSum A V h) (f : (i : Fin r) → A' i → A i) :
    RowSum A' V (fun a => h (fun i => f i (a i))) := by
  obtain ⟨g, hg⟩ := hh
  exact ⟨fun i u v => g i (f i u) (f (finRotate r i) v), fun a => hg _⟩

protected theorem constant (hr : 0 < r) (v : V) : RowSum A V (fun _ => v) := by
  classical
  let j : Fin r := ⟨0, hr⟩
  refine ⟨fun i _ _ => if i = j then v else 0, ?_⟩
  intro a
  simp

/-- Extending the adjacent-coordinate terms, not an arbitrary full-address
function, gives the extension on a product subdomain used by private buffers. -/
theorem extend {A' : Fin r → Type} {h : ((i : Fin r) → A i) → V}
    (hh : RowSum A V h) (f : (i : Fin r) → A i → A' i)
    (hf : ∀ i, Function.Injective (f i)) :
    ∃ h', RowSum A' V h' ∧ ∀ a, h' (fun i => f i (a i)) = h a := by
  classical
  obtain ⟨g, hg⟩ := hh
  let F (i : Fin r) : (A i × A (finRotate r i)) → (A' i × A' (finRotate r i)) :=
    Prod.map (f i) (f (finRotate r i))
  have hF (i : Fin r) : Function.Injective (F i) := by
    intro p q hp
    exact Prod.ext (hf i (congrArg Prod.fst hp))
      (hf (finRotate r i) (congrArg Prod.snd hp))
  let g' (i : Fin r) := Function.extend (F i) (fun p => g i p.1 p.2) (fun _ => (0 : V))
  refine ⟨fun a => ∑ i, g' i (a i, a (finRotate r i)),
    ⟨fun i u v => g' i (u, v), fun _ => rfl⟩, ?_⟩
  intro a
  rw [hg]
  apply Finset.sum_congr rfl
  intro i _
  exact (hF i).extend_apply _ _ (a i, a (finRotate r i))

end RowSum

/-- One link, with arbitrary nonempty coordinate match domains, has legal
vertical offsets exactly when the horizontal ring sums have the required shift.
This is the local-to-global step used independently on every private wire link. -/
theorem square_lifting {r : ℕ} (hr : 3 ≤ r) (A : Fin r → Type)
    (base : (i : Fin r) → A i)
    (left right beta : (i : Fin r) → A i → A (finRotate r i) → Bit) :
    (∃ y : (i : Fin r) → A i → Bit, ∀ i u v,
      left i u v + right i u v + y i u + y (finRotate r i) v = beta i u v) ↔
    ∀ a : (i : Fin r) → A i,
      (∑ i, left i (a i) (a (finRotate r i))) +
        (∑ i, right i (a i) (a (finRotate r i))) =
      ∑ i, beta i (a i) (a (finRotate r i)) := by
  constructor
  · rintro ⟨y, hy⟩ a
    have hh := congrArg (fun f : Fin r → Bit => ∑ i, f i)
      (funext (fun i => hy i (a i) (a (finRotate r i))))
    simp only [Finset.sum_add_distrib] at hh
    rw [Equiv.sum_comp (finRotate r) (fun i => y i (a i))] at hh
    simpa only [add_assoc, CharTwo.add_self_eq_zero, add_zero] using hh
  · intro h
    let g (i : Fin r) (u : A i) (v : A (finRotate r i)) :=
      left i u v + right i u v + beta i u v
    have hg (a : (i : Fin r) → A i) : ∑ i, g i (a i) (a (finRotate r i)) = 0 := by
      dsimp only [g]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, h a, CharTwo.add_self_eq_zero]
    obtain ⟨y, hy⟩ := cycle_lifting hr A g base hg
    refine ⟨y, ?_⟩
    intro i u v
    have he := hy i u v
    dsimp only [g] at he
    calc
      left i u v + right i u v + y i u + y (finRotate r i) v =
          (left i u v + right i u v) + (y i u + y (finRotate r i) v) := by abel
      _ = beta i u v := by
        rw [← he]
        calc
          _ = ((left i u v + right i u v) + (left i u v + right i u v)) + beta i u v := by abel
          _ = beta i u v := by rw [CharTwo.add_self_eq_zero, zero_add]

end CycleRows

structure RingLayout (r : ℕ) (T L : Type) where
  typeIndex : T ↪ ℕ
  linkIndex : L ↪ ℕ
  dimension : T → ℕ
  dimension_bound : ∀ t, dimension t = 1 ∨ dimension t = 2
  labels : T → Fin r → Finset Bool
  labels_nonempty : ∀ t i, (labels t i).Nonempty
  first : L → T
  second : L → T
  endpoints_ne : ∀ e, first e ≠ second e
  internal_endpoint : ∀ e, dimension (first e) = 1 ∨ dimension (second e) = 1
  matchLabels : L → Fin r → Finset Bool
  matchLabels_nonempty : ∀ e i, (matchLabels e i).Nonempty
  firstLabel : (e : L) → (i : Fin r) → {a // a ∈ matchLabels e i} → {a // a ∈ labels (first e) i}
  secondLabel : (e : L) → (i : Fin r) → {a // a ∈ matchLabels e i} → {a // a ∈ labels (second e) i}
  firstLabel_injective : ∀ e i, Function.Injective (firstLabel e i)
  secondLabel_injective : ∀ e i, Function.Injective (secondLabel e i)
  firstForm : (e : L) → (Fin (dimension (first e)) → Bit) →ₗ[Bit] Bit
  secondForm : (e : L) → (Fin (dimension (second e)) → Bit) →ₗ[Bit] Bit

namespace RingLayout
variable {r : ℕ} {T L : Type} (R : RingLayout r T L)

abbrev Label (t : T) (i : Fin r) := {a // a ∈ R.labels t i}
abbrev Match (e : L) (i : Fin r) := {a // a ∈ R.matchLabels e i}
abbrev HName := Σ t : T, Σ i : Fin r, R.Label t i × R.Label t (finRotate r i)
abbrev VName := Σ e : L, Σ i : Fin r, R.Match e i
abbrev Square := Σ e : L, Σ i : Fin r, R.Match e i × R.Match e (finRotate r i)
abbrev Coordinate := (Σ h : R.HName, Fin (R.dimension h.1)) ⊕ R.VName
abbrev Block := R.HName ⊕ R.Square

def leftH (b : R.Square) : R.HName :=
  ⟨R.first b.1, b.2.1, R.firstLabel b.1 b.2.1 b.2.2.1,
    R.firstLabel b.1 (finRotate r b.2.1) b.2.2.2⟩

def rightH (b : R.Square) : R.HName :=
  ⟨R.second b.1, b.2.1, R.secondLabel b.1 b.2.1 b.2.2.1,
    R.secondLabel b.1 (finRotate r b.2.1) b.2.2.2⟩

def topV (b : R.Square) : R.VName := ⟨b.1, b.2.1, b.2.2.1⟩
def bottomV (b : R.Square) : R.VName := ⟨b.1, finRotate r b.2.1, b.2.2.2⟩

theorem vertical_ne (hr : 2 ≤ r) (b : R.Square) : R.topV b ≠ R.bottomV b := by
  intro h
  have hi : b.2.1 = finRotate r b.2.1 := congrArg (fun v : R.VName => v.2.1) h
  exact CycleRows.rotate_ne_self hr _ hi.symm

theorem horizontal_ne (b : R.Square) : R.leftH b ≠ R.rightH b := by
  intro h
  exact R.endpoints_ne b.1 (congrArg Sigma.fst h)

noncomputable instance coordinateDecidableEq : DecidableEq R.Coordinate := Classical.decEq _
noncomputable instance blockDecidableEq : DecidableEq R.Block := Classical.decEq _

noncomputable def hCoords (h : R.HName) : Finset R.Coordinate := by
  classical
  exact Finset.univ.image (fun j => Sum.inl ⟨h, j⟩)

noncomputable def coordinates : R.Block → Finset R.Coordinate
  | .inl h => R.hCoords h
  | .inr b => R.hCoords (R.leftH b) ∪ R.hCoords (R.rightH b) ∪
      {Sum.inr (R.topV b), Sum.inr (R.bottomV b)}

theorem hCoord_mem (h : R.HName) (j : Fin (R.dimension h.1)) :
    Sum.inl ⟨h, j⟩ ∈ R.hCoords h := by
  classical
  exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩

theorem left_mem (b : R.Square) (j : Fin (R.dimension (R.first b.1))) :
    Sum.inl ⟨R.leftH b, j⟩ ∈ R.coordinates (.inr b) := by
  classical
  exact Finset.mem_union_left _ (Finset.mem_union_left _ (R.hCoord_mem (R.leftH b) j))

theorem right_mem (b : R.Square) (j : Fin (R.dimension (R.second b.1))) :
    Sum.inl ⟨R.rightH b, j⟩ ∈ R.coordinates (.inr b) := by
  classical
  exact Finset.mem_union_left _ (Finset.mem_union_right _ (R.hCoord_mem (R.rightH b) j))

theorem top_mem (b : R.Square) : Sum.inr (R.topV b) ∈ R.coordinates (.inr b) := by
  classical
  exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)

theorem bottom_mem (b : R.Square) : Sum.inr (R.bottomV b) ∈ R.coordinates (.inr b) := by
  classical
  exact Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

def localProj (b : R.Block) (c : R.Coordinate) (hc : c ∈ R.coordinates b) :
    ((a : R.coordinates b) → Bit) →ₗ[Bit] Bit := LinearMap.proj ⟨c, hc⟩

noncomputable def squareForm (b : R.Square) :
    ((c : R.coordinates (.inr b)) → Bit) →ₗ[Bit] Bit :=
  (R.firstForm b.1).comp (LinearMap.pi (fun j => R.localProj _ _ (R.left_mem b j))) +
  (R.secondForm b.1).comp (LinearMap.pi (fun j => R.localProj _ _ (R.right_mem b j))) +
  R.localProj _ _ (R.top_mem b) + R.localProj _ _ (R.bottom_mem b)

theorem squareForm_apply (b : R.Square) (x : (c : R.coordinates (.inr b)) → Bit) :
    R.squareForm b x =
      R.firstForm b.1 (fun j => x ⟨_, R.left_mem b j⟩) +
      R.secondForm b.1 (fun j => x ⟨_, R.right_mem b j⟩) +
      x ⟨_, R.top_mem b⟩ + x ⟨_, R.bottom_mem b⟩ := rfl

theorem squareForm_nonzero (hr : 2 ≤ r) (b : R.Square) : R.squareForm b ≠ 0 := by
  classical
  let c : R.coordinates (.inr b) := ⟨.inr (R.topV b), R.top_mem b⟩
  let x : (a : R.coordinates (.inr b)) → Bit := Pi.single c 1
  have hl : (fun j => x ⟨_, R.left_mem b j⟩) = 0 := by
    funext j
    apply Pi.single_eq_of_ne
    intro hh
    have := congrArg Subtype.val hh
    cases this
  have hu : (fun j => x ⟨_, R.right_mem b j⟩) = 0 := by
    funext j
    apply Pi.single_eq_of_ne
    intro hh
    have := congrArg Subtype.val hh
    cases this
  have hb : x ⟨_, R.bottom_mem b⟩ = 0 := by
    apply Pi.single_eq_of_ne
    intro hh
    exact R.vertical_ne hr b (Sum.inr.inj (congrArg Subtype.val hh)).symm
  have hx : R.squareForm b x = 1 := by
    rw [R.squareForm_apply, hl, hu, map_zero, map_zero, hb]
    change 0 + 0 + (Pi.single c (1 : Bit) : (a : R.coordinates (.inr b)) → Bit) c + 0 = 1
    simp
  intro h
  rw [h, LinearMap.zero_apply] at hx
  exact zero_ne_one hx

variable [Fintype T] [Fintype L]

def hIndex : R.HName ↪ ℕ :=
  NaturalCode.sigma R.typeIndex (fun _ => NaturalCode.sigma (NaturalCode.fin r) (fun _ =>
    NaturalCode.prod (NaturalCode.subtype NaturalCode.bool _) (NaturalCode.subtype NaturalCode.bool _)))

def vIndex : R.VName ↪ ℕ :=
  NaturalCode.sigma R.linkIndex (fun _ => NaturalCode.sigma (NaturalCode.fin r) (fun _ =>
    NaturalCode.subtype NaturalCode.bool _))

def squareIndex : R.Square ↪ ℕ :=
  NaturalCode.sigma R.linkIndex (fun _ => NaturalCode.sigma (NaturalCode.fin r) (fun _ =>
    NaturalCode.prod (NaturalCode.subtype NaturalCode.bool _) (NaturalCode.subtype NaturalCode.bool _)))

def colorIndex : (R.Coordinate ⊕ R.Block) ↪ ℕ :=
  NaturalCode.sum
    (NaturalCode.sum (NaturalCode.sigma R.hIndex (fun _ => NaturalCode.fin _)) R.vIndex)
    (NaturalCode.sum R.hIndex R.squareIndex)

noncomputable def affine (hr : 2 ≤ r) : AffineBlocks R.Coordinate R.Block where
  colorIndex := R.colorIndex
  coordinates := R.coordinates
  form b := match b with
    | .inl _ => 0
    | .inr q => R.squareForm q
  constrained b := match b with
    | .inl _ => false
    | .inr _ => true
  nonzero b hb := by
    cases b with
    | inl h => cases hb
    | inr b => exact R.squareForm_nonzero hr b

end RingLayout

namespace RingLayout
variable {r : ℕ} {T L : Type} [Fintype T] [Fintype L] (R : RingLayout r T L)

abbrev Horizontal := (h : R.HName) → Fin (R.dimension h.1) → Bit
abbrev Vertical := R.VName → Bit

def horizontal (z : R.Coordinate → Bit) : R.Horizontal := fun h j => z (.inl ⟨h, j⟩)
def vertical (z : R.Coordinate → Bit) : R.Vertical := fun v => z (.inr v)
def pack (x : R.Horizontal) (y : R.Vertical) : R.Coordinate → Bit
  | .inl h => x h.1 h.2
  | .inr v => y v

theorem solves_iff (hr : 2 ≤ r) (beta : R.Block → Bit) (z : R.Coordinate → Bit) :
    (R.affine hr).Solves beta z ↔ ∀ b : R.Square,
      R.firstForm b.1 (R.horizontal z (R.leftH b)) +
      R.secondForm b.1 (R.horizontal z (R.rightH b)) +
      R.vertical z (R.topV b) + R.vertical z (R.bottomV b) = beta (.inr b) := by
  constructor
  · intro h b
    exact h (.inr b) rfl
  · intro h b
    cases b with
    | inl h => intro hf; cases hf
    | inr b => exact fun _ => h b

abbrev Address (t : T) := (i : Fin r) → R.Label t i
abbrev MatchAddress (e : L) := (i : Fin r) → R.Match e i

def leftAddress (e : L) (a : R.MatchAddress e) : R.Address (R.first e) :=
  fun i => R.firstLabel e i (a i)
def rightAddress (e : L) (a : R.MatchAddress e) : R.Address (R.second e) :=
  fun i => R.secondLabel e i (a i)

def ringValue (x : R.Horizontal) (t : T) (a : R.Address t) : Fin (R.dimension t) → Bit :=
  ∑ i, x ⟨t, i, a i, a (finRotate r i)⟩

def linkShift (beta : R.Block → Bit) (e : L) (a : R.MatchAddress e) : Bit :=
  ∑ i, beta (.inr ⟨e, i, a i, a (finRotate r i)⟩)

omit [Fintype T] [Fintype L] in
theorem ringValue_rowSum (x : R.Horizontal) (t : T) :
    CycleRows.RowSum (R.Label t) (Fin (R.dimension t) → Bit) (R.ringValue x t) :=
  ⟨fun i u v => x ⟨t, i, u, v⟩, fun _ => rfl⟩

omit [Fintype T] [Fintype L] in
theorem linkShift_rowSum (beta : R.Block → Bit) (e : L) :
    CycleRows.RowSum (R.Match e) Bit (R.linkShift beta e) :=
  ⟨fun i u v => beta (.inr ⟨e, i, u, v⟩), fun _ => rfl⟩

/-- All link square equations are lifted simultaneously. No arbitrary-address
assignment substitutes for readouts shared by adjacent-coordinate pairs. -/
theorem offsets_iff_horizontal (hr : 3 ≤ r) (beta : R.Block → Bit) :
    (∃ z, (R.affine (by omega)).Solves beta z) ↔
    ∃ x : R.Horizontal, ∀ e (a : R.MatchAddress e),
      R.firstForm e (R.ringValue x (R.first e) (R.leftAddress e a)) +
      R.secondForm e (R.ringValue x (R.second e) (R.rightAddress e a)) = R.linkShift beta e a := by
  classical
  have hb (e : L) (i : Fin r) : Nonempty (R.Match e i) :=
    ⟨⟨(R.matchLabels_nonempty e i).choose, (R.matchLabels_nonempty e i).choose_spec⟩⟩
  let base (e : L) (i : Fin r) : R.Match e i := Classical.choice (hb e i)
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨R.horizontal z, ?_⟩
    intro e a
    have hsq := (R.solves_iff (by omega) beta z).mp hz
    have hh := (CycleRows.square_lifting hr (R.Match e) (base e)
      (fun i u v => R.firstForm e (R.horizontal z (R.leftH ⟨e, i, u, v⟩)))
      (fun i u v => R.secondForm e (R.horizontal z (R.rightH ⟨e, i, u, v⟩)))
      (fun i u v => beta (.inr ⟨e, i, u, v⟩))).mp
        ⟨fun i u => R.vertical z ⟨e, i, u⟩, fun i u v => hsq ⟨e, i, u, v⟩⟩ a
    simpa only [ringValue, map_sum, linkShift, leftAddress, rightAddress, leftH, rightH] using hh
  · rintro ⟨x, hx⟩
    have he (e : L) : ∃ y : (i : Fin r) → R.Match e i → Bit, ∀ i u v,
        R.firstForm e (x (R.leftH ⟨e, i, u, v⟩)) +
        R.secondForm e (x (R.rightH ⟨e, i, u, v⟩)) +
        y i u + y (finRotate r i) v = beta (.inr ⟨e, i, u, v⟩) := by
      apply (CycleRows.square_lifting hr (R.Match e) (base e) _ _ _).mpr
      intro a
      simpa only [ringValue, map_sum, linkShift, leftAddress, rightAddress, leftH, rightH] using hx e a
    choose y hy using he
    refine ⟨R.pack x (fun v => y v.1 v.2.1 v.2.2), (R.solves_iff (by omega) beta _).mpr ?_⟩
    intro b
    exact hy b.1 b.2.1 b.2.2.1 b.2.2.2

theorem offsets_iff_rowSums (hr : 3 ≤ r) (beta : R.Block → Bit) :
    (∃ z, (R.affine (by omega)).Solves beta z) ↔
    ∃ h : (t : T) → R.Address t → Fin (R.dimension t) → Bit,
      (∀ t, CycleRows.RowSum (R.Label t) (Fin (R.dimension t) → Bit) (h t)) ∧
      ∀ e (a : R.MatchAddress e),
        R.firstForm e (h (R.first e) (R.leftAddress e a)) +
        R.secondForm e (h (R.second e) (R.rightAddress e a)) = R.linkShift beta e a := by
  rw [R.offsets_iff_horizontal hr beta]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨R.ringValue x, R.ringValue_rowSum x, hx⟩
  · rintro ⟨h, hs, he⟩
    choose f hf using hs
    let x : R.Horizontal := fun a => f a.1 a.2.1 a.2.2.1 a.2.2.2
    have hx (t : T) (a : R.Address t) : R.ringValue x t a = h t a := (hf t a).symm
    refine ⟨x, ?_⟩
    intro e a
    rw [hx, hx]
    exact he e a

end RingLayout

namespace AffineBlocks
variable {C B : Type} [Fintype C] [DecidableEq C]

/-- A nonzero scalar equation cuts a binary valuation class exactly in half. -/
theorem constrained_card (D : AffineBlocks C B) (beta : B → Bit) (b : B)
    (hc : D.constrained b = true) :
    2 * Fintype.card {v // D.Legal beta b v} = 2 ^ (D.coordinates b).card := by
  classical
  have hf (c : Bit) : Fintype.card {v : D.Local b // D.form b v = c} =
      Fintype.card {v // D.Legal beta b v} := by
    calc
      _ = Fintype.card {v // D.Legal (fun _ => c) b v} :=
        Fintype.card_congr (Equiv.subtypeEquivRight (fun v => by simp [Legal, hc]))
      _ = _ := D.legal_card _ _ b
  have h := Fintype.card_congr (Equiv.sigmaFiberEquiv (D.form b))
  simpa only [Fintype.card_sigma, hf, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, Local, Fintype.card_fun, Fintype.card_coe, Bit, ZMod.card] using h

theorem local_card_le (D : AffineBlocks C B) (beta : B → Bit) (b : B) :
    Fintype.card {v // D.Legal beta b v} ≤ 2 ^ (D.coordinates b).card := by
  classical
  simpa only [Local, Fintype.card_fun, Fintype.card_coe, Bit, ZMod.card] using
    Fintype.card_subtype_le (D.Legal beta b)

theorem piece_card_bound (D : AffineBlocks C B) (beta : B → Bit) (b : B)
    (hs : (D.coordinates b).card ≤ 5)
    (hu : D.constrained b ≠ true → (D.coordinates b).card ≤ 2) :
    Fintype.card (D.Piece beta b) ≤ 26 := by
  classical
  have he : Fintype.card (D.Piece beta b) =
      2 * (D.coordinates b).card + Fintype.card {v // D.Legal beta b v} := by
    simp only [Piece, Fintype.card_sum, Fintype.card_prod, Fintype.card_coe, Bit, ZMod.card]
    omega
  rw [he]
  by_cases hc : D.constrained b = true
  · have h := D.constrained_card beta b hc
    have hp := Nat.pow_le_pow_right (by omega : 0 < 2) hs
    norm_num at hp
    omega
  · have h := D.local_card_le beta b
    have hd := hu hc
    have hp := Nat.pow_le_pow_right (by omega : 0 < 2) hd
    norm_num at hp
    omega

end AffineBlocks

namespace RingLayout
variable {r : ℕ} {T L : Type} [Fintype T] [Fintype L] (R : RingLayout r T L)

omit [Fintype T] [Fintype L] in
theorem hCoords_card (h : R.HName) : (R.hCoords h).card = R.dimension h.1 := by
  classical
  rw [hCoords, Finset.card_image_of_injective]
  · simp
  · intro i j hh
    exact (Sigma.mk.inj (Sum.inl.inj hh)).2 |> eq_of_heq

omit [Fintype T] [Fintype L] in
theorem coordinates_card (b : R.Block) : (R.coordinates b).card ≤ 5 := by
  classical
  cases b with
  | inl h =>
    change (R.hCoords h).card ≤ 5
    rw [R.hCoords_card]
    rcases R.dimension_bound h.1 with h | h <;> omega
  | inr b =>
    have h1 := R.dimension_bound (R.first b.1)
    have h2 := R.dimension_bound (R.second b.1)
    have h3 := R.internal_endpoint b.1
    have ha := Finset.card_union_le (R.hCoords (R.leftH b)) (R.hCoords (R.rightH b))
    have hb := Finset.card_union_le (R.hCoords (R.leftH b) ∪ R.hCoords (R.rightH b))
      {Sum.inr (R.topV b), Sum.inr (R.bottomV b)}
    have hc : ({Sum.inr (R.topV b), Sum.inr (R.bottomV b)} : Finset R.Coordinate).card ≤ 2 :=
      (Finset.card_insert_le _ _).trans (by simp)
    rw [R.hCoords_card, R.hCoords_card] at ha
    change (R.hCoords (R.leftH b) ∪ R.hCoords (R.rightH b) ∪
      {Sum.inr (R.topV b), Sum.inr (R.bottomV b)}).card ≤ 5
    change _ ≤ R.dimension (R.first b.1) + R.dimension (R.second b.1) at ha
    omega

/-- The advertised 26-vertex bound, including both vertices of every readout bit. -/
theorem piece_card_le (hr : 2 ≤ r) (beta : R.Block → Bit) (b : R.Block) :
    Fintype.card ((R.affine hr).Piece beta b) ≤ 26 := by
  apply AffineBlocks.piece_card_bound
  · exact R.coordinates_card b
  · intro hc
    cases b with
    | inl h =>
      change (R.hCoords h).card ≤ 2
      rw [R.hCoords_card]
      rcases R.dimension_bound h.1 with h | h <;> omega
    | inr b => exact False.elim (hc rfl)

/-- Every vertical name has a neighboring square, even for singleton factors. -/
noncomputable def owner : R.Coordinate → R.Block
  | .inl h => .inl h.1
  | .inr v => .inr ⟨v.1, v.2.1, v.2.2,
      ⟨(R.matchLabels_nonempty v.1 (finRotate r v.2.1)).choose,
        (R.matchLabels_nonempty v.1 (finRotate r v.2.1)).choose_spec⟩⟩

omit [Fintype T] [Fintype L] in
theorem owner_covers (c : R.Coordinate) : c ∈ R.coordinates (R.owner c) := by
  cases c with
  | inl h => exact R.hCoord_mem h.1 h.2
  | inr v => exact R.top_mem _

/-- All-mates reconstruction for the ring construction when r≥32. -/
theorem arbitrary_mate (hr : 32 ≤ r) (H : Graph)
    (h : Equivalent r ((R.affine (by omega)).graph 0) H) :
    ∃ beta, Isomorphic H ((R.affine (by omega)).graph beta) :=
  (R.affine (by omega)).graph_arbitrary_mate (by omega)
    (fun b => (R.piece_card_le (by omega) 0 b).trans (by omega)) H h

end RingLayout

end WLIdentification

end OAI
