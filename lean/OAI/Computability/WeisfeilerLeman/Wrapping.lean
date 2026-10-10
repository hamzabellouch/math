import OAI.Computability.WeisfeilerLeman.Offsets

namespace OAI

universe uV uB uLabel uI

namespace WLTime.Compression

variable {V : Type uV} {G : SimpleGraph V}

theorem walkWeight_ne_zero_edge (mark : V → V → F₂) {u v : V} (p : G.Walk u v)
    (h : walkWeight mark p ≠ 0) :
    ∃ a b, G.Adj a b ∧ mark a b ≠ 0 := by
  induction p with
  | nil => exact (h rfl).elim
  | @cons a b c e p ih =>
    by_cases hab : mark a b = 0
    · apply ih
      simpa only [walkWeight_cons, hab, zero_add] using h
    · exact ⟨a, b, e, hab⟩

theorem closed_row_weights_eq {r : ℕ} (mark : Fin (r + 1) → V → V → F₂)
    (boundary : Fin r → V → F₂)
    (balance : ∀ i u v, G.Adj u v →
      mark i.castSucc u v + mark i.succ u v = boundary i u + boundary i v)
    {v : V} (p : G.Walk v v) (i j : Fin (r + 1)) :
    walkWeight (mark i) p = walkWeight (mark j) p := by
  have hstep (i : Fin r) :
      walkWeight (mark i.castSucc) p = walkWeight (mark i.succ) p := by
    have h := walkWeight_congr _ _ (balance i) p
    rw [walkWeight_add, walkWeight_coboundary, CharTwo.add_self_eq_zero] at h
    exact add_right_cancel (h.trans (CharTwo.add_self_eq_zero _).symm)
  have hzero (i : Fin (r + 1)) : walkWeight (mark i) p = walkWeight (mark 0) p :=
    Fin.induction rfl (fun i ih => (hstep i).symm.trans ih) i
  exact (hzero i).trans (hzero j).symm

theorem wrapping_all_rows {r : ℕ} {B : Type uB} (U : Finset B) (row : B → Fin (r + 1))
    (mark : Fin (r + 1) → V → V → F₂) (boundary : Fin r → V → F₂)
    (balance : ∀ i u v, G.Adj u v →
      mark i.castSucc u v + mark i.succ u v = boundary i u + boundary i v)
    (support : ∀ i u v, G.Adj u v → mark i u v ≠ 0 → ∃ b ∈ U, row b = i)
    {v : V} (p : G.Walk v v) (seam : Fin (r + 1))
    (wraps : walkWeight (mark seam) p ≠ 0) :
    ∀ i, ∃ b ∈ U, row b = i := by
  intro i
  have hi : walkWeight (mark i) p ≠ 0 := by
    rwa [closed_row_weights_eq mark boundary balance p i seam]
  obtain ⟨u, v, huv, hmark⟩ := walkWeight_ne_zero_edge _ p hi
  exact support i u v huv hmark

theorem wrapping_card_lower {r : ℕ} {B : Type uB} (U : Finset B) (row : B → Fin (r + 1))
    (mark : Fin (r + 1) → V → V → F₂) (boundary : Fin r → V → F₂)
    (balance : ∀ i u v, G.Adj u v →
      mark i.castSucc u v + mark i.succ u v = boundary i u + boundary i v)
    (support : ∀ i u v, G.Adj u v → mark i u v ≠ 0 → ∃ b ∈ U, row b = i)
    {v : V} (p : G.Walk v v) (seam : Fin (r + 1))
    (wraps : walkWeight (mark seam) p ≠ 0) : r + 1 ≤ U.card := by
  classical
  have hall := wrapping_all_rows U row mark boundary balance support p seam wraps
  have heq : U.image row = Finset.univ := by
    ext i
    simp only [Finset.mem_image, Finset.mem_univ, iff_true]
    exact hall i
  calc
    r + 1 = (U.image row).card := by rw [heq]; simp
    _ ≤ U.card := Finset.card_image_le

theorem unique_block_per_row {r : ℕ} {B : Type uB} (U : Finset B) (row : B → Fin (r + 1))
    (hall : ∀ i, ∃ b ∈ U, row b = i) (hcard : U.card = r + 1) :
    ∀ i, ∃! b, b ∈ U ∧ row b = i := by
  classical
  have heq : U.image row = Finset.univ := by
    ext i
    simp only [Finset.mem_image, Finset.mem_univ, iff_true]
    exact hall i
  have hinj : Set.InjOn row U := Finset.injOn_of_card_image_eq (by rw [heq, hcard]; simp)
  intro i
  obtain ⟨b, hb, hbi⟩ := hall i
  refine ⟨b, ⟨hb, hbi⟩, ?_⟩
  intro c hc
  exact hinj hc.1 hb (hc.2.trans hbi.symm)

end WLTime.Compression

namespace WLTime.Compression

variable {V : Type uV} {G : SimpleGraph V}

theorem boundary_label_recovery {Label : Type uLabel} [DecidableEq Label]
    (leftRow rightRow : V → V → F₂) (leftLabel rightLabel : Label)
    (boundary : Label → V → F₂)
    (balance : ∀ label u v, G.Adj u v →
      (if leftLabel = label then leftRow u v else 0) +
        (if rightLabel = label then rightRow u v else 0) =
          boundary label u + boundary label v)
    {v : V} (p : G.Walk v v) (wraps : walkWeight leftRow p ≠ 0) :
    leftLabel = rightLabel := by
  classical
  by_contra hne
  have h := walkWeight_congr _ _ (balance leftLabel) p
  simp only [ite_eq_right (Ne.symm hne), add_zero] at h
  rw [walkWeight_coboundary, CharTwo.add_self_eq_zero] at h
  exact wraps h

theorem difference_card_le_one {B : Type uB} [DecidableEq B]
    (U A B' : Finset B) (hA : A ⊆ U) (hB : B' ⊆ U) (d : ℕ)
    (hcardB : B'.card = d) (hcardU : U.card ≤ d + 1) : (A \ B').card ≤ 1 := by
  have hun : A ∪ B' ⊆ U := Finset.union_subset hA hB
  have hsize := Finset.card_le_card hun
  have hsum := Finset.card_sdiff_add_card A B'
  omega

theorem recovered_addresses_agree {B : Type uB} {I : Type uI} {Label : Type uLabel} [DecidableEq B]
    (next : Equiv.Perm I) (next_ne : ∀ i, next i ≠ i)
    (row : B → I) (leftLabel rightLabel : B → Label)
    (U A B' : Finset B) (hA : A ⊆ U) (hB : B' ⊆ U) (d : ℕ)
    (hcardB : B'.card = d) (hcardU : U.card ≤ d + 1)
    (rowsA : ∀ i, ∃ b ∈ A, row b = i)
    (addressA addressB : I → Label)
    (readsA : ∀ b ∈ A, addressA (row b) = leftLabel b ∧
      addressA (next (row b)) = rightLabel b)
    (readsB : ∀ b ∈ B', addressB (row b) = leftLabel b ∧
      addressB (next (row b)) = rightLabel b) : addressA = addressB := by
  have hdiff := difference_card_le_one U A B' hA hB d hcardB hcardU
  funext i
  obtain ⟨b, hb, hbi⟩ := rowsA i
  obtain ⟨c, hc, hci⟩ := rowsA (next.symm i)
  have hbc : b ≠ c := by
    intro heq
    have hi : i = next.symm i := hbi.symm.trans ((congrArg row heq).trans hci)
    have hh := congrArg next hi
    rw [next.apply_symm_apply] at hh
    exact next_ne i hh
  have hcommon : b ∈ B' ∨ c ∈ B' := by
    by_contra! hn
    have hsub : {b, c} ⊆ A \ B' := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_sdiff.mpr ⟨hb, hn.1⟩
      · exact Finset.mem_sdiff.mpr ⟨hc, hn.2⟩
    have htwo := Finset.card_le_card hsub
    rw [Finset.card_pair hbc] at htwo
    omega
  rcases hcommon with hb' | hc'
  · rw [← hbi, (readsA b hb).1, (readsB b hb').1]
  · have hi : next (row c) = i := by rw [hci, next.apply_symm_apply]
    rw [← hi, (readsA c hc).2, (readsB c hc').2]

end WLTime.Compression

namespace WLTime.Compression

@[simp] theorem rotate_castSucc {r : ℕ} (i : Fin r) :
    finRotate (r + 1) i.castSucc = i.succ := finRotate_of_lt i.isLt

theorem rotate_ne_self {r : ℕ} (hr : 1 ≤ r) (i : Fin (r + 1)) :
    finRotate (r + 1) i ≠ i := by
  intro he
  have hv := congrArg Fin.val he
  rw [coe_finRotate] at hv
  split_ifs at hv with h
  · have hi := congrArg Fin.val h
    simp only [Fin.val_last] at hi
    omega
  · omega

theorem rotate_no_two_cycle {r : ℕ} (hr : 2 ≤ r) (i j : Fin (r + 1)) :
    ¬(finRotate (r + 1) i = j ∧ finRotate (r + 1) j = i) := by
  rintro ⟨hij, hji⟩
  have hv := congrArg Fin.val hij
  have hw := congrArg Fin.val hji
  rw [coe_finRotate] at hv hw
  by_cases hi : i = Fin.last r <;> by_cases hj : j = Fin.last r
  all_goals simp [hi, hj] at hv hw
  all_goals omega

structure BlockDrawing (r : ℕ) (B : Type uB) (V : Type uV) where
  boundary : V → Fin (r + 1)
  row : B → Fin (r + 1)
  low : B → Bool → V
  high : B → Bool → V
  low_boundary : ∀ b s, boundary (low b s) = row b
  high_boundary : ∀ b s, boundary (high b s) = finRotate (r + 1) (row b)

namespace BlockDrawing

variable {r : ℕ} {B : Type uB} {V : Type uV} (D : BlockDrawing r B V)

def Edge (b : B) (x y : V) : Prop :=
  (∃ s, x = D.low b s ∧ y = D.high b s) ∨
  (x = D.low b false ∧ y = D.low b true) ∨
  (x = D.high b false ∧ y = D.high b true)

def graph (U : Finset B) : SimpleGraph V where
  Adj x y := x ≠ y ∧ ∃ b ∈ U, D.Edge b x y ∨ D.Edge b y x
  symm := ⟨by
    rintro x y ⟨h, b, hb, he⟩
    exact ⟨h.symm, b, hb, he.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

def rowMark (i : Fin (r + 1)) (x y : V) : F₂ :=
  if (D.boundary x = i ∧ D.boundary y = finRotate (r + 1) i) ∨
      (D.boundary y = i ∧ D.boundary x = finRotate (r + 1) i) then 1 else 0

@[simp] theorem rowMark_symm (i : Fin (r + 1)) (x y : V) :
    D.rowMark i x y = D.rowMark i y x := by
  simp only [rowMark, or_comm]

@[simp] theorem rowMark_horizontal (hr : 2 ≤ r) (i : Fin (r + 1)) (b : B) (s : Bool) :
    D.rowMark i (D.low b s) (D.high b s) = if i = D.row b then 1 else 0 := by
  simp only [rowMark, D.low_boundary, D.high_boundary]
  have hrev : ¬(finRotate (r + 1) (D.row b) = i ∧
      D.row b = finRotate (r + 1) i) := by
    rintro ⟨h1, h2⟩
    exact rotate_no_two_cycle hr (D.row b) i ⟨h1, h2.symm⟩
  simp only [hrev, or_false, Equiv.apply_eq_iff_eq, and_self, eq_comm (a := D.row b) (b := i)]

theorem rowMark_zero_of_boundary_eq (hr : 1 ≤ r) (i : Fin (r + 1))
    {x y : V} (hxy : D.boundary x = D.boundary y) : D.rowMark i x y = 0 := by
  rw [rowMark, ite_eq_right]
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
  · exact rotate_ne_self hr i (h2.symm.trans (hxy.symm.trans h1))
  · exact rotate_ne_self hr i (h2.symm.trans (hxy.trans h1))

def boundaryMark (i : Fin (r + 1)) (x : V) : F₂ :=
  if D.boundary x = i then 1 else 0

theorem row_balance_horizontal (hr : 2 ≤ r) (i : Fin r) (b : B) (s : Bool) :
    D.rowMark i.castSucc (D.low b s) (D.high b s) +
      D.rowMark i.succ (D.low b s) (D.high b s) =
    D.boundaryMark i.succ (D.low b s) + D.boundaryMark i.succ (D.high b s) := by
  rw [D.rowMark_horizontal hr, D.rowMark_horizontal hr]
  simp only [boundaryMark, D.low_boundary, D.high_boundary,
    ← rotate_castSucc i, Equiv.apply_eq_iff_eq]
  simp only [eq_comm (a := D.row b) (b := i.castSucc), eq_comm (a := D.row b) (b := ((finRotate (r + 1)) i.castSucc))]
  exact add_comm _ _

theorem row_balance_vertical (hr : 2 ≤ r) (i : Fin r) {x y : V}
    (hxy : D.boundary x = D.boundary y) :
    D.rowMark i.castSucc x y + D.rowMark i.succ x y =
      D.boundaryMark i.succ x + D.boundaryMark i.succ y := by
  rw [D.rowMark_zero_of_boundary_eq (by omega) _ hxy,
    D.rowMark_zero_of_boundary_eq (by omega) _ hxy, zero_add]
  unfold boundaryMark
  rw [hxy, CharTwo.add_self_eq_zero]

theorem row_balance_edge (hr : 2 ≤ r) (i : Fin r) {b : B} {x y : V}
    (h : D.Edge b x y) :
    D.rowMark i.castSucc x y + D.rowMark i.succ x y =
      D.boundaryMark i.succ x + D.boundaryMark i.succ y := by
  rcases h with ⟨s, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact D.row_balance_horizontal hr i b s
  · exact D.row_balance_vertical hr i ((D.low_boundary b false).trans (D.low_boundary b true).symm)
  · exact D.row_balance_vertical hr i ((D.high_boundary b false).trans (D.high_boundary b true).symm)

theorem row_balance (hr : 2 ≤ r) (U : Finset B) (i : Fin r) {x y : V}
    (h : (D.graph U).Adj x y) :
    D.rowMark i.castSucc x y + D.rowMark i.succ x y =
      D.boundaryMark i.succ x + D.boundaryMark i.succ y := by
  obtain ⟨_, b, _, h | h⟩ := h
  · exact D.row_balance_edge hr i h
  · simpa only [D.rowMark_symm _ y x, add_comm (D.boundaryMark i.succ y)] using
      D.row_balance_edge hr i h

theorem row_support_edge (hr : 2 ≤ r) (i : Fin (r + 1)) {b : B} {x y : V}
    (h : D.Edge b x y) (hm : D.rowMark i x y ≠ 0) : D.row b = i := by
  rcases h with ⟨s, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [D.rowMark_horizontal hr] at hm
    by_contra hne
    exact hm (ite_eq_right (Ne.symm hne))
  · exact (hm (D.rowMark_zero_of_boundary_eq (by omega) _
      ((D.low_boundary b false).trans (D.low_boundary b true).symm))).elim
  · exact (hm (D.rowMark_zero_of_boundary_eq (by omega) _
      ((D.high_boundary b false).trans (D.high_boundary b true).symm))).elim

theorem row_support (hr : 2 ≤ r) (U : Finset B) (i : Fin (r + 1)) {x y : V}
    (h : (D.graph U).Adj x y) (hm : D.rowMark i x y ≠ 0) : ∃ b ∈ U, D.row b = i := by
  obtain ⟨_, b, hb, h | h⟩ := h
  · exact ⟨b, hb, D.row_support_edge hr i h hm⟩
  · exact ⟨b, hb, D.row_support_edge hr i h (by rwa [D.rowMark_symm])⟩

def Wraps (U : Finset B) : Prop :=
  ∃ v, ∃ p : (D.graph U).Walk v v, walkWeight (D.rowMark (Fin.last r)) p ≠ 0

theorem wraps_card (hr : 2 ≤ r) (U : Finset B) (h : D.Wraps U) : r + 1 ≤ U.card := by
  obtain ⟨v, p, hp⟩ := h
  exact wrapping_card_lower U D.row D.rowMark (fun i => D.boundaryMark i.succ)
    (fun i x y h => D.row_balance hr U i h)
    (fun i x y h hm => D.row_support hr U i h hm) p (Fin.last r) hp

theorem wraps_unique_row (hr : 2 ≤ r) (U : Finset B) (h : D.Wraps U)
    (hc : U.card = r + 1) : ∀ i, ∃! b, b ∈ U ∧ D.row b = i := by
  obtain ⟨v, p, hp⟩ := h
  apply unique_block_per_row U D.row ?_ hc
  exact wrapping_all_rows U D.row D.rowMark (fun i => D.boundaryMark i.succ)
    (fun i x y h => D.row_balance hr U i h)
    (fun i x y h hm => D.row_support hr U i h hm) p (Fin.last r) hp

end BlockDrawing
end WLTime.Compression

namespace WLTime.Compression
namespace BlockDrawing
variable {r : ℕ} {B : Type uB} {V : Type uV} {Label : Type uLabel} (D : BlockDrawing r B V)

theorem edge_reachable (U : Finset B) {b : B} (hb : b ∈ U) {x y : V}
    (h : D.Edge b x y) : (D.graph U).Reachable x y := by
  by_cases he : x = y
  · subst y; exact SimpleGraph.Reachable.refl _
  · exact (show (D.graph U).Adj x y from ⟨he, b, hb, Or.inl h⟩).reachable

theorem low_reachable (U : Finset B) {b : B} (hb : b ∈ U) (s : Bool) :
    (D.graph U).Reachable (D.low b false) (D.low b s) := by
  cases s
  · exact SimpleGraph.Reachable.refl _
  · exact D.edge_reachable U hb (Or.inr (Or.inl ⟨rfl, rfl⟩))

theorem high_reachable (U : Finset B) {b : B} (hb : b ∈ U) (s : Bool) :
    (D.graph U).Reachable (D.low b false) (D.high b s) :=
  (D.low_reachable U hb s).trans (D.edge_reachable U hb (Or.inl ⟨s, rfl, rfl⟩))

theorem edge_left_reachable (U : Finset B) {b : B} (hb : b ∈ U) {x y : V}
    (h : D.Edge b x y) : (D.graph U).Reachable (D.low b false) x := by
  rcases h with ⟨s, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact D.low_reachable U hb s
  · exact D.low_reachable U hb false
  · exact D.high_reachable U hb false

theorem edge_right_reachable (U : Finset B) {b : B} (hb : b ∈ U) {x y : V}
    (h : D.Edge b x y) : (D.graph U).Reachable (D.low b false) y :=
  (D.edge_left_reachable U hb h).trans (D.edge_reachable U hb h)

theorem row_weight_nonzero_has_block (hr : 2 ≤ r) (U : Finset B)
    {v w : V} (p : (D.graph U).Walk v w) (i : Fin (r + 1))
    (h : walkWeight (D.rowMark i) p ≠ 0) :
    ∃ b ∈ U, D.row b = i ∧ (D.graph U).Reachable v (D.low b false) := by
  induction p with
  | nil => exact (h rfl).elim
  | @cons x y z hxy p ih =>
    by_cases hm : D.rowMark i x y = 0
    · have hp : walkWeight (D.rowMark i) p ≠ 0 := by
        simpa only [walkWeight_cons, hm, zero_add] using h
      obtain ⟨b, hb, hbi, hrch⟩ := ih hp
      exact ⟨b, hb, hbi, hxy.reachable.trans hrch⟩
    · obtain ⟨_, b, hb, he | he⟩ := hxy
      · exact ⟨b, hb, D.row_support_edge hr i he hm, (D.edge_left_reachable U hb he).symm⟩
      · exact ⟨b, hb, D.row_support_edge hr i he (by rwa [D.rowMark_symm]),
          (D.edge_right_reachable U hb he).symm⟩

theorem wraps_connected (hr : 2 ≤ r) (U : Finset B) (h : D.Wraps U)
    (hc : U.card = r + 1) : ∀ b ∈ U, ∀ c ∈ U,
    (D.graph U).Reachable (D.low b false) (D.low c false) := by
  have hu := D.wraps_unique_row hr U h hc
  obtain ⟨v, p, hp⟩ := h
  have hreach : ∀ b ∈ U, (D.graph U).Reachable v (D.low b false) := by
    intro b hb
    have hrow : walkWeight (D.rowMark (D.row b)) p ≠ 0 := by
      rwa [closed_row_weights_eq D.rowMark (fun i => D.boundaryMark i.succ)
        (fun i x y h => D.row_balance hr U i h) p (D.row b) (Fin.last r)]
    obtain ⟨c, hc', he, hreach⟩ := D.row_weight_nonzero_has_block hr U p (D.row b) hrow
    obtain ⟨d, hd, huniq⟩ := hu (D.row b)
    have hcb : c = b := (huniq c ⟨hc', he⟩).trans (huniq b ⟨hb, rfl⟩).symm
    simpa only [hcb] using hreach
  exact fun b hb c hc => (hreach b hb).symm.trans (hreach c hc)

variable [DecidableEq Label]

def labeledBoundary (label : V → Label) (i : Fin (r + 1)) (a : Label) (x : V) : F₂ :=
  if D.boundary x = i ∧ label x = a then 1 else 0

omit [DecidableEq Label] in
theorem side_label_low (label : V → Label) {b : B}
    (h : label (D.low b false) = label (D.low b true)) (s : Bool) :
    label (D.low b s) = label (D.low b false) := by cases s <;> simp_all

omit [DecidableEq Label] in
theorem side_label_high (label : V → Label) {b : B}
    (h : label (D.high b false) = label (D.high b true)) (s : Bool) :
    label (D.high b s) = label (D.high b false) := by cases s <;> simp_all

theorem labeled_balance_horizontal (hr : 2 ≤ r) (U : Finset B) (label : V → Label)
    (lo hi : Fin (r + 1) → Label)
    (labels : ∀ b ∈ U, ∀ s, label (D.low b s) = lo (D.row b) ∧
      label (D.high b s) = hi (D.row b))
    (i : Fin (r + 1)) (a : Label) {b : B} (hb : b ∈ U) (s : Bool) :
    (if hi i = a then D.rowMark i (D.low b s) (D.high b s) else 0) +
    (if lo (finRotate (r + 1) i) = a then
      D.rowMark (finRotate (r + 1) i) (D.low b s) (D.high b s) else 0) =
    D.labeledBoundary label (finRotate (r + 1) i) a (D.low b s) +
      D.labeledBoundary label (finRotate (r + 1) i) a (D.high b s) := by
  rw [D.rowMark_horizontal hr, D.rowMark_horizontal hr]
  simp only [labeledBoundary, D.low_boundary, D.high_boundary, (labels b hb s).1,
    (labels b hb s).2, Equiv.apply_eq_iff_eq]
  by_cases hbi : D.row b = i
  · have hni := rotate_ne_self (by omega : 1 ≤ r) i
    simp only [hbi, hni, Ne.symm hni, ↓reduceIte, false_and, true_and, ite_self, zero_add, add_zero]
  · by_cases hbn : D.row b = finRotate (r + 1) i
    · have hni := rotate_ne_self (by omega : 1 ≤ r) i
      simp only [hbn, hni, Ne.symm hni, ↓reduceIte, false_and, true_and, ite_self, zero_add, add_zero]
    · simp only [hbi, hbn, Ne.symm hbi, Ne.symm hbn, ↓reduceIte, false_and, ite_self, zero_add]

theorem labeled_balance_vertical (hr : 2 ≤ r) (label : V → Label)
    (lo hi : Fin (r + 1) → Label) (i : Fin (r + 1)) (a : Label) {x y : V}
    (hxy : D.boundary x = D.boundary y) (hl : label x = label y) :
    (if hi i = a then D.rowMark i x y else 0) +
      (if lo (finRotate (r + 1) i) = a then D.rowMark (finRotate (r + 1) i) x y else 0) =
    D.labeledBoundary label (finRotate (r + 1) i) a x +
      D.labeledBoundary label (finRotate (r + 1) i) a y := by
  rw [D.rowMark_zero_of_boundary_eq (by omega) _ hxy,
    D.rowMark_zero_of_boundary_eq (by omega) _ hxy]
  simp only [ite_self, labeledBoundary, hxy, hl, CharTwo.add_self_eq_zero]

theorem labeled_balance_edge (hr : 2 ≤ r) (U : Finset B) (label : V → Label)
    (lo hi : Fin (r + 1) → Label)
    (labels : ∀ b ∈ U, ∀ s, label (D.low b s) = lo (D.row b) ∧
      label (D.high b s) = hi (D.row b))
    (i : Fin (r + 1)) (a : Label) {b : B} (hb : b ∈ U) {x y : V}
    (h : D.Edge b x y) :
    (if hi i = a then D.rowMark i x y else 0) +
      (if lo (finRotate (r + 1) i) = a then D.rowMark (finRotate (r + 1) i) x y else 0) =
    D.labeledBoundary label (finRotate (r + 1) i) a x +
      D.labeledBoundary label (finRotate (r + 1) i) a y := by
  rcases h with ⟨s, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact D.labeled_balance_horizontal hr U label lo hi labels i a hb s
  · exact D.labeled_balance_vertical hr label lo hi i a
      ((D.low_boundary b false).trans (D.low_boundary b true).symm)
      ((labels b hb false).1.trans (labels b hb true).1.symm)
  · exact D.labeled_balance_vertical hr label lo hi i a
      ((D.high_boundary b false).trans (D.high_boundary b true).symm)
      ((labels b hb false).2.trans (labels b hb true).2.symm)

theorem labeled_balance (hr : 2 ≤ r) (U : Finset B) (label : V → Label)
    (lo hi : Fin (r + 1) → Label)
    (labels : ∀ b ∈ U, ∀ s, label (D.low b s) = lo (D.row b) ∧
      label (D.high b s) = hi (D.row b))
    (i : Fin (r + 1)) (a : Label) {x y : V} (h : (D.graph U).Adj x y) :
    (if hi i = a then D.rowMark i x y else 0) +
      (if lo (finRotate (r + 1) i) = a then D.rowMark (finRotate (r + 1) i) x y else 0) =
    D.labeledBoundary label (finRotate (r + 1) i) a x +
      D.labeledBoundary label (finRotate (r + 1) i) a y := by
  obtain ⟨_, b, hb, h | h⟩ := h
  · exact D.labeled_balance_edge hr U label lo hi labels i a hb h
  · simpa only [D.rowMark_symm _ y x, add_comm (D.labeledBoundary label _ a y)] using
      D.labeled_balance_edge hr U label lo hi labels i a hb h

theorem wrapping_labels_join (hr : 2 ≤ r) (U : Finset B) (label : V → Label)
    (lo hi : Fin (r + 1) → Label)
    (labels : ∀ b ∈ U, ∀ s, label (D.low b s) = lo (D.row b) ∧
      label (D.high b s) = hi (D.row b)) (h : D.Wraps U) :
    ∀ i, hi i = lo (finRotate (r + 1) i) := by
  obtain ⟨v, p, hp⟩ := h
  intro i
  apply boundary_label_recovery (D.rowMark i) (D.rowMark (finRotate (r + 1) i))
    (hi i) (lo (finRotate (r + 1) i)) (D.labeledBoundary label (finRotate (r + 1) i))
    (fun a x y h => D.labeled_balance hr U label lo hi labels i a h) p
  rwa [closed_row_weights_eq D.rowMark (fun i => D.boundaryMark i.succ)
    (fun i x y h => D.row_balance hr U i h) p i (Fin.last r)]

end BlockDrawing
end WLTime.Compression

end OAI
