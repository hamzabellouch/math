import Mathlib
import OAI.Computability.DirectedFeedback.Games.ExpanderFamily
import OAI.Computability.DirectedFeedback.Games.Overlay

namespace OAI


namespace DFVSGames.Foundations.PCP.PreprocessingOverlayTables

open PoweringWalks

def overlayPorts (d e : Nat) : (Fin d ⊕ Fin e) ≃ Fin (d + e) := finSumFinEquiv

@[simp] theorem overlayPorts_inl_val (d e : Nat) (i : Fin d) :
    (overlayPorts d e (Sum.inl i)).val = i.val := rfl

@[simp] theorem overlayPorts_inr_val (d e : Nat) (i : Fin e) :
    (overlayPorts d e (Sum.inr i)).val = d + i.val := rfl

def lazyPorts (d : Nat) : (Bool × Fin d) ≃ Fin (2 * d) :=
  (Equiv.prodCongr finTwoEquiv.symm (Equiv.refl (Fin d))).trans finProdFinEquiv

@[simp] theorem lazyPorts_false_val (d : Nat) (i : Fin d) :
    (lazyPorts d (false, i)).val = i.val := by
  simp [lazyPorts, finTwoEquiv, finProdFinEquiv]

@[simp] theorem lazyPorts_true_val (d : Nat) (i : Fin d) :
    (lazyPorts d (true, i)).val = i.val + d := by
  simp [lazyPorts, finTwoEquiv, finProdFinEquiv]

def materialize {n d : Nat} {D : Type*}
    (G : ConstraintGraph (Fin n) (Fin n × D) PortTables.Label)
    (ports : D ≃ Fin d) : PortTables.Table n d :=
  PortTables.ofPortGraph
    (GraphTransport.reindex (Overlay.originalPortGraph G) (Equiv.refl _) ports)
    (fun x a b => G.accepts (x.1, ports.symm x.2) a b)
    (by
      intro x a b
      simp only [GraphTransport.reindex, Overlay.originalPortGraph,
        Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.prodCongr_symm,
        Equiv.refl_apply, Equiv.symm_apply_apply, Prod.map]
      convert G.reverse_accepts (x.1, ports.symm x.2) a b using 1 ; rfl)

theorem rotation_materialize {n d : Nat} {D : Type*}
    (G : ConstraintGraph (Fin n) (Fin n × D) PortTables.Label)
    (ports : D ≃ Fin d) (x : Fin n × Fin d) :
    PortTables.rotation (materialize G ports) x =
      ((G.reverse (x.1, ports.symm x.2)).1,
        ports (G.reverse (x.1, ports.symm x.2)).2) := by
  simp only [materialize, PortTables.rotation_ofPortGraph, GraphTransport.reindex,
    Overlay.originalPortGraph, Equiv.trans_apply, Equiv.prodCongr_apply,
    Equiv.prodCongr_symm, Equiv.refl_apply, Prod.map]
  rfl

theorem rotation_materialize_image {n d : Nat} {D : Type*}
    (G : ConstraintGraph (Fin n) (Fin n × D) PortTables.Label)
    (ports : D ≃ Fin d) (v : Fin n) (i : D) :
    PortTables.rotation (materialize G ports) (v, ports i) =
      ((G.reverse (v, i)).1, ports (G.reverse (v, i)).2) := by
  rw [rotation_materialize, Equiv.symm_apply_apply]

@[simp] theorem accepts_materialize {n d : Nat} {D : Type*}
    (G : ConstraintGraph (Fin n) (Fin n × D) PortTables.Label)
    (ports : D ≃ Fin d) (x : Fin n × Fin d) (a b : PortTables.Label) :
    PortTables.accepts (materialize G ports) x a b =
      G.accepts (x.1, ports.symm x.2) a b := by
  exact PortTables.accepts_ofPortGraph _ _ _ x a b

private theorem constraintGraph_ext_inline_PreprocessingOverlayTables {V E A : Type*} {G H : ConstraintGraph V E A}
    (hreverse : ∀ e, G.reverse e = H.reverse e)
    (htail : ∀ e, G.tail e = H.tail e)
    (haccepts : ∀ e a b, G.accepts e a b = H.accepts e a b) : G = H := by
  rcases G with ⟨r, hi, t, p, hp⟩
  rcases H with ⟨r', hi', t', p', hp'⟩
  have hr : r = r' := Equiv.ext hreverse
  cases hr
  have ht : t = t' := funext htail
  cases ht
  have ha : p = p' := funext fun e => funext fun a => funext fun b => haccepts e a b
  cases ha
  rfl

theorem baseGraph_materialize {n d : Nat} {D : Type*}
    (G : ConstraintGraph (Fin n) (Fin n × D) PortTables.Label)
    (ports : D ≃ Fin d) (htail : G.tail = Prod.fst) :
    PortTables.baseGraph (materialize G ports) =
      G.reindex (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _) ports) (Equiv.refl _) := by
  apply constraintGraph_ext_inline_PreprocessingOverlayTables
  · intro x
    rw [PortTables.baseGraph_reverse, rotation_materialize]
    rfl
  · intro x
    change x.1 = G.tail (x.1, ports.symm x.2)
    rw [htail]
  · intro x a b
    rw [PortTables.baseGraph_accepts, accepts_materialize]
    rfl

def overlay {n d e : Nat} (G : PortTables.Table n d) (H : ExpanderTables.Table n e) :
    PortTables.Table n (d + e) :=
  materialize (Overlay.constraintGraph (PortTables.baseGraph G) (ExpanderTables.graph H))
    (overlayPorts d e)

theorem overlay_rotation_old {n d e : Nat} (G : PortTables.Table n d)
    (H : ExpanderTables.Table n e) (v : Fin n) (i : Fin d) :
    PortTables.rotation (overlay G H) (v, overlayPorts d e (Sum.inl i)) =
      ((PortTables.rotation G (v, i)).1,
        overlayPorts d e (Sum.inl (PortTables.rotation G (v, i)).2)) := by
  exact rotation_materialize_image _ _ v (Sum.inl i)

theorem overlay_rotation_expander {n d e : Nat} (G : PortTables.Table n d)
    (H : ExpanderTables.Table n e) (v : Fin n) (i : Fin e) :
    PortTables.rotation (overlay G H) (v, overlayPorts d e (Sum.inr i)) =
      ((ExpanderTables.lookup H (v, i)).1,
        overlayPorts d e (Sum.inr (ExpanderTables.lookup H (v, i)).2)) := by
  exact rotation_materialize_image _ _ v (Sum.inr i)

@[simp] theorem overlay_accepts_old {n d e : Nat} (G : PortTables.Table n d)
    (H : ExpanderTables.Table n e) (v : Fin n) (i : Fin d) (a b : PortTables.Label) :
    PortTables.accepts (overlay G H) (v, overlayPorts d e (Sum.inl i)) a b =
      PortTables.accepts G (v, i) a b := by
  simp only [overlay, accepts_materialize, Equiv.symm_apply_apply]
  rfl

@[simp] theorem overlay_accepts_expander {n d e : Nat} (G : PortTables.Table n d)
    (H : ExpanderTables.Table n e) (v : Fin n) (i : Fin e) (a b : PortTables.Label) :
    PortTables.accepts (overlay G H) (v, overlayPorts d e (Sum.inr i)) a b = true := by
  simp only [overlay, accepts_materialize, Equiv.symm_apply_apply]
  rfl

theorem overlay_semantics {n d e : Nat} (G : PortTables.Table n d)
    (H : ExpanderTables.Table n e) :
    PortTables.baseGraph (overlay G H) =
      (Overlay.constraintGraph (PortTables.baseGraph G) (ExpanderTables.graph H)).reindex
        (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _) (overlayPorts d e))
        (Equiv.refl _) :=
  baseGraph_materialize _ _ rfl

def lazy {n d : Nat} (G : PortTables.Table n d) : PortTables.Table n (2 * d) :=
  materialize (LazyConstraint.constraintGraph (PortTables.baseGraph G)) (lazyPorts d)

theorem lazy_rotation_false {n d : Nat} (G : PortTables.Table n d)
    (v : Fin n) (i : Fin d) :
    PortTables.rotation (lazy G) (v, lazyPorts d (false, i)) =
      (v, lazyPorts d (false, i)) := by
  exact rotation_materialize_image _ _ v (false, i)

theorem lazy_rotation_true {n d : Nat} (G : PortTables.Table n d)
    (v : Fin n) (i : Fin d) :
    PortTables.rotation (lazy G) (v, lazyPorts d (true, i)) =
      ((PortTables.rotation G (v, i)).1,
        lazyPorts d (true, (PortTables.rotation G (v, i)).2)) := by
  exact rotation_materialize_image _ _ v (true, i)

@[simp] theorem lazy_accepts_false {n d : Nat} (G : PortTables.Table n d)
    (v : Fin n) (i : Fin d) (a b : PortTables.Label) :
    PortTables.accepts (lazy G) (v, lazyPorts d (false, i)) a b = true := by
  simp only [lazy, accepts_materialize, Equiv.symm_apply_apply]
  rfl

@[simp] theorem lazy_accepts_true {n d : Nat} (G : PortTables.Table n d)
    (v : Fin n) (i : Fin d) (a b : PortTables.Label) :
    PortTables.accepts (lazy G) (v, lazyPorts d (true, i)) a b =
      PortTables.accepts G (v, i) a b := by
  simp only [lazy, accepts_materialize, Equiv.symm_apply_apply]
  rfl

theorem lazy_semantics {n d : Nat} (G : PortTables.Table n d) :
    PortTables.baseGraph (lazy G) =
      (LazyConstraint.constraintGraph (PortTables.baseGraph G)).reindex
        (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _) (lazyPorts d)) (Equiv.refl _) :=
  baseGraph_materialize _ _ rfl

end DFVSGames.Foundations.PCP.PreprocessingOverlayTables


namespace DFVSGames.Foundations.PCP.CloudRounding

open scoped BigOperators

theorem dart_rejection_count_le
    {E V A : Type*} [Fintype E] [DecidableEq A]
    (tail : E → V) (reverse : E ≃ E) (accepts : E → A → A → Bool)
    (ell : E → A) (rounded : V → A) :
    (Finset.univ.filter (fun e =>
      accepts e (rounded (tail e)) (rounded (tail (reverse e))) = false)).card ≤
    (Finset.univ.filter (fun e => accepts e (ell e) (ell (reverse e)) = false)).card +
      2 * (Finset.univ.filter (fun e => ell e ≠ rounded (tail e))).card := by
  classical
  let R : Finset E := Finset.univ.filter (fun e =>
    accepts e (rounded (tail e)) (rounded (tail (reverse e))) = false)
  let B : Finset E := Finset.univ.filter (fun e =>
    accepts e (ell e) (ell (reverse e)) = false)
  let M : Finset E := Finset.univ.filter (fun e => ell e ≠ rounded (tail e))
  let MR : Finset E := Finset.univ.filter (fun e =>
    ell (reverse e) ≠ rounded (tail (reverse e)))
  have hrev : MR.card = M.card := by
    have hsets : MR = M.map reverse.symm.toEmbedding := by
      ext e
      constructor
      · intro he
        apply Finset.mem_map.mpr
        refine ⟨reverse e, ?_, reverse.symm_apply_apply e⟩
        simpa [MR, M] using he
      · intro he
        obtain ⟨d, hd, rfl⟩ := Finset.mem_map.mp he
        simpa [MR, M] using hd
    rw [hsets, Finset.card_map]
  have hsub : R ⊆ (B ∪ M) ∪ MR := by
    intro e he
    by_cases hl : ell e = rounded (tail e)
    · by_cases hr : ell (reverse e) = rounded (tail (reverse e))
      · have hb : e ∈ B := by simpa [B, R, hl, hr] using he
        exact Finset.mem_union_left _ (Finset.mem_union_left _ hb)
      · exact Finset.mem_union_right _ (by simp [MR, hr])
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (by simp [M, hl]))
  change R.card ≤ B.card + 2 * M.card
  calc
    R.card ≤ ((B ∪ M) ∪ MR).card := Finset.card_le_card hsub
    _ ≤ (B ∪ M).card + MR.card := Finset.card_union_le _ _
    _ ≤ (B.card + M.card) + MR.card :=
      Nat.add_le_add_right (Finset.card_union_le B M) _
    _ = B.card + 2 * M.card := by rw [hrev]; omega

section CloudCounts

variable {X A D : Type*} [Fintype X] [Fintype A] [Fintype D]
variable [DecidableEq X] [DecidableEq A]

def colorSet (ell : X → A) (a : A) : Finset X :=
  Finset.univ.filter (fun x => ell x = a)

def minoritySet (ell : X → A) (m : A) : Finset X :=
  Finset.univ.filter (fun x => ell x ≠ m)

def directedCut (next : X × D → X) (S : Finset X) : Finset (X × D) :=
  Finset.univ.filter (fun xd => xd.1 ∈ S ∧ next xd ∉ S)

def disagreementSet (ell : X → A) (next : X × D → X) : Finset (X × D) :=
  Finset.univ.filter (fun xd => ell xd.1 ≠ ell (next xd))

abbrev Nonmajor (m : A) := {a : A // a ≠ m}

omit [DecidableEq X] in
theorem exists_max_color (ell : X → A) [Nonempty A] :
    ∃ m : A, ∀ a, (colorSet ell a).card ≤ (colorSet ell m).card := by
  classical
  obtain ⟨m, _, hm⟩ := Finset.exists_max_image Finset.univ
    (fun a : A => (colorSet ell a).card) Finset.univ_nonempty
  exact ⟨m, fun a => hm a (Finset.mem_univ a)⟩

noncomputable def majority (ell : X → A) [Nonempty A] : A :=
  Classical.choose (exists_max_color ell)

omit [DecidableEq X] in
theorem majority_maximal (ell : X → A) [Nonempty A] (a : A) :
    (colorSet ell a).card ≤ (colorSet ell (majority ell)).card :=
  Classical.choose_spec (exists_max_color ell) a

omit [Fintype A] in

theorem nonchosen_color_twice_le (ell : X → A) (m : A)
    (maximal : ∀ a, (colorSet ell a).card ≤ (colorSet ell m).card)
    (a : A) (ha : a ≠ m) :
    2 * (colorSet ell a).card ≤ Fintype.card X := by
  have hd : Disjoint (colorSet ell a) (colorSet ell m) := by
    apply Finset.disjoint_left.mpr
    intro x hx hm
    have hxa : ell x = a := by simpa [colorSet] using hx
    have hxm : ell x = m := by simpa [colorSet] using hm
    exact ha (hxa.symm.trans hxm)
  have hu : (colorSet ell a).card + (colorSet ell m).card ≤ Fintype.card X := by
    calc
      _ = (colorSet ell a ∪ colorSet ell m).card :=
        (Finset.card_union_of_disjoint hd).symm
      _ ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ _)
      _ = Fintype.card X := Finset.card_univ
  have hm := maximal a
  omega

def minorityEquiv (ell : X → A) (m : A) :
    (Σ a : Nonmajor m, ↥(colorSet ell a.val)) ≃ ↥(minoritySet ell m) where
  toFun t := ⟨t.2.val, by
    have hc : ell t.2.val = t.1.val := (Finset.mem_filter.mp t.2.property).2
    have hn : ell t.2.val ≠ m := fun h => t.1.property (hc.symm.trans h)
    simpa [minoritySet] using hn⟩
  invFun x :=
    ⟨⟨ell x.val, by simpa [minoritySet] using x.property⟩,
      ⟨x.val, by simp [colorSet]⟩⟩
  left_inv t := by
    rcases t with ⟨⟨a, ha⟩, ⟨x, hx⟩⟩
    have hxa : ell x = a := by simpa [colorSet] using hx
    cases hxa
    rfl
  right_inv x := by apply Subtype.ext; rfl

omit [DecidableEq X] in
theorem minority_card_eq_sum (ell : X → A) (m : A) :
    (minoritySet ell m).card = ∑ a : Nonmajor m, (colorSet ell a.val).card := by
  have h := Fintype.card_congr (minorityEquiv ell m)
  simpa only [Fintype.card_sigma, Fintype.card_coe] using h.symm

def minorityCutEmbedding (ell : X → A) (next : X × D → X) (m : A) :
    (Σ a : Nonmajor m, ↥(directedCut next (colorSet ell a.val))) ↪
      ↥(disagreementSet ell next) where
  toFun t := ⟨t.2.val, by
    have hc : ell t.2.val.1 = t.1.val ∧ ell (next t.2.val) ≠ t.1.val := by
      simpa [directedCut, colorSet] using t.2.property
    have hn : ell t.2.val.1 ≠ ell (next t.2.val) :=
      fun h => hc.2 (h.symm.trans hc.1)
    simpa [disagreementSet] using hn⟩
  inj' p q h := by
    rcases p with ⟨⟨a, ha⟩, ⟨x, hx⟩⟩
    rcases q with ⟨⟨b, hb⟩, ⟨y, hy⟩⟩
    have hxy : x = y := congrArg Subtype.val h
    cases hxy
    have hxa : ell x.1 = a := by
      have hc : ell x.1 = a ∧ ell (next x) ≠ a := by
        simpa [directedCut, colorSet] using hx
      exact hc.1
    have hxb : ell x.1 = b := by
      have hc : ell x.1 = b ∧ ell (next x) ≠ b := by
        simpa [directedCut, colorSet] using hy
      exact hc.1
    have hab : a = b := hxa.symm.trans hxb
    cases hab
    rfl

theorem minority_cut_sum_le (ell : X → A) (next : X × D → X) (m : A) :
    (∑ a : Nonmajor m, (directedCut next (colorSet ell a.val)).card) ≤
      (disagreementSet ell next).card := by
  have h := Fintype.card_le_of_injective
    (minorityCutEmbedding ell next m) (minorityCutEmbedding ell next m).injective
  simpa only [Fintype.card_sigma, Fintype.card_coe] using h

theorem minority_expansion_bound (ell : X → A) (next : X × D → X) (m : A)
    (h : ℚ)
    (maximal : ∀ a, (colorSet ell a).card ≤ (colorSet ell m).card)
    (expansion : ∀ S : Finset X, S.card ≤ Fintype.card X / 2 →
      h * (S.card : ℚ) ≤ ((directedCut next S).card : ℚ)) :
    h * ((minoritySet ell m).card : ℚ) ≤ ((disagreementSet ell next).card : ℚ) := by
  have each (a : Nonmajor m) :
      h * ((colorSet ell a.val).card : ℚ) ≤
        ((directedCut next (colorSet ell a.val)).card : ℚ) := by
    apply expansion
    have ha := nonchosen_color_twice_le ell m maximal a.val a.property
    omega
  calc
    h * ((minoritySet ell m).card : ℚ) =
        ∑ a : Nonmajor m, h * ((colorSet ell a.val).card : ℚ) := by
      rw [minority_card_eq_sum, Nat.cast_sum, Finset.mul_sum]
    _ ≤ ∑ a : Nonmajor m, ((directedCut next (colorSet ell a.val)).card : ℚ) :=
      Finset.sum_le_sum (fun a _ => each a)
    _ ≤ ((disagreementSet ell next).card : ℚ) := by
      exact_mod_cast minority_cut_sum_le ell next m

end CloudCounts

section GraphRounding

open DegreeReplacement PoweringWalks

variable {V E A D : Type*} [Fintype V] [Fintype E] [Fintype A] [Fintype D]
variable [DecidableEq V] [DecidableEq E] [DecidableEq A]

def mismatchSet (G : ConstraintGraph V E A) (ell : E → A) (rounded : V → A) :
    Finset E :=
  Finset.univ.filter (fun e => ell e ≠ rounded (G.tail e))

def copiedRejectionCount (G : ConstraintGraph V E A) (ell : E → A) : Nat :=
  (Finset.univ.filter (fun e => G.accepts e (ell e) (ell (G.reverse e)) = false)).card

def innerDisagreementSet (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) (ell : E → A) : Finset (E × D) :=
  Finset.univ.filter (fun ed => ell ed.1 ≠ ell (innerRotation G H ed).1)

noncomputable def roundLabels [Nonempty A]
    (G : ConstraintGraph V E A) (ell : E → A) : V → A :=
  fun v => majority (fun e : Cloud G v => ell e.val)

def mismatchFiberEquiv (G : ConstraintGraph V E A) (ell : E → A)
    (rounded : V → A) :
    (Σ v, ↥(minoritySet (fun e : Cloud G v => ell e.val) (rounded v))) ≃
      ↥(mismatchSet G ell rounded) where
  toFun := by
    rintro ⟨v, ⟨⟨e, he⟩, hbad⟩⟩
    cases he
    exact ⟨e, by simpa [mismatchSet, minoritySet] using hbad⟩
  invFun e :=
    ⟨G.tail e.val, ⟨⟨e.val, rfl⟩, by
      simpa [mismatchSet, minoritySet] using e.property⟩⟩
  left_inv := by
    rintro ⟨v, ⟨⟨e, he⟩, hbad⟩⟩
    cases he
    rfl
  right_inv := by intro e; apply Subtype.ext; rfl

omit [Fintype A] [DecidableEq E] in
theorem mismatch_card_eq_sum (G : ConstraintGraph V E A) (ell : E → A)
    (rounded : V → A) :
    (mismatchSet G ell rounded).card =
      ∑ v, (minoritySet (fun e : Cloud G v => ell e.val) (rounded v)).card := by
  have h := Fintype.card_congr (mismatchFiberEquiv G ell rounded)
  simpa only [Fintype.card_sigma, Fintype.card_coe] using h.symm

def disagreementFiberEquiv (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) (ell : E → A) :
    (Σ v, ↥(disagreementSet (fun e : Cloud G v => ell e.val)
      (fun ed => ((H v).rot ed).1))) ≃ ↥(innerDisagreementSet G H ell) where
  toFun := by
    rintro ⟨v, ⟨⟨⟨e, he⟩, d⟩, hbad⟩⟩
    cases he
    refine ⟨(e, d), ?_⟩
    simpa [disagreementSet, innerDisagreementSet, innerRotation,
      cloudIndexEquiv, cloudRotation] using hbad
  invFun := by
    rintro ⟨⟨e, d⟩, hbad⟩
    refine ⟨G.tail e, ⟨(⟨e, rfl⟩, d), ?_⟩⟩
    simpa [disagreementSet, innerDisagreementSet, innerRotation,
      cloudIndexEquiv, cloudRotation] using hbad
  left_inv := by
    rintro ⟨v, ⟨⟨⟨e, he⟩, d⟩, hbad⟩⟩
    cases he
    rfl
  right_inv := by intro ed; apply Subtype.ext; rfl

omit [Fintype A] [DecidableEq E] in
theorem disagreement_card_eq_sum (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) (ell : E → A) :
    (innerDisagreementSet G H ell).card =
      ∑ v, (disagreementSet (fun e : Cloud G v => ell e.val)
        (fun ed => ((H v).rot ed).1)).card := by
  have h := Fintype.card_congr (disagreementFiberEquiv G H ell)
  simpa only [Fintype.card_sigma, Fintype.card_coe] using h.symm

theorem rounded_mismatch_expansion [Nonempty A]
    (G : ConstraintGraph V E A) (H : ∀ v, PortGraph (Cloud G v) D)
    (ell : E → A) (h : ℚ)
    (expansion : ∀ v (S : Finset (Cloud G v)),
      S.card ≤ Fintype.card (Cloud G v) / 2 →
      h * (S.card : ℚ) ≤ ((directedCut (fun ed => ((H v).rot ed).1) S).card : ℚ)) :
    h * ((mismatchSet G ell (roundLabels G ell)).card : ℚ) ≤
      ((innerDisagreementSet G H ell).card : ℚ) := by
  rw [mismatch_card_eq_sum, disagreement_card_eq_sum, Nat.cast_sum, Nat.cast_sum,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  exact minority_expansion_bound (fun e : Cloud G v => ell e.val)
    (fun ed => ((H v).rot ed).1) (roundLabels G ell v) h
    (majority_maximal (fun e : Cloud G v => ell e.val)) (expansion v)

omit [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq E] in
theorem rounded_endpoint_bound (G : ConstraintGraph V E A)
    (ell : E → A) (rounded : V → A) :
    G.rejectionCount rounded ≤ copiedRejectionCount G ell +
      2 * (mismatchSet G ell rounded).card :=
  dart_rejection_count_le G.tail G.reverse G.accepts ell rounded

omit [Fintype V] [Fintype E] [Fintype A] [Fintype D] [DecidableEq V] [DecidableEq E] in
@[simp] theorem copied_satisfied_inl (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) (ell : E → A) (e : E) (d : D) :
    (replacementGraph G H).edgeSatisfied ell (e, Sum.inl d) =
      decide (ell e = ell (innerRotation G H (e, d)).1) := rfl

omit [Fintype V] [Fintype E] [Fintype A] [Fintype D] [DecidableEq V] [DecidableEq E] in
@[simp] theorem copied_satisfied_inr (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) (ell : E → A) (e : E) (u : Unit) :
    (replacementGraph G H).edgeSatisfied ell (e, Sum.inr u) =
      G.accepts e (ell e) (ell (G.reverse e)) := rfl

omit [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq E] in

theorem replacement_rejection_split (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) (ell : E → A) :
    (replacementGraph G H).rejectionCount ell =
      copiedRejectionCount G ell + (innerDisagreementSet G H ell).card := by
  classical
  simp only [rejectionCount_eq_sum, Fintype.sum_prod_type, Fintype.sum_sum_type,
    copied_satisfied_inl, copied_satisfied_inr, decide_eq_false_iff_not,
    Fintype.sum_unique, Finset.sum_add_distrib]
  simp only [copiedRejectionCount, innerDisagreementSet, Finset.card_eq_sum_ones,
    Finset.sum_filter, Fintype.sum_prod_type]
  exact Nat.add_comm _ _

theorem replacement_soundness [Nonempty A]
    (G : ConstraintGraph V E A) (H : ∀ v, PortGraph (Cloud G v) D)
    (expansion : ∀ v (S : Finset (Cloud G v)),
      S.card ≤ Fintype.card (Cloud G v) / 2 →
      2 * S.card ≤ (directedCut (fun ed => ((H v).rot ed).1) S).card)
    (ell : E → A) :
    G.rejectionCount (roundLabels G ell) ≤ (replacementGraph G H).rejectionCount ell := by
  have hc := rounded_mismatch_expansion G H ell 2 (by
    intro v S hS
    exact_mod_cast expansion v S hS)
  have hcNat : 2 * (mismatchSet G ell (roundLabels G ell)).card ≤
      (innerDisagreementSet G H ell).card := by exact_mod_cast hc
  rw [replacement_rejection_split]
  exact (rounded_endpoint_bound G ell (roundLabels G ell)).trans
    (Nat.add_le_add_left hcNat _)

theorem padded_replacement_soundness [Nonempty A]
    (G : ConstraintGraph V E A) (dummy : V → Type*) [∀ v, Fintype (dummy v)]
    [∀ v, DecidableEq (dummy v)]
    (H : ∀ v, PortGraph (Cloud (paddedGraph G dummy) v) D)
    (expansion : ∀ v (S : Finset (Cloud (paddedGraph G dummy) v)),
      S.card ≤ Fintype.card (Cloud (paddedGraph G dummy) v) / 2 →
      2 * S.card ≤ (directedCut (fun ed => ((H v).rot ed).1) S).card)
    (ell : PaddedDart G dummy → A) :
    G.rejectionCount (roundLabels (paddedGraph G dummy) ell) ≤
      (paddedReplacementGraph G dummy H).rejectionCount ell := by
  simpa only [paddedReplacementGraph, padded_rejectionCount] using
    replacement_soundness (paddedGraph G dummy) H expansion ell

end GraphRounding

theorem combine_counts (R b M c : Nat) (h : ℚ) (hh : 0 < h)
    (endpoint : R ≤ b + 2 * M) (cloud : h * (M : ℚ) ≤ (c : ℚ)) :
    (R : ℚ) ≤ max 1 (2 / h) * ((b : ℚ) + (c : ℚ)) := by
  let K : ℚ := max 1 (2 / h)
  have hK : 1 ≤ K := le_max_left _ _
  have hK0 : 0 ≤ K := le_trans zero_le_one hK
  have hcoef : 2 ≤ K * h := (div_le_iff₀ hh).mp (le_max_right _ _)
  have hm : (2 : ℚ) * M ≤ K * c := by
    calc
      (2 : ℚ) * M ≤ (K * h) * M :=
        mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg M)
      _ = K * (h * M) := mul_assoc _ _ _
      _ ≤ K * c := mul_le_mul_of_nonneg_left cloud hK0
  have hb : (b : ℚ) ≤ K * b := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hK (Nat.cast_nonneg b)
  have hr : (R : ℚ) ≤ (b : ℚ) + 2 * (M : ℚ) := by exact_mod_cast endpoint
  exact hr.trans ((add_le_add hb hm).trans_eq (mul_add K (b : ℚ) (c : ℚ)).symm)

end DFVSGames.Foundations.PCP.CloudRounding


noncomputable section
namespace DFVSGames.Foundations.PCP.SpectralCut

open scoped BigOperators
open PoweringWalks SpectralReturn

section Indicators
variable {V : Type*} [Fintype V] [DecidableEq V]

def indicator (S : Finset V) (v : V) : ℝ := if v ∈ S then 1 else 0

theorem mean_indicator (S : Finset V) :
    mean (indicator S) = (S.card : ℝ) / (Fintype.card V : ℝ) := by
  have hf : Finset.univ.filter (fun v : V => v ∈ S) = S := by
    ext v
    simp
  rw [mean_eq_sum_div_card]
  simp only [indicator, Finset.sum_boole, hf]

theorem energy_indicator (S : Finset V) : energy (indicator S) = mean (indicator S) := by
  unfold energy
  congr 1
  funext v
  unfold indicator
  split_ifs <;> norm_num

omit [Fintype V] in
theorem indicator_nonnegative (S : Finset V) (v : V) : 0 ≤ indicator S v := by
  unfold indicator
  split_ifs <;> norm_num
end Indicators

variable {V D : Type*} [Fintype V] [Fintype D] [DecidableEq V]

def cut (G : PortGraph V D) (S : Finset V) : Finset (V × D) :=
  Finset.univ.filter (fun e => e.1 ∈ S ∧ (G.rot e).1 ∉ S)

section Nonempty
variable [Nonempty V] [Nonempty D] (G : PortGraph V D)

omit [Nonempty V] in

theorem cut_density_eq (S : Finset V) :
    ((cut G S).card : ℝ) / (Fintype.card (V × D) : ℝ) =
      mean (indicator S) - correlation (indicator S) (averagingOperator G (indicator S)) := by
  classical
  calc
    _ = mean (indicator (cut G S)) := (mean_indicator (cut G S)).symm
    _ = mean (fun e : V × D => indicator S e.1 -
        indicator S e.1 * indicator S (G.rot e).1) := by
      congr 1
      funext e
      by_cases hv : e.1 ∈ S <;> by_cases hw : (G.rot e).1 ∈ S <;>
        simp [indicator, cut, hv, hw]
    _ = mean (fun v => mean (fun d : D => indicator S v -
        indicator S v * indicator S (G.rot (v,d)).1)) := mean_prod _
    _ = mean (fun v => indicator S v -
        indicator S v * averagingOperator G (indicator S) v) := by
      congr 1
      funext v
      rw [mean_sub, mean_const, mean_mul_left]
      rfl
    _ = _ := mean_sub _ _

theorem cut_density_ge_variance
    (certificate : SpectralCertificate G (1/2)) (S : Finset V) :
    (1/2:ℝ) * mean (indicator S) * (1 - mean (indicator S)) ≤
      ((cut G S).card : ℝ) / (Fintype.card (V × D) : ℝ) := by
  let f := indicator S
  have hz : mean (fun v => f v - mean f) = 0 := by
    rw [mean_sub, mean_const, sub_self]
  have he : energy (fun v => f v - mean f) = mean f - mean f ^ 2 := by
    rw [energy_sub_const, energy_indicator]
    ring
  have hb := zero_mean_correlation_bound G (1/2) certificate
    (fun v => f v - mean f) hz 1
  have hc := correlation_centered G f 1
  simp only [iterateOperator, pow_one, he] at hb hc
  rw [cut_density_eq]
  change (1/2:ℝ) * mean f * (1 - mean f) ≤
    mean f - correlation f (averagingOperator G f)
  nlinarith

theorem cut_density_ge_quarter
    (certificate : SpectralCertificate G (1/2)) (S : Finset V)
    (hsmall : 2 * S.card ≤ Fintype.card V) :
    mean (indicator S) / 4 ≤
      ((cut G S).card : ℝ) / (Fintype.card (V × D) : ℝ) := by
  have hN : (0:ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hp0 : 0 ≤ mean (indicator S) := mean_nonnegative _ (indicator_nonnegative S)
  have hp : mean (indicator S) ≤ (1/2:ℝ) := by
    rw [mean_indicator]
    apply (div_le_iff₀ hN).mpr
    have hs : (2:ℝ) * (S.card : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hsmall
    nlinarith
  have hv := cut_density_ge_variance G certificate S
  have hprod := mul_nonneg hp0 (sub_nonneg.mpr hp)
  nlinarith

theorem cut_card_ge_quarter_degree
    (certificate : SpectralCertificate G (1/2)) (S : Finset V)
    (hsmall : 2 * S.card ≤ Fintype.card V) :
    (Fintype.card D : ℝ) * (S.card : ℝ) / 4 ≤ ((cut G S).card : ℝ) := by
  have hN : (0:ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hD : (0:ℝ) < Fintype.card D := by exact_mod_cast Fintype.card_pos
  have h := cut_density_ge_quarter G certificate S hsmall
  rw [Fintype.card_prod, Nat.cast_mul] at h
  have hh := (le_div_iff₀ (mul_pos hN hD)).mp h
  have he : mean (indicator S) / 4 *
      ((Fintype.card V : ℝ) * (Fintype.card D : ℝ)) =
        (Fintype.card D : ℝ) * (S.card : ℝ) / 4 := by
    rw [mean_indicator]
    field_simp [ne_of_gt hN]

  rw [he] at hh
  exact hh

theorem degree_mul_card_le_four_cut
    (certificate : SpectralCertificate G (1/2)) (S : Finset V)
    (hsmall : 2 * S.card ≤ Fintype.card V) :
    Fintype.card D * S.card ≤ 4 * (cut G S).card := by
  have h := cut_card_ge_quarter_degree G certificate S hsmall
  have hr : (Fintype.card D : ℝ) * (S.card : ℝ) ≤ 4 * ((cut G S).card : ℝ) := by
    linarith
  exact_mod_cast hr

theorem cut_card_ge_quarter_degree_of_card_le_half
    (certificate : SpectralCertificate G (1/2)) (S : Finset V)
    (hsmall : S.card ≤ Fintype.card V / 2) :
    (Fintype.card D : ℝ) * (S.card : ℝ) / 4 ≤ ((cut G S).card : ℝ) :=
  cut_card_ge_quarter_degree G certificate S (by omega)
end Nonempty

theorem cut_card_ge_twice (G : PortGraph V D)
    (certificate : SpectralCertificate G (1/2)) (hdegree : 8 ≤ Fintype.card D)
    (S : Finset V) (hsmall : 2 * S.card ≤ Fintype.card V) :
    2 * S.card ≤ (cut G S).card := by
  let : Nonempty D := Fintype.card_pos_iff.mp (by omega)
  rcases isEmpty_or_nonempty V with hV | hV
  · let := hV
    have hzero : Fintype.card V = 0 := Fintype.card_eq_zero
    have hs : S.card = 0 := by omega
    simp only [hs, mul_zero, Nat.zero_le]
  · let := hV
    have h := degree_mul_card_le_four_cut G certificate S hsmall
    have hdeg := Nat.mul_le_mul_right S.card hdegree
    omega

end DFVSGames.Foundations.PCP.SpectralCut
end


noncomputable section

namespace DFVSGames.Foundations.PCP.Regularization

open PoweringWalks DegreeReplacement

variable {V E A : Type*} [Fintype V] [Fintype E] [Fintype A]
variable [DecidableEq V] [DecidableEq E] [DecidableEq A]

abbrev Vertex (G : ConstraintGraph V E A) := PaddedDart G (CloudPadding.dummy G)
abbrev Port := ExpanderFamily.Port ⊕ Unit

def degree : Nat := Fintype.card Port

theorem degree_eq : degree = Fintype.card ExpanderFamily.Port + 1 := by
  simp [degree, Port]

theorem degree_positive : 0 < degree := by rw [degree_eq]; omega

def cloudEquiv (G : ConstraintGraph V E A) (v : V)
    (hk : 0 < Fintype.card (Cloud G v)) :
    ExpanderFamily.Vertex (ExpanderFamily.level (Fintype.card (Cloud G v))) ≃
      Cloud (paddedGraph G (CloudPadding.dummy G)) v :=
  Fintype.equivOfCardEq (CloudPadding.card_cloud_eq_family G v hk).symm

def cloudGraph (G : ConstraintGraph V E A) (v : V) :
    PortGraph (Cloud (paddedGraph G (CloudPadding.dummy G)) v) ExpanderFamily.Port :=
  if hk : Fintype.card (Cloud G v) = 0 then
    { rot := Equiv.refl _
      rot_involutive := fun _ => rfl }
  else
    GraphTransport.reindex
      (ExpanderFamily.family (ExpanderFamily.level (Fintype.card (Cloud G v))))
      (cloudEquiv G v (Nat.pos_of_ne_zero hk)) (Equiv.refl _)

omit [Fintype A] [DecidableEq E] [DecidableEq A] in
theorem cloudGraph_of_pos (G : ConstraintGraph V E A) (v : V)
    (hk : 0 < Fintype.card (Cloud G v)) :
    cloudGraph G v = GraphTransport.reindex
      (ExpanderFamily.family (ExpanderFamily.level (Fintype.card (Cloud G v))))
      (cloudEquiv G v hk) (Equiv.refl _) := by
  simp only [cloudGraph, dite_eq_right (Nat.ne_of_gt hk)]

omit [Fintype A] [DecidableEq E] [DecidableEq A] in
theorem cloudGraph_certificate_of_pos (G : ConstraintGraph V E A) (v : V)
    (hk : 0 < Fintype.card (Cloud G v)) :
    SpectralReturn.SpectralCertificate (cloudGraph G v) (1 / 2 : ℝ) := by
  rw [cloudGraph_of_pos G v hk]
  exact GraphTransport.reindex_spectralCertificate _ _ _ _
    (ExpanderFamily.family_certificate _)

omit [Fintype A] [DecidableEq A] in

theorem cloud_expansion (G : ConstraintGraph V E A) (v : V)
    (S : Finset (Cloud (paddedGraph G (CloudPadding.dummy G)) v))
    (hsmall : S.card ≤
      Fintype.card (Cloud (paddedGraph G (CloudPadding.dummy G)) v) / 2) :
    2 * S.card ≤
      (CloudRounding.directedCut (fun ed => ((cloudGraph G v).rot ed).1) S).card := by
  by_cases hk : Fintype.card (Cloud G v) = 0
  · have hzero : Fintype.card (Cloud (paddedGraph G (CloudPadding.dummy G)) v) = 0 := by
      rw [CloudPadding.card_cloud, hk, CloudPadding.paddedSize_zero]
    have hs : S.card = 0 := by omega
    simp only [hs, mul_zero, Nat.zero_le]
  · exact SpectralCut.cut_card_ge_twice (cloudGraph G v)
      (cloudGraph_certificate_of_pos G v (Nat.pos_of_ne_zero hk))
      ExpanderFamily.port_degree_ge_eight S (by omega)

def portGraph (G : ConstraintGraph V E A) : PortGraph (Vertex G) Port :=
  paddedReplacementPortGraph G (CloudPadding.dummy G) (cloudGraph G)

def graph (G : ConstraintGraph V E A) :
    ConstraintGraph (Vertex G) (Vertex G × Port) A :=
  paddedReplacementGraph G (CloudPadding.dummy G) (cloudGraph G)

omit [Fintype A] [DecidableEq E] in
@[simp] theorem graph_tail (G : ConstraintGraph V E A) (e : Vertex G × Port) :
    (graph G).tail e = e.1 := rfl

omit [Fintype A] [DecidableEq E] in
theorem graph_reverse (G : ConstraintGraph V E A) :
    (graph G).reverse = (portGraph G).rot := rfl

def degreeEquiv (G : ConstraintGraph V E A) (v : Vertex G) :
    Cloud (graph G) v ≃ Port where
  toFun e := e.val.2
  invFun d := ⟨(v, d), rfl⟩
  left_inv := by
    rintro ⟨⟨w, d⟩, hw⟩
    change w = v at hw
    cases hw
    rfl
  right_inv _ := rfl

omit [Fintype A] in
theorem fixed_degree (G : ConstraintGraph V E A) (v : Vertex G) :
    Fintype.card (Cloud (graph G) v) = degree :=
  Fintype.card_congr (degreeEquiv G v)

omit [Fintype A] [DecidableEq E] [DecidableEq A] in
theorem vertex_count_le (G : ConstraintGraph V E A) :
    Fintype.card (Vertex G) ≤ ExpanderFamily.growth * Fintype.card E :=
  CloudPadding.card_paddedDart_le G

omit [Fintype A] [DecidableEq E] [DecidableEq A] in
theorem dart_count (G : ConstraintGraph V E A) :
    Fintype.card (Vertex G × Port) = Fintype.card (Vertex G) * degree :=
  Fintype.card_prod _ _

omit [Fintype A] [DecidableEq E] [DecidableEq A] in
theorem dart_count_le (G : ConstraintGraph V E A) :
    Fintype.card (Vertex G × Port) ≤
      (ExpanderFamily.growth * degree) * Fintype.card E := by
  rw [dart_count]
  calc
    Fintype.card (Vertex G) * degree ≤
        (ExpanderFamily.growth * Fintype.card E) * degree :=
      Nat.mul_le_mul_right degree (vertex_count_le G)
    _ = (ExpanderFamily.growth * degree) * Fintype.card E := Nat.mul_right_comm _ _ _

def liftLabel (G : ConstraintGraph V E A) (labeling : V → A) : Vertex G → A :=
  DegreeReplacement.liftLabel (paddedGraph G (CloudPadding.dummy G)) labeling

omit [Fintype A] [DecidableEq E] in

theorem lift_rejectionCount (G : ConstraintGraph V E A) (labeling : V → A) :
    (graph G).rejectionCount (liftLabel G labeling) = G.rejectionCount labeling :=
  paddedReplacement_rejectionCount G (CloudPadding.dummy G) (cloudGraph G) labeling

omit [Fintype A] [DecidableEq E] in
theorem completeness (G : ConstraintGraph V E A) (h : G.Satisfiable) :
    (graph G).Satisfiable :=
  replacement_satisfiable (paddedGraph G (CloudPadding.dummy G)) (cloudGraph G)
    (padded_satisfiable G (CloudPadding.dummy G) h)

def roundLabels [Nonempty A] (G : ConstraintGraph V E A) (ell : Vertex G → A) : V → A :=
  CloudRounding.roundLabels (paddedGraph G (CloudPadding.dummy G)) ell

theorem soundness [Nonempty A] (G : ConstraintGraph V E A) (ell : Vertex G → A) :
    G.rejectionCount (roundLabels G ell) ≤ (graph G).rejectionCount ell :=
  CloudRounding.padded_replacement_soundness G (CloudPadding.dummy G)
    (cloudGraph G) (cloud_expansion G) ell

theorem exists_rounding [Nonempty A] (G : ConstraintGraph V E A) (ell : Vertex G → A) :
    ∃ labeling : V → A, G.rejectionCount labeling ≤ (graph G).rejectionCount ell :=
  ⟨roundLabels G ell, soundness G ell⟩

theorem soundness_of_uniform_lower_bound [Nonempty A] (G : ConstraintGraph V E A)
    (k : Nat) (lower : ∀ labeling : V → A, k ≤ G.rejectionCount labeling)
    (ell : Vertex G → A) : k ≤ (graph G).rejectionCount ell :=
  (lower (roundLabels G ell)).trans (soundness G ell)

end DFVSGames.Foundations.PCP.Regularization

end

end OAI
