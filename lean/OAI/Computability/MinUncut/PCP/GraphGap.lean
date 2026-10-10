import Mathlib
import OAI.Computability.MinUncut.PCP.ExpanderFamily
import OAI.Computability.MinUncut.PCP.Overlay

namespace OAI

noncomputable section

namespace MinUncutGames.Foundations.PCP.ConstraintGraph

variable {V E A : Type*}

section Minimum

variable [Fintype V] [Fintype E] [Fintype A] [Nonempty A]

def rejectionCounts (G : ConstraintGraph V E A) : Finset Nat := by
  classical
  exact Finset.univ.image G.rejectionCount

theorem rejectionCounts_nonempty (G : ConstraintGraph V E A) :
    G.rejectionCounts.Nonempty := by
  classical
  exact Finset.univ_nonempty.image G.rejectionCount

def minimumRejections (G : ConstraintGraph V E A) : Nat :=
  G.rejectionCounts.min' G.rejectionCounts_nonempty

theorem minimumRejections_le (G : ConstraintGraph V E A) (labeling : V → A) :
    G.minimumRejections ≤ G.rejectionCount labeling := by
  classical
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨labeling, Finset.mem_univ _, rfl⟩)

theorem exists_minimizer (G : ConstraintGraph V E A) :
    ∃ labeling : V → A, G.rejectionCount labeling = G.minimumRejections := by
  classical
  have h := Finset.min'_mem G.rejectionCounts G.rejectionCounts_nonempty
  obtain ⟨labeling, _, heq⟩ := Finset.mem_image.mp h
  exact ⟨labeling, heq⟩

theorem le_minimumRejections_iff (G : ConstraintGraph V E A) (bound : Nat) :
    bound ≤ G.minimumRejections ↔ ∀ labeling : V → A, bound ≤ G.rejectionCount labeling := by
  constructor
  · intro h labeling
    exact h.trans (G.minimumRejections_le labeling)
  · intro h
    obtain ⟨labeling, heq⟩ := G.exists_minimizer
    rw [← heq]
    exact h labeling

theorem minimumRejections_le_card (G : ConstraintGraph V E A) :
    G.minimumRejections ≤ Fintype.card E := by
  obtain ⟨labeling, heq⟩ := G.exists_minimizer
  rw [← heq]
  exact G.rejectionCount_le labeling

omit [Fintype V] [Fintype A] [Nonempty A] in
theorem rejectionCount_eq_zero_iff (G : ConstraintGraph V E A) (labeling : V → A) :
    G.rejectionCount labeling = 0 ↔ ∀ e, G.edgeSatisfied labeling e = true := by
  classical
  constructor
  · intro h e
    have hempty : G.rejectedDarts labeling = ∅ := Finset.card_eq_zero.mp h
    cases he : G.edgeSatisfied labeling e with
    | false =>
        have hm := (G.mem_rejectedDarts labeling e).mpr he
        rw [hempty] at hm
        simp at hm
    | true => rfl
  · intro h
    simp [rejectionCount, rejectedDarts, h]

theorem minimumRejections_eq_zero_iff (G : ConstraintGraph V E A) :
    G.minimumRejections = 0 ↔ G.Satisfiable := by
  constructor
  · intro h
    obtain ⟨labeling, heq⟩ := G.exists_minimizer
    exact ⟨labeling, (G.rejectionCount_eq_zero_iff labeling).mp (heq.trans h)⟩
  · rintro ⟨labeling, h⟩
    have hc := (G.rejectionCount_eq_zero_iff labeling).mpr h
    exact Nat.eq_zero_of_le_zero (hc ▸ G.minimumRejections_le labeling)

def gap (G : ConstraintGraph V E A) : ℝ :=
  (G.minimumRejections : ℝ) / Fintype.card E

theorem gap_nonnegative (G : ConstraintGraph V E A) : 0 ≤ G.gap :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem gap_le_one [Nonempty E] (G : ConstraintGraph V E A) : G.gap ≤ 1 := by
  have he : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ he).mpr
  simpa only [one_mul] using (Nat.cast_le.mpr G.minimumRejections_le_card :
    (G.minimumRejections : ℝ) ≤ (Fintype.card E : ℝ))

theorem gap_eq_zero_iff [Nonempty E] (G : ConstraintGraph V E A) :
    G.gap = 0 ↔ G.Satisfiable := by
  have he : (Fintype.card E : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [gap, div_eq_zero_iff, he, or_false, Nat.cast_eq_zero]
  exact G.minimumRejections_eq_zero_iff

theorem le_gap_iff [Nonempty E] (G : ConstraintGraph V E A) (ε : ℝ) :
    ε ≤ G.gap ↔ ∀ labeling : V → A,
      ε * Fintype.card E ≤ (G.rejectionCount labeling : ℝ) := by
  have he : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  change ε ≤ (G.minimumRejections : ℝ) / Fintype.card E ↔ _
  rw [le_div_iff₀ he]
  constructor
  · intro h labeling
    exact h.trans (Nat.cast_le.mpr (G.minimumRejections_le labeling))
  · intro h
    obtain ⟨labeling, heq⟩ := G.exists_minimizer
    simpa only [heq] using h labeling

theorem inverse_card_le_gap_of_unsatisfiable [Nonempty E]
    (G : ConstraintGraph V E A) (unsat : ¬ G.Satisfiable) :
    1 / (Fintype.card E : ℝ) ≤ G.gap := by
  apply (G.le_gap_iff _).mpr
  intro labeling
  have he : (Fintype.card E : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hc : (1 : ℝ) ≤ (G.rejectionCount labeling : ℝ) := by
    exact_mod_cast G.rejectionCount_positive unsat labeling
  simpa only [div_mul_cancel₀ _ he] using hc

end Minimum

variable {W D B : Type*}

def reindex (G : ConstraintGraph V E A) (vertices : V ≃ W) (darts : E ≃ D)
    (labels : A ≃ B) : ConstraintGraph W D B where
  reverse := darts.symm.trans (G.reverse.trans darts)
  reverse_involutive := by
    intro d
    change darts (G.reverse (darts.symm (darts (G.reverse (darts.symm d))))) = d
    rw [darts.symm_apply_apply, G.reverse_involutive, darts.apply_symm_apply]
  tail := fun d => vertices (G.tail (darts.symm d))
  accepts := fun d a b => G.accepts (darts.symm d) (labels.symm a) (labels.symm b)
  reverse_accepts := by
    intro d a b
    simpa only [Equiv.trans_apply, darts.symm_apply_apply] using
      G.reverse_accepts (darts.symm d) (labels.symm a) (labels.symm b)

def labelingEquiv (vertices : V ≃ W) (labels : A ≃ B) : (V → A) ≃ (W → B) where
  toFun := fun labeling w => labels (labeling (vertices.symm w))
  invFun := fun labeling v => labels.symm (labeling (vertices v))
  left_inv := by intro labeling; funext v; simp
  right_inv := by intro labeling; funext w; simp

theorem reindex_edgeSatisfied (G : ConstraintGraph V E A)
    (vertices : V ≃ W) (darts : E ≃ D) (labels : A ≃ B)
    (labeling : V → A) (e : E) :
    (G.reindex vertices darts labels).edgeSatisfied (labelingEquiv vertices labels labeling)
      (darts e) = G.edgeSatisfied labeling e := by
  simp [reindex, labelingEquiv, edgeSatisfied, head, Equiv.trans_apply]

theorem reindex_rejectionCount [Fintype E] [Fintype D] (G : ConstraintGraph V E A)
    (vertices : V ≃ W) (darts : E ≃ D) (labels : A ≃ B) (labeling : V → A) :
    (G.reindex vertices darts labels).rejectionCount (labelingEquiv vertices labels labeling) =
      G.rejectionCount labeling := by
  classical
  unfold rejectionCount
  symm
  apply Finset.card_bij (fun e _ => darts e)
  · intro e he
    rw [mem_rejectedDarts, reindex_edgeSatisfied]
    exact (G.mem_rejectedDarts labeling e).mp he
  · intro e _ f _ h
    exact darts.injective h
  · intro d hd
    refine ⟨darts.symm d, ?_, darts.apply_symm_apply d⟩
    rw [mem_rejectedDarts]
    rw [← reindex_edgeSatisfied G vertices darts labels labeling (darts.symm d)]
    rw [darts.apply_symm_apply]
    exact (mem_rejectedDarts _ _ _).mp hd

variable [Fintype V] [Fintype E] [Fintype A] [Nonempty A]
  [Fintype W] [Fintype D] [Fintype B] [Nonempty B]

omit [Nonempty A] [Nonempty B] in
theorem rejectionCounts_reindex (G : ConstraintGraph V E A)
    (vertices : V ≃ W) (darts : E ≃ D) (labels : A ≃ B) :
    (G.reindex vertices darts labels).rejectionCounts = G.rejectionCounts := by
  classical
  ext n
  simp only [rejectionCounts, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨labeling, hn⟩
    refine ⟨(labelingEquiv vertices labels).symm labeling, ?_⟩
    rw [← reindex_rejectionCount G vertices darts labels,
      Equiv.apply_symm_apply]
    exact hn
  · rintro ⟨labeling, hn⟩
    refine ⟨labelingEquiv vertices labels labeling, ?_⟩
    rw [reindex_rejectionCount]
    exact hn

theorem minimumRejections_reindex (G : ConstraintGraph V E A)
    (vertices : V ≃ W) (darts : E ≃ D) (labels : A ≃ B) :
    (G.reindex vertices darts labels).minimumRejections = G.minimumRejections := by
  unfold minimumRejections
  simp only [rejectionCounts_reindex]

theorem gap_reindex (G : ConstraintGraph V E A)
    (vertices : V ≃ W) (darts : E ≃ D) (labels : A ≃ B) :
    (G.reindex vertices darts labels).gap = G.gap := by
  unfold gap
  rw [minimumRejections_reindex, Fintype.card_congr darts]

theorem satisfiable_reindex (G : ConstraintGraph V E A)
    (vertices : V ≃ W) (darts : E ≃ D) (labels : A ≃ B) :
    (G.reindex vertices darts labels).Satisfiable ↔ G.Satisfiable := by
  rw [← minimumRejections_eq_zero_iff, minimumRejections_reindex,
    minimumRejections_eq_zero_iff]

end MinUncutGames.Foundations.PCP.ConstraintGraph

end
namespace MinUncutGames.Foundations.PCP.PreprocessingOverlayTables

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
      convert G.reverse_accepts (x.1, ports.symm x.2) a b using 1
      rfl)

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

theorem constraintGraph_ext {V E A : Type*} {G H : ConstraintGraph V E A}
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
  apply constraintGraph_ext
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

end MinUncutGames.Foundations.PCP.PreprocessingOverlayTables

namespace MinUncutGames.Foundations.PCP.CloudRounding

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

end MinUncutGames.Foundations.PCP.CloudRounding

end OAI
