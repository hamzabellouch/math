import OAI.Computability.UniqueGames.PCP.AlphabetReductionLemmas
import OAI.Computability.UniqueGames.PCP.CloudRoundingLemmas
import OAI.Computability.UniqueGames.PCP.ExpanderTables
import OAI.Computability.UniqueGames.PCP.OverlayLemmas

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayTables

open PoweringWalks

/-- Old ports precede expander ports. -/
def overlayPorts (d e : Nat) : (Fin d ⊕ Fin e) ≃ Fin (d + e) := finSumFinEquiv

@[simp] theorem overlayPorts_inl_val (d e : Nat) (i : Fin d) :
    (overlayPorts d e (Sum.inl i)).val = i.val := rfl

@[simp] theorem overlayPorts_inr_val (d e : Nat) (i : Fin e) :
    (overlayPorts d e (Sum.inr i)).val = d + i.val := rfl

/-- False/stay ports occupy rows `0,...,d-1`; true/move ports occupy
rows `d,...,2*d-1`, before the vertex offset is added. -/
def lazyPorts (d : Nat) : (Bool × Fin d) ≃ Fin (2 * d) :=
  (Equiv.prodCongr finTwoEquiv.symm (Equiv.refl (Fin d))).trans finProdFinEquiv

@[simp] theorem lazyPorts_false_val (d : Nat) (i : Fin d) :
    (lazyPorts d (false, i)).val = i.val := by
  simp [lazyPorts, finTwoEquiv, finProdFinEquiv]

@[simp] theorem lazyPorts_true_val (d : Nat) (i : Fin d) :
    (lazyPorts d (true, i)).val = i.val + d := by
  simp [lazyPorts, finTwoEquiv, finProdFinEquiv]

/-- Materialize explicitly supplied pair-dart semantics in numbered port
coordinates. The executable rotation only conjugates `G.reverse` by `ports`.
The hypothesis about reversal affects proofs, not stored data. -/
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

private theorem constraintGraph_ext {V E A : Type*} {G H : ConstraintGraph V E A}
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

/-- Add the expander's stored ports; every new constraint always accepts. -/
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

end UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayTables

end

end OAI
