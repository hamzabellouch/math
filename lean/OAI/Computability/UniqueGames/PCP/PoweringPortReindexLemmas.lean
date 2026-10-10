import OAI.Computability.UniqueGames.PCP.CloudRoundingLemmas
import OAI.Computability.UniqueGames.PCP.PoweringTableSemanticsLemmas
import OAI.Computability.UniqueGames.PCP.PreprocessingTableSpectral
import OAI.Computability.UniqueGames.PCP.ZigzagGraphsLemmas

namespace OAI

section

/-! Exact transport of powering through a change of ports. The target's actual
address selector is pulled back, so no compatibility of enumeration orders or
consistency restriction on raw padded labels is needed. -/

noncomputable section
namespace UniqueGamesTheorem.Foundations.PCP.PoweringPortReindex
open PoweringWalks PoweringLabels PoweringReach PoweringTest
open SpectralReturn PoweringSoundness

variable {V D E A : Type*}

def wordEquiv (ports : D ≃ E) (n : Nat) : (Fin n → D) ≃ (Fin n → E) where
  toFun p := fun i => ports (p i)
  invFun p := fun i => ports.symm (p i)
  left_inv p := by funext i; exact ports.symm_apply_apply (p i)
  right_inv p := by funext i; exact ports.apply_symm_apply (p i)

def walkEquiv (ports : D ≃ E) (n : Nat) : Walk V D n ≃ Walk V E n :=
  Equiv.prodCongr (Equiv.refl V) (wordEquiv ports n)

def addressEquiv (ports : D ≃ E) (t : Nat) : PortWords D t ≃ PortWords E t where
  toFun w := ⟨w.1, wordEquiv ports w.1.val w.2⟩
  invFun w := ⟨w.1, (wordEquiv ports w.1.val).symm w.2⟩
  left_inv w := by rcases w with ⟨n,p⟩; simp
  right_inv w := by rcases w with ⟨n,p⟩; simp

/-- Pull target raw labels back to old port coordinates; this is a bijection. -/
def labelEquiv (ports : D ≃ E) (t : Nat) : PaddedLabel E t A ≃ PaddedLabel D t A where
  toFun a := fun w => a (addressEquiv ports t w)
  invFun a := fun w => a ((addressEquiv ports t).symm w)
  left_inv a := by funext w; simp
  right_inv a := by funext w; simp

variable (G : PortGraph V D) (H : PortGraph V E) (ports : D ≃ E)
variable (rotation : ∀ v d, H.rot (v, ports d) =
  ((G.rot (v,d)).1, ports (G.rot (v,d)).2))

include rotation

theorem wordEnd_map (n : Nat) (v : V) (p : Fin n → D) :
    wordEnd H n v (wordEquiv ports n p) = wordEnd G n v p := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    simp only [wordEnd, next, wordEquiv, Equiv.coe_fn_mk, rotation]
    exact ih _ _

theorem endpoint_map (n : Nat) (w : Walk V D n) :
    endpoint H (walkEquiv ports n w) = endpoint G w :=
  wordEnd_map G H ports rotation n w.1 w.2

theorem reach_iff (t : Nat) (v u : V) :
    (∃ n, n ≤ t ∧ ∃ p : Fin n → D, wordEnd G n v p = u) ↔
    (∃ n, n ≤ t ∧ ∃ p : Fin n → E, wordEnd H n v p = u) := by
  constructor
  · rintro ⟨n,hn,p,hp⟩
    exact ⟨n,hn,wordEquiv ports n p,(wordEnd_map G H ports rotation n v p).trans hp⟩
  · rintro ⟨n,hn,p,hp⟩
    refine ⟨n,hn,(wordEquiv ports n).symm p,?_⟩
    rw [← wordEnd_map G H ports rotation, Equiv.apply_symm_apply]
    exact hp

def ballEquiv (t : Nat) (v : V) : Ball G t v ≃ Ball H t v where
  toFun u := ⟨u.val,(reach_iff G H ports rotation t v u.val).mp u.property⟩
  invFun u := ⟨u.val,(reach_iff G H ports rotation t v u.val).mpr u.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem wordToBall_map (t : Nat) (v : V) (w : PortWords D t) :
    wordToBall H t v (addressEquiv ports t w) =
      ballEquiv G H ports rotation t v (wordToBall G t v w) := by
  apply Subtype.ext
  exact wordEnd_map G H ports rotation w.1.val v w.2

/-- Use the target selector, including its concrete enumeration choices. -/
def pullSelector {t : Nat} {v : V} (S : AddressSelector H t v) :
    AddressSelector G t v where
  address u := (addressEquiv ports t).symm
    (S.address (ballEquiv G H ports rotation t v u))
  correct u := by
    apply (ballEquiv G H ports rotation t v).injective
    rw [← wordToBall_map, Equiv.apply_symm_apply, S.correct]

theorem decode_pullSelector {t : Nat} {v : V} (S : AddressSelector H t v)
    (a : PaddedLabel E t A) (u : Ball G t v) :
    decode (pullSelector G H ports rotation S) (labelEquiv ports t a) u =
      decode S a (ballEquiv G H ports rotation t v u) := by
  simp [decode, pullSelector, labelEquiv]

theorem decode_transport {t : Nat} (selectors : ∀v, AddressSelector H t v)
    (a : PaddedLabel E t A) {v w : V} (hvw : v = w)
    (u : Ball G t v) (u' : Ball H t w) (hu : u.val = u'.val) :
    decode (pullSelector G H ports rotation (selectors v)) (labelEquiv ports t a) u =
      decode (selectors w) a u' := by
  subst w
  rw [decode_pullSelector]
  congr 1
  exact Subtype.ext hu

theorem opinionAt_pullSelector (t : Nat) (selectors : ∀v, AddressSelector H t v)
    (labels : V → PaddedLabel E t A) (fallback : A) (u v : V) :
    PoweringOpinions.opinionAt G t (fun v => pullSelector G H ports rotation (selectors v))
      (fun v => labelEquiv ports t (labels v)) fallback u v =
    PoweringOpinions.opinionAt H t selectors labels fallback u v := by
  classical
  unfold PoweringOpinions.opinionAt
  split_ifs with hG hH hH
  · exact decode_pullSelector G H ports rotation (selectors v) (labels v) ⟨u,hG⟩
  · exact False.elim (hH ((reach_iff G H ports rotation t v u).mp hG))
  · exact False.elim (hG ((reach_iff G H ports rotation t v u).mpr hH))
  · rfl

theorem advanceTail_map (n : Nat) (w : Walk V D (n+1)) :
    advanceTail H (walkEquiv ports (n+1) w) =
      walkEquiv ports n (advanceTail G w) := by
  apply Prod.ext
  · change (H.rot (w.1, ports (w.2 0))).1 = (G.rot (w.1,w.2 0)).1
    rw [rotation]
  · rfl

theorem edgeAt_map (n : Nat) (w : Walk V D (n+1)) (k : Fin (n+1)) :
    edgeAt H n (walkEquiv ports (n+1) w) k =
      ((edgeAt G n w k).1, ports (edgeAt G n w k).2) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    induction k using Fin.cases with
    | zero => rfl
    | succ k =>
      simp only [edgeAt, Fin.cases_succ]
      rw [advanceTail_map G H ports rotation]
      exact ih _ _

variable (accepts : Edge V E → A → A → Bool)

def pullAccepts : Edge V D → A → A → Bool :=
  fun e => accepts (e.1, ports e.2)

theorem pathAccepts_map (n : Nat) (selectors : ∀v, AddressSelector H (n+1) v)
    (w : Walk V D (n+1)) (a b : PaddedLabel E (n+1) A) :
    pathAccepts G (pullAccepts ports accepts) n
      (fun v => pullSelector G H ports rotation (selectors v)) w
      (labelEquiv ports (n+1) a) (labelEquiv ports (n+1) b) =
    pathAccepts H accepts n selectors (walkEquiv ports (n+1) w) a b := by
  classical
  unfold pathAccepts
  congr 1
  apply propext
  apply forall_congr'
  intro k
  have ht := decode_transport G H ports rotation selectors a rfl
    (tailFromStart G n w k) (tailFromStart H n (walkEquiv ports (n+1) w) k)
    (congrArg Prod.fst (edgeAt_map G H ports rotation n w k)).symm
  have hh := decode_transport G H ports rotation selectors b
    (endpoint_map G H ports rotation (n+1) w).symm
    (headFromEnd G n w k) (headFromEnd H n (walkEquiv ports (n+1) w) k)
    (by
      change (G.rot (edgeAt G n w k)).1 =
        (H.rot (edgeAt H n (walkEquiv ports (n+1) w) k)).1
      rw [edgeAt_map G H ports rotation, rotation])
  rw [ht, hh]
  simp only [pullAccepts, edgeAt_map G H ports rotation]
  rfl

def dartEquiv (n : Nat) : Dart V D n ≃ Dart V E n :=
  Equiv.prodCongr (Equiv.refl Bool) (walkEquiv ports (n+1))

theorem edgeSatisfied_map (n : Nat) (selectors : ∀v, AddressSelector H (n+1) v)
    (labels : V → PaddedLabel E (n+1) A) (e : Dart V D n) :
    (poweredGraph G (pullAccepts ports accepts) n
      (fun v => pullSelector G H ports rotation (selectors v))).edgeSatisfied
        (fun v => labelEquiv ports (n+1) (labels v)) e =
    (poweredGraph H accepts n selectors).edgeSatisfied labels (dartEquiv ports n e) := by
  rcases e with ⟨direction,w⟩
  rw [poweredGraph_edgeSatisfied]
  change _ = (poweredGraph H accepts n selectors).edgeSatisfied labels
    (direction, walkEquiv ports (n+1) w)
  rw [poweredGraph_edgeSatisfied, endpoint_map G H ports rotation]
  exact pathAccepts_map G H ports rotation accepts n selectors w _ _

theorem rejectionCount_map [Fintype V] [Fintype D] [Fintype E]
    (n : Nat) (selectors : ∀v, AddressSelector H (n+1) v)
    (labels : V → PaddedLabel E (n+1) A) :
    (poweredGraph G (pullAccepts ports accepts) n
      (fun v => pullSelector G H ports rotation (selectors v))).rejectionCount
        (fun v => labelEquiv ports (n+1) (labels v)) =
    (poweredGraph H accepts n selectors).rejectionCount labels := by
  classical
  unfold ConstraintGraph.rejectionCount
  apply Finset.card_bij (fun e _ => dartEquiv ports n e)
  · intro e he
    rw [ConstraintGraph.mem_rejectedDarts, ← edgeSatisfied_map G H ports rotation]
    exact (ConstraintGraph.mem_rejectedDarts _ _ _).mp he
  · intro e _ f _ h
    exact (dartEquiv ports n).injective h
  · intro e he
    refine ⟨(dartEquiv ports n).symm e, ?_, (dartEquiv ports n).apply_symm_apply e⟩
    rw [ConstraintGraph.mem_rejectedDarts, edgeSatisfied_map G H ports rotation,
      Equiv.apply_symm_apply]
    exact (ConstraintGraph.mem_rejectedDarts _ _ _).mp he

theorem satisfiable_iff (n : Nat) (selectors : ∀v, AddressSelector H (n+1) v) :
    (poweredGraph G (pullAccepts ports accepts) n
      (fun v => pullSelector G H ports rotation (selectors v))).Satisfiable ↔
    (poweredGraph H accepts n selectors).Satisfiable := by
  constructor
  · rintro ⟨labels,hlabels⟩
    refine ⟨fun v => (labelEquiv ports (n+1)).symm (labels v), ?_⟩
    intro e
    obtain ⟨e,rfl⟩ := (dartEquiv ports n).surjective e
    rw [← edgeSatisfied_map G H ports rotation]
    simpa only [Equiv.apply_symm_apply] using hlabels e
  · rintro ⟨labels,hlabels⟩
    refine ⟨fun v => labelEquiv ports (n+1) (labels v), ?_⟩
    intro e
    rw [edgeSatisfied_map G H ports rotation]
    exact hlabels _

theorem pullReverse
    (reverse_accepts : ∀ e a b, accepts (H.rot e) b a = accepts e a b)
    (e : Edge V D) (a b : A) :
    pullAccepts ports accepts (G.rot e) b a = pullAccepts ports accepts e a b := by
  simpa only [pullAccepts, rotation] using reverse_accepts (e.1,ports e.2) a b

theorem base_edgeSatisfied_map
    (reverse_accepts : ∀ e a b, accepts (H.rot e) b a = accepts e a b)
    (assignment : V → A) (e : Edge V D) :
    (baseGraph G (pullAccepts ports accepts)
      (pullReverse G H ports rotation accepts reverse_accepts)).edgeSatisfied assignment e =
    (baseGraph H accepts reverse_accepts).edgeSatisfied assignment (e.1,ports e.2) := by
  change accepts (e.1,ports e.2) (assignment e.1) (assignment (G.rot e).1) =
    accepts (e.1,ports e.2) (assignment e.1) (assignment (H.rot (e.1,ports e.2)).1)
  rw [rotation]

theorem base_rejectionCount_map [Fintype V] [Fintype D] [Fintype E]
    (reverse_accepts : ∀ e a b, accepts (H.rot e) b a = accepts e a b)
    (assignment : V → A) :
    (baseGraph G (pullAccepts ports accepts)
      (pullReverse G H ports rotation accepts reverse_accepts)).rejectionCount assignment =
    (baseGraph H accepts reverse_accepts).rejectionCount assignment := by
  classical
  let e : Edge V D ≃ Edge V E := Equiv.prodCongr (Equiv.refl V) ports
  have edgeEq (x : Edge V D) :=
    base_edgeSatisfied_map G H ports rotation accepts reverse_accepts assignment x
  unfold ConstraintGraph.rejectionCount
  apply Finset.card_bij (fun x _ => e x)
  · intro x hx
    rw [ConstraintGraph.mem_rejectedDarts]
    change (baseGraph H accepts reverse_accepts).edgeSatisfied assignment (x.1,ports x.2) = false
    rw [← edgeEq]
    exact (ConstraintGraph.mem_rejectedDarts _ _ _).mp hx
  · intro x _ y _ h
    exact e.injective h
  · intro y hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    rw [ConstraintGraph.mem_rejectedDarts, edgeEq]
    change (baseGraph H accepts reverse_accepts).edgeSatisfied assignment (e (e.symm y)) = false
    rw [e.apply_symm_apply]
    exact (ConstraintGraph.mem_rejectedDarts _ _ _).mp hy

omit rotation in
/-- The generic lazy-graph gap survives a genuine rotation-preserving port
change and the target's chosen selectors, for every raw target labeling. -/
theorem uniform_count_gap
    [Fintype V] [Fintype D] [Fintype E] [Nonempty V] [Nonempty D]
    [Fintype A] [Nonempty A]
    (G : PortGraph V D) (H : PortGraph V E) (ports : (Bool × D) ≃ E)
    (rotation : ∀ v d, H.rot (v, ports d) =
      (((lazyGraph G).rot (v,d)).1, ports ((lazyGraph G).rot (v,d)).2))
    (lambda : ℝ) (certificate : SpectralCertificate (lazyGraph G) lambda)
    (accepts : Edge V E → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts (H.rot e) b a = accepts e a b)
    (M : Nat) (hM : 1 ≤ M)
    (selectors : ∀v, AddressSelector H (2*center (Fintype.card A) M+1) v)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hgap : ∀ assignment : V → A,
      epsilon * (Fintype.card (Edge V E) : ℝ) ≤
        ((baseGraph H accepts reverse_accepts).rejectionCount assignment : ℝ))
    (labels : V → PaddedLabel E (2*center (Fintype.card A) M+1) A) :
    (gain (Fintype.card A) M lambda *
      min epsilon (1 / ((2*center (Fintype.card A) M+1 : Nat) : ℝ))) *
        (Fintype.card (Dart V E (2*center (Fintype.card A) M)) : ℝ) ≤
      ((poweredGraph H accepts (2*center (Fintype.card A) M) selectors).rejectionCount labels : ℝ) := by
  have hbase : ∀ assignment : V → A,
      epsilon * (Fintype.card (Edge V (Bool × D)) : ℝ) ≤
      ((baseGraph (lazyGraph G) (pullAccepts ports accepts)
        (pullReverse (lazyGraph G) H ports rotation accepts reverse_accepts)).rejectionCount assignment : ℝ) := by
    intro assignment
    rw [base_rejectionCount_map (lazyGraph G) H ports rotation,
      Fintype.card_congr (Equiv.prodCongr (Equiv.refl V) ports)]
    exact hgap assignment
  have bound := PoweringGap.uniform_count_gap G lambda certificate
    (pullAccepts ports accepts)
    (pullReverse (lazyGraph G) H ports rotation accepts reverse_accepts) M hM
    (fun v => pullSelector (lazyGraph G) H ports rotation (selectors v))
    epsilon hepsilon hbase (fun v => labelEquiv ports _ (labels v))
  rw [rejectionCount_map (lazyGraph G) H ports rotation,
    Fintype.card_congr (dartEquiv (V := V) ports (2*center (Fintype.card A) M))] at bound
  exact bound

omit rotation in
/-- Gap bound for the actual numbered power table built from a lazified port
table. The spectral certificate is on the genuine Boolean-flag lazy graph. -/
theorem lazy_table_uniform_count_gap {vertices d : Nat}
    (input : PortTables.Table vertices d) (hv : 0 < vertices) (hd : 0 < d)
    (lambda : ℝ)
    (certificate : SpectralCertificate (lazyGraph (PortTables.portGraph input)) lambda)
    (M : Nat) (hM : 1 ≤ M) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hgap : ∀ assignment : Fin vertices → Fin 64,
      epsilon * (Fintype.card (Fin vertices × Fin (2*d)) : ℝ) ≤
        ((PortTables.baseGraph (PreprocessingOverlayTables.lazy input)).rejectionCount assignment : ℝ)) :
    ∀ labels : PoweringTableSemantics.EncodedLabeling vertices (2*d) (2*center 64 M),
    (gain 64 M lambda * min epsilon (1 / ((2*center 64 M+1 : Nat) : ℝ))) *
      ((PoweringTables.table (PreprocessingOverlayTables.lazy input) (2*center 64 M)).darts : ℝ) ≤
      ((GenericGraphTables.semantics
        (PoweringTables.table (PreprocessingOverlayTables.lazy input) (2*center 64 M))).rejectionCount labels : ℝ) := by
  let : Nonempty (Fin vertices) := ⟨⟨0,hv⟩⟩
  let : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  apply PoweringTableSemantics.uniform_count_gap
  intro labels
  have hrot : ∀ v p,
      (PortTables.portGraph (PreprocessingOverlayTables.lazy input)).rot
          (v, PreprocessingOverlayTables.lazyPorts d p) =
        (((lazyGraph (PortTables.portGraph input)).rot (v,p)).1,
          PreprocessingOverlayTables.lazyPorts d
            ((lazyGraph (PortTables.portGraph input)).rot (v,p)).2) := by
    intro v p
    rw [PreprocessingTableSpectral.lazy_portGraph]
    exact GraphTransport.reindex_rot _ (Equiv.refl _) _ v p
  have bound := uniform_count_gap (PortTables.portGraph input)
      (PortTables.portGraph (PreprocessingOverlayTables.lazy input))
      (PreprocessingOverlayTables.lazyPorts d) hrot lambda certificate
      (PortTables.accepts (PreprocessingOverlayTables.lazy input))
      (PortTables.accepts_rotation (PreprocessingOverlayTables.lazy input)) M hM
      (PoweringAddresses.finitePortSelector
        (PortTables.portGraph (PreprocessingOverlayTables.lazy input)) _) epsilon hepsilon
      hgap
  simp only [PortTables.Label, GraphTables.Label, Fintype.card_fin] at bound
  exact bound labels

omit rotation in
/-- The same exact table bound with a separately stored walk parameter. Its
proved equality may be used without evaluating a huge closed alphabet size. -/
theorem lazy_table_uniform_count_gap_at {vertices d : Nat}
    (input : PortTables.Table vertices d) (hv : 0 < vertices) (hd : 0 < d)
    (lambda : ℝ)
    (certificate : SpectralCertificate (lazyGraph (PortTables.portGraph input)) lambda)
    (M : Nat) (hM : 1 ≤ M) (n : Nat) (hn : n = 2*center 64 M)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hgap : ∀ assignment : Fin vertices → Fin 64,
      epsilon * (Fintype.card (Fin vertices × Fin (2*d)) : ℝ) ≤
        ((PortTables.baseGraph (PreprocessingOverlayTables.lazy input)).rejectionCount
          assignment : ℝ)) :
    ∀ labels : PoweringTableSemantics.EncodedLabeling vertices (2*d) n,
    (gain 64 M lambda * min epsilon (1 / ((n+1 : Nat) : ℝ))) *
      ((PoweringTables.table (PreprocessingOverlayTables.lazy input) n).darts : ℝ) ≤
      ((GenericGraphTables.semantics
        (PoweringTables.table (PreprocessingOverlayTables.lazy input) n)).rejectionCount
          labels : ℝ) := by
  subst n
  exact lazy_table_uniform_count_gap input hv hd lambda certificate M hM
    epsilon hepsilon hgap

end UniqueGamesTheorem.Foundations.PCP.PoweringPortReindex

end

end

section

/-!
An actual fixed-degree graph obtained by padding each outgoing-dart cloud to
the explicit expander family and then replacing vertices by cloud darts.
Expansion and majority rounding are proved dependencies, not hypotheses of
the final soundness theorem. Isolated original vertices have empty clouds.
-/

noncomputable section

namespace UniqueGamesTheorem.Foundations.PCP.Regularization

open PoweringWalks DegreeReplacement

variable {V E A : Type*} [Fintype V] [Fintype E] [Fintype A]
variable [DecidableEq V] [DecidableEq E] [DecidableEq A]

abbrev Vertex (G : ConstraintGraph V E A) := PaddedDart G (CloudPadding.dummy G)
abbrev Port := ExpanderFamily.Port ⊕ Unit

/-- The degree is one absolute constant, independent of the input graph. -/
def degree : Nat := Fintype.card Port

theorem degree_eq : degree = Fintype.card ExpanderFamily.Port + 1 := by
  simp [degree, Port]

theorem degree_positive : 0 < degree := by rw [degree_eq]; omega

/-- A positive padded cloud has exactly the size of one explicit family member. -/
def cloudEquiv (G : ConstraintGraph V E A) (v : V)
    (hk : 0 < Fintype.card (Cloud G v)) :
    ExpanderFamily.Vertex (ExpanderFamily.level (Fintype.card (Cloud G v))) ≃
      Cloud (paddedGraph G (CloudPadding.dummy G)) v :=
  Fintype.equivOfCardEq (CloudPadding.card_cloud_eq_family G v hk).symm

/-- Empty clouds use the empty rotation; every other cloud uses the proved family. -/
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
/-- The exact expansion premise required by the checked finite rounding theorem. -/
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

/-- The actual constraint graph, with its equality and inherited original tests. -/
def graph (G : ConstraintGraph V E A) :
    ConstraintGraph (Vertex G) (Vertex G × Port) A :=
  paddedReplacementGraph G (CloudPadding.dummy G) (cloudGraph G)

omit [Fintype A] [DecidableEq E] in
@[simp] theorem graph_tail (G : ConstraintGraph V E A) (e : Vertex G × Port) :
    (graph G).tail e = e.1 := rfl

omit [Fintype A] [DecidableEq E] in
theorem graph_reverse (G : ConstraintGraph V E A) :
    (graph G).reverse = (portGraph G).rot := rfl

/-- The outgoing darts at each new vertex are exactly its fixed port alphabet. -/
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
/-- Completeness preserves the absolute rejection count exactly. -/
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

/-- Actual regularization soundness with no remaining expansion or rounding premise. -/
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

end UniqueGamesTheorem.Foundations.PCP.Regularization

end

end

end OAI
