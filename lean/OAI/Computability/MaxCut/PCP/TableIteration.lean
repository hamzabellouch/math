import Mathlib
import OAI.Computability.MaxCut.PCP.RoundGap
import OAI.Computability.MaxCut.Machines.RawInitialMachineBudget

namespace OAI

/-! Iteration of the concrete stored-table round, with the original formula's
actual initial graph size controlling the number of rounds. -/

namespace MaxCutGames.Foundations.PCP.TableIteration

open RoundTables
open Target Complexity

def run (H : BaseTable) : Nat → Input → Input := AmplificationIteration.run (step H)

/-- The same data computation on all validated tables; positivity is an invariant,
and is erased from the runtime path. -/
def runTables (H : BaseTable) : Nat → GraphTables.Table → GraphTables.Table :=
  AmplificationIteration.run (build H)

theorem run_val (H : BaseTable) (n : Nat) (input : Input) :
    (run H n input).val = runTables H n input.val := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change build H (run H n input).val = build H (runTables H n input.val)
      rw [ih]

def iterationCount (F : Formula) : Nat := AmplificationIteration.rounds (size (initial F))

def output (H : BaseTable) (F : Formula) : Input := run H (iterationCount F) (initial F)

def outputTable (H : BaseTable) (F : Formula) : GraphTables.Table :=
  runTables H (iterationCount F) (RawInitialTables.table F)

theorem output_val (H : BaseTable) (F : Formula) : (output H F).val = outputTable H F :=
  run_val H (iterationCount F) (initial F)

def gapMap (H : BaseTable) (F : Formula) : Formula := FinalTableFormula.output (outputTable H F)

/-- A checked initialized degree avoids evaluating enormous fixed logarithms
while applying polynomial identities. Its bound is part of the stored data. -/
opaque degreeData : {n : Nat // sizeFactor ≤ 2 ^ n} :=
  ⟨AmplificationIteration.rounds sizeFactor, (AmplificationIteration.rounds_large sizeFactor).le⟩

def polynomialDegree : Nat := degreeData.val

theorem sizeFactor_le_power : sizeFactor ≤ 2 ^ polynomialDegree :=
  degreeData.property

theorem run_completeness (H : BaseTable) (n : Nat) (input : Input)
    (sat : Satisfiable input) : Satisfiable (run H n input) :=
  AmplificationIteration.run_preserves (step H) Satisfiable (step_completeness H) n input sat

theorem output_completeness (H : BaseTable) (F : Formula) (sat : F.Satisfiable) :
    Satisfiable (output H F) :=
  run_completeness H _ _ ((initial_satisfiable_iff F).mpr sat)

theorem gapMap_completeness (H : BaseTable) (F : Formula) (sat : F.Satisfiable) :
    (gapMap H F).Satisfiable := by
  apply (FinalTableFormula.satisfiable_iff (outputTable H F)).mpr
  rw [← output_val]
  exact output_completeness H F sat

theorem output_darts_positive (H : BaseTable) (F : Formula) : 0 < (outputTable H F).darts := by
  rw [← output_val]
  exact (output H F).property

theorem gapMap_nonempty (H : BaseTable) (F : Formula) : (gapMap H F).clauses ≠ [] :=
  FinalTableFormula.nonempty (outputTable H F) (output_darts_positive H F)

theorem run_size (H : BaseTable) (n : Nat) (input : Input) :
    size (run H n input) ≤ sizeFactor ^ n * size input :=
  AmplificationIteration.run_size (step H) size sizeFactor (step_size H) n input

theorem output_size (H : BaseTable) (F : Formula) :
    size (output H F) ≤ (2 * size (initial F)) ^ polynomialDegree * size (initial F) :=
  AmplificationIteration.run_size_polynomial (step H) size (size_positive (initial F))
    sizeFactor_le_power (step_size H) (initial F)

theorem initial_size_le (F : Formula) : size (initial F) ≤ 7 * (formulaBits F).length :=
  RawInitialMachineBudget.graph_size_bound F

theorem output_size_le_input (H : BaseTable) (F : Formula) :
    (outputTable H F).vertices + (outputTable H F).darts ≤
      (14 * (formulaBits F).length) ^ polynomialDegree * (7 * (formulaBits F).length) := by
  rw [← output_val]
  have h := initial_size_le F
  exact (output_size H F).trans
    (Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) _) h)

noncomputable def tableSizePolynomial : Polynomial Nat :=
  (Polynomial.C 14 * Polynomial.X) ^ polynomialDegree * (Polynomial.C 7 * Polynomial.X)

theorem tableSizePolynomial_eval (N : Nat) :
    tableSizePolynomial.eval N = (14 * N) ^ polynomialDegree * (7 * N) := by
  simp only [tableSizePolynomial, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]

noncomputable def tableBitsPolynomial : Polynomial Nat :=
  (GraphTableComplexity.encodingPolynomial 64).comp tableSizePolynomial

theorem output_bits_le (H : BaseTable) (F : Formula) :
    (GraphTables.tableBits (outputTable H F)).length ≤ tableBitsPolynomial.eval (formulaBits F).length := by
  rw [tableBitsPolynomial, Polynomial.eval_comp, tableSizePolynomial_eval]
  exact GraphTableComplexity.bits_le_of_size_le _ (output_size_le_input H F)

noncomputable def formulaBitsPolynomial : Polynomial Nat :=
  FinalTableFormula.sizePolynomial.comp tableBitsPolynomial

theorem gapMap_bits_le (H : BaseTable) (F : Formula) :
    (formulaBits (gapMap H F)).length ≤ formulaBitsPolynomial.eval (formulaBits F).length := by
  rw [formulaBitsPolynomial, Polynomial.eval_comp]
  exact (FinalTableFormula.formulaBits_length_le_polynomial (outputTable H F)).trans
    (MachineComposition.natPolynomial_eval_mono _ (output_bits_le H F))

end MaxCutGames.Foundations.PCP.TableIteration

/-! Exact transport of powering through a change of ports. The target's actual
address selector is pulled back, so no compatibility of enumeration orders or
consistency restriction on raw padded labels is needed. -/

noncomputable section
namespace MaxCutGames.Foundations.PCP.PoweringPortReindex
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
  left_inv _u := rfl
  right_inv _u := rfl

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

end MaxCutGames.Foundations.PCP.PoweringPortReindex

end

/-! Gap amplification for the actual numbered table round. The fixed base
expander is the only supplied construction datum with a spectral certificate. -/

namespace MaxCutGames.Foundations.PCP.RoundTableGap

open RoundTables
open PoweringWalks SpectralReturn

variable (H : BaseTable)
  (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))

include certificate

theorem powered_count_gap (input : Input)
    (labeling : Fin (powered H input.val).vertices → Fin alphabet) :
    RoundGap.poweredLower (gap input) * ((powered H input.val).darts : ℝ) ≤
      ((GenericGraphTables.semantics (powered H input.val)).rejectionCount labeling : ℝ) := by
  let old := PreprocessingOverlayTables.overlay
    (PreprocessingTables.padded H input.val) (PreprocessingTables.overlayFamily H input.val)
  have hd : 0 < (PreprocessingRegularTables.internalDegree + 1) +
      PreprocessingRegularTables.internalDegree := by omega
  let : Nonempty (Fin ((PreprocessingRegularTables.internalDegree + 1) +
      PreprocessingRegularTables.internalDegree)) := ⟨⟨0, hd⟩⟩
  have spectral : SpectralCertificate (lazyGraph (PortTables.portGraph old)) (31 / 32 : ℝ) :=
    LazySpectral.lazy_certificate_31_32 (PortTables.portGraph old)
      (PreprocessingGuarantees.overlay_certificate H certificate input.val)
  have lower := PreprocessingGuarantees.gap_transfer_real H certificate input.val input.property
    (gap input) (gap_nonnegative input)
    (by simpa only [Fintype.card_fin] using
      ((GraphTables.semantics input.val).le_gap_iff (gap input)).mp le_rfl)
  have hs : (0 : ℝ) < Preprocessing.sizeFactor := Nat.cast_pos.mpr Preprocessing.sizeFactor_positive
  have hn : walkParameter = 2 * PoweringSoundness.center 64 FinalConstants.windowHalf :=
    walkParameter_eq
  have bound := PoweringPortReindex.lazy_table_uniform_count_gap_at old
    (PreprocessingTables.vertices_positive input.val) hd (31 / 32) spectral
    FinalConstants.windowHalf FinalConstants.windowHalf_positive walkParameter hn
    (gap input / Preprocessing.sizeFactor) (div_nonneg (gap_nonnegative input) hs.le)
    lower labeling
  have hw : walkParameter + 1 = FinalConstants.walkLength := by
    rw [walkParameter_eq]
    rfl
  simpa only [RoundGap.poweredLower, PoweringFinalConstants.card_alphabet,
    hw, FinalConstants.cap, powered, PreprocessingTables.preprocess, old] using! bound

theorem build_count_gap (input : Input)
    (labeling : Fin (build H input.val).vertices → GraphTables.Label) :
    min (2 * gap input) FinalConstants.cap * ((build H input.val).darts : ℝ) ≤
      ((GraphTables.semantics (build H input.val)).rejectionCount labeling : ℝ) := by
  have h := AlphabetTableBounds.gap_transfer_real alphabet_positive (powered H input.val)
    (RoundGap.poweredLower (gap input))
    (RoundGap.poweredLower_nonnegative (gap input) (gap_nonnegative input))
    (powered_count_gap H certificate input) labeling
  have scalar : min (2 * gap input) FinalConstants.cap ≤
      RoundGap.poweredLower (gap input) / 12288 := by
    simpa only [RoundGap.poweredLower, FinalConstants.cap, FinalConstants.walkLength,
      PoweringFinalConstants.center_eq] using
      PoweringFinalConstants.composed_scaled_gap (gap input) (gap_nonnegative input)
  exact (mul_le_mul_of_nonneg_right scalar (Nat.cast_nonneg _)).trans h

theorem step_gap (input : Input) :
    min (2 * gap input) FinalConstants.cap ≤ gap (step H input) := by
  apply ((GraphTables.semantics (step H input).val).le_gap_iff _).mpr
  change ∀ labeling : Fin (build H input.val).vertices → GraphTables.Label,
    min (2 * gap input) FinalConstants.cap *
        (Fintype.card (Fin (build H input.val).darts) : ℝ) ≤
      ((GraphTables.semantics (build H input.val)).rejectionCount labeling : ℝ)
  simpa only [Fintype.card_fin, step] using build_count_gap H certificate input

end MaxCutGames.Foundations.PCP.RoundTableGap

/-! Both semantic implications for the actual stored-table 3SAT gap map.
The positive clause gap follows from the full actual repeated transformation.
The full map's polynomial-time machine is certified separately. -/

namespace MaxCutGames.Foundations.PCP.TableGapReduction

open RoundTables TableIteration SpectralReturn Target

variable (H : BaseTable)
  (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))

include certificate

theorem run_gap (n : Nat) (input : Input) :
    min (2 ^ n * gap input) FinalConstants.cap ≤ gap (TableIteration.run H n input) :=
  AmplificationIteration.run_gap (step H) gap FinalConstants.cap FinalConstants.cap_positive.le
    (RoundTableGap.step_gap H certificate) n input

theorem output_gap (F : Formula) (unsat : ¬ F.Satisfiable) :
    FinalConstants.cap ≤ gap (TableIteration.output H F) := by
  have hu : ¬ Satisfiable (initial F) := fun sat => unsat ((initial_satisfiable_iff F).mp sat)
  exact AmplificationIteration.run_reaches_cap (step H) gap FinalConstants.cap
    FinalConstants.cap_positive.le FinalConstants.cap_le_one (RoundTableGap.step_gap H certificate)
    (size (initial F)) (initial F) (gap_nonnegative (initial F))
    (one_le_size_mul_gap (initial F) hu)

theorem output_satisfiable_iff (F : Formula) :
    Satisfiable (TableIteration.output H F) ↔ F.Satisfiable := by
  constructor
  · intro sat
    by_contra unsat
    have bound := output_gap H certificate F unsat
    rw [(gap_eq_zero_iff (TableIteration.output H F)).mpr sat] at bound
    exact (not_le_of_gt FinalConstants.cap_positive) bound
  · exact TableIteration.output_completeness H F

theorem gapMap_satisfiable_iff (F : Formula) : (gapMap H F).Satisfiable ↔ F.Satisfiable := by
  rw [gapMap, FinalTableFormula.satisfiable_iff, ← output_val]
  exact output_satisfiable_iff H certificate F

theorem output_count_gap (F : Formula) (unsat : ¬ F.Satisfiable)
    (labeling : Fin (outputTable H F).vertices → GraphTables.Label) :
    (outputTable H F).darts ≤ FinalConstants.walkLength *
      (GraphTables.semantics (outputTable H F)).rejectionCount labeling := by
  have hp := output_darts_positive H F
  let : Nonempty (Fin (outputTable H F).darts) := ⟨⟨0, hp⟩⟩
  have bound := output_gap H certificate F unsat
  change FinalConstants.cap ≤ (GraphTables.semantics (TableIteration.output H F).val).gap at bound
  rw [output_val] at bound
  have count := ((GraphTables.semantics (outputTable H F)).le_gap_iff FinalConstants.cap).mp bound labeling
  simp only [Fintype.card_fin] at count
  have ht : (0 : ℝ) < FinalConstants.walkLength := Nat.cast_pos.mpr FinalConstants.walkLength_positive
  have divided : ((outputTable H F).darts : ℝ) / FinalConstants.walkLength ≤
      ((GraphTables.semantics (outputTable H F)).rejectionCount labeling : ℝ) := by
    simpa only [FinalConstants.cap, one_div_mul_eq_div] using count
  have multiplied := (div_le_iff₀ ht).mp divided
  exact_mod_cast (show ((outputTable H F).darts : ℝ) ≤ (FinalConstants.walkLength : ℝ) *
      ((GraphTables.semantics (outputTable H F)).rejectionCount labeling : ℝ) by
    simpa only [mul_comm] using multiplied)

theorem gapMap_clauseGap (F : Formula) (unsat : ¬ F.Satisfiable) :
    Hastad.SourceGap.ClauseGap (gapMap H F) PCPIteration.finalClauseGap :=
  FinalTableFormula.clauseGap (outputTable H F) (output_darts_positive H F)
    (output_count_gap H certificate F unsat)

omit certificate in
theorem finalClauseGap_le_one : PCPIteration.finalClauseGap ≤ 1 := by
  have hw : (1 : ℚ) ≤ (FinalConstants.walkLength : ℚ) := by
    exact_mod_cast FinalConstants.walkLength_positive
  have hd : (0 : ℚ) < 40960 * (FinalConstants.walkLength : ℚ) := by positivity
  rw [PCPIteration.finalClauseGap, div_le_one hd]
  linarith

end MaxCutGames.Foundations.PCP.TableGapReduction

end OAI
