import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Basic.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import OAI.Computability.UniqueGames.PCP.AlphabetRetractionLemmas
import OAI.Computability.UniqueGames.PCP.ExpandersLemmas
import OAI.Computability.UniqueGames.PCP.InitialGraphLemmas
import OAI.Computability.UniqueGames.PCP.PoweringOpinionsLemmas
import OAI.Computability.UniqueGames.PCP.PoweringTablesLemmas

namespace OAI

noncomputable section

/-!
# Exact semantics of the executable powering tables

The explicit label and dart bijections preserve every actual edge test and
every rejected directed occurrence. The inverse label map covers all encoded
assignments, so satisfiability and uniform rejection-count bounds transport
without any consistency restriction on padded labels.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringTableSemantics

open PoweringWalks PoweringLabels PoweringAddresses PoweringEnumeration PoweringTables

abbrev RawLabeling (vertices d n : Nat) :=
  Fin vertices → PaddedLabel (Fin d) (n + 1) (Fin 64)

abbrev EncodedLabeling (vertices d n : Nat) :=
  Fin vertices → Fin (labelCount d n)

def encodeLabeling {vertices : Nat} (d n : Nat) (labels : RawLabeling vertices d n) :
    EncodedLabeling vertices d n :=
  fun v => encodeLabel d (n + 1) 64 (labels v)

def decodeLabeling {vertices : Nat} (d n : Nat) (labels : EncodedLabeling vertices d n) :
    RawLabeling vertices d n :=
  fun v => decodeLabel d (n + 1) 64 (labels v)

@[simp] theorem decodeLabeling_encodeLabeling {vertices : Nat} (d n : Nat)
    (labels : RawLabeling vertices d n) :
    decodeLabeling d n (encodeLabeling d n labels) = labels := by
  funext v
  exact decodeLabel_encodeLabel d (n + 1) 64 (labels v)

@[simp] theorem encodeLabeling_decodeLabeling {vertices : Nat} (d n : Nat)
    (labels : EncodedLabeling vertices d n) :
    encodeLabeling d n (decodeLabeling d n labels) = labels := by
  funext v
  exact encodeLabel_decodeLabel d (n + 1) 64 (labels v)

/-- Each enumerated directed occurrence evaluates its actual powering test. -/
theorem edgeSatisfied_encoded {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (labels : RawLabeling vertices d n)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n) :
    (GenericGraphTables.semantics (table input n)).edgeSatisfied
      (encodeLabeling d n labels) (encodeDart vertices d n e) =
        (mathematicalGraph input n).edgeSatisfied labels e := by
  rw [semantics_table]
  unfold encodeLabeling encodeLabel encodeDart
  simpa using!
    GenericGraphTables.enumeratedGraph_edgeSatisfied (mathematicalGraph input n)
      (Equiv.refl _) (dartEquiv vertices d n) (paddedLabelEquiv d (n + 1) 64) labels e

/-- The equality also holds for every encoded assignment and every stored row. -/
theorem edgeSatisfied_decoded {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (labels : EncodedLabeling vertices d n) (i : Fin (dartCount vertices d n)) :
    (GenericGraphTables.semantics (table input n)).edgeSatisfied labels i =
      (mathematicalGraph input n).edgeSatisfied (decodeLabeling d n labels)
        (decodeDart vertices d n i) := by
  have h := edgeSatisfied_encoded input n (decodeLabeling d n labels)
    (decodeDart vertices d n i)
  erw [encodeLabeling_decodeLabeling d n labels,
    encodeDart_decodeDart vertices d n i] at h
  exact h

/-- The stored Boolean test is exactly the path test at the recorded endpoints. -/
theorem edgeSatisfied_eq_path {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (labels : EncodedLabeling vertices d n) (direction : Bool)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) :
    (GenericGraphTables.semantics (table input n)).edgeSatisfied labels
      (encodeDart vertices d n (direction, w)) =
    PoweringTest.pathAccepts (PortTables.portGraph input) (PortTables.accepts input) n
      (finitePortSelector (PortTables.portGraph input) (n + 1)) w
      (decodeLabeling d n labels w.1)
      (decodeLabeling d n labels (endpoint (PortTables.portGraph input) w)) := by
  rw [edgeSatisfied_decoded input n labels (encodeDart vertices d n (direction, w)),
    decodeDart_encodeDart vertices d n (direction, w)]
  exact PoweringTest.poweredGraph_edgeSatisfied (PortTables.portGraph input)
    (PortTables.accepts input) n (finitePortSelector (PortTables.portGraph input) (n + 1))
    (decodeLabeling d n labels) direction w

/-- Exact rejected-dart counting, retaining both orientations and repeated walks. -/
theorem rejectionCount_encoded {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (labels : RawLabeling vertices d n) :
    (GenericGraphTables.semantics (table input n)).rejectionCount
      (encodeLabeling d n labels) = (mathematicalGraph input n).rejectionCount labels := by
  rw [semantics_table]
  unfold encodeLabeling encodeLabel
  simpa using!
    GenericGraphTables.enumeratedGraph_rejectionCount (mathematicalGraph input n)
      (Equiv.refl _) (dartEquiv vertices d n) (paddedLabelEquiv d (n + 1) 64) labels

theorem rejectionCount_decoded {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (labels : EncodedLabeling vertices d n) :
    (GenericGraphTables.semantics (table input n)).rejectionCount labels =
      (mathematicalGraph input n).rejectionCount (decodeLabeling d n labels) := by
  have h := rejectionCount_encoded input n (decodeLabeling d n labels)
  erw [encodeLabeling_decodeLabeling d n labels] at h
  exact h

/-- The denominator equality comes from the same explicit dart bijection. -/
theorem card_darts_eq_table {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) :
    Fintype.card (PoweringTest.Dart (Fin vertices) (Fin d) n) = (table input n).darts := by
  change Fintype.card (PoweringTest.Dart (Fin vertices) (Fin d) n) =
    2 * vertices * d ^ (n + 1)
  simpa only [Fintype.card_fin] using Fintype.card_congr (dartEquiv vertices d n)

/-- The table has a satisfying encoded assignment exactly when the powered graph does. -/
theorem satisfiable_iff {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat) :
    (GenericGraphTables.semantics (table input n)).Satisfiable ↔
      (mathematicalGraph input n).Satisfiable := by
  constructor
  · rintro ⟨labels, satisfies⟩
    refine ⟨decodeLabeling d n labels, ?_⟩
    intro e
    have h := edgeSatisfied_encoded input n (decodeLabeling d n labels) e
    erw [encodeLabeling_decodeLabeling d n labels] at h
    exact h.symm.trans (satisfies (encodeDart vertices d n e))
  · rintro ⟨labels, satisfies⟩
    refine ⟨encodeLabeling d n labels, ?_⟩
    intro i
    have h := edgeSatisfied_encoded input n labels (decodeDart vertices d n i)
    rw [encodeDart_decodeDart vertices d n i] at h
    exact h.trans (satisfies (decodeDart vertices d n i))

/-- Perfect completeness from the actual stored base predicates. -/
theorem preserves_satisfiability {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (h : (PortTables.baseGraph input).Satisfiable) :
    (GenericGraphTables.semantics (table input n)).Satisfiable := by
  apply (satisfiable_iff input n).mpr
  exact PoweringTest.preserves_satisfiability (PortTables.portGraph input)
    (PortTables.accepts input) (PortTables.accepts_rotation input) n
    (finitePortSelector (PortTables.portGraph input) (n + 1)) h

/-- The path rejection average equals the encoded table's actual rejection fraction. -/
theorem path_rejection_mean_eq_table_fraction {vertices d : Nat}
    (input : PortTables.Table vertices d) (n : Nat) (labels : EncodedLabeling vertices d n) :
    SpectralReturn.mean (fun w : Walk (Fin vertices) (Fin d) (n + 1) =>
      PoweringMoment.bit
        (PoweringTest.pathAccepts (PortTables.portGraph input) (PortTables.accepts input) n
          (finitePortSelector (PortTables.portGraph input) (n + 1)) w
          (decodeLabeling d n labels w.1)
          (decodeLabeling d n labels (endpoint (PortTables.portGraph input) w)) = false)) =
      ((GenericGraphTables.semantics (table input n)).rejectionCount labels : ℝ) /
        ((table input n).darts : ℝ) := by
  rw [rejectionCount_decoded input n labels, ← card_darts_eq_table input n]
  exact PoweringCounting.path_rejection_mean_eq_count (PortTables.portGraph input)
    (PortTables.accepts input) n (finitePortSelector (PortTables.portGraph input) (n + 1))
    (decodeLabeling d n labels)

/-- Uniform actual rejection-count gaps are invariant under the executable encoding. -/
theorem uniform_count_gap_iff {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (epsilon : ℝ) :
    (∀ labels : EncodedLabeling vertices d n,
      epsilon * ((table input n).darts : ℝ) ≤
        ((GenericGraphTables.semantics (table input n)).rejectionCount labels : ℝ)) ↔
    (∀ labels : RawLabeling vertices d n,
      epsilon * (Fintype.card (PoweringTest.Dart (Fin vertices) (Fin d) n) : ℝ) ≤
        ((mathematicalGraph input n).rejectionCount labels : ℝ)) := by
  constructor
  · intro h labels
    have hlabels := h (encodeLabeling d n labels)
    erw [rejectionCount_encoded input n labels, ← card_darts_eq_table input n] at hlabels
    exact hlabels
  · intro h labels
    rw [rejectionCount_decoded input n labels]
    have hlabels := h (decodeLabeling d n labels)
    rw [card_darts_eq_table input n] at hlabels
    exact hlabels

/-- Apply an established powering count bound to every encoded table labeling. -/
theorem uniform_count_gap {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (epsilon : ℝ)
    (hgap : ∀ labels : RawLabeling vertices d n,
      epsilon * (Fintype.card (PoweringTest.Dart (Fin vertices) (Fin d) n) : ℝ) ≤
        ((mathematicalGraph input n).rejectionCount labels : ℝ)) :
    ∀ labels : EncodedLabeling vertices d n,
      epsilon * ((table input n).darts : ℝ) ≤
        ((GenericGraphTables.semantics (table input n)).rejectionCount labels : ℝ) :=
  (uniform_count_gap_iff input n epsilon).mpr hgap

end UniqueGamesTheorem.Foundations.PCP.PoweringTableSemantics

/-!
# The actual first moment of an endpoint-opinion witness

The pivot factorization is applied to actual finite walks. Its two endpoint
operator bounds are obtained from the proved lazy-graph mixture and smoothing
theorem. No witness-event probability law is assumed.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringWitness

open PoweringWalks SpectralReturn PoweringReturn PoweringLazy
open PoweringMoment (bit)

variable {V D : Type*}

/-- A constant scalar passes through every iterate of the actual graph mean. -/
theorem iterate_mul_const [Fintype D] (G : PortGraph V D)
    (n : Nat) (c : ℝ) (h : V → ℝ) :
    iterateOperator G n (fun x => c * h x) =
      fun x => c * iterateOperator G n h x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change averagingOperator G (iterateOperator G n (fun x => c * h x)) =
      fun x => c * averagingOperator G (iterateOperator G n h) x
    rw [ih]
    funext v
    exact mean_mul_left c (fun d => iterateOperator G n h (G.rot (v, d)).1)

/-- The actual pivot dart is marked and both endpoint opinions pass their
tests. For indicator opinions this is the indicator of their conjunction. -/
noncomputable def endpointWitness (G : PortGraph V D) (bad : Edge V D → Bool)
    (φ ψ : Edge V D → V → ℝ) (n : Nat) (k : Fin (n + 1))
    (w : Walk V D (n + 1)) : ℝ :=
  bit (bad (edgeAt G n w k) = true) *
    φ (edgeAt G n w k) w.1 * ψ (edgeAt G n w k) (endpoint G w)

/-- Vertex-indexed opinions are tested at the two endpoints of the pivot dart. -/
noncomputable def vertexWitness (G : PortGraph V D) (bad : Edge V D → Bool)
    (f : V → V → ℝ) (n : Nat) (k : Fin (n + 1)) :
    Walk V D (n + 1) → ℝ :=
  endpointWitness G bad (fun e => f e.1) (fun e => f (next G e.1 e.2)) n k

/-- Pointwise bounds on the two genuine earlier-length graph iterates give
the witness first moment. The hypotheses are only needed on marked darts. -/
theorem endpoint_lower_bound [Fintype V] [Fintype D] [Nonempty D]
    (G : PortGraph V D) (n : Nat) (k : Fin (n + 1)) (bad : Edge V D → Bool)
    (φ ψ : Edge V D → V → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (hL : ∀ e, bad e = true → a ≤ iterateOperator G k.val (φ e) e.1)
    (hR : ∀ e, bad e = true →
      a ≤ iterateOperator G (n - k.val) (ψ e) (next G e.1 e.2)) :
    edgeDensity bad * a ^ 2 ≤ mean (endpointWitness G bad φ ψ n k) := by
  have hfactor : mean (endpointWitness G bad φ ψ n k) =
      mean (fun e : Edge V D =>
        (bit (bad e = true) * iterateOperator G k.val (φ e) e.1) *
          iterateOperator G (n - k.val) (ψ e) (next G e.1 e.2)) := by
    unfold endpointWitness
    rw [mean_edge_endpoints G n k (fun e x => bit (bad e = true) * φ e x) ψ]
    simp_rw [iterate_mul_const]
  have hbitMean : mean (fun e : Edge V D => bit (bad e = true)) = edgeDensity bad := by
    calc
      _ = mean (fun v : V => mean (fun d : D => bit (bad (v, d) = true))) :=
        mean_prod (A := V) (B := D) (fun e => bit (bad e = true))
      _ = edgeDensity bad := by simp only [mean_edge_bit, edgeDensity]
  calc
    edgeDensity bad * a ^ 2 =
        mean (fun e : Edge V D => bit (bad e = true) * a ^ 2) := by
      rw [mean_mul_right, hbitMean]
    _ ≤ mean (fun e : Edge V D =>
        (bit (bad e = true) * iterateOperator G k.val (φ e) e.1) *
          iterateOperator G (n - k.val) (ψ e) (next G e.1 e.2)) := by
      apply mean_mono
      intro e
      cases hb : bad e with
      | false => simp [bit]
      | true =>
        have hprod := mul_le_mul (hL e hb) (hR e hb) ha (ha.trans (hL e hb))
        simpa [bit, hb, pow_two] using hprod
    _ = mean (endpointWitness G bad φ ψ n k) := hfactor.symm

/-- The two endpoint-opinion tests each retain probability at least `1/(2q)`
at every middle pivot. The walk has `2N+1` edges, with `N=(4qM)^2`, so the
prefix and suffix lengths are exactly `k` and `2N-k`.

The only modal input is the actual centered lazy iterate at each vertex. It
will be supplied by the finite modal-opinion decoder, not by a witness law.
-/
theorem lazy_middle_witness_mean [Fintype V] [Fintype D] [Nonempty D]
    (G : PortGraph V D) (q M : Nat) (hq : 1 ≤ q) (hM : 1 ≤ M)
    (k : Fin (2 * (4 * q * M) ^ 2 + 1))
    (hlo : (4 * q * M) ^ 2 - M ≤ k.val)
    (hhi : k.val ≤ (4 * q * M) ^ 2 + M)
    (bad : Edge V (Bool × D) → Bool) (f : V → V → ℝ)
    (hf : ∀ u w, f u w ∈ Set.Icc (0 : ℝ) 1)
    (hmodal : ∀ u, 1 / (q : ℝ) ≤
      iterateOperator (lazyGraph G) ((4 * q * M) ^ 2) (f u) u) :
    edgeDensity bad / (4 * (q : ℝ) ^ 2) ≤
      mean (vertexWitness (lazyGraph G) bad f (2 * (4 * q * M) ^ 2) k) := by
  have hk : k.val ≤ 2 * (4 * q * M) ^ 2 := Nat.le_of_lt_succ k.isLt
  have hslo : (4 * q * M) ^ 2 - M ≤ 2 * (4 * q * M) ^ 2 - k.val := by omega
  have hshi : 2 * (4 * q * M) ^ 2 - k.val ≤ (4 * q * M) ^ 2 + M := by omega
  have ha : (0 : ℝ) ≤ 1 / (2 * (q : ℝ)) := by positivity
  have hbound := endpoint_lower_bound (lazyGraph G) (2 * (4 * q * M) ^ 2) k bad
    (fun e => f e.1) (fun e => f (next (lazyGraph G) e.1 e.2))
    (1 / (2 * (q : ℝ))) ha
    (by
      intro e _
      exact lazy_endpoint_modal_transfer G q M k.val hq hM hlo hhi
        (f e.1) (hf e.1) e.1 (hmodal e.1))
    (by
      intro e _
      exact lazy_endpoint_modal_transfer G q M (2 * (4 * q * M) ^ 2 - k.val)
        hq hM hslo hshi (f (next (lazyGraph G) e.1 e.2))
        (hf (next (lazyGraph G) e.1 e.2)) (next (lazyGraph G) e.1 e.2)
        (hmodal (next (lazyGraph G) e.1 e.2)))
  have hscale : edgeDensity bad * (1 / (2 * (q : ℝ))) ^ 2 =
      edgeDensity bad / (4 * (q : ℝ) ^ 2) := by ring
  simpa only [vertexWitness, hscale] using hbound

end UniqueGamesTheorem.Foundations.PCP.PoweringWitness

/-! The actual graph-powering soundness bound. Modal endpoint opinions give
the first moment, spectral return gives the second moment, and an actual
checked path constraint turns each witness into rejection. -/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringSoundness

open scoped BigOperators
open PoweringWalks PoweringLabels PoweringOpinions PoweringTest
open SpectralReturn PoweringWitness PoweringMomentBound
open PoweringMoment (bit hits)

variable {V D A : Type*}

def center (q M : Nat) : Nat := (4 * q * M) ^ 2

theorem le_center (q M : Nat) (hq : 1 ≤ q) (hM : 1 ≤ M) : M ≤ center q M := by
  have hfour : 1 ≤ 4 * q := by omega
  have hx : M ≤ 4 * q * M := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right M hfour
  have hone : 1 ≤ 4 * q * M := hM.trans hx
  have hsquare : 4 * q * M ≤ (4 * q * M) * (4 * q * M) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (4 * q * M) hone
  exact hx.trans (by simpa only [center, pow_two] using hsquare)

def gain (q M : Nat) (lambda : ℝ) : ℝ :=
  (1 / (2 * (q : ℝ))) ^ 4 * ((2 * M + 1 : Nat) : ℝ) /
    ((1 + 2 / (1 - lambda)) + 1)

variable [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
  [Fintype A] [Nonempty A]

def decodedError (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (n N : Nat) (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) (fallback : A) : ℝ :=
  edgeDensity (decodedBad G accepts (decoded G (n + 1) N selectors labels fallback))

def poweredRejection (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (n : Nat) (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) : ℝ :=
  mean (fun d : Dart V D n => bit ((poweredGraph G accepts n selectors).edgeSatisfied labels d = false))

omit [Fintype V] [Nonempty V] [Nonempty D] in
theorem witness_bit_eq (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (n N : Nat) (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) (fallback : A)
    (w : Walk V D (n + 1)) (k : Fin (n + 1)) :
    bit (witness G accepts n selectors labels fallback
      (decoded G (n + 1) N selectors labels fallback) w k) =
      vertexWitness G
        (decodedBad G accepts (decoded G (n + 1) N selectors labels fallback))
        (matchFn G (n + 1) N selectors labels fallback) n k w := by
  simp only [witness, vertexWitness, endpointWitness, matchFn,
    PoweringMoment.bit_mul, next, and_assoc]

omit [Nonempty V] in
theorem modal_witness_mean (G : PortGraph V D) (M : Nat) (hM : 1 ≤ M)
    (accepts : Edge V (Bool × D) → A → A → Bool)
    (selectors : ∀ v, AddressSelector (lazyGraph G) (2 * center (Fintype.card A) M + 1) v)
    (labels : V → PaddedLabel (Bool × D) (2 * center (Fintype.card A) M + 1) A)
    (fallback : A) (k : Fin (2 * center (Fintype.card A) M + 1))
    (hlo : center (Fintype.card A) M - M ≤ k.val)
    (hhi : k.val ≤ center (Fintype.card A) M + M) :
    decodedError (lazyGraph G) accepts (2 * center (Fintype.card A) M)
      (center (Fintype.card A) M) selectors labels fallback / (4 * (Fintype.card A : ℝ) ^ 2) ≤
      mean (fun w => bit (witness (lazyGraph G) accepts (2 * center (Fintype.card A) M)
        selectors labels fallback (decoded (lazyGraph G) (2 * center (Fintype.card A) M + 1)
          (center (Fintype.card A) M) selectors labels fallback) w k)) := by
  have h := lazy_middle_witness_mean G (Fintype.card A) M Fintype.card_pos hM k hlo hhi
    (decodedBad (lazyGraph G) accepts
      (decoded (lazyGraph G) (2 * center (Fintype.card A) M + 1)
        (center (Fintype.card A) M) selectors labels fallback))
    (matchFn (lazyGraph G) (2 * center (Fintype.card A) M + 1)
      (center (Fintype.card A) M) selectors labels fallback)
    (matchFn_mem_Icc (lazyGraph G) (2 * center (Fintype.card A) M + 1)
      (center (Fintype.card A) M) selectors labels fallback)
    (decoded_modal_baseline (lazyGraph G) (2 * center (Fintype.card A) M + 1)
      (center (Fintype.card A) M) selectors labels fallback)
  simp_rw [witness_bit_eq]
  convert h using 1 <;> rfl

/-- Positive decoded error forces rejection of the actual powered graph.
The cap and amplification coefficient are explicit constants. -/
theorem rejection_lower_bound (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate (lazyGraph G) lambda)
    (accepts : Edge V (Bool × D) → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts ((lazyGraph G).rot e) b a = accepts e a b)
    (M : Nat) (hM : 1 ≤ M)
    (selectors : ∀ v, AddressSelector (lazyGraph G) (2 * center (Fintype.card A) M + 1) v)
    (labels : V → PaddedLabel (Bool × D) (2 * center (Fintype.card A) M + 1) A)
    (fallback : A)
    (hε : 0 < decodedError (lazyGraph G) accepts (2 * center (Fintype.card A) M)
      (center (Fintype.card A) M) selectors labels fallback) :
    gain (Fintype.card A) M lambda *
        min (decodedError (lazyGraph G) accepts (2 * center (Fintype.card A) M)
          (center (Fintype.card A) M) selectors labels fallback)
          (1 / ((2 * center (Fintype.card A) M + 1 : Nat) : ℝ)) ≤
      poweredRejection (lazyGraph G) accepts (2 * center (Fintype.card A) M) selectors labels := by
  let q := Fintype.card A
  let N := center q M
  let n := 2 * N
  let m := 2 * M + 1
  let start := N - M
  let L := lazyGraph G
  let assignment := decoded L (n + 1) N selectors labels fallback
  let bad := decodedBad L accepts assignment
  let ε := edgeDensity bad
  let α : ℝ := 1 / (2 * (q : ℝ))
  let C : ℝ := 1 + 2 / (1 - lambda)
  have hNM : M ≤ N := le_center q M Fintype.card_pos hM
  have hw : start + m ≤ n + 1 := by dsimp [start, m, n]; omega
  let E := windowEvent L bad n start m hw
  let W : Fin m → Walk V (Bool × D) (n + 1) → Prop := fun i w =>
    witness L accepts n selectors labels fallback assignment w (windowIndex n start m hw i)
  let R : Walk V (Bool × D) (n + 1) → Prop := fun w =>
    pathAccepts L accepts n selectors w (labels w.1) (labels (endpoint L w)) = false
  have hWE : ∀ i w, W i w → E i w := by
    intro i w h
    exact h.1
  have hWR : ∀ i w, W i w → R w := by
    intro i w h
    exact witness_implies_path_rejection L accepts n selectors labels fallback assignment w
      (windowIndex n start m hw i) h
  have hpoint (i : Fin m) : ε / (4 * (q : ℝ) ^ 2) ≤ mean (fun w => bit (W i w)) := by
    have hlo : N - M ≤ (windowIndex n start m hw i).val := by
      dsimp [windowIndex, start]
      omega
    have hhi : (windowIndex n start m hw i).val ≤ N + M := by
      have hi := i.isLt
      dsimp [windowIndex, start]
      dsimp [m] at hi
      omega
    exact modal_witness_mean G M hM accepts selectors labels fallback
      (windowIndex n start m hw i) hlo hhi
  have hfirst : α ^ 2 * (m : ℝ) * ε ≤ mean (hits W) := by
    change α ^ 2 * (m : ℝ) * ε ≤ PoweringMoment.mean (hits W)
    rw [PoweringMoment.mean_hits]
    calc
      _ = ∑ _i : Fin m, ε / (4 * (q : ℝ) ^ 2) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        dsimp [α]
        ring
      _ ≤ _ := Finset.sum_le_sum (fun i _ => hpoint i)
  have hsecond : mean (fun w => hits E w ^ 2) ≤
      (m : ℝ) * ε * (C + ((m : ℝ) - 1) * ε) :=
    window_second_moment_le L lambda certificate bad
      (decodedBad_rot L accepts reverse_accepts assignment) n start m hw
  have hε' : 0 < ε := hε
  have hm : 0 < m := by dsimp [m]; omega
  have hmReal : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hqReal : (0 : ℝ) < q := Nat.cast_pos.mpr Fintype.card_pos
  have hden : 0 < 1 - lambda := sub_pos.mpr certificate.lt_one
  have hC : 0 < C := by dsimp [C]; positivity
  have hmOne : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hα : 0 < α := by dsimp [α]; positivity
  have ha : 0 < α ^ 2 * (m : ℝ) * ε := by positivity
  have hb : 0 < (m : ℝ) * ε * (C + ((m : ℝ) - 1) * ε) := by
    have hdiff : 0 ≤ (m : ℝ) - 1 := sub_nonneg.mpr hmOne
    positivity
  have hCS := PoweringMoment.rejection_lower_bound E W R hWE hWR
    (α ^ 2 * (m : ℝ) * ε) ((m : ℝ) * ε * (C + ((m : ℝ) - 1) * ε))
    ha hb hfirst hsecond
  have ht : (0 : ℝ) < ((n + 1 : Nat) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos n)
  have hmn : m ≤ n + 1 := by dsimp [m, n]; omega
  have hmt : (m : ℝ) - 1 ≤ ((n + 1 : Nat) : ℝ) := by
    have hmnReal : (m : ℝ) ≤ ((n + 1 : Nat) : ℝ) := by exact_mod_cast hmn
    linarith
  have hratio := PoweringNumeric.count_moment_ratio_lower α ε C ((n + 1 : Nat) : ℝ)
    m hm hε' hC ht hmt
  change (α ^ 4 * (m : ℝ) / (C + 1)) * min ε (1 / ((n + 1 : Nat) : ℝ)) ≤ _
  change _ ≤ mean (fun d : Dart V (Bool × D) n =>
    bit ((poweredGraph L accepts n selectors).edgeSatisfied labels d = false))
  rw [rejection_mean_eq_path_mean]
  exact hratio.trans hCS

end UniqueGamesTheorem.Foundations.PCP.PoweringSoundness

namespace UniqueGamesTheorem.Foundations.PCP.PoweringGap

open PoweringWalks PoweringLabels PoweringOpinions PoweringTest
open SpectralReturn PoweringSoundness PoweringCounting

variable {V D A : Type*}

theorem gain_nonneg (q M : Nat) (lambda : ℝ) (hlambda : lambda < 1) :
    0 ≤ gain q M lambda := by
  have hden : 0 < 1 - lambda := sub_pos.mpr hlambda
  unfold gain
  positivity

variable [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
  [Fintype A] [Nonempty A]

theorem uniform_count_gap (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate (lazyGraph G) lambda)
    (accepts : Edge V (Bool × D) → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts ((lazyGraph G).rot e) b a = accepts e a b)
    (M : Nat) (hM : 1 ≤ M)
    (selectors : ∀ v, AddressSelector (lazyGraph G)
      (2 * center (Fintype.card A) M + 1) v)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hgap : ∀ assignment : V → A,
      epsilon * (Fintype.card (Edge V (Bool × D)) : ℝ) ≤
        ((baseGraph (lazyGraph G) accepts reverse_accepts).rejectionCount assignment : ℝ))
    (labels : V → PaddedLabel (Bool × D) (2 * center (Fintype.card A) M + 1) A) :
    (gain (Fintype.card A) M lambda *
      min epsilon (1 / ((2 * center (Fintype.card A) M + 1 : Nat) : ℝ))) *
        (Fintype.card (Dart V (Bool × D) (2 * center (Fintype.card A) M)) : ℝ) ≤
      ((poweredGraph (lazyGraph G) accepts (2 * center (Fintype.card A) M)
        selectors).rejectionCount labels : ℝ) := by
  classical
  let L := lazyGraph G
  let N := center (Fintype.card A) M
  let n := 2 * N
  let H := poweredGraph L accepts n selectors
  change (gain (Fintype.card A) M lambda *
      min epsilon (1 / ((n + 1 : Nat) : ℝ))) *
        (Fintype.card (Dart V (Bool × D) n) : ℝ) ≤
      (H.rejectionCount labels : ℝ)
  rcases eq_or_lt_of_le hepsilon with hzero | hpositive
  · rw [← hzero]
    have hcap : (0 : ℝ) ≤ 1 / ((n + 1 : Nat) : ℝ) := by positivity
    rw [min_eq_left hcap, mul_zero, zero_mul]
    exact Nat.cast_nonneg _
  · let fallback : A := Classical.choice (inferInstance : Nonempty A)
    let assignment := decoded L (n + 1) N selectors labels fallback
    have hdecoded : epsilon ≤ decodedError L accepts n N selectors labels fallback := by
      change epsilon ≤ edgeDensity (decodedBad L accepts assignment)
      exact base_count_lower_to_density L accepts reverse_accepts assignment
        Fintype.card_pos epsilon (hgap assignment)
    have herror : 0 < decodedError L accepts n N selectors labels fallback :=
      hpositive.trans_le hdecoded
    have hsound := PoweringSoundness.rejection_lower_bound G lambda certificate
      accepts reverse_accepts M hM selectors labels fallback herror
    have hgain : 0 ≤ gain (Fintype.card A) M lambda :=
      gain_nonneg (Fintype.card A) M lambda certificate.lt_one
    have hmin : min epsilon (1 / ((n + 1 : Nat) : ℝ)) ≤
        min (decodedError L accepts n N selectors labels fallback)
          (1 / ((n + 1 : Nat) : ℝ)) :=
      min_le_min hdecoded (le_refl _)
    have hlower : gain (Fintype.card A) M lambda *
        min epsilon (1 / ((n + 1 : Nat) : ℝ)) ≤
        poweredRejection L accepts n selectors labels :=
      (mul_le_mul_of_nonneg_left hmin hgain).trans hsound
    exact (constraint_rejection_lower_iff H labels Fintype.card_pos
      (gain (Fintype.card A) M lambda *
        min epsilon (1 / ((n + 1 : Nat) : ℝ)))).mp hlower

end UniqueGamesTheorem.Foundations.PCP.PoweringGap

/-! Actual directed-cut expansion from the graph's zero-mean spectral
certificate. Parallel edges and loops retain their indexed port multiplicities. -/
namespace UniqueGamesTheorem.Foundations.PCP.SpectralCut

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
/-- The normalized cut count is exactly mean minus one-step correlation. -/
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

/-- The real cardinal estimate before removing denominators. -/
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

/-- The natural-number expansion used in cloud rounding. Empty vertex sets
are included; a degree of at least eight supplies the nonempty port type. -/
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

end UniqueGamesTheorem.Foundations.PCP.SpectralCut

/-!
# Uniform restriction of Boolean tapes

Restricting a uniformly sampled Boolean function to a decidable subset gives
the uniform law on functions on that subset.  The subset and its complement
may be empty: their Boolean function spaces still contain the constant-false
function.  Extending by false gives a canonical full-domain oracle address.
-/

namespace UniqueGamesTheorem.Foundations.PCP.UniformRestriction

open scoped BigOperators

variable {B : Type*} (p : B → Prop)

/-- The values of a full Boolean tape on the legal coordinates. -/
def restrict (f : B → Bool) : {b // p b} → Bool := fun b => f b.1

variable [DecidablePred p]

/-- Extend a tape on legal coordinates by false on every other coordinate. -/
def extend (g : {b // p b} → Bool) : B → Bool :=
  fun b => if hb : p b then g ⟨b, hb⟩ else false

/-- Replace the values outside the legal coordinates by false. -/
def canonicalize (f : B → Bool) : B → Bool := extend p (restrict p f)

omit [DecidablePred p] in
@[simp] theorem restrict_apply (f : B → Bool) (b : {b // p b}) :
    restrict p f b = f b.1 := rfl

@[simp] theorem extend_apply_of_mem (g : {b // p b} → Bool) (b : B) (hb : p b) :
    extend p g b = g ⟨b, hb⟩ := by
  simp [extend, hb]

@[simp] theorem extend_apply_of_not_mem (g : {b // p b} → Bool) (b : B)
    (hb : ¬ p b) : extend p g b = false := by
  simp [extend, hb]

@[simp] theorem restrict_extend (g : {b // p b} → Bool) :
    restrict p (extend p g) = g := by
  funext b
  simp [restrict, extend, b.property]

@[simp] theorem canonicalize_apply_of_mem (f : B → Bool) (b : B) (hb : p b) :
    canonicalize p f b = f b := by
  simp [canonicalize, hb]

@[simp] theorem canonicalize_apply_of_not_mem (f : B → Bool) (b : B)
    (hb : ¬ p b) : canonicalize p f b = false := by
  simp [canonicalize, hb]

@[simp] theorem restrict_canonicalize (f : B → Bool) :
    restrict p (canonicalize p f) = restrict p f := by
  exact restrict_extend p (restrict p f)

@[simp] theorem canonicalize_idempotent (f : B → Bool) :
    canonicalize p (canonicalize p f) = canonicalize p f := by
  simp only [canonicalize, restrict_extend]

theorem canonicalize_eq_iff (f g : B → Bool) :
    canonicalize p f = canonicalize p g ↔ restrict p f = restrict p g := by
  constructor
  · intro h
    simpa only [restrict_canonicalize] using congrArg (restrict p) h
  · intro h
    exact congrArg (extend p) h

variable [Fintype B] [DecidableEq B]

/-- Uniform full tapes induce exactly uniform legal-coordinate tapes. -/
theorem expect_restrict (h : ({b // p b} → Bool) → ℝ) :
    (𝔼 f : B → Bool, h (restrict p f)) = 𝔼 g : {b // p b} → Bool, h g := by
  calc
    (𝔼 f : B → Bool, h (restrict p f)) =
        𝔼 g : ({b // p b} → Bool) × ({b // ¬ p b} → Bool), h g.1 :=
      Fintype.expect_equiv (Equiv.piEquivPiSubtypeProd p (fun _ => Bool))
        _ _ (fun _ => rfl)
    _ = 𝔼 g : {b // p b} → Bool, 𝔼 _k : {b // ¬ p b} → Bool, h g := by
      simpa only [Finset.univ_product_univ] using
        Finset.expect_product
          (Finset.univ : Finset ({b // p b} → Bool))
          (Finset.univ : Finset ({b // ¬ p b} → Bool))
          (fun g : ({b // p b} → Bool) × ({b // ¬ p b} → Bool) => h g.1)
    _ = 𝔼 g : {b // p b} → Bool, h g := by
      simp only [Fintype.expect_const]

/-- The same law after choosing the canonical full-domain oracle address. -/
theorem expect_canonicalize (h : (B → Bool) → ℝ) :
    (𝔼 f : B → Bool, h (canonicalize p f)) =
      𝔼 g : {b // p b} → Bool, h (extend p g) :=
  expect_restrict p (fun g => h (extend p g))

/-- Two independent full tapes restrict to two independent uniform legal tapes. -/
theorem expect_restrict_pair (h : ({b // p b} → Bool) → ({b // p b} → Bool) → ℝ) :
    (𝔼 f : B → Bool, 𝔼 g : B → Bool, h (restrict p f) (restrict p g)) =
      𝔼 f : {b // p b} → Bool, 𝔼 g : {b // p b} → Bool, h f g := by
  calc
    _ = 𝔼 f : B → Bool, 𝔼 g : {b // p b} → Bool, h (restrict p f) g := by
      apply Finset.expect_congr rfl
      intro f _
      exact expect_restrict p (h (restrict p f))
    _ = _ := expect_restrict p (fun f => 𝔼 g : {b // p b} → Bool, h f g)

end UniqueGamesTheorem.Foundations.PCP.UniformRestriction

end

end OAI
