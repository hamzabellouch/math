import OAI.Computability.UniqueGames.PCP.AlphabetReductionLemmas
import OAI.Computability.UniqueGames.PCP.ExpandersLemmas
import OAI.Computability.UniqueGames.PCP.PoweringLabelsLemmas

namespace OAI

section

/-! Actual local-label opinions, modal decoding at the reference length, and
its proved persistence at nearby lazy-walk lengths. -/

noncomputable section

namespace UniqueGamesTheorem.Foundations.PCP.PoweringOpinions

open PoweringWalks PoweringLabels SpectralReturn
open PoweringMoment (bit)

variable {V D A : Type*}

/-- Outside the full-radius neighborhood a fixed fallback makes the opinion
function total. Actual tested path vertices will be certified inside it. -/
def opinionAt (G : PortGraph V D) (t : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (u v : V) : A := by
  classical
  exact if h : ∃ n, n ≤ t ∧ ∃ p : Fin n → D, wordEnd G n v p = u then
    decode (selectors v) (labels v) ⟨u, h⟩ else fallback

theorem opinionAt_eq_decode (G : PortGraph V D) (t : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (v : V) (u : Ball G t v) :
    opinionAt G t selectors labels fallback u.val v = decode (selectors v) (labels v) u := by
  classical
  simp [opinionAt, u.property]
  rfl

def honestLabels (G : PortGraph V D) (t : Nat) (assignment : V → A) :
    V → PaddedLabel D t A := fun v => encode G t v (fun u => assignment u.val)

theorem opinionAt_honest (G : PortGraph V D) (t : Nat)
    (selectors : ∀ v, AddressSelector G t v) (assignment : V → A)
    (fallback : A) (v : V) (u : Ball G t v) :
    opinionAt G t selectors (honestLabels G t assignment) fallback u.val v =
      assignment u.val := by
  rw [opinionAt_eq_decode]
  exact congrFun (decode_encode (selectors v) (fun u => assignment u.val)) u

variable [Fintype D] [Nonempty D] [Fintype A] [Nonempty A]

def sampleOpinion (G : PortGraph V D) (t N : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (u : V) (p : Fin N → D) : A :=
  opinionAt G t selectors labels fallback u (wordEnd G N u p)

def decoded (G : PortGraph V D) (t N : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (u : V) : A :=
  PoweringDecoding.mode (sampleOpinion G t N selectors labels fallback u)

def matchFn (G : PortGraph V D) (t N : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (u v : V) : ℝ :=
  bit (opinionAt G t selectors labels fallback u v = decoded G t N selectors labels fallback u)

omit [Nonempty D] in
theorem matchFn_mem_Icc (G : PortGraph V D) (t N : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (u v : V) :
    matchFn G t N selectors labels fallback u v ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  constructor
  · exact PoweringMoment.bit_nonneg _
  · unfold matchFn bit
    split <;> simp

/-- The reference-length modal lower bound is proved from actual port samples. -/
theorem decoded_modal_baseline (G : PortGraph V D) (t N : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (u : V) :
    1 / (Fintype.card A : ℝ) ≤
      iterateOperator G N (matchFn G t N selectors labels fallback u) u := by
  have h := PoweringDecoding.mode_mass_lower (sampleOpinion G t N selectors labels fallback u)
  change 1 / (Fintype.card A : ℝ) ≤ mean (fun p : Fin N → D =>
    matchFn G t N selectors labels fallback u (wordEnd G N u p)) at h
  rwa [PoweringReturn.mean_wordEnd] at h

/-- Actual decoded letters retain positive mass throughout the middle window. -/
theorem decoded_modal_near (G : PortGraph V D) (t M m : Nat)
    (selectors : ∀ v, AddressSelector (lazyGraph G) t v)
    (labels : V → PaddedLabel (Bool × D) t A) (fallback : A)
    (hM : 1 ≤ M)
    (hlo : (4 * Fintype.card A * M) ^ 2 - M ≤ m)
    (hhi : m ≤ (4 * Fintype.card A * M) ^ 2 + M) (u : V) :
    1 / (2 * (Fintype.card A : ℝ)) ≤
      iterateOperator (lazyGraph G) m
        (matchFn (lazyGraph G) t ((4 * Fintype.card A * M) ^ 2)
          selectors labels fallback u) u := by
  exact PoweringLazy.lazy_endpoint_modal_transfer G (Fintype.card A) M m
    Fintype.card_pos hM hlo hhi _
    (matchFn_mem_Icc (lazyGraph G) t ((4 * Fintype.card A * M) ^ 2)
      selectors labels fallback u) u
    (decoded_modal_baseline (lazyGraph G) t ((4 * Fintype.card A * M) ^ 2)
      selectors labels fallback u)

end UniqueGamesTheorem.Foundations.PCP.PoweringOpinions

end

end

section

/-!
# The actual constraint-graph powering test

Every recorded port walk gives two directed darts. Reversal flips an
orientation bit while preserving the recorded walk. The common vertex
alphabet is the full-radius padded local-label alphabet. The test checks the
actual base constraint at every traversed edge using the two endpoint labels.

Honest local encodings give perfect completeness. A decoded bad edge together
with the two matching local opinions forces rejection of the actual test.
Neither conclusion is assumed as a rejection-inclusion or distribution law.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringTest

open PoweringWalks PoweringLabels PoweringReach PoweringOpinions

variable {V D A : Type*}

/-- The base port predicates packaged as a constraint graph. -/
def baseGraph (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts (G.rot e) b a = accepts e a b) :
    ConstraintGraph V (Edge V D) A where
  reverse := G.rot
  reverse_involutive := G.rot_involutive
  tail := Prod.fst
  accepts := accepts
  reverse_accepts := reverse_accepts

/-- Check all base constraints along the recorded walk. The reach certificates
select genuine vertices in the two full-radius neighborhood balls. -/
def pathAccepts (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (n : Nat) (selectors : ∀ v, AddressSelector G (n + 1) v)
    (w : Walk V D (n + 1)) (a b : PaddedLabel D (n + 1) A) : Bool :=
  decide (∀ k : Fin (n + 1),
    accepts (edgeAt G n w k)
      (decode (selectors w.1) a (tailFromStart G n w k))
      (decode (selectors (endpoint G w)) b (headFromEnd G n w k)) = true)

theorem pathAccepts_eq_true_iff (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool)
    (n : Nat) (selectors : ∀ v, AddressSelector G (n + 1) v)
    (w : Walk V D (n + 1)) (a b : PaddedLabel D (n + 1) A) :
    pathAccepts G accepts n selectors w a b = true ↔
      ∀ k : Fin (n + 1),
        accepts (edgeAt G n w k)
          (decode (selectors w.1) a (tailFromStart G n w k))
          (decode (selectors (endpoint G w)) b (headFromEnd G n w k)) = true := by
  simp [pathAccepts]

abbrev Dart (V D : Type*) (n : Nat) := Bool × Walk V D (n + 1)

/-- Reversal preserves the recorded walk and changes its direction flag. -/
def reverseDart (V D : Type*) (n : Nat) : Dart V D n ≃ Dart V D n where
  toFun d := (!d.1, d.2)
  invFun d := (!d.1, d.2)
  left_inv := by
    rintro ⟨b, w⟩
    cases b <;> rfl
  right_inv := by
    rintro ⟨b, w⟩
    cases b <;> rfl

theorem reverseDart_involutive (V D : Type*) (n : Nat) :
    Function.Involutive (reverseDart V D n) := by
  rintro ⟨b, w⟩
  cases b <;> rfl

/-- An actual powered constraint graph, with a common raw alphabet at all
vertices. Its reversal law is witnessed by the orientation bit. -/
def poweredGraph (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (n : Nat) (selectors : ∀ v, AddressSelector G (n + 1) v) :
    ConstraintGraph V (Dart V D n) (PaddedLabel D (n + 1) A) where
  reverse := reverseDart V D n
  reverse_involutive := reverseDart_involutive V D n
  tail d := if d.1 then endpoint G d.2 else d.2.1
  accepts d a b := if d.1 then pathAccepts G accepts n selectors d.2 b a
    else pathAccepts G accepts n selectors d.2 a b
  reverse_accepts := by
    rintro ⟨direction, w⟩ a b
    cases direction <;> rfl

@[simp] theorem poweredGraph_tail_false (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v) (w : Walk V D (n + 1)) :
    (poweredGraph G accepts n selectors).tail (false, w) = w.1 := rfl

@[simp] theorem poweredGraph_tail_true (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v) (w : Walk V D (n + 1)) :
    (poweredGraph G accepts n selectors).tail (true, w) = endpoint G w := rfl

/-- Both directed copies evaluate the same original-start/original-end path
test. Uniformly doubling the darts therefore introduces no change of event. -/
theorem poweredGraph_edgeSatisfied (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A)
    (direction : Bool) (w : Walk V D (n + 1)) :
    (poweredGraph G accepts n selectors).edgeSatisfied labels (direction, w) =
      pathAccepts G accepts n selectors w (labels w.1) (labels (endpoint G w)) := by
  cases direction <;> rfl

/-- The actual directed-dart rejection average is exactly the recorded-walk
rejection average. Only the orientation-bit average is removed, so the vertex
type and the walk type are allowed to be empty. -/
theorem rejection_mean_eq_path_mean [Fintype V] [Fintype D]
    (G : PortGraph V D) (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) :
    SpectralReturn.mean (fun d : Dart V D n => PoweringMoment.bit
      ((poweredGraph G accepts n selectors).edgeSatisfied labels d = false)) =
      SpectralReturn.mean (fun w : Walk V D (n + 1) => PoweringMoment.bit
        (pathAccepts G accepts n selectors w (labels w.1) (labels (endpoint G w)) = false)) := by
  rw [SpectralReturn.mean_prod]
  simp only [poweredGraph_edgeSatisfied, SpectralReturn.mean_const]

theorem pathAccepts_honest (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (assignment : V → A)
    (satisfies : ∀ e, accepts e (assignment e.1) (assignment (G.rot e).1) = true)
    (w : Walk V D (n + 1)) :
    pathAccepts G accepts n selectors w
      (honestLabels G (n + 1) assignment w.1)
      (honestLabels G (n + 1) assignment (endpoint G w)) = true := by
  apply (pathAccepts_eq_true_iff G accepts n selectors w _ _).2
  intro k
  simpa only [honestLabels, decode_encode, tailFromStart_val, headFromEnd_val] using
    satisfies (edgeAt G n w k)

/-- Perfect completeness for the actual powered graph and its common alphabet. -/
theorem perfect_completeness (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (assignment : V → A)
    (satisfies : ∀ e, accepts e (assignment e.1) (assignment (G.rot e).1) = true) :
    ∀ d, (poweredGraph G accepts n selectors).edgeSatisfied
      (honestLabels G (n + 1) assignment) d = true := by
  rintro ⟨direction, w⟩
  rw [poweredGraph_edgeSatisfied]
  exact pathAccepts_honest G accepts n selectors assignment satisfies w

theorem preserves_satisfiability (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts (G.rot e) b a = accepts e a b)
    (n : Nat) (selectors : ∀ v, AddressSelector G (n + 1) v)
    (h : (baseGraph G accepts reverse_accepts).Satisfiable) :
    (poweredGraph G accepts n selectors).Satisfiable := by
  obtain ⟨assignment, satisfies⟩ := h
  refine ⟨honestLabels G (n + 1) assignment, ?_⟩
  apply perfect_completeness G accepts n selectors assignment
  intro e
  exact satisfies e

/-- Badness is computed from the actual base predicate and the decoded labels. -/
def decodedBad (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (assignment : V → A) (e : Edge V D) : Bool :=
  !(accepts e (assignment e.1) (assignment (G.rot e).1))

theorem decodedBad_eq_true_iff (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (assignment : V → A) (e : Edge V D) :
    decodedBad G accepts assignment e = true ↔
      accepts e (assignment e.1) (assignment (G.rot e).1) = false := by
  simp [decodedBad]

/-- The base reversal law makes the decoded bad-edge event rotor-invariant. -/
theorem decodedBad_rot (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts (G.rot e) b a = accepts e a b)
    (assignment : V → A) (e : Edge V D) :
    decodedBad G accepts assignment (G.rot e) = decodedBad G accepts assignment e := by
  have h := congrArg Bool.not
    (reverse_accepts e (assignment e.1) (assignment (G.rot e).1))
  simpa only [decodedBad, G.rot_involutive e] using h

/-- A bad decoded edge with matching opinions at its two true endpoints. -/
noncomputable def witness (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) (fallback : A)
    (assignment : V → A) (w : Walk V D (n + 1)) (k : Fin (n + 1)) : Prop :=
  decodedBad G accepts assignment (edgeAt G n w k) = true ∧
    opinionAt G (n + 1) selectors labels fallback (edgeAt G n w k).1 w.1 =
      assignment (edgeAt G n w k).1 ∧
    opinionAt G (n + 1) selectors labels fallback
      (G.rot (edgeAt G n w k)).1 (endpoint G w) =
        assignment (G.rot (edgeAt G n w k)).1

theorem witness_bad (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) (fallback : A)
    (assignment : V → A) (w : Walk V D (n + 1)) (k : Fin (n + 1))
    (h : witness G accepts n selectors labels fallback assignment w k) :
    decodedBad G accepts assignment (edgeAt G n w k) = true := h.1

/-- The witness forces failure of the actual kth checked path constraint.
The opinion/decode identities use the genuine reach certificates. -/
theorem witness_implies_path_rejection (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) (fallback : A)
    (assignment : V → A) (w : Walk V D (n + 1)) (k : Fin (n + 1))
    (h : witness G accepts n selectors labels fallback assignment w k) :
    pathAccepts G accepts n selectors w (labels w.1) (labels (endpoint G w)) = false := by
  obtain ⟨hBad, hTail, hHead⟩ := h
  have hTailDecode :
      decode (selectors w.1) (labels w.1) (tailFromStart G n w k) =
        assignment (edgeAt G n w k).1 :=
    (opinionAt_eq_decode G (n + 1) selectors labels fallback w.1
      (tailFromStart G n w k)).symm.trans hTail
  have hHeadDecode :
      decode (selectors (endpoint G w)) (labels (endpoint G w))
          (headFromEnd G n w k) = assignment (G.rot (edgeAt G n w k)).1 :=
    (opinionAt_eq_decode G (n + 1) selectors labels fallback (endpoint G w)
      (headFromEnd G n w k)).symm.trans hHead
  have hFalse := (decodedBad_eq_true_iff G accepts assignment (edgeAt G n w k)).1 hBad
  cases hPath : pathAccepts G accepts n selectors w
      (labels w.1) (labels (endpoint G w)) with
  | false => rfl
  | true =>
      have hChecked := (pathAccepts_eq_true_iff G accepts n selectors w _ _).1 hPath k
      rw [hTailDecode, hHeadDecode, hFalse] at hChecked
      exact False.elim (Bool.noConfusion hChecked)

/-- Rejection inclusion for the actual powered graph, derived from its test. -/
theorem witness_implies_rejection (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) (fallback : A)
    (assignment : V → A) (w : Walk V D (n + 1)) (k : Fin (n + 1))
    (h : witness G accepts n selectors labels fallback assignment w k)
    (direction : Bool) :
    (poweredGraph G accepts n selectors).edgeSatisfied labels (direction, w) = false := by
  rw [poweredGraph_edgeSatisfied]
  exact witness_implies_path_rejection G accepts n selectors labels fallback assignment w k h

end UniqueGamesTheorem.Foundations.PCP.PoweringTest

end

section

/-!
# Actual rejection counts and sizes for the powering construction

Normalized rejection averages are the cardinal ratios of the corresponding
rejected-dart sets. These identities include empty finite types. Positivity
of the dart cardinality is required only when translating inequalities by
division. The powered dart count and common alphabet size are computed from
their actual product and function types.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringCounting

open PoweringWalks PoweringLabels PoweringTest
open scoped BigOperators

variable {V D A E : Type*}

/-- An arbitrary constraint graph's rejection probability is its actual
rejected-dart cardinal ratio, including the empty-dart case. -/
theorem constraint_rejection_mean_eq_count [Fintype E]
    (H : ConstraintGraph V E A) (labels : V → A) :
    SpectralReturn.mean (fun e : E => PoweringMoment.bit
      (H.edgeSatisfied labels e = false)) =
      (H.rejectionCount labels : ℝ) / (Fintype.card E : ℝ) := by
  classical
  rw [SpectralReturn.mean_eq_sum_div_card]
  simp only [PoweringMoment.bit, ConstraintGraph.rejectionCount, ConstraintGraph.rejectedDarts]
  apply congrArg (fun x : ℝ => x / (Fintype.card E : ℝ))
  convert (Finset.sum_boole (R := ℝ)
    (fun e => H.edgeSatisfied labels e = false) Finset.univ) using 1
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : H.edgeSatisfied labels e = false <;> simp [h]

/-- Multiplying a normalized lower bound by the actual positive dart count. -/
theorem constraint_rejection_lower_iff [Fintype E]
    (H : ConstraintGraph V E A) (labels : V → A)
    (hcard : 0 < Fintype.card E) (ε : ℝ) :
    ε ≤ SpectralReturn.mean (fun e : E => PoweringMoment.bit
      (H.edgeSatisfied labels e = false)) ↔
      ε * (Fintype.card E : ℝ) ≤ (H.rejectionCount labels : ℝ) := by
  rw [constraint_rejection_mean_eq_count]
  exact le_div_iff₀ (Nat.cast_pos.mpr hcard)

/-- The edge-profile definition equals its actual directed-edge indicator
mean without any nonemptiness assumption on vertices or ports. -/
theorem edgeDensity_eq_bit_mean [Fintype V] [Fintype D]
    (bad : Edge V D → Bool) :
    SpectralReturn.edgeDensity bad =
      SpectralReturn.mean (fun e : Edge V D => PoweringMoment.bit (bad e = true)) := by
  convert (SpectralReturn.mean_prod
    (fun e : Edge V D => PoweringMoment.bit (bad e = true))).symm using 1
  change SpectralReturn.mean (fun v => SpectralReturn.mean
    (fun d => if bad (v, d) then (1 : ℝ) else 0)) = _
  apply congrArg SpectralReturn.mean
  funext v
  apply congrArg SpectralReturn.mean
  funext d
  cases bad (v, d) <;> simp [PoweringMoment.bit]

/-- Decoded badness is exactly rejection in the actual base constraint graph. -/
theorem base_edgeDensity_eq_rejection_count [Fintype V] [Fintype D]
    (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts (G.rot e) b a = accepts e a b)
    (assignment : V → A) :
    SpectralReturn.edgeDensity (decodedBad G accepts assignment) =
      ((baseGraph G accepts reverse_accepts).rejectionCount assignment : ℝ) /
        (Fintype.card (Edge V D) : ℝ) := by
  calc
    _ = SpectralReturn.mean (fun e : Edge V D => PoweringMoment.bit
        (decodedBad G accepts assignment e = true)) := edgeDensity_eq_bit_mean _
    _ = SpectralReturn.mean (fun e : Edge V D => PoweringMoment.bit
        ((baseGraph G accepts reverse_accepts).edgeSatisfied assignment e = false)) := by
      apply congrArg SpectralReturn.mean
      funext e
      exact congrArg PoweringMoment.bit
        (propext (decodedBad_eq_true_iff G accepts assignment e))
    _ = _ := constraint_rejection_mean_eq_count _ _

theorem base_count_lower_to_density [Fintype V] [Fintype D]
    (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts (G.rot e) b a = accepts e a b)
    (assignment : V → A) (hcard : 0 < Fintype.card (Edge V D)) (ε : ℝ)
    (hcount : ε * (Fintype.card (Edge V D) : ℝ) ≤
      ((baseGraph G accepts reverse_accepts).rejectionCount assignment : ℝ)) :
    ε ≤ SpectralReturn.edgeDensity (decodedBad G accepts assignment) := by
  rw [base_edgeDensity_eq_rejection_count G accepts reverse_accepts assignment]
  exact (le_div_iff₀ (Nat.cast_pos.mpr hcard)).2 hcount

/-- The actual powered graph's directed-dart average is its rejected-dart
fraction. No nonemptiness premise is needed for this identity. -/
theorem powered_rejection_mean_eq_count [Fintype V] [Fintype D]
    (G : PortGraph V D) (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) :
    SpectralReturn.mean (fun d : Dart V D n => PoweringMoment.bit
      ((poweredGraph G accepts n selectors).edgeSatisfied labels d = false)) =
      ((poweredGraph G accepts n selectors).rejectionCount labels : ℝ) /
        (Fintype.card (Dart V D n) : ℝ) :=
  constraint_rejection_mean_eq_count _ _

/-- The recorded-walk rejection average used in soundness is the actual
powered graph's rejected-dart fraction. -/
theorem path_rejection_mean_eq_count [Fintype V] [Fintype D]
    (G : PortGraph V D) (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) :
    SpectralReturn.mean (fun w : Walk V D (n + 1) => PoweringMoment.bit
      (pathAccepts G accepts n selectors w (labels w.1) (labels (endpoint G w)) = false)) =
      ((poweredGraph G accepts n selectors).rejectionCount labels : ℝ) /
        (Fintype.card (Dart V D n) : ℝ) := by
  rw [← rejection_mean_eq_path_mean G accepts n selectors labels]
  exact powered_rejection_mean_eq_count G accepts n selectors labels

/-- Convert a proved path-test rejection lower bound into the actual powered
constraint graph's rejected-dart count inequality. -/
theorem powered_density_lower_to_count [Fintype V] [Fintype D]
    (G : PortGraph V D) (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A)
    (hcard : 0 < Fintype.card (Dart V D n)) (ε : ℝ)
    (hlower : ε ≤ SpectralReturn.mean (fun w : Walk V D (n + 1) => PoweringMoment.bit
      (pathAccepts G accepts n selectors w (labels w.1) (labels (endpoint G w)) = false))) :
    ε * (Fintype.card (Dart V D n) : ℝ) ≤
      ((poweredGraph G accepts n selectors).rejectionCount labels : ℝ) := by
  rw [path_rejection_mean_eq_count G accepts n selectors labels] at hlower
  exact (le_div_iff₀ (Nat.cast_pos.mpr hcard)).1 hlower

/-- Exact size of the powered dart type, retaining both direction flags and
all recorded port words, including repeated vertices and edges. -/
theorem natCard_dart [Finite V] [Finite D] (n : Nat) :
    Nat.card (Dart V D n) = 2 * Nat.card V * Nat.card D ^ (n + 1) := by
  simp [Dart, Walk, Nat.card_prod, Nat.card_fun, Nat.mul_assoc]

theorem fintypeCard_dart [Fintype V] [Fintype D] (n : Nat) :
    Fintype.card (Dart V D n) =
      2 * Fintype.card V * Fintype.card D ^ (n + 1) := by
  simpa only [Nat.card_eq_fintype_card] using (natCard_dart (V := V) (D := D) n)

/-- The common powered alphabet size depends only on degree, radius, and the
base alphabet. The ambient vertex cardinality does not occur. -/
theorem natCard_poweredAlphabet [Finite D] [Finite A] (n : Nat) :
    Nat.card (PaddedLabel D (n + 1) A) =
      Nat.card A ^ (∑ j : Fin (n + 2), Nat.card D ^ j.val) :=
  PoweringLabels.card_paddedLabel (n + 1)

/-- With finite numbered ports, the same exponent is the length of the
already constructed executable address enumeration. -/
theorem natCard_finitePortAlphabet [Finite A] (d n : Nat) :
    Nat.card (PaddedLabel (Fin d) (n + 1) A) =
      Nat.card A ^ (PoweringAddresses.allAddresses d (n + 1)).length := by
  rw [PoweringLabels.card_paddedLabel, PoweringAddresses.length_allAddresses]
  simp only [Nat.card_fin]

end UniqueGamesTheorem.Foundations.PCP.PoweringCounting

end

end OAI
