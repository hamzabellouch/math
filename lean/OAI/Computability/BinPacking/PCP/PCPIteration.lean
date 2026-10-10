import Mathlib.Data.Nat.Log
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import OAI.Computability.BinPacking.Information.SourceNonempty
import OAI.Computability.BinPacking.PCP.PoweringFinalConstants

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.PCP.AmplificationIteration

def run {X : Type*} (step : X → X) : Nat → X → X
  | 0, x => x
  | n + 1, x => step (run step n x)

private theorem min_double_min (u cap : ℝ) (hc : 0 ≤ cap) :
    min (2 * min u cap) cap = min (2 * u) cap := by
  by_cases hu : u ≤ cap
  · rw [min_eq_left hu]
  · have hcu : cap ≤ u := le_of_not_ge hu
    rw [min_eq_right hcu, min_eq_right (by linarith : cap ≤ 2 * cap),
      min_eq_right (by linarith : cap ≤ 2 * u)]

theorem run_gap {X : Type*} (step : X → X) (gap : X → ℝ)
    (cap : ℝ) (hc : 0 ≤ cap)
    (amplifies : ∀ x, min (2 * gap x) cap ≤ gap (step x))
    (n : Nat) (x : X) :
    min (2 ^ n * gap x) cap ≤ gap (run step n x) := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    have hm : min (2 * min (2 ^ n * gap x) cap) cap ≤
        min (2 * gap (run step n x)) cap :=
      min_le_min (mul_le_mul_of_nonneg_left ih (by norm_num)) le_rfl
    rw [min_double_min _ _ hc] at hm
    have h := hm.trans (amplifies (run step n x))
    simpa [run, pow_succ, mul_assoc, mul_left_comm, mul_comm] using h

theorem run_preserves {X : Type*} (step : X → X) (P : X → Prop)
    (preserves : ∀ x, P x → P (step x)) (n : Nat) (x : X) (hx : P x) :
    P (run step n x) := by
  induction n with
  | zero => exact hx
  | succ n ih => exact preserves _ ih

theorem run_size {X : Type*} (step : X → X) (size : X → Nat) (C : Nat)
    (blowup : ∀ x, size (step x) ≤ C * size x) (n : Nat) (x : X) :
    size (run step n x) ≤ C ^ n * size x := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    have h := (blowup (run step n x)).trans (Nat.mul_le_mul_left C ih)
    simpa [run, pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h

def rounds (n : Nat) : Nat := Nat.log2 n + 1

theorem rounds_large (n : Nat) : n < 2 ^ rounds n := by
  simpa [rounds, Nat.log2_eq_log_two] using
    (Nat.lt_pow_succ_log_self (by decide : 1 < 2) n)

theorem rounds_power_le {n : Nat} (hn : 0 < n) : 2 ^ rounds n ≤ 2 * n := by
  have h := Nat.pow_log_le_self 2 (Nat.ne_of_gt hn)
  simpa [rounds, Nat.log2_eq_log_two, pow_succ, Nat.mul_comm] using
    (Nat.mul_le_mul_right 2 h)

theorem blowup_rounds_le {C degree n : Nat} (hn : 0 < n) (hC : C ≤ 2 ^ degree) :
    C ^ rounds n ≤ (2 * n) ^ degree := by
  calc
    C ^ rounds n ≤ (2 ^ degree) ^ rounds n := Nat.pow_le_pow_left hC _
    _ = (2 ^ rounds n) ^ degree := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm degree (rounds n)]
    _ ≤ (2 * n) ^ degree := Nat.pow_le_pow_left (rounds_power_le hn) _

theorem run_size_polynomial {X : Type*} (step : X → X) (size : X → Nat)
    {C degree n : Nat} (hn : 0 < n) (hC : C ≤ 2 ^ degree)
    (blowup : ∀ x, size (step x) ≤ C * size x) (x : X) :
    size (run step (rounds n) x) ≤ (2 * n) ^ degree * size x :=
  (run_size step size C blowup (rounds n) x).trans
    (Nat.mul_le_mul_right _ (blowup_rounds_le hn hC))

theorem run_reaches_cap {X : Type*} (step : X → X) (gap : X → ℝ)
    (cap : ℝ) (hc : 0 ≤ cap) (hc1 : cap ≤ 1)
    (amplifies : ∀ x, min (2 * gap x) cap ≤ gap (step x))
    (n : Nat) (x : X) (hg : 0 ≤ gap x) (hstart : 1 ≤ (n : ℝ) * gap x) :
    cap ≤ gap (run step (rounds n) x) := by
  have hp : (n : ℝ) ≤ (2 : ℝ) ^ rounds n := by
    exact_mod_cast (Nat.le_of_lt (rounds_large n))
  have hcap : cap ≤ (2 : ℝ) ^ rounds n * gap x :=
    hc1.trans (hstart.trans (mul_le_mul_of_nonneg_right hp hg))
  have h := run_gap step gap cap hc amplifies (rounds n) x
  rwa [min_eq_right hcap] at h

end BinPackingGames.Foundations.PCP.AmplificationIteration

namespace BinPackingGames.Foundations.PCP.AlphabetGraphBounds

open scoped BigOperators

abbrev OutputVertex (V E A : Type*) :=
  QueryIncidence.Vertex (AlphabetGraph.Event E A) (AlphabetGraph.Address V E A)

abbrev OutputDart (E A : Type*) := QueryIncidence.Dart (AlphabetGraph.Event E A) 6

def localEventFactor (q : Nat) : Nat :=
  4 * (2 * 2 ^ q) * (2 ^ (q * q)) ^ 5

def vertexFactor (q : Nat) : Nat := localEventFactor q + 2 ^ (q * q)

def dartFactor (q : Nat) : Nat := 12 * localEventFactor q

def sizeFactor (q : Nat) : Nat := 2 ^ q + vertexFactor q + dartFactor q

theorem sizeFactor_positive (q : Nat) : 0 < sizeFactor q := by
  have hp : (0 : Nat) < 2 ^ q := pow_pos (by decide) q
  unfold sizeFactor
  omega

variable {V E A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

theorem gap_transfer_real [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : ConstraintGraph V E A) (eps : ℝ) (_eps_nonnegative : 0 ≤ eps)
    (source : ∀ labeling : V → A,
      eps * (Fintype.card E : ℝ) ≤ (G.rejectionCount labeling : ℝ))
    (labeling : OutputVertex V E A → QueryIncidence.Label 6) :
    (eps / 12288) * (Fintype.card (OutputDart E A) : ℝ) ≤
      ((AlphabetGraph.graph G).rejectionCount labeling : ℝ) := by
  let assignment := QueryIncidence.decodedAssignment (by decide : 0 < 6) labeling
  have htest :
      (Fintype.card (AlphabetGraph.LocalEvent A) : ℝ) *
          (G.rejectionCount (AlphabetGraph.decodedLabeling assignment) : ℝ) ≤
        2048 * (QueryIncidence.verifierRejectionCount (AlphabetGraph.verifier G) assignment : ℝ) := by
    exact_mod_cast AlphabetGraph.rejection_count_bound G assignment
  have hinc :
      2 * (QueryIncidence.verifierRejectionCount (AlphabetGraph.verifier G) assignment : ℝ) ≤
        ((AlphabetGraph.graph G).rejectionCount labeling : ℝ) := by
    exact_mod_cast QueryIncidence.rejection_count_bound
      (AlphabetGraph.verifier G) (by decide : 0 < 6) labeling
  have hscaled :
      eps * (Fintype.card E : ℝ) * (Fintype.card (AlphabetGraph.LocalEvent A) : ℝ) ≤
        2048 * (QueryIncidence.verifierRejectionCount (AlphabetGraph.verifier G) assignment : ℝ) := by
    calc
      _ = (Fintype.card (AlphabetGraph.LocalEvent A) : ℝ) *
          (eps * (Fintype.card E : ℝ)) := by ring
      _ ≤ (Fintype.card (AlphabetGraph.LocalEvent A) : ℝ) *
          (G.rejectionCount (AlphabetGraph.decodedLabeling assignment) : ℝ) :=
        mul_le_mul_of_nonneg_left (source (AlphabetGraph.decodedLabeling assignment))
          (Nat.cast_nonneg _)
      _ ≤ _ := htest
  change (eps / 12288) *
    (Fintype.card (QueryIncidence.Dart (AlphabetGraph.Event E A) 6) : ℝ) ≤ _
  rw [QueryIncidence.card_dart, AlphabetGraph.card_event]
  push_cast
  nlinarith

variable [Fintype V] [Fintype E]

omit [Nonempty A]

theorem card_output_vertex :
    Fintype.card (OutputVertex V E A) =
      Fintype.card V * 2 ^ Fintype.card A +
        Fintype.card E * vertexFactor (Fintype.card A) := by
  rw [QueryIncidence.card_vertex, AlphabetGraph.card_event,
    AlphabetGraph.card_address, AlphabetGraph.card_localEvent]
  unfold vertexFactor localEventFactor
  ring

theorem card_output_dart :
    Fintype.card (OutputDart E A) = Fintype.card E * dartFactor (Fintype.card A) := by
  rw [QueryIncidence.card_dart, AlphabetGraph.card_event, AlphabetGraph.card_localEvent]
  unfold dartFactor localEventFactor
  ring

theorem card_output_total :
    Fintype.card (OutputVertex V E A) + Fintype.card (OutputDart E A) =
      Fintype.card V * 2 ^ Fintype.card A +
        Fintype.card E * (vertexFactor (Fintype.card A) + dartFactor (Fintype.card A)) := by
  rw [card_output_vertex, card_output_dart]
  ring

theorem card_output_total_le :
    Fintype.card (OutputVertex V E A) + Fintype.card (OutputDart E A) ≤
      sizeFactor (Fintype.card A) * (Fintype.card V + Fintype.card E) := by
  rw [card_output_total]
  have hv : 2 ^ Fintype.card A ≤ sizeFactor (Fintype.card A) := by
    unfold sizeFactor
    omega
  have he : vertexFactor (Fintype.card A) + dartFactor (Fintype.card A) ≤
      sizeFactor (Fintype.card A) := by
    unfold sizeFactor
    exact Nat.add_le_add_right (Nat.le_add_left _ _) _
  calc
    _ ≤ Fintype.card V * sizeFactor (Fintype.card A) +
        Fintype.card E * sizeFactor (Fintype.card A) :=
      Nat.add_le_add (Nat.mul_le_mul_left _ hv) (Nat.mul_le_mul_left _ he)
    _ = _ := by ring

theorem card_output_vertex_le :
    Fintype.card (OutputVertex V E A) ≤
      sizeFactor (Fintype.card A) * (Fintype.card V + Fintype.card E) :=
  (Nat.le_add_right _ _).trans card_output_total_le

theorem card_output_dart_le :
    Fintype.card (OutputDart E A) ≤
      sizeFactor (Fintype.card A) * (Fintype.card V + Fintype.card E) :=
  (Nat.le_add_left _ _).trans card_output_total_le

end BinPackingGames.Foundations.PCP.AlphabetGraphBounds

namespace BinPackingGames.Foundations.PCP.AmplificationRound

abbrev Label := QueryIncidence.Label 6
abbrev Addresses := PoweringLabels.PortWords Preprocessing.Port FinalConstants.walkLength
abbrev PoweredAlphabet :=
  PoweringLabels.PaddedLabel Preprocessing.Port FinalConstants.walkLength Label

instance : Fintype PoweredAlphabet := Fintype.ofFinite _
instance : DecidableEq PoweredAlphabet := Classical.decEq _

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  [Nonempty E]

abbrev PoweredDart (G : ConstraintGraph V E Label) :=
  PoweringTest.Dart (Preprocessing.Vertex G) Preprocessing.Port
    (2 * FinalConstants.endpointLength)

instance (G : ConstraintGraph V E Label) : DecidableEq (PoweredDart G) := Classical.decEq _

def selectors (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
    (G : ConstraintGraph V E Label) (v : Preprocessing.Vertex G) :
    PoweringLabels.AddressSelector (Preprocessing.portGraph G)
      FinalConstants.walkLength v :=
  PoweringLabels.listSelector (Preprocessing.portGraph G) FinalConstants.walkLength
    v addresses complete

def powered (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
    (G : ConstraintGraph V E Label) :
    ConstraintGraph (Preprocessing.Vertex G) (PoweredDart G) PoweredAlphabet :=
  PoweringTest.poweredGraph (Preprocessing.portGraph G) (Preprocessing.graph G).accepts
    (2 * FinalConstants.endpointLength) (selectors addresses complete G)

abbrev Vertex (G : ConstraintGraph V E Label) :=
  QueryIncidence.Vertex
    (AlphabetGraph.Event (PoweredDart G) PoweredAlphabet)
    (AlphabetGraph.Address (Preprocessing.Vertex G) (PoweredDart G) PoweredAlphabet)

abbrev Dart (G : ConstraintGraph V E Label) :=
  QueryIncidence.Dart (AlphabetGraph.Event (PoweredDart G) PoweredAlphabet) 6

instance (G : ConstraintGraph V E Label) : Fintype (Vertex G) := by
  letI : Fintype (AlphabetGraph.Event (PoweredDart G) PoweredAlphabet) := inferInstance
  letI : Fintype
      (AlphabetGraph.Address (Preprocessing.Vertex G) (PoweredDart G) PoweredAlphabet) :=
    inferInstance
  change Fintype
    (AlphabetGraph.Event (PoweredDart G) PoweredAlphabet ⊕
      AlphabetGraph.Address (Preprocessing.Vertex G) (PoweredDart G) PoweredAlphabet)
  infer_instance
instance (G : ConstraintGraph V E Label) : Fintype (Dart G) := by
  change Fintype ((AlphabetGraph.Event (PoweredDart G) PoweredAlphabet × Fin 6) × Bool)
  infer_instance
instance (G : ConstraintGraph V E Label) : DecidableEq (Vertex G) := Classical.decEq _

def graph (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
    (G : ConstraintGraph V E Label) : ConstraintGraph (Vertex G) (Dart G) Label :=
  AlphabetGraph.graph (powered addresses complete G)

omit [Nonempty E] in
theorem powered_completeness (addresses : List Addresses)
    (complete : ∀ w, w ∈ addresses) (G : ConstraintGraph V E Label)
    (satisfied : G.Satisfiable) : (powered addresses complete G).Satisfiable := by
  obtain ⟨assignment, hassignment⟩ := Preprocessing.completeness G satisfied
  refine ⟨PoweringOpinions.honestLabels (Preprocessing.portGraph G)
    FinalConstants.walkLength assignment, ?_⟩
  apply PoweringTest.perfect_completeness (Preprocessing.portGraph G)
    (Preprocessing.graph G).accepts (2 * FinalConstants.endpointLength)
    (selectors addresses complete G) assignment
  intro e
  exact hassignment e

omit [Nonempty E] in
theorem completeness (addresses : List Addresses)
    (complete : ∀ w, w ∈ addresses) (G : ConstraintGraph V E Label)
    (satisfied : G.Satisfiable) : (graph addresses complete G).Satisfiable :=
  AlphabetGraph.perfect_completeness _
    (powered_completeness addresses complete G satisfied)

end BinPackingGames.Foundations.PCP.AmplificationRound

namespace BinPackingGames.Foundations.PCP.RoundSize

open scoped BigOperators

theorem card_padded_alphabet {D A : Type*} [Fintype D] [DecidableEq D]
    [Fintype A] (t : Nat) :
    Fintype.card (PoweringLabels.PaddedLabel D t A) =
      Fintype.card A ^ (∑ k : Fin (t + 1), Fintype.card D ^ k.val) := by
  simpa only [Nat.card_eq_fintype_card] using
    PoweringLabels.card_paddedLabel (D := D) (A := A) t

theorem card_powered_dart {V D : Type*} [Fintype V] [Fintype D]
    (n : Nat) : Fintype.card (PoweringTest.Dart V D n) =
      Fintype.card V * (2 * Fintype.card D ^ (n + 1)) := by
  simp only [PoweringTest.Dart, PoweringWalks.Walk, Fintype.card_prod,
    Fintype.card_bool, Fintype.card_fun, Fintype.card_fin]
  ring

private opaque lockedNat (n : Nat) : {m : Nat // m = n} := ⟨n, rfl⟩

def poweredAlphabetSize : Nat :=
  (lockedNat (64 ^ (∑ k : Fin (FinalConstants.walkLength + 1),
    Preprocessing.degree ^ k.val))).val

def poweredDartFactor : Nat :=
  (lockedNat (2 * Preprocessing.degree ^ (2 * FinalConstants.endpointLength + 1))).val

def sizeFactor : Nat :=
  (lockedNat (AlphabetGraphBounds.sizeFactor poweredAlphabetSize *
    (1 + poweredDartFactor) * ExpanderFamily.growth ^ 2)).val

theorem poweredAlphabetSize_eq : poweredAlphabetSize =
    64 ^ (∑ k : Fin (FinalConstants.walkLength + 1), Preprocessing.degree ^ k.val) :=
  (lockedNat _).property

theorem poweredDartFactor_eq : poweredDartFactor =
    2 * Preprocessing.degree ^ (2 * FinalConstants.endpointLength + 1) :=
  (lockedNat _).property

theorem sizeFactor_eq : sizeFactor = AlphabetGraphBounds.sizeFactor poweredAlphabetSize *
    (1 + poweredDartFactor) * ExpanderFamily.growth ^ 2 :=
  (lockedNat _).property

private theorem coefficient_positive (q d g : Nat) (hg : 0 < g) :
    0 < AlphabetGraphBounds.sizeFactor q * (1 + d) * g ^ 2 := by
  exact Nat.mul_pos (Nat.mul_pos (AlphabetGraphBounds.sizeFactor_positive q)
    (Nat.zero_lt_one.trans_le (Nat.le_add_right 1 d))) (pow_pos hg 2)

theorem poweredAlphabet_card : Fintype.card AmplificationRound.PoweredAlphabet =
    poweredAlphabetSize := by
  have h := PoweringLabels.card_paddedLabel (D := Preprocessing.Port)
    (A := QueryIncidence.Label 6) FinalConstants.walkLength
  change Nat.card AmplificationRound.PoweredAlphabet = _ at h
  simp only [Nat.card_eq_fintype_card, ← Preprocessing.degree_eq_card,
    QueryIncidence.six_query_alphabet] at h
  exact h.trans poweredAlphabetSize_eq.symm

theorem sizeFactor_positive : 0 < sizeFactor := by
  have hG : 0 < ExpanderFamily.growth :=
    Nat.zero_lt_one.trans ExpanderFamily.growth_gt_one
  rw [sizeFactor_eq]
  exact coefficient_positive _ _ _ hG

private theorem factor_total (c v d : Nat) : c * (v + v * d) = c * (1 + d) * v := by
  ring

private theorem nat_card_output_vertex {V E A : Type*}
    [Fintype V] [Fintype E] [Fintype A] [DecidableEq A] [Nonempty A] :
    Nat.card (AlphabetGraphBounds.OutputVertex V E A) =
      Nat.card V * 2 ^ Nat.card A +
        Nat.card E * AlphabetGraphBounds.vertexFactor (Nat.card A) := by
  simpa only [← Nat.card_eq_fintype_card] using
    AlphabetGraphBounds.card_output_vertex (V := V) (E := E) (A := A)

private theorem nat_card_output_dart {E A : Type*}
    [Fintype E] [Fintype A] [DecidableEq A] [Nonempty A] :
    Nat.card (AlphabetGraphBounds.OutputDart E A) =
      Nat.card E * AlphabetGraphBounds.dartFactor (Nat.card A) := by
  simpa only [← Nat.card_eq_fintype_card] using
    AlphabetGraphBounds.card_output_dart (E := E) (A := A)

private theorem nat_card_output_total_le {V E A : Type*}
    [Fintype V] [Fintype E] [Fintype A] [DecidableEq A] [Nonempty A] :
    Nat.card (AlphabetGraphBounds.OutputVertex V E A) +
        Nat.card (AlphabetGraphBounds.OutputDart E A) ≤
      AlphabetGraphBounds.sizeFactor (Nat.card A) * (Nat.card V + Nat.card E) := by
  simpa only [← Nat.card_eq_fintype_card] using
    AlphabetGraphBounds.card_output_total_le (V := V) (E := E) (A := A)

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  [Nonempty E]

omit [DecidableEq E] [Nonempty E] in
theorem poweredDart_card (G : ConstraintGraph V E AmplificationRound.Label) :
    Fintype.card (AmplificationRound.PoweredDart G) =
      Fintype.card (Preprocessing.Vertex G) * poweredDartFactor := by
  have h := card_powered_dart (V := Preprocessing.Vertex G) (D := Preprocessing.Port)
    (2 * FinalConstants.endpointLength)
  rw [← Preprocessing.degree_eq_card] at h
  exact h.trans (congrArg (fun d => Fintype.card (Preprocessing.Vertex G) * d)
    poweredDartFactor_eq.symm)

omit [DecidableEq E] [Nonempty E] in

theorem output_vertex_card (G : ConstraintGraph V E AmplificationRound.Label) :
    Fintype.card (AmplificationRound.Vertex G) =
      Fintype.card (Preprocessing.Vertex G) * 2 ^ poweredAlphabetSize +
        (Fintype.card (Preprocessing.Vertex G) * poweredDartFactor) *
          AlphabetGraphBounds.vertexFactor poweredAlphabetSize := by
  have h := nat_card_output_vertex (V := Preprocessing.Vertex G)
    (E := AmplificationRound.PoweredDart G) (A := AmplificationRound.PoweredAlphabet)
  change Nat.card (AmplificationRound.Vertex G) =
    Nat.card (Preprocessing.Vertex G) * 2 ^ Nat.card AmplificationRound.PoweredAlphabet +
      Nat.card (AmplificationRound.PoweredDart G) *
        AlphabetGraphBounds.vertexFactor (Nat.card AmplificationRound.PoweredAlphabet) at h
  simpa only [Nat.card_eq_fintype_card, poweredAlphabet_card, poweredDart_card] using h

omit [DecidableEq E] [Nonempty E] in

theorem output_dart_card (G : ConstraintGraph V E AmplificationRound.Label) :
    Fintype.card (AmplificationRound.Dart G) =
      (Fintype.card (Preprocessing.Vertex G) * poweredDartFactor) *
        AlphabetGraphBounds.dartFactor poweredAlphabetSize := by
  have h := nat_card_output_dart (E := AmplificationRound.PoweredDart G)
    (A := AmplificationRound.PoweredAlphabet)
  change Nat.card (AmplificationRound.Dart G) = Nat.card (AmplificationRound.PoweredDart G) *
    AlphabetGraphBounds.dartFactor (Nat.card AmplificationRound.PoweredAlphabet) at h
  simpa only [Nat.card_eq_fintype_card, poweredAlphabet_card, poweredDart_card] using h

omit [DecidableEq E] in
theorem output_total_le_darts (G : ConstraintGraph V E AmplificationRound.Label) :
    Fintype.card (AmplificationRound.Vertex G) + Fintype.card (AmplificationRound.Dart G) ≤
      sizeFactor * Fintype.card E := by
  have h := nat_card_output_total_le
    (V := Preprocessing.Vertex G) (E := AmplificationRound.PoweredDart G)
    (A := AmplificationRound.PoweredAlphabet)
  change Nat.card (AmplificationRound.Vertex G) + Nat.card (AmplificationRound.Dart G) ≤
    AlphabetGraphBounds.sizeFactor (Nat.card AmplificationRound.PoweredAlphabet) *
      (Nat.card (Preprocessing.Vertex G) + Nat.card (AmplificationRound.PoweredDart G)) at h
  simp only [Nat.card_eq_fintype_card] at h
  rw [poweredAlphabet_card, poweredDart_card] at h
  calc
    _ ≤ AlphabetGraphBounds.sizeFactor poweredAlphabetSize *
        (Fintype.card (Preprocessing.Vertex G) +
          Fintype.card (Preprocessing.Vertex G) * poweredDartFactor) := h
    _ = (AlphabetGraphBounds.sizeFactor poweredAlphabetSize *
        (1 + poweredDartFactor)) * Fintype.card (Preprocessing.Vertex G) :=
      factor_total _ _ _
    _ ≤ (AlphabetGraphBounds.sizeFactor poweredAlphabetSize *
        (1 + poweredDartFactor)) * (ExpanderFamily.growth ^ 2 * Fintype.card E) :=
      Nat.mul_le_mul_left _ (Preprocessing.vertex_count_le G)
    _ = sizeFactor * Fintype.card E := by
      rw [sizeFactor_eq]
      exact (Nat.mul_assoc _ _ _).symm

omit [DecidableEq E] in
theorem output_total_le (G : ConstraintGraph V E AmplificationRound.Label) :
    Fintype.card (AmplificationRound.Vertex G) + Fintype.card (AmplificationRound.Dart G) ≤
      sizeFactor * (Fintype.card V + Fintype.card E) :=
  (output_total_le_darts G).trans (Nat.mul_le_mul_left _ (Nat.le_add_left _ _))

end BinPackingGames.Foundations.PCP.RoundSize

namespace BinPackingGames.Foundations.PCP.RoundGap

open AmplificationRound

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  [Nonempty E]

def poweredLower (epsilon : ℝ) : ℝ :=
  PoweringSoundness.gain (Fintype.card Label) FinalConstants.windowHalf (31 / 32) *
    min (epsilon / (Preprocessing.sizeFactor : ℝ)) FinalConstants.cap

theorem poweredLower_nonnegative (epsilon : ℝ) (he : 0 ≤ epsilon) :
    0 ≤ poweredLower epsilon := by
  have hg := PoweringGap.gain_nonneg (Fintype.card Label)
    FinalConstants.windowHalf (31 / 32) (by norm_num)
  have hs : (0 : ℝ) < Preprocessing.sizeFactor := by
    exact_mod_cast Preprocessing.sizeFactor_positive
  exact mul_nonneg hg (le_min (div_nonneg he hs.le) FinalConstants.cap_positive.le)

theorem powered_count_gap (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
    (G : ConstraintGraph V E Label)
    (labeling : Preprocessing.Vertex G → PoweredAlphabet) :
    poweredLower G.gap * (Fintype.card (PoweredDart G) : ℝ) ≤
      ((powered addresses complete G).rejectionCount labeling : ℝ) := by
  let H := Overlay.originalPortGraph (Preprocessing.overlayGraph G)
  have certificate : SpectralReturn.SpectralCertificate
      (PoweringWalks.lazyGraph H) (31 / 32 : ℝ) :=
    Preprocessing.spectral_certificate G
  have lower : ∀ assignment : Preprocessing.Vertex G → Label,
      (G.gap / (Preprocessing.sizeFactor : ℝ)) *
          (Fintype.card (Preprocessing.Vertex G × Preprocessing.Port) : ℝ) ≤
        ((Preprocessing.graph G).rejectionCount assignment : ℝ) :=
    Preprocessing.gap_transfer_real G G.gap G.gap_nonnegative
      ((G.le_gap_iff G.gap).mp le_rfl)
  have hs : (0 : ℝ) < Preprocessing.sizeFactor := by
    exact_mod_cast Preprocessing.sizeFactor_positive
  have h := PoweringGap.uniform_count_gap H (31 / 32) certificate
    (Preprocessing.graph G).accepts (Preprocessing.accepts_reverse G)
    FinalConstants.windowHalf FinalConstants.windowHalf_positive
    (selectors addresses complete G)
    (G.gap / (Preprocessing.sizeFactor : ℝ)) (div_nonneg G.gap_nonnegative hs.le)
    lower labeling
  convert h using 1 <;>
    simp only [poweredLower, powered, FinalConstants.cap, FinalConstants.walkLength,
      PoweringFinalConstants.center_eq]
  rfl

theorem amplifies (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
    (G : ConstraintGraph V E Label) :
    min (2 * G.gap) FinalConstants.cap ≤ (graph addresses complete G).gap := by
  apply ((graph addresses complete G).le_gap_iff _).mpr
  intro labeling
  have hcount := AlphabetGraphBounds.gap_transfer_real (powered addresses complete G)
    (poweredLower G.gap) (poweredLower_nonnegative G.gap G.gap_nonnegative)
    (powered_count_gap addresses complete G) labeling
  have hscalar : min (2 * G.gap) FinalConstants.cap ≤ poweredLower G.gap / 12288 := by
    simpa only [poweredLower, FinalConstants.cap, FinalConstants.walkLength,
      PoweringFinalConstants.center_eq] using
      PoweringFinalConstants.composed_scaled_gap G.gap G.gap_nonnegative
  exact (mul_le_mul_of_nonneg_right hscalar (Nat.cast_nonneg _)).trans hcount

end BinPackingGames.Foundations.PCP.RoundGap

namespace BinPackingGames.Foundations.PCP.PCPIteration

open FiniteGraph

abbrev Label := AlphabetRetraction.Label64
abbrev Graph := Bundle Label
abbrev Addresses := AmplificationRound.Addresses

def step (addresses : List Addresses) (complete : ∀ w, w ∈ addresses) (G : Graph) : Graph := by
  classical
  exact Bundle.ofGraph (AmplificationRound.graph addresses complete G.graph)

def run (addresses : List Addresses) (complete : ∀ w, w ∈ addresses) : Nat → Graph → Graph :=
  AmplificationIteration.run (step addresses complete)

def initial (F : Target.Formula) : Graph := Bundle.ofGraph (AlphabetRetraction.initial64 F)

def iterationCount (F : Target.Formula) : Nat := AmplificationIteration.rounds (initial F).size

def output (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
    (F : Target.Formula) : Graph := run addresses complete (iterationCount F) (initial F)

def polynomialDegree : Nat := AmplificationIteration.rounds RoundSize.sizeFactor

def finalClauseGap : ℚ := 1 / (40960 * (FinalConstants.walkLength : ℚ))

theorem finalClauseGap_positive : 0 < finalClauseGap := by
  apply one_div_pos.mpr
  exact mul_pos (by norm_num) (by exact_mod_cast FinalConstants.walkLength_positive)

theorem sizeFactor_le_power : RoundSize.sizeFactor ≤ 2 ^ polynomialDegree :=
  (AmplificationIteration.rounds_large RoundSize.sizeFactor).le

theorem initial_satisfiable_iff (F : Target.Formula) :
    (initial F).Satisfiable ↔ F.Satisfiable :=
  AlphabetRetraction.initial64_satisfiable_iff F

theorem initial_size_positive (F : Target.Formula) : 0 < (initial F).size :=
  (initial F).size_positive

theorem initial_size_bound (F : Target.Formula) :
    (initial F).size ≤ 10 * F.clauses.length + 2 := by
  change Fintype.card (InitialGraph.CompactVertex F) +
    Fintype.card (InitialGraph.CompactDart F) ≤ _
  rw [InitialGraph.build_dart_count]
  have h := InitialGraph.build_vertex_bound F
  omega

theorem step_completeness (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
    (G : Graph) (satisfied : G.Satisfiable) : (step addresses complete G).Satisfiable :=
  AmplificationRound.completeness addresses complete G.graph satisfied

theorem step_gap (addresses : List Addresses) (complete : ∀ w, w ∈ addresses) (G : Graph) :
    min (2 * G.gap) FinalConstants.cap ≤ (step addresses complete G).gap :=
  RoundGap.amplifies addresses complete G.graph

theorem step_size (addresses : List Addresses) (complete : ∀ w, w ∈ addresses) (G : Graph) :
    (step addresses complete G).size ≤ RoundSize.sizeFactor * G.size :=
  RoundSize.output_total_le G.graph

theorem run_completeness (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
    (n : Nat) (G : Graph) (satisfied : G.Satisfiable) :
    (run addresses complete n G).Satisfiable :=
  AmplificationIteration.run_preserves (step addresses complete) Bundle.Satisfiable
    (step_completeness addresses complete) n G satisfied

theorem run_gap (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
    (n : Nat) (G : Graph) :
    min (2 ^ n * G.gap) FinalConstants.cap ≤ (run addresses complete n G).gap :=
  AmplificationIteration.run_gap (step addresses complete) Bundle.gap
    FinalConstants.cap FinalConstants.cap_positive.le (step_gap addresses complete) n G

theorem run_size (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
    (n : Nat) (G : Graph) :
    (run addresses complete n G).size ≤ RoundSize.sizeFactor ^ n * G.size :=
  AmplificationIteration.run_size (step addresses complete) Bundle.size RoundSize.sizeFactor
    (step_size addresses complete) n G

theorem output_completeness (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
    (F : Target.Formula) (satisfied : F.Satisfiable) :
    (output addresses complete F).Satisfiable :=
  run_completeness addresses complete (iterationCount F) (initial F)
    ((initial_satisfiable_iff F).mpr satisfied)

theorem output_gap (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
    (F : Target.Formula) (unsat : ¬ F.Satisfiable) :
    FinalConstants.cap ≤ (output addresses complete F).gap := by
  have hinitial : ¬ (initial F).Satisfiable :=
    fun h => unsat ((initial_satisfiable_iff F).mp h)
  exact AmplificationIteration.run_reaches_cap (step addresses complete) Bundle.gap
    FinalConstants.cap FinalConstants.cap_positive.le FinalConstants.cap_le_one
    (step_gap addresses complete) (initial F).size (initial F)
    (initial F).gap_nonnegative ((initial F).one_le_size_mul_gap hinitial)

theorem output_satisfiable_iff (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
    (F : Target.Formula) : (output addresses complete F).Satisfiable ↔ F.Satisfiable := by
  constructor
  · intro satisfied
    by_contra unsat
    have hgap := output_gap addresses complete F unsat
    rw [(output addresses complete F).gap_eq_zero_iff.mpr satisfied] at hgap
    exact (not_le_of_gt FinalConstants.cap_positive) hgap
  · exact output_completeness addresses complete F

theorem output_size_polynomial (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
    (F : Target.Formula) :
    (output addresses complete F).size ≤
      (2 * (initial F).size) ^ polynomialDegree * (initial F).size :=
  AmplificationIteration.run_size_polynomial (step addresses complete) Bundle.size
    (initial_size_positive F) sizeFactor_le_power (step_size addresses complete) (initial F)

theorem output_size_clause_bound (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
    (F : Target.Formula) :
    (output addresses complete F).size ≤
      (2 * (10 * F.clauses.length + 2)) ^ polynomialDegree * (10 * F.clauses.length + 2) := by
  have h := initial_size_bound F
  exact (output_size_polynomial addresses complete F).trans
    (Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.mul_le_mul_left 2 h) _) h)

theorem output_count_gap (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
    (F : Target.Formula) (unsat : ¬ F.Satisfiable)
    (labeling : (output addresses complete F).Vertex → Label) :
    Fintype.card (output addresses complete F).Dart ≤
      FinalConstants.walkLength * (output addresses complete F).rejectionCount labeling := by
  have h := ((output addresses complete F).le_gap_iff FinalConstants.cap).mp
    (output_gap addresses complete F unsat) labeling
  have ht : (0 : ℝ) < FinalConstants.walkLength := by
    exact_mod_cast FinalConstants.walkLength_positive
  have h' : (Fintype.card (output addresses complete F).Dart : ℝ) /
      FinalConstants.walkLength ≤
      ((output addresses complete F).rejectionCount labeling : ℝ) := by
    simpa only [FinalConstants.cap, one_div_mul_eq_div] using h
  have h'' := (div_le_iff₀ ht).mp h'
  exact_mod_cast (show (Fintype.card (output addresses complete F).Dart : ℝ) ≤
    (FinalConstants.walkLength : ℝ) *
      ((output addresses complete F).rejectionCount labeling : ℝ) by
        simpa only [mul_comm] using h'')

variable (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
  (F : Target.Formula) {n m : Nat}
  (vertices : (output addresses complete F).Vertex ≃ Fin n)
  (darts : (output addresses complete F).Dart ≃ Fin m)

def finalCNF : Target.Formula :=
  FinalBooleanVerifier.cnf (output addresses complete F).graph vertices darts

theorem finalCNF_satisfiable_iff :
    (finalCNF addresses complete F vertices darts).Satisfiable ↔ F.Satisfiable :=
  (FinalBooleanVerifier.cnf_satisfiable_iff _ vertices darts).trans
    (output_satisfiable_iff addresses complete F)

theorem finalCNF_clause_count :
    (finalCNF addresses complete F vertices darts).clauses.length = m * 40960 :=
  FinalBooleanVerifier.cnf_clause_count _ vertices darts

theorem finalCNF_variable_count :
    (finalCNF addresses complete F vertices darts).variables = n * 6 + m * 36864 :=
  FinalBooleanVerifier.cnf_variable_count _ vertices darts

theorem finalCNF_nonempty : (finalCNF addresses complete F vertices darts).clauses ≠ [] := by
  have hm : Fintype.card (output addresses complete F).Dart = m := by
    simpa only [Fintype.card_fin] using Fintype.card_congr darts
  have hpositive : 0 < m := hm ▸ (Fintype.card_pos :
    0 < Fintype.card (output addresses complete F).Dart)
  exact FinalBooleanVerifier.cnf_nonempty _ vertices darts hpositive

theorem finalCNF_gap (unsat : ¬ F.Satisfiable)
    (assignment : Fin (finalCNF addresses complete F vertices darts).variables → Bool) :
    (finalCNF addresses complete F vertices darts).clauses.length ≤
      (FinalConstants.walkLength * 40960) *
        NameCompaction.failedCount (finalCNF addresses complete F vertices darts) assignment := by
  have source (labeling : (output addresses complete F).Vertex → Label) :
      1 * Fintype.card (output addresses complete F).Dart ≤
        FinalConstants.walkLength * (output addresses complete F).graph.rejectionCount labeling := by
    simpa only [one_mul, Bundle.rejectionCount] using output_count_gap addresses complete F unsat labeling
  simpa only [one_mul, finalCNF] using FinalBooleanVerifier.cnf_gap
    (output addresses complete F).graph vertices darts 1 FinalConstants.walkLength source assignment

theorem finalCNF_clauseGap (unsat : ¬ F.Satisfiable) :
    Hastad.SourceGap.ClauseGap (finalCNF addresses complete F vertices darts) finalClauseGap :=
  Hastad.SourceNonempty.cnf_clauseGap_unit (output addresses complete F).graph
    vertices darts FinalConstants.walkLength FinalConstants.walkLength_positive
    (output_count_gap addresses complete F unsat)

theorem finalCNF_total_size :
    (finalCNF addresses complete F vertices darts).variables +
        (finalCNF addresses complete F vertices darts).clauses.length ≤
      77824 * (output addresses complete F).size := by
  have hn : Fintype.card (output addresses complete F).Vertex = n := by
    simpa only [Fintype.card_fin] using Fintype.card_congr vertices
  have hm : Fintype.card (output addresses complete F).Dart = m := by
    simpa only [Fintype.card_fin] using Fintype.card_congr darts
  have hsize : (output addresses complete F).size = n + m := congrArg₂ Nat.add hn hm
  calc
    _ = n * 6 + m * 36864 + m * 40960 :=
      congrArg₂ Nat.add (finalCNF_variable_count addresses complete F vertices darts)
        (finalCNF_clause_count addresses complete F vertices darts)
    _ ≤ 77824 * (n + m) := by omega
    _ = 77824 * (output addresses complete F).size :=
      congrArg (fun k => 77824 * k) hsize.symm

theorem finalCNF_polynomial_size :
    (finalCNF addresses complete F vertices darts).variables +
        (finalCNF addresses complete F vertices darts).clauses.length ≤
      77824 * ((2 * (10 * F.clauses.length + 2)) ^ polynomialDegree *
        (10 * F.clauses.length + 2)) :=
  (finalCNF_total_size addresses complete F vertices darts).trans
    (Nat.mul_le_mul_left _ (output_size_clause_bound addresses complete F))

end BinPackingGames.Foundations.PCP.PCPIteration

end

end OAI
