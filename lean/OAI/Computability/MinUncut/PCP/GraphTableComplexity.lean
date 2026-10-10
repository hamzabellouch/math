import Mathlib
import OAI.Computability.MinUncut.PCP.RawInitialTables

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.GraphTableComplexity

open MinUncutGames.Foundations.Complexity
open Polynomial

noncomputable def encodingPolynomial (q : Nat) : Polynomial Nat :=
  X ^ 2 + C (2 * (q * q) + 1) * X + C 2

theorem encodingPolynomial_eval (q n : Nat) :
    (encodingPolynomial q).eval n = n ^ 2 + (2 * (q * q) + 1) * n + 2 := by
  simp [encodingPolynomial]

theorem encodingPolynomial_mono (q : Nat) {n m : Nat} (hnm : n ≤ m) :
    (encodingPolynomial q).eval n ≤ (encodingPolynomial q).eval m := by
  rw [encodingPolynomial_eval, encodingPolynomial_eval]
  exact Nat.add_le_add_right
    (Nat.add_le_add (Nat.pow_le_pow_left hnm 2) (Nat.mul_le_mul_left _ hnm)) 2

theorem rowBound_le_polynomial (q vertices darts : Nat) :
    vertices + darts + 2 + darts * (vertices + darts + 2 * (q * q)) ≤
      (encodingPolynomial q).eval (vertices + darts) := by
  have hd : darts ≤ vertices + darts := Nat.le_add_left darts vertices
  calc
    _ ≤ vertices + darts + 2 +
        (vertices + darts) * (vertices + darts + 2 * (q * q)) :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ hd) _
    _ = _ := by rw [encodingPolynomial_eval]; ring

theorem generic_size_add_two_le_bits {q : Nat} (table : GenericGraphTables.Table q) :
    table.vertices + table.darts + 2 ≤ (GenericGraphTables.tableBits table).length := by
  simp only [GenericGraphTables.tableBits, GenericGraphTables.tableWords,
    encodeWords_append, List.length_append, encodeWords, encodeWord_length, List.length_nil]
  omega

theorem generic_bits_le_polynomial {q : Nat} (table : GenericGraphTables.Table q) :
    (GenericGraphTables.tableBits table).length ≤
      (encodingPolynomial q).eval (table.vertices + table.darts) :=
  (GenericGraphTables.tableBits_length_le table).trans
    (rowBound_le_polynomial q table.vertices table.darts)

theorem generic_bits_le_of_size_le {q N : Nat} (table : GenericGraphTables.Table q)
    (hsize : table.vertices + table.darts ≤ N) :
    (GenericGraphTables.tableBits table).length ≤ (encodingPolynomial q).eval N :=
  (generic_bits_le_polynomial table).trans (encodingPolynomial_mono q hsize)

theorem size_add_two_le_bits (table : GraphTables.Table) :
    table.vertices + table.darts + 2 ≤ (GraphTables.tableBits table).length := by
  simp only [GraphTables.tableBits, GraphTables.tableWords,
    encodeWords_append, List.length_append, encodeWords, encodeWord_length, List.length_nil]
  omega

theorem bits_le_polynomial (table : GraphTables.Table) :
    (GraphTables.tableBits table).length ≤
      (encodingPolynomial 64).eval (table.vertices + table.darts) :=
  (GraphTables.tableBits_length_le table).trans
    (rowBound_le_polynomial 64 table.vertices table.darts)

theorem bits_le_of_size_le {N : Nat} (table : GraphTables.Table)
    (hsize : table.vertices + table.darts ≤ N) :
    (GraphTables.tableBits table).length ≤ (encodingPolynomial 64).eval N :=
  (bits_le_polynomial table).trans (encodingPolynomial_mono 64 hsize)

end MinUncutGames.Foundations.PCP.GraphTableComplexity

end
section
noncomputable section

namespace MinUncutGames.Foundations.PCP.AmplificationRound

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

end MinUncutGames.Foundations.PCP.AmplificationRound

end
end
section
namespace MinUncutGames.Foundations.PCP.PoweringWitness

open PoweringWalks SpectralReturn PoweringReturn PoweringLazy
open PoweringMoment (bit)

variable {V D : Type*}

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

noncomputable def endpointWitness (G : PortGraph V D) (bad : Edge V D → Bool)
    (φ ψ : Edge V D → V → ℝ) (n : Nat) (k : Fin (n + 1))
    (w : Walk V D (n + 1)) : ℝ :=
  bit (bad (edgeAt G n w k) = true) *
    φ (edgeAt G n w k) w.1 * ψ (edgeAt G n w k) (endpoint G w)

noncomputable def vertexWitness (G : PortGraph V D) (bad : Edge V D → Bool)
    (f : V → V → ℝ) (n : Nat) (k : Fin (n + 1)) :
    Walk V D (n + 1) → ℝ :=
  endpointWitness G bad (fun e => f e.1) (fun e => f (next G e.1 e.2)) n k

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

end MinUncutGames.Foundations.PCP.PoweringWitness

end
section
namespace MinUncutGames.Foundations.PCP.PoweringMomentBound

open scoped BigOperators
open PoweringWalks SpectralReturn PoweringReturn
open PoweringMoment (bit hits)

theorem symmetric_gap_matrix_sum (ε : ℝ) (r : Nat → ℝ) :
    ∀ (m : Nat) (f : Fin m → Fin m → ℝ),
      (∀ i j, f i j = f j i) → (∀ i, f i i = ε) →
      (∀ i j, i.val < j.val → f i j = r (j.val - i.val - 1)) →
      (∑ i, ∑ j, f i j) = (m : ℝ) * ε +
        2 * ∑ j ∈ Finset.range m, ∑ gap ∈ Finset.range j, r gap := by
  intro m
  induction m with
  | zero => intro f _hSym _hDiag _hUpper; simp
  | succ m ih =>
    intro f hSym hDiag hUpper
    have hOld : (∑ i : Fin m, ∑ j : Fin m, f i.castSucc j.castSucc) =
        (m : ℝ) * ε + 2 * ∑ j ∈ Finset.range m, ∑ gap ∈ Finset.range j, r gap := by
      apply ih (fun i j => f i.castSucc j.castSucc)
      · intro i j; exact hSym i.castSucc j.castSucc
      · intro i; exact hDiag i.castSucc
      · intro i j hij; exact hUpper i.castSucc j.castSucc hij
    have hLast : (∑ i : Fin m, f i.castSucc (Fin.last m)) =
        ∑ gap ∈ Finset.range m, r gap := by
      calc
        _ = ∑ i : Fin m, r (m - 1 - i.val) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hUpper i.castSucc (Fin.last m) i.isLt]
          simp only [Fin.val_last, Fin.val_castSucc]
          congr 1
          omega
        _ = ∑ i ∈ Finset.range m, r (m - 1 - i) :=
          Fin.sum_univ_eq_sum_range (fun i => r (m - 1 - i)) m
        _ = _ := Finset.sum_range_reflect r m
    have hLastRow : (∑ j : Fin m, f (Fin.last m) j.castSucc) =
        ∑ gap ∈ Finset.range m, r gap := by
      calc
        _ = ∑ j : Fin m, f j.castSucc (Fin.last m) := by
          apply Finset.sum_congr rfl
          intro j _
          exact hSym (Fin.last m) j.castSucc
        _ = _ := hLast
    calc
      (∑ i, ∑ j, f i j) =
          (∑ i : Fin m, ∑ j : Fin m, f i.castSucc j.castSucc) +
            (∑ i : Fin m, f i.castSucc (Fin.last m)) +
            (∑ j : Fin m, f (Fin.last m) j.castSucc) + f (Fin.last m) (Fin.last m) := by
        simp only [Fin.sum_univ_castSucc, Finset.sum_add_distrib]
        ring
      _ = (m : ℝ) * ε +
          2 * (∑ j ∈ Finset.range m, ∑ gap ∈ Finset.range j, r gap) +
          (∑ gap ∈ Finset.range m, r gap) + (∑ gap ∈ Finset.range m, r gap) + ε := by
        rw [hOld, hLast, hLastRow, hDiag]
      _ = ((m + 1 : Nat) : ℝ) * ε +
          2 * ∑ j ∈ Finset.range (m + 1), ∑ gap ∈ Finset.range j, r gap := by
        rw [Finset.sum_range_succ]
        simp only [Nat.cast_add, Nat.cast_one]
        ring

def windowIndex (n start m : Nat) (h : start + m ≤ n + 1) (i : Fin m) : Fin (n + 1) :=
  ⟨start + i.val, (Nat.add_lt_add_left i.isLt start).trans_le h⟩

variable {V D : Type*} [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]

def windowEvent (G : PortGraph V D) (bad : V × D → Bool)
    (n start m : Nat) (h : start + m ≤ n + 1) (i : Fin m) (w : Walk V D (n + 1)) : Prop :=
  bad (edgeAt G n w (windowIndex n start m h i)) = true

theorem window_second_moment_eq (G : PortGraph V D) (bad : V × D → Bool)
    (n start m : Nat) (h : start + m ≤ n + 1) :
    mean (fun w => hits (windowEvent G bad n start m h) w ^ 2) =
      (m : ℝ) * edgeDensity bad +
        2 * ∑ j ∈ Finset.range m, ∑ gap ∈ Finset.range j, returnMass G bad gap := by
  rw [show mean (fun w => hits (windowEvent G bad n start m h) w ^ 2) =
      ∑ i, ∑ j, mean (fun w => bit (windowEvent G bad n start m h i w ∧
        windowEvent G bad n start m h j w)) from
    PoweringMoment.second_moment_eq (windowEvent G bad n start m h)]
  apply symmetric_gap_matrix_sum
  · intro i j
    congr 1
    funext w
    simp only [and_comm]
  · intro i
    simp only [and_self]
    exact hit_mean G bad n (windowIndex n start m h i)
  · intro i j hij
    have hwin : windowIndex n start m h i < windowIndex n start m h j :=
      Nat.add_lt_add_left hij start
    have hp := pair_event_mean G bad n (windowIndex n start m h i)
      (windowIndex n start m h j) hwin
    simpa only [windowEvent, windowIndex, Nat.add_sub_add_left] using hp

theorem window_second_moment_le (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate G lambda) (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e)
    (n start m : Nat) (h : start + m ≤ n + 1) :
    mean (fun w => hits (windowEvent G bad n start m h) w ^ 2) ≤
      (m : ℝ) * edgeDensity bad *
        (1 + 2 / (1 - lambda) + ((m : ℝ) - 1) * edgeDensity bad) := by
  rw [window_second_moment_eq]
  exact secondMoment_return_envelope G lambda certificate bad reversal m

end MinUncutGames.Foundations.PCP.PoweringMomentBound

end
section
namespace MinUncutGames.Foundations.PCP.PoweringNumeric

theorem min_density_ratio (ε C k t : ℝ)
    (hε : 0 < ε) (hC : 0 < C) (hk : 0 ≤ k)
    (ht : 0 < t) (hkt : k ≤ t) :
    min ε (1 / t) / (C + 1) ≤ ε / (C + k * ε) := by
  have hx : 0 ≤ min ε (1 / t) :=
    le_min hε.le (one_div_nonneg.mpr ht.le)
  have hxt : min ε (1 / t) * t ≤ 1 :=
    (le_div_iff₀ ht).mp (min_le_right ε (1 / t))
  have hkx : k * min ε (1 / t) ≤ 1 := by
    calc
      k * min ε (1 / t) ≤ t * min ε (1 / t) :=
        mul_le_mul_of_nonneg_right hkt hx
      _ ≤ 1 := by simpa only [mul_comm] using hxt
  have hC1 : 0 < C + 1 := by positivity
  have hden : 0 < C + k * ε :=
    add_pos_of_pos_of_nonneg hC (mul_nonneg hk hε.le)
  apply (div_le_div_iff₀ hC1 hden).2
  calc
    min ε (1 / t) * (C + k * ε) =
        C * min ε (1 / t) + ε * (k * min ε (1 / t)) := by ring
    _ ≤ C * ε + ε * 1 :=
      add_le_add
        (mul_le_mul_of_nonneg_left (min_le_left ε (1 / t)) hC.le)
        (mul_le_mul_of_nonneg_left hkx hε.le)
    _ = ε * (C + 1) := by ring

theorem count_moment_ratio_lower (α ε C t : ℝ) (m : ℕ)
    (hm : 0 < m) (hε : 0 < ε) (hC : 0 < C) (ht : 0 < t)
    (hmt : (m : ℝ) - 1 ≤ t) :
    (α ^ 4 * (m : ℝ) / (C + 1)) * min ε (1 / t) ≤
      (α ^ 2 * (m : ℝ) * ε) ^ 2 /
        ((m : ℝ) * ε * (C + ((m : ℝ) - 1) * ε)) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hm)
  have hk : 0 ≤ (m : ℝ) - 1 := sub_nonneg.mpr hm1
  have hden : 0 < C + ((m : ℝ) - 1) * ε :=
    add_pos_of_pos_of_nonneg hC (mul_nonneg hk hε.le)
  have hαm : 0 ≤ α ^ 4 * (m : ℝ) := by positivity
  have hratio := min_density_ratio ε C ((m : ℝ) - 1) t hε hC hk ht hmt
  calc
    (α ^ 4 * (m : ℝ) / (C + 1)) * min ε (1 / t) =
        (α ^ 4 * (m : ℝ)) * (min ε (1 / t) / (C + 1)) := by ring
    _ ≤ (α ^ 4 * (m : ℝ)) * (ε / (C + ((m : ℝ) - 1) * ε)) :=
      mul_le_mul_of_nonneg_left hratio hαm
    _ = (α ^ 2 * (m : ℝ) * ε) ^ 2 /
        ((m : ℝ) * ε * (C + ((m : ℝ) - 1) * ε)) := by
      field_simp [ne_of_gt hm0, ne_of_gt hε, ne_of_gt hden]

end MinUncutGames.Foundations.PCP.PoweringNumeric

end
section
noncomputable section

namespace MinUncutGames.Foundations.PCP.PoweringSoundness

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

end MinUncutGames.Foundations.PCP.PoweringSoundness

end
end
section
namespace MinUncutGames.Foundations.PCP.PoweringGap

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

end MinUncutGames.Foundations.PCP.PoweringGap

end

end OAI
