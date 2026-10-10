import Mathlib
import OAI.Combinatorics.IndependentSets.Expansion.Profiles
import OAI.Combinatorics.IndependentSets.Expansion.PoweringLazy
import OAI.Combinatorics.IndependentSets.Expansion.PoweringReturn

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.PoweringWitness

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

end IndependentSetsGames.Foundations.PCP.PoweringWitness
namespace IndependentSetsGames.Foundations.PCP.PoweringMomentBound

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

end IndependentSetsGames.Foundations.PCP.PoweringMomentBound

end OAI
