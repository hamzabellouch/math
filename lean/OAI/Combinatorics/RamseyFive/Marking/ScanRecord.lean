import Mathlib
import OAI.Combinatorics.RamseyFive.Marking.ScanChoice

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence
open scoped LinearAlgebra.Projectivization Classical BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def scanRecord (a : ℕ → ℙ K V) (b : ℕ → ℙ K (Dual K V))
    (q : ℝ) (n : ℕ) : Option (ℙ K V × ℙ K (Dual K V)) :=
  if Expensive (scanState a b q n) (a n) (b n) q then some (a n,b n) else none

noncomputable def decodeState (record : ℕ → Option (ℙ K V × ℙ K (Dual K V))) :
    ℕ → ℙ K (Dual K V) → Submodule K (Dual K V)
  | 0 => fun _ => ⊥
  | n+1 => match record n with
    | none => decodeState record n
    | some ab => nextState (decodeState record n) ab.1 ab.2

omit [FiniteDimensional K V] [Fintype (ℙ K V)] in
lemma decode_scanRecord (a : ℕ → ℙ K V) (b : ℕ → ℙ K (Dual K V))
    (q : ℝ) (n : ℕ) : decodeState (scanRecord a b q) n=scanState a b q n := by
  induction n with
  | zero => funext y; exact (state_empty a b y).symm
  | succ n ih =>
    rw [decodeState,scanRecord]
    split_ifs with he
    · simp only [ih]
      exact (scanState_update a b q n he).symm
    · simp only [ih]
      change state a b (scanSet a b q n)=state a b (scanSet a b q (n+1))
      change ¬Expensive (state a b (scanSet a b q n)) (a n) (b n) q at he
      rw [scanSet,ite_eq_right he]

omit [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma decodeState_congr_prefix (record record' : ℕ → Option (ℙ K V × ℙ K (Dual K V)))
    (n : ℕ) (h : ∀ i<n,record i=record' i) : decodeState record n=decodeState record' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [decodeState,decodeState,h n (Nat.lt_succ_self n),ih (fun i hi => h i (Nat.lt_succ_of_lt hi))]

noncomputable def rankMask (a : ℕ → ℙ K V) (b : ℕ → ℙ K (Dual K V))
    (q : ℝ) (n : ℕ) : Fin 5 := ⟨finrank K (scanState a b q n (b n))%5,Nat.mod_lt _ (by decide)⟩

omit [Fintype (ℙ K V)] in
lemma rankMask_val (hdim : finrank K V=5)
    (a : ℕ → ℙ K V) (b : ℕ → ℙ K (Dual K V)) (q : ℝ) (N : ℕ)
    (hF : ∀ i j,i<j → j<N → Incident (a i) (b j) → Incident (a j) (b i))
    {n : ℕ} (hn : n<N) : (rankMask a b q n).val=finrank K (scanState a b q n (b n)) :=
  Nat.mod_eq_of_lt (Nat.lt_succ_iff.mpr (scan_rank hdim a b q N hF hn))

noncomputable def cheapDomain (W : ℙ K (Dual K V) → Submodule K (Dual K V)) (r : Fin 5) :
    Finset (ℙ K V × ℙ K (Dual K V)) :=
  if (levelSet W (chooseLevel W r.val)).Nonempty then
    popularDomain W r.val (chooseLevel W r.val) ∪ poorDomain W r.val (chooseLevel W r.val)
  else ∅

variable [Finite K]

theorem cheapDomain_card (hdim : finrank K V=5)
    (W : ℙ K (Dual K V) → Submodule K (Dual K V)) (r : Fin 5) :
    ((cheapDomain W r).card:ℝ)≤153*(Nat.card K:ℝ)^4 := by
  unfold cheapDomain
  split_ifs with hz
  · have hp:=popularDomain_card hdim W r.val (chooseLevel W r.val)
      (chooseLevel_le W r.val) (by omega) hz
    have hs:=poorDomain_card hdim W r.val (by omega)
    have hu : (((popularDomain W r.val (chooseLevel W r.val) ∪
        poorDomain W r.val (chooseLevel W r.val)).card):ℝ)≤
        (popularDomain W r.val (chooseLevel W r.val)).card+
          (poorDomain W r.val (chooseLevel W r.val)).card := by
      exact_mod_cast Finset.card_union_le _ _
    linarith
  · simp only [Finset.card_empty,Nat.cast_zero]
    positivity

omit [Finite K] in

theorem scan_decoding (hdim : finrank K V=5)
    (a : ℕ → ℙ K V) (b : ℕ → ℙ K (Dual K V)) (N : ℕ)
    (hflag : ∀ n<N,Incident (a n) (b n))
    (hF : ∀ i j,i<j → j<N → Incident (a i) (b j) → Incident (a j) (b i))
    {n : ℕ} (hn : n<N) (hc : scanRecord a b (Nat.card K) n=none) :
    (a n,b n)∈cheapDomain (decodeState (scanRecord a b (Nat.card K)) n)
      (rankMask a b (Nat.card K) n) := by
  have he : ¬Expensive (scanState a b (Nat.card K) n) (a n) (b n) (Nat.card K) := by
    intro he
    simp only [scanRecord,ite_eq_left he] at hc
    contradiction
  rw [decode_scanRecord]
  unfold cheapDomain
  rw [rankMask_val hdim a b (Nat.card K) N hF hn,
    ite_eq_left (chooseLevel_nonempty (scanState a b (Nat.card K) n) (b n))]
  exact Finset.mem_union.mpr (cheap_mem_domains a b N hflag hF hn he)

end SharpRamseyFive.Marking

end OAI
