import OAI.MeasureTheory.Falconer.Recursion.Ledger
import Mathlib.Data.Finset.Max

namespace OAI

namespace PlanarFalconer

noncomputable def finiteArgmin (S : Finset ℕ) (f : ℕ → ℝ) : ℕ :=
  if h : S.Nonempty then Classical.choose (Finset.exists_mem_eq_inf' h f) else 0

theorem finiteArgmin_spec {S : Finset ℕ} (hS : S.Nonempty) (f : ℕ → ℝ) :
    finiteArgmin S f ∈ S ∧ ∀ j ∈ S, f (finiteArgmin S f) ≤ f j := by
  rw [finiteArgmin,dite_eq_left hS]
  have hs := Classical.choose_spec (Finset.exists_mem_eq_inf' hS f)
  refine ⟨hs.1,?_⟩
  intro j hj
  rw [← hs.2]
  exact Finset.inf'_le f hj

def policyBlock (N q k : ℕ) : Finset ℕ := Finset.Ico (k*q) (min ((k+1)*q) (N+1))

noncomputable def policyRepresentative (A : ℕ → ℝ) (N q k : ℕ) : ℕ :=
  finiteArgmin (policyBlock N q k) A

def policyBlocks (N q a t : ℕ) : Finset ℕ :=
  (Finset.range (N/q+1)).filter fun k => a+q ≤ k*q ∧ (k+1)*q ≤ t-q+1

noncomputable def policyKey (A : ℕ → ℝ) (N q a t : ℕ) : ℕ :=
  finiteArgmin (policyBlocks N q a t) (fun k => A (policyRepresentative A N q k))

noncomputable def policyDepth (A : ℕ → ℝ) (N q a t : ℕ) : ℕ :=
  policyRepresentative A N q (policyKey A N q a t)

theorem policyBlock_nonempty {N q k : ℕ} (hq : 0 < q) (hk : k*q ≤ N) :
    (policyBlock N q k).Nonempty := by
  apply Finset.nonempty_Ico.mpr
  have he : (k+1)*q = k*q+q := by ring
  omega

theorem policyRepresentative_spec (A : ℕ → ℝ) {N q k : ℕ} (hq : 0 < q) (hk : k*q ≤ N) :
    k*q ≤ policyRepresentative A N q k ∧ policyRepresentative A N q k < (k+1)*q ∧
      policyRepresentative A N q k ≤ N ∧
      ∀ n ∈ policyBlock N q k, A (policyRepresentative A N q k) ≤ A n := by
  have hh := finiteArgmin_spec (policyBlock_nonempty hq hk) A
  have hm := Finset.mem_Ico.mp hh.1
  refine ⟨hm.1,lt_of_lt_of_le hm.2 (min_le_left _ _),?_,hh.2⟩
  exact Nat.le_of_lt_succ (lt_of_lt_of_le hm.2 (min_le_right _ _))

theorem policyBlocks_mem {N q a t k : ℕ} (h : k ∈ policyBlocks N q a t) :
    k ≤ N/q ∧ a+q ≤ k*q ∧ (k+1)*q ≤ t-q+1 := by
  obtain ⟨hk,hl,hr⟩ := Finset.mem_filter.mp h
  exact ⟨Nat.le_of_lt_succ (Finset.mem_range.mp hk),hl,hr⟩

theorem policy_left_block {N q a t : ℕ} (hq : 0 < q) (ht : t ≤ N) (hwide : a+100*q < t) :
    ∃ k ∈ policyBlocks N q a t, k*q ≤ a+2*q := by
  let k := (a+2*q-1)/q
  have hlo := Nat.div_mul_le_self (a+2*q-1) q
  have hhi := Nat.lt_mul_div_succ (a+2*q-1) hq
  have hprod : (k+1)*q = k*q+q := by ring
  change k*q ≤ a+2*q-1 at hlo
  have hceil : a+q ≤ k*q := by
    rw [Nat.mul_comm q] at hhi
    change a+2*q-1 < (k+1)*q at hhi
    omega
  have hend : (k+1)*q ≤ t-q+1 := by omega
  have hkn : k*q ≤ N := by omega
  refine ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_,hceil,hend⟩,by omega⟩
  exact Nat.lt_succ_of_le ((Nat.le_div_iff_mul_le hq).mpr hkn)

theorem policy_right_block {N q a t : ℕ} (hq : 0 < q) (ht : t ≤ N) (hwide : a+100*q < t) :
    ∃ k ∈ policyBlocks N q a t, t-2*q ≤ (k+1)*q-1 := by
  let j := (t-q+1)/q
  have hj : 0 < j := Nat.div_pos (by omega) hq
  have hlo := Nat.div_mul_le_self (t-q+1) q
  have hhi := Nat.lt_mul_div_succ (t-q+1) hq
  change j*q ≤ t-q+1 at hlo
  rw [Nat.mul_comm q] at hhi
  change t-q+1 < (j+1)*q at hhi
  have hmul : (j+1)*q = j*q+q := by ring
  have he : (j-1+1)*q = j*q := by rw [Nat.sub_add_cancel hj]
  have he' : (j-1)*q+q = j*q := by simpa only [Nat.add_mul,one_mul] using he
  have hleft : a+q ≤ (j-1)*q := by omega
  have hkn : (j-1)*q ≤ N := by omega
  refine ⟨j-1,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_,hleft,by omega⟩,by omega⟩
  exact Nat.lt_succ_of_le ((Nat.le_div_iff_mul_le hq).mpr hkn)

theorem policyBlocks_nonempty {N q a t : ℕ} (hq : 0 < q) (ht : t ≤ N) (hwide : a+100*q < t) :
    (policyBlocks N q a t).Nonempty := by
  obtain ⟨k,hk,_⟩ := policy_left_block hq ht hwide
  exact ⟨k,hk⟩

theorem policyDepth_minimizes (A : ℕ → ℝ) {N q a t n : ℕ} (hq : 0 < q)
    (hne : (policyBlocks N q a t).Nonempty) (hn : n ≤ N)
    (hblock : n/q ∈ policyBlocks N q a t) : A (policyDepth A N q a t) ≤ A n := by
  have hkey := finiteArgmin_spec hne (fun k => A (policyRepresentative A N q k))
  have hcell : n ∈ policyBlock N q (n/q) := by
    apply Finset.mem_Ico.mpr
    have hlo := Nat.div_mul_le_self n q
    have hhi := Nat.lt_mul_div_succ n hq
    rw [Nat.mul_comm q] at hhi
    exact ⟨hlo,lt_min hhi (Nat.lt_succ_of_le hn)⟩
  exact (hkey.2 _ hblock).trans
    ((policyRepresentative_spec A hq ((Nat.div_mul_le_self n q).trans hn)).2.2.2 n hcell)

theorem policyDepth_interior (A : ℕ → ℝ) {N q a t : ℕ} (hq : 0 < q)
    (hne : (policyBlocks N q a t).Nonempty) :
    a+q ≤ policyDepth A N q a t ∧ policyDepth A N q a t ≤ t-q := by
  have hkey := (finiteArgmin_spec hne (fun k => A (policyRepresentative A N q k))).1
  have hb := policyBlocks_mem hkey
  have hrep := policyRepresentative_spec A hq ((Nat.le_div_iff_mul_le hq).mp hb.1)
  exact ⟨hb.2.1.trans hrep.1,Nat.le_of_lt_succ (hrep.2.1.trans_le hb.2.2)⟩

theorem policy_move_length (A : ℕ → ℝ) {N q a t : ℕ} (hq : 0 < q)
    (hne : (policyBlocks N q a t).Nonempty) :
    let p := policyDepth A N q a t
    let l := min (p-a) (t-p)
    q ≤ l ∧ a ≤ p-l ∧ p+l ≤ t := by
  have hh := policyDepth_interior A hq hne
  dsimp only
  omega

end PlanarFalconer

end OAI
