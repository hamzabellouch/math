import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Set.Pairwise.Basic

namespace OAI

namespace FiniteFactor
open Finset

/-- Finite greedy packing, with the precise loss supplied by forbidden neighbors. -/
theorem finite_greedy_packing {α : Type*} [DecidableEq α] (bad : α → α → Prop)
    [DecidableRel bad] (symm : ∀ a b, bad a b → bad b a)
    (refl : ∀ a, bad a a) (S : Finset α) (D : ℕ)
    (bound : ∀ a ∈ S, (S.filter (bad a)).card ≤ D) :
    ∃ N ⊆ S, (N : Set α).Pairwise (fun a b => ¬bad a b) ∧ S.card ≤ D*N.card := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases hs : S = ∅
    · subst S; exact ⟨∅, by simp, by simp, by simp⟩
    obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    let T := S.filter (fun b => ¬bad a b)
    have hTa : a ∉ T := by simp [T, refl]
    have hTS : T ⊂ S := Finset.ssubset_iff_subset_ne.mpr
      ⟨filter_subset _ _, fun h => hTa (h.symm ▸ ha)⟩
    obtain ⟨N,hNT,hN,hcard⟩ := ih T hTS (fun b hb =>
      (card_le_card (filter_subset_filter _ (filter_subset _ _))).trans (bound b (mem_of_mem_filter b hb)))
    have haN : a ∉ N := fun h => hTa (hNT h)
    refine ⟨insert a N, insert_subset ha (hNT.trans (filter_subset _ _)), ?_, ?_⟩
    · rw [coe_insert, Set.pairwise_insert_of_notMem haN]
      refine ⟨hN, ?_⟩
      intro b hb
      constructor
      · exact (mem_filter.mp (hNT hb)).2
      · intro h; exact (mem_filter.mp (hNT hb)).2 (symm b a h)
    · have hsplit : (S.filter (bad a)).card + T.card = S.card := by
        exact card_filter_add_card_filter_not (s := S) (bad a)
      rw [card_insert_of_notMem haN]
      have := bound a ha
      rw [Nat.mul_add, Nat.mul_one]
      omega

/-- A fixed nonzero second frequency excludes at most 2R+1 integers. -/
theorem forbidden_frequency_card (S : Finset ℤ) (v v' n : ℤ) (R : ℕ) (hv' : v' ≠ 0) :
    (S.filter (fun n' => |v*n+v'*n'| ≤ (R : ℤ))).card ≤ 2*R+1 := by
  have h := card_le_card_of_injOn (fun n' : ℤ => v*n+v'*n')
    (s := S.filter (fun n' => |v*n+v'*n'| ≤ (R : ℤ)))
    (t := Finset.Icc (-(R : ℤ)) (R : ℤ))
    (fun n' hn' => Finset.mem_Icc.mpr (abs_le.mp (mem_filter.mp hn').2))
    (fun a _ b _ he => mul_left_cancel₀ hv' (add_left_cancel he))
  have hc : (Finset.Icc (-(R : ℤ)) (R : ℤ)).card = 2*R+1 := by
    rw [Int.card_Icc]
    omega
  exact h.trans_eq hc

/-- Failure of the full symmetric bounded-frequency separation condition. -/
def SamplingConflict (H R : ℕ) (n n' : ℤ) : Prop :=
  ∃ v ∈ Finset.Icc (-(H : ℤ)) (H : ℤ),
    ∃ v' ∈ Finset.Icc (-(H : ℤ)) (H : ℤ),
      (v ≠ 0 ∨ v' ≠ 0) ∧ |v*n+v'*n'| ≤ (R : ℤ)

instance (H R : ℕ) : DecidableRel (SamplingConflict H R) := fun _ _ =>
  inferInstanceAs (Decidable (∃ v ∈ Finset.Icc (-(H : ℤ)) (H : ℤ),
    ∃ v' ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), _))

theorem samplingConflict_symm (H R : ℕ) (n n' : ℤ) :
    SamplingConflict H R n n' → SamplingConflict H R n' n := by
  rintro ⟨v,hv,v',hv',hne,hb⟩
  exact ⟨v',hv',v,hv,hne.symm,by simpa [add_comm] using hb⟩

theorem samplingConflict_refl (H R : ℕ) (hH : 1 ≤ H) (n : ℤ) :
    SamplingConflict H R n n := by
  refine ⟨1, mem_Icc.mpr ?_, -1, mem_Icc.mpr ?_, Or.inl (by omega), ?_⟩
  · constructor <;> omega
  · constructor <;> omega
  · simp

/-- Total forbidden-neighbor count, with no unspecified asymptotic constant. -/
theorem samplingConflict_card (H R : ℕ) (S : Finset ℤ) (n : ℤ) (hn : (R : ℤ) < n) :
    (S.filter (SamplingConflict H R n)).card ≤ (2*H+1)^2*(2*R+1) := by
  let F := (Finset.Icc (-(H : ℤ)) (H : ℤ)).product
    ((Finset.Icc (-(H : ℤ)) (H : ℤ)).filter (fun v => v ≠ 0))
  let B := fun p : ℤ × ℤ => S.filter (fun n' => |p.1*n+p.2*n'| ≤ (R : ℤ))
  have hsub : S.filter (SamplingConflict H R n) ⊆ F.biUnion B := by
    intro n' hn'
    obtain ⟨hs,v,hv,v',hv',hne,hb⟩ := mem_filter.mp hn'
    have hv'0 : v' ≠ 0 := by
      intro he
      subst v'
      have hv0 := hne.resolve_right (by simp)
      have hv1 : 1 ≤ |v| := by have := abs_pos.mpr hv0; omega
      have hn0 : 0 ≤ n := by omega
      simp only [zero_mul, add_zero, abs_mul, abs_of_nonneg hn0] at hb
      nlinarith
    exact mem_biUnion.mpr ⟨(v,v'), mem_product.mpr ⟨hv,mem_filter.mpr ⟨hv',hv'0⟩⟩,
      mem_filter.mpr ⟨hs,hb⟩⟩
  have hF : F.card ≤ (2*H+1)^2 := by
    have hc : (Finset.Icc (-(H : ℤ)) (H : ℤ)).card = 2*H+1 := by
      rw [Int.card_Icc]; omega
    dsimp [F]
    rw [card_product]
    calc
      _ ≤ (Finset.Icc (-(H : ℤ)) (H : ℤ)).card ^ 2 := by
        rw [pow_two]
        exact Nat.mul_le_mul_left _ (card_filter_le _ _)
      _ = _ := by rw [hc]
  calc
    _ ≤ (F.biUnion B).card := card_le_card hsub
    _ ≤ ∑ p ∈ F, (B p).card := card_biUnion_le
    _ ≤ ∑ _p ∈ F, (2*R+1) := sum_le_sum fun p hp =>
      forbidden_frequency_card S p.1 p.2 n R (mem_filter.mp (mem_product.mp hp).2).2
    _ = F.card*(2*R+1) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ hF

/-- Deterministic selection from any positive integer interval above R. -/
theorem exists_sampling_separated (H R : ℕ) (hH : 1 ≤ H) (S : Finset ℤ)
    (hS : ∀ n ∈ S, (R : ℤ) < n) :
    ∃ N ⊆ S, (N : Set ℤ).Pairwise (fun n n' => ¬SamplingConflict H R n n') ∧
      S.card ≤ ((2*H+1)^2*(2*R+1))*N.card :=
  finite_greedy_packing (SamplingConflict H R) (samplingConflict_symm H R)
    (samplingConflict_refl H R hH) S _ (fun n hn => samplingConflict_card H R S n (hS n hn))

end FiniteFactor

end OAI
