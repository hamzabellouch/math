import OAI.Analysis.LipschitzHilbert.Phase.AngularAnalyticWeight
import Mathlib.Order.Interval.Finset.Nat

namespace OAI

/-! The actual shifted block endpoints of §8. The first block is allowed
to be shorter. Every transition has one phase tag, and each completed
block contains its distinguished phase exactly at the last transition. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert.ShiftedBlocks

variable {K : ℕ}

def endpoint (σ : Fin K) : ℕ → ℕ
  | 0 => 0
  | j + 1 => 1 + σ.val + j * K

@[simp] theorem endpoint_zero (σ : Fin K) : endpoint σ 0 = 0 := rfl

@[simp] theorem endpoint_succ (σ : Fin K) (j : ℕ) :
    endpoint σ (j + 1) = 1 + σ.val + j * K := rfl

theorem endpoint_strictMono (_hK : 0 < K) (σ : Fin K) : StrictMono (endpoint σ) := by
  apply strictMono_nat_of_lt_succ
  intro j
  cases j with
  | zero => simp
  | succ j => simp only [endpoint_succ, Nat.succ_mul]; omega

def block (σ : Fin K) (j : ℕ) : Finset ℕ :=
  Finset.Ico (endpoint σ j) (endpoint σ (j + 1))

def lastTransition (σ : Fin K) (j : ℕ) : ℕ := endpoint σ (j + 1) - 1

@[simp] theorem lastTransition_eq (σ : Fin K) (j : ℕ) :
    lastTransition σ j = σ.val + j * K := by
  unfold lastTransition
  rw [endpoint_succ]
  omega

theorem lastTransition_succ (σ : Fin K) (j : ℕ) :
    lastTransition σ j + 1 = endpoint σ (j + 1) := by
  rw [lastTransition_eq, endpoint_succ]
  omega

theorem endpoint_first_bounds (σ : Fin K) : 1 ≤ endpoint σ 1 ∧ endpoint σ 1 ≤ K := by
  simp only [endpoint_succ, Nat.zero_mul, Nat.add_zero]
  have hs := σ.isLt
  omega

theorem endpoint_step (σ : Fin K) (j : ℕ) :
    endpoint σ (j + 2) = endpoint σ (j + 1) + K := by
  simp only [show j + 2 = (j + 1) + 1 by omega, endpoint_succ, Nat.add_mul, Nat.one_mul]
  omega

theorem endpoint_width_le (σ : Fin K) (j : ℕ) :
    endpoint σ (j + 1) ≤ endpoint σ j + K := by
  cases j with
  | zero => simpa using (endpoint_first_bounds σ).2
  | succ j => exact le_of_eq (endpoint_step σ j)

theorem block_card_first (σ : Fin K) : (block σ 0).card = 1 + σ.val := by
  simp [block]

theorem block_card_succ (σ : Fin K) (j : ℕ) : (block σ (j + 1)).card = K := by
  rw [block, Nat.card_Ico]
  change endpoint σ (j + 2) - endpoint σ (j + 1) = K
  rw [endpoint_step]
  omega

theorem block_card_le (σ : Fin K) (j : ℕ) : (block σ j).card ≤ K := by
  cases j with
  | zero =>
    rw [block_card_first]
    simpa only [endpoint_succ, Nat.zero_mul, Nat.add_zero] using (endpoint_first_bounds σ).2
  | succ j => exact (block_card_succ σ j).le

theorem lastTransition_mem (hK : 0 < K) (σ : Fin K) (j : ℕ) :
    lastTransition σ j ∈ block σ j := by
  have h := endpoint_strictMono hK σ (Nat.lt_succ_self j)
  change endpoint σ j < endpoint σ (j + 1) at h
  have hl := lastTransition_succ σ j
  exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩

theorem block_nonempty (hK : 0 < K) (σ : Fin K) (j : ℕ) : (block σ j).Nonempty :=
  ⟨lastTransition σ j, lastTransition_mem hK σ j⟩

theorem block_disjoint_of_lt (hK : 0 < K) (σ : Fin K) {j k : ℕ} (hjk : j < k) :
    Disjoint (block σ j) (block σ k) := by
  apply Finset.disjoint_left.mpr
  intro i hi hk
  have hle := (endpoint_strictMono hK σ).monotone (Nat.succ_le_of_lt hjk)
  change endpoint σ (j + 1) ≤ endpoint σ k at hle
  have hi' := Finset.mem_Ico.mp hi
  have hk' := Finset.mem_Ico.mp hk
  omega

theorem blocks_pairwiseDisjoint (hK : 0 < K) (σ : Fin K) :
    Pairwise (fun j k => Disjoint (block σ j) (block σ k)) := by
  intro j k hjk
  rcases lt_or_gt_of_ne hjk with h | h
  · exact block_disjoint_of_lt hK σ h
  · exact (block_disjoint_of_lt hK σ h).symm

/-- The phase coordinate of a transition in the shared analytic family. -/
def tag (hK : 0 < K) (i : ℕ) : Fin K := ⟨i % K, Nat.mod_lt i hK⟩

@[simp] theorem tag_val (hK : 0 < K) (i : ℕ) : (tag hK i).val = i % K := rfl

theorem tag_lastTransition (hK : 0 < K) (σ : Fin K) (j : ℕ) :
    tag hK (lastTransition σ j) = σ := by
  apply Fin.ext
  simp [tag, lastTransition_eq, Nat.add_mod, Nat.mod_eq_of_lt σ.isLt]

theorem endpoint_tag_div (hK : 0 < K) (i : ℕ) :
    endpoint (tag hK i) (i / K + 1) = i + 1 := by
  rw [endpoint_succ, tag_val]
  have h := Nat.mod_add_div i K
  nlinarith

/-- The block ending at transition i starts at the source's shared
boundary ancestor i+1-K, with truncated subtraction at the root. -/
theorem endpoint_eq_last_sub (σ : Fin K) (j : ℕ) :
    endpoint σ j = lastTransition σ j + 1 - K := by
  cases j with
  | zero =>
    simp only [endpoint_zero, lastTransition_eq, Nat.zero_mul, Nat.add_zero]
    have hs := σ.isLt
    omega
  | succ j =>
    simp only [endpoint_succ, lastTransition_eq, Nat.succ_mul]
    omega

theorem block_start_tag_div (hK : 0 < K) (i : ℕ) :
    endpoint (tag hK i) (i / K) = i + 1 - K := by
  rw [endpoint_eq_last_sub]
  have h := endpoint_tag_div hK i
  have hs := lastTransition_succ (tag hK i) (i / K)
  omega

theorem is_last_iff_tag (hK : 0 < K) (σ : Fin K) (i : ℕ) :
    (∃ j, i = lastTransition σ j) ↔ tag hK i = σ := by
  constructor
  · rintro ⟨j, rfl⟩
    exact tag_lastTransition hK σ j
  · intro htag
    refine ⟨i / K, ?_⟩
    have h := endpoint_tag_div hK i
    rw [htag] at h
    have hs := lastTransition_succ σ (i / K)
    omega

theorem tag_injective_on_block (hK : 0 < K) (σ : Fin K) (j : ℕ) :
    Set.InjOn (tag hK) (block σ j) := by
  intro i hi k hk heq
  have hwidth := endpoint_width_le σ j
  have him := Finset.mem_Ico.mp hi
  have hkm := Finset.mem_Ico.mp hk
  apply Nat.mod_injOn_Ico (endpoint σ j) K
    (Finset.mem_Ico.mpr ⟨him.1, him.2.trans_le hwidth⟩)
    (Finset.mem_Ico.mpr ⟨hkm.1, hkm.2.trans_le hwidth⟩)
  exact congrArg Fin.val heq

theorem tag_eq_shift_iff (hK : 0 < K) (σ : Fin K) (j i : ℕ) (hi : i ∈ block σ j) :
    tag hK i = σ ↔ i = lastTransition σ j := by
  constructor
  · intro heq
    exact tag_injective_on_block hK σ j hi (lastTransition_mem hK σ j)
      (heq.trans (tag_lastTransition hK σ j).symm)
  · rintro rfl
    exact tag_lastTransition hK σ j

theorem prod_block_eq_last {M : Type*} [CommMonoid M] (hK : 0 < K) (σ : Fin K)
    (j : ℕ) (f : ℕ → M) (h : ∀ i ∈ block σ j, tag hK i ≠ σ → f i = 1) :
    (∏ i ∈ block σ j, f i) = f (lastTransition σ j) := by
  apply Finset.prod_eq_single_of_mem (lastTransition σ j) (lastTransition_mem hK σ j)
  intro i hi hne
  exact h i hi (fun htag => hne ((tag_eq_shift_iff hK σ j i hi).mp htag))

theorem packetPathProduct_norm_eq_last (hK : 0 < K) (σ : Fin K) (j : ℕ)
    (g : AngularGrid) (transition : ℕ → ℤ → ℂ) (slope : ℝ)
    (h : ∀ i ∈ block σ j, tag hK i ≠ σ →
      ‖transition i (g.index (i + 1) slope)‖ = 1) :
    ‖g.packetPathProduct transition (endpoint σ j) (endpoint σ (j + 1)) slope‖ =
      ‖transition (lastTransition σ j) (g.index (endpoint σ (j + 1)) slope)‖ := by
  rw [AngularGrid.packetPathProduct, norm_prod]
  have hp := prod_block_eq_last hK σ j
    (fun i => ‖transition i (g.index (i + 1) slope)‖) h
  simpa only [block, lastTransition_succ] using hp

/-- At a vertex parameter, the modulus of a complete block product is
the modulus contributed by its final transition alone. Other phase
coordinates may still have arbitrary imaginary parts. -/
theorem analytic_block_norm (hK : 0 < K) (σ : Fin K) (j : ℕ)
    (g : AngularGrid) (mass boundary : ℕ → ℤ → ℝ) (phase : Fin K → ℂ) (slope : ℝ)
    (hphase : ∀ τ, τ ≠ σ → (phase τ).re = 0)
    (hm : ∀ i ∈ block σ j, 0 < mass (i + 1) (g.index (i + 1) slope))
    (hb : ∀ i ∈ block σ j, 0 < boundary i (g.index (i + 1) slope)) :
    ‖g.packetPathProduct (AngularGrid.analyticTransition mass boundary (fun i => phase (tag hK i)))
      (endpoint σ j) (endpoint σ (j + 1)) slope‖ =
      (mass (endpoint σ (j + 1)) (g.index (endpoint σ (j + 1)) slope) /
        boundary (lastTransition σ j) (g.index (endpoint σ (j + 1)) slope)) ^ (phase σ).re := by
  rw [packetPathProduct_norm_eq_last hK σ j g _ slope]
  · have hlast := lastTransition_mem hK σ j
    have hnorm := AngularGrid.analyticTransition_norm mass boundary
      (fun i => phase (tag hK i)) (lastTransition σ j)
      (g.index (lastTransition σ j + 1) slope) (hm _ hlast) (hb _ hlast)
    simpa only [lastTransition_succ, tag_lastTransition] using hnorm
  · intro i hi htag
    rw [AngularGrid.analyticTransition_norm mass boundary (fun i => phase (tag hK i))
      i _ (hm i hi) (hb i hi), hphase _ htag, Real.rpow_zero]

end LipschitzHilbert.ShiftedBlocks

end

end OAI
