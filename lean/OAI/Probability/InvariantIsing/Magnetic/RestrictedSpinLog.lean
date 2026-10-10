import OAI.Probability.InvariantIsing.Core.Model

namespace OAI

/-! Restricted spin sums retain the original cube mass. A deterministic
map of slices costs its energy error and the logarithm of its largest fiber. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

def restrictedSpinLog {N : ℕ} (S : Finset (Spin N)) (H : Spin N → ℝ) : ℝ :=
  Real.log (∑ σ ∈ S, Real.exp (H σ)) - N * Real.log 2

lemma restrictedSpinLog_univ {N : ℕ} (H : Spin N → ℝ) :
    restrictedSpinLog Finset.univ H = logPartition H := by
  rw [restrictedSpinLog, logPartition_eq, log_card_spin]

lemma restrictedSpinLog_add_const {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (H : Spin N → ℝ) (c : ℝ) :
    restrictedSpinLog S (fun σ => H σ + c) = restrictedSpinLog S H + c := by
  have hp : 0 < ∑ σ ∈ S, Real.exp (H σ) :=
    Finset.sum_pos (fun σ _ => Real.exp_pos (H σ)) hS
  simp_rw [restrictedSpinLog, Real.exp_add]
  rw [← Finset.sum_mul, Real.log_mul hp.ne' (Real.exp_ne_zero c), Real.log_exp]
  ring

lemma restrictedSpinLog_mono {N : ℕ} {S T : Finset (Spin N)} (hS : S.Nonempty)
    (hST : S ⊆ T) {H K : Spin N → ℝ} (hHK : ∀ σ ∈ S, H σ ≤ K σ) :
    restrictedSpinLog S H ≤ restrictedSpinLog T K := by
  apply sub_le_sub_right
  apply Real.log_le_log (Finset.sum_pos (fun σ _ => Real.exp_pos (H σ)) hS)
  exact (Finset.sum_le_sum (fun σ hσ => Real.exp_le_exp.mpr (hHK σ hσ))).trans
    (Finset.sum_le_sum_of_subset_of_nonneg hST (fun σ _ _ => (Real.exp_pos (K σ)).le))

lemma restrictedSpinLog_le_full {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (H : Spin N → ℝ) : restrictedSpinLog S H ≤ logPartition H := by
  rw [← restrictedSpinLog_univ]
  exact restrictedSpinLog_mono hS (Finset.subset_univ S) (fun _ _ => le_rfl)

lemma sum_exp_le_of_fiber_bound {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (S : Finset X) (T : Finset Y) (f : X → Y) (H : X → ℝ) (K : Y → ℝ)
    (c B : ℝ) (hf : ∀ x ∈ S, f x ∈ T)
    (hE : ∀ x ∈ S, H x ≤ K (f x) + c)
    (hB : ∀ y ∈ T, ((S.filter fun x => f x = y).card : ℝ) ≤ B) :
    ∑ x ∈ S, Real.exp (H x) ≤ Real.exp c * B * ∑ y ∈ T, Real.exp (K y) := by
  rw [← Finset.sum_fiberwise_of_maps_to hf, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y hy
  calc
    _ ≤ ∑ _x ∈ S.filter (fun x => f x = y), Real.exp (K y + c) := by
      apply Finset.sum_le_sum
      intro x hx
      obtain ⟨hxS, hxy⟩ := Finset.mem_filter.mp hx
      apply Real.exp_le_exp.mpr
      simpa only [hxy] using hE x hxS
    _ = ((S.filter fun x => f x = y).card : ℝ) * Real.exp (K y + c) := by
      simp
    _ ≤ B * Real.exp (K y + c) :=
      mul_le_mul_of_nonneg_right (hB y hy) (Real.exp_pos _).le
    _ = Real.exp c * B * Real.exp (K y) := by rw [Real.exp_add]; ring

lemma restrictedSpinLog_le_of_map {N : ℕ} (S T : Finset (Spin N))
    (hS : S.Nonempty) (hT : T.Nonempty) (f : Spin N → Spin N)
    (H K : Spin N → ℝ) (c B : ℝ) (hB0 : 0 < B)
    (hf : ∀ σ ∈ S, f σ ∈ T) (hE : ∀ σ ∈ S, H σ ≤ K (f σ) + c)
    (hB : ∀ τ ∈ T, ((S.filter fun σ => f σ = τ).card : ℝ) ≤ B) :
    restrictedSpinLog S H ≤ restrictedSpinLog T K + c + Real.log B := by
  have h := Real.log_le_log (Finset.sum_pos (fun σ _ => Real.exp_pos (H σ)) hS)
    (sum_exp_le_of_fiber_bound S T f H K c B hf hE hB)
  have hp : 0 < ∑ τ ∈ T, Real.exp (K τ) :=
    Finset.sum_pos (fun τ _ => Real.exp_pos (K τ)) hT
  rw [Real.log_mul (mul_pos (Real.exp_pos c) hB0).ne' hp.ne',
    Real.log_mul (Real.exp_ne_zero c) hB0.ne', Real.log_exp] at h
  unfold restrictedSpinLog
  linarith

end InvariantIsing

end

end OAI
