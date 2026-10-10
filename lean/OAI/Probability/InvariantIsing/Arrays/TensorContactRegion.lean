import OAI.Probability.InvariantIsing.Arrays.TensorObjectiveContinuity

namespace OAI

/-! The genuine compact parameter region for the finite upper comparison.
Field covariance increments are nonnegative and their sum is capped. -/

noncomputable section
open Set
open scoped BigOperators

namespace InvariantIsing

abbrev TensorContactParameter (N m n : ℕ) :=
  ℝ × (Fin (n + 1) → ℝ) × (Fin N → ℝ) × (Fin m → ℝ)

def tensorContactRegion (N m n : ℕ) (H : ℝ) : Set (TensorContactParameter N m n) :=
  Icc (0, (fun _ => 0), (fun _ => 1), (fun _ => 1))
    (1, (fun _ => H), (fun _ => 2), (fun _ => 2)) ∩
      {p | (∑ j, p.2.1 j) ≤ H}

lemma tensorContactRegion_bounds {N m n : ℕ} {H : ℝ}
    {p : TensorContactParameter N m n} (hp : p ∈ tensorContactRegion N m n H) :
    p.1 ∈ Icc (0 : ℝ) 1 ∧ (∀ j, 0 ≤ p.2.1 j) ∧ (∑ j, p.2.1 j) ≤ H ∧
      (∀ j, p.2.2.1 j ∈ Icc (1 : ℝ) 2) ∧ (∀ a, p.2.2.2 a ∈ Icc (1 : ℝ) 2) := by
  exact ⟨⟨hp.1.1.1, hp.1.2.1⟩, hp.1.1.2.1, hp.2,
    fun j => ⟨hp.1.1.2.2.1 j, hp.1.2.2.2.1 j⟩,
    fun a => ⟨hp.1.1.2.2.2 a, hp.1.2.2.2.2 a⟩⟩

lemma tensorContactRegion_mem {N m n : ℕ} {H : ℝ}
    {p : TensorContactParameter N m n} (ht : p.1 ∈ Icc (0 : ℝ) 1)
    (ha : ∀ j, 0 ≤ p.2.1 j) (hcap : (∑ j, p.2.1 j) ≤ H)
    (hu : ∀ j, p.2.2.1 j ∈ Icc (1 : ℝ) 2)
    (hv : ∀ a, p.2.2.2 a ∈ Icc (1 : ℝ) 2) : p ∈ tensorContactRegion N m n H := by
  refine ⟨⟨⟨ht.1, ha, (fun j => (hu j).1), (fun a => (hv a).1)⟩,
    ht.2, ?_, (fun j => (hu j).2), (fun a => (hv a).2)⟩, hcap⟩
  intro j
  exact (Finset.single_le_sum (fun i _ => ha i) (Finset.mem_univ j)).trans hcap

lemma isCompact_tensorContactRegion (N m n : ℕ) (H : ℝ) :
    IsCompact (tensorContactRegion N m n H) :=
  isCompact_Icc.inter_right (isClosed_le (by fun_prop) continuous_const)

lemma tensorContactRegion_nonempty (N m n : ℕ) {H : ℝ} (hH : 0 ≤ H) :
    (tensorContactRegion N m n H).Nonempty := by
  refine ⟨(0, fun _ => 0, fun _ => 3 / 2, fun _ => 3 / 2),
    tensorContactRegion_mem (by norm_num) (fun _ => le_rfl) ?_ ?_ ?_⟩
  · simpa only [Finset.sum_const_zero] using hH
  · intro j; norm_num
  · intro a; norm_num

end InvariantIsing

end

end OAI
