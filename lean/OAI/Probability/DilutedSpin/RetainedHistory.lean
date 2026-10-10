import OAI.Probability.DilutedSpin.TreeMarkLaw

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
noncomputable local instance retainedHistoryPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {Ω : Type} [Fintype Ω]

/-- The actual signed history sum with a retained test. Each fresh branch
carries its probability kernels, and every further extension transports ALL
retained variables with oldSample. Old-leaf choices introduce no new variable. -/
noncomputable def referenceHistoryExpectation {n : ℕ} (T : PrescribedTree n)
    (m : Fin (n+1) → ℝ) (K : KernelTower Ω n) :
    {p : ℕ} → {s : Fin (p+1) → Leaf T} → ReferencePlan T s →
      (S : PrescribedTree n) → (Fin (p+1) → Leaf S) → (Sample Ω S → ℝ) → ℝ
  | _, _, .nil, S, _, H => (sampleLaw S K).expect H
  | _, s, .cons b _ _ _ next, S, r, H =>
      (∑ x : Leaf S, if labeledOldMatch S T r s b x then
        referenceHistoryExpectation T m K next S (Fin.cons x r) H else 0) +
      (∑ v : Internal S, if labeledFreshMatch S T r s b v then
        gamma S m v * referenceHistoryExpectation T m K next (grow S v)
          (Fin.cons (newLeaf S v) (oldLeaf S v ∘ r))
          (fun x => H (oldSample S v x)) else 0)

/-- Complete joint-marginal normalization for any retained old test (not just
constant tests). The history is combinatorial, never a condition on values. -/
theorem reference_history_expectation {n p : ℕ} (T : PrescribedTree n)
    (m : Fin (n+1) → ℝ) (hend : m (Fin.last n) = 1) (K : KernelTower Ω n)
    {s : Fin (p+1) → Leaf T} (P : ReferencePlan T s) (S : PrescribedTree n)
    (r : Fin (p+1) → Leaf S)
    (hsplit : ∀ i j, splitDepth S (r i) (r j) = splitDepth T (s i) (s j))
    (H : Sample Ω S → ℝ) :
    referenceHistoryExpectation T m K P S r H =
      referencePlanNormalizer T m P * (sampleLaw S K).expect H := by
  induction P generalizing S with
  | nil => simp only [referenceHistoryExpectation,referencePlanNormalizer,one_mul]
  | @cons p s b a hne hmax next ih =>
    dsimp only [referenceHistoryExpectation,referencePlanNormalizer]
    have ho (x : Leaf S) :
        (if labeledOldMatch S T r s b x then
          referenceHistoryExpectation T m K next S (Fin.cons x r) H else 0) =
        (if labeledOldMatch S T r s b x then (1:ℝ) else 0) *
          (referencePlanNormalizer T m next * (sampleLaw S K).expect H) := by
      split_ifs with hx
      · rw [ih S (Fin.cons x r) (labeledOldMatch_cons S T r s b x hsplit hx),one_mul]
      · simp
    have hf (v : Internal S) :
        (if labeledFreshMatch S T r s b v then gamma S m v *
          referenceHistoryExpectation T m K next (grow S v)
            (Fin.cons (newLeaf S v) (oldLeaf S v ∘ r))
            (fun x => H (oldSample S v x)) else 0) =
        (if labeledFreshMatch S T r s b v then gamma S m v else 0) *
          (referencePlanNormalizer T m next * (sampleLaw S K).expect H) := by
      split_ifs with hv
      · rw [ih (grow S v) (Fin.cons (newLeaf S v) (oldLeaf S v ∘ r))
          (labeledFreshMatch_cons S T r s b v hsplit hv),grow_projectivity]
      · simp
    simp_rw [ho,hf]
    rw [← Finset.sum_mul,← Finset.sum_mul,← add_mul,
      labeled_choice_total S T r s b a hsplit (hne a) hmax m hend,mul_assoc]

/-- The first new path is retained along with every old path; all later paths
are sampled and summed exactly as in the reference-history expansion. -/
noncomputable def firstReferenceExpectation {n p : ℕ} (T : PrescribedTree n)
    (m : Fin (n+1) → ℝ) (K : KernelTower Ω n) {s : Fin (p+1) → Leaf T}
    (b : Leaf T) (next : ReferencePlan T (Fin.cons b s))
    (S : PrescribedTree n) (r : Fin (p+1) → Leaf S)
    (H : Sample Ω S → FinitePath Ω n → ℝ) : ℝ :=
  (∑ a : Leaf S, if labeledOldMatch S T r s b a then
    referenceHistoryExpectation T m K next S (Fin.cons a r)
      (fun x => H x (pathAt S a x)) else 0) +
  (∑ v : Internal S, if labeledFreshMatch S T r s b v then
    gamma S m v * referenceHistoryExpectation T m K next (grow S v)
      (Fin.cons (newLeaf S v) (oldLeaf S v ∘ r))
      (fun x => H (oldSample S v x) (newPath S v x)) else 0)

/-- The genuine old-test/first-path marginal factors from every later signed
reference sum. In particular this applies to any first-path prefix observable. -/
theorem first_reference_expectation {n p : ℕ} (T : PrescribedTree n)
    (m : Fin (n+1) → ℝ) (hend : m (Fin.last n) = 1) (K : KernelTower Ω n)
    {s : Fin (p+1) → Leaf T} (b : Leaf T) (next : ReferencePlan T (Fin.cons b s))
    (S : PrescribedTree n) (r : Fin (p+1) → Leaf S)
    (hsplit : ∀ i j, splitDepth S (r i) (r j) = splitDepth T (s i) (s j))
    (H : Sample Ω S → FinitePath Ω n → ℝ) :
    firstReferenceExpectation T m K b next S r H =
      referencePlanNormalizer T m next *
        ((∑ a : Leaf S, if labeledOldMatch S T r s b a then
          (sampleLaw S K).expect (fun x => H x (pathAt S a x)) else 0) +
        (∑ v : Internal S, if labeledFreshMatch S T r s b v then
          gamma S m v * (sampleLaw (grow S v) K).expect
            (fun x => H (oldSample S v x) (newPath S v x)) else 0)) := by
  classical
  unfold firstReferenceExpectation
  rw [mul_add,Finset.mul_sum,Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro a _
    split_ifs with ha
    · exact reference_history_expectation T m hend K next S (Fin.cons a r)
        (labeledOldMatch_cons S T r s b a hsplit ha) _
    · exact (mul_zero _).symm
  · apply Finset.sum_congr rfl
    intro v _
    split_ifs with hv
    · rw [reference_history_expectation T m hend K next (grow S v)
        (Fin.cons (newLeaf S v) (oldLeaf S v ∘ r))
        (labeledFreshMatch_cons S T r s b v hsplit hv)]
      ring
    · exact (mul_zero _).symm

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
