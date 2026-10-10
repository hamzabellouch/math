import OAI.NumberTheory.JointDickman.Arithmetic.FormRectangleSieve

namespace OAI

/-! # The weighted affine-line rectangle sieve -/

namespace JointDickman

open Finset

noncomputable def affineFormWeight {k p : ℕ} (a b c : Fin k → ZMod p)
    (θ : Fin k → ℝ) (r s : ZMod p) : ℝ :=
  ∏ i, if a i * r + b i * s = c i then θ i else 1

/-- The manuscript's rectangle sieve for proper affine forms, with the
exact local mean and an explicit polynomial remainder. -/
theorem affine_rectangle_sieve
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {k : ℕ} (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset ℕ)
      (a b c : ∀ p : P, Fin k → ZMod p.val) (θ : P → Fin k → ℝ)
      (u v w x Z : ℕ), u ≤ v → w ≤ x → 2 ≤ Z →
      (∀ p ∈ P, p.Prime ∧ p ≤ Z ∧ 2 * k ≤ p) →
      (∀ p i, a p i ≠ 0 ∨ b p i ≠ 0) →
      (∀ p i, 0 ≤ θ p i ∧ θ p i ≤ 1) →
      (∑ r ∈ Ico u v, ∑ s ∈ Ico w x, ∏ p : P,
        affineFormWeight (a p) (b p) (c p) (θ p) (r : ZMod p.val) (s : ZMod p.val)) ≤
      C * ((v : ℝ) - u) * ((x : ℝ) - w) *
        (∏ p : P, (∑ r ∈ range p.val, ∑ s ∈ range p.val,
          affineFormWeight (a p) (b p) (c p) (θ p)
            (r : ZMod p.val) (s : ZMod p.val)) / (p.val : ℝ) ^ 2) +
      2 * (((v : ℝ) - u) + ((x : ℝ) - w) + 2 * Z) * (Z + 1 : ℝ) * (Z : ℝ) ^ k := by
  obtain ⟨C, hC, hbound⟩ := form_rectangle_sieve hFord hM hk
  refine ⟨C, hC, ?_⟩
  intro P a b c θ u v w x Z huv hwx hZ hP hproper hθ
  classical
  let : ∀ p : P, NeZero p.val := fun p => ⟨(hP p.val p.property).1.ne_zero⟩
  let F := fun (p : P) (i : Fin k) => affineResidueLine (a p i) (b p i) (c p i)
  have hF (p : P) (i : Fin k) : (F p i).card ≤ p.val :=
    affineResidueLine_card_le (hP p.val p.property).1 _ _ _ (hproper p i)
  have heq (p : P) (r s : ZMod p.val) :
      formSetWeight (F p) (θ p) (r, s) = affineFormWeight (a p) (b p) (c p) (θ p) r s := by
    simp [formSetWeight, F, affineResidueLine, prod_filter, affineFormWeight]
  simpa only [heq] using hbound P F θ u v w x Z huv hwx hZ hP hF hθ

end JointDickman

end OAI
