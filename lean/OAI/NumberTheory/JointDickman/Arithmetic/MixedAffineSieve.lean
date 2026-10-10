import OAI.NumberTheory.JointDickman.Arithmetic.MixedTwoFormSieve

namespace OAI

/-! # Both affine orientations of the numeric-addition sieve -/

namespace JointDickman
open Finset Classical

theorem affine_two_roots_ne {p : ℕ} [Fact p.Prime] (a b c d : ZMod p)
    (hb : b ≠ 0) (hd : d ≠ 0) (hdet : a*d-c*b ≠ 0) : -a/b ≠ -c/d := by
  intro h
  have he := (div_eq_div_iff hb hd).mp h
  apply hdet
  linear_combination -he

theorem residueWeight_affine {p : ℕ} [Fact p.Prime] (a b x : ZMod p)
    (hb : b ≠ 0) (q : ℝ) :
    residueWeight q 0 (a+b*x) = residueWeight q (-a/b) x := by
  have he := affine_residue_root a b x hb
  simp only [residueWeight,he]
  split_ifs <;> rfl

/-- Negative slopes are included, so the same statement applies when the
large numeric addition occurs at either endpoint. -/
theorem mixed_affine_interval_sieve
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : Finset ℕ) (a b c d : ℤ) (q : ℝ) (u v Z : ℕ),
      0 ≤ q → q ≤ 1 → u ≤ v → 2 ≤ Z →
      (∀ p ∈ P, p.Prime ∧ p ≤ Z ∧ 4 ≤ p) →
      (∀ p ∈ P, (b : ZMod p) ≠ 0 ∧ (d : ZMod p) ≠ 0 ∧
        (a : ZMod p)*d-c*b ≠ 0) →
      (∑ n ∈ Ico u v, ∏ p ∈ P,
        residueWeight q 0 ((a : ZMod p)+b*n)*residueWeight (1/2) 0 ((c : ZMod p)+d*n)) ≤
        K*((v : ℝ)-u)*(∏ p ∈ P, (1-(3/2-q)/(p : ℝ)))+2*(Z+1 : ℝ)*(Z : ℝ)^2 := by
  obtain ⟨K,hK,hbound⟩ := mixed_two_root_interval_sieve hFord hM
  refine ⟨K,hK,?_⟩
  intro P a b c d q u v Z hq hq1 huv hZ hP hdet
  let : ∀ p : P, Fact p.val.Prime := fun p => ⟨(hP p.val p.property).1⟩
  let r₁ := fun p : P => -(a : ZMod p.val)/(b : ZMod p.val)
  let r₂ := fun p : P => -(c : ZMod p.val)/(d : ZMod p.val)
  have hr (p : P) : r₁ p ≠ r₂ p :=
    affine_two_roots_ne _ _ _ _ (hdet p.val p.property).1 (hdet p.val p.property).2.1
      (hdet p.val p.property).2.2
  have hh := hbound P r₁ r₂ q u v Z hq hq1 huv hZ hP hr
  have hterm (n : ℕ) : (∏ p : P,
      residueWeight q (r₁ p) (n : ZMod p.val)*residueWeight (1/2) (r₂ p) (n : ZMod p.val)) =
      ∏ p ∈ P, residueWeight q 0 ((a : ZMod p)+b*n)*
        residueWeight (1/2) 0 ((c : ZMod p)+d*n) := by
    rw [← P.prod_coe_sort]
    apply prod_congr rfl
    intro p _
    rw [residueWeight_affine _ _ _ (hdet p.val p.property).1,
      residueWeight_affine _ _ _ (hdet p.val p.property).2.1]
  simpa only [hterm] using hh

end JointDickman

end OAI
