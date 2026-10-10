import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem346
namespace PolynomialWeights

open MvPolynomial

variable {R σ : Type*} [CommSemiring R] [Fintype σ]

/-- The Euler derivation associated with natural-number weights. -/
def weightedEuler (w : σ → ℕ) :
    Derivation R (MvPolynomial σ R) (MvPolynomial σ R) :=
  ∑ i : σ, (w i) • ((X i : MvPolynomial σ R) • pderiv i)

@[simp] theorem weightedEuler_apply (w : σ → ℕ) (f : MvPolynomial σ R) :
    weightedEuler w f = ∑ i : σ, w i • (X i * pderiv i f) := by
  classical
  unfold weightedEuler
  induction (Finset.univ : Finset σ) using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [Finset.sum_insert ha, Derivation.smul_apply, ih, smul_eq_mul]

@[simp] theorem weightedEuler_X (w : σ → ℕ) (i : σ) :
    weightedEuler (R := R) w (X i) = w i • X i := by
  classical
  simp [weightedEuler_apply, Pi.single_apply]

/-- Euler's identity, expressed using a bundled derivation. -/
theorem weightedEuler_of_homogeneous (w : σ → ℕ) {n : ℕ}
    {f : MvPolynomial σ R} (hf : f.IsWeightedHomogeneous w n) :
    weightedEuler w f = n • f := by
  rw [weightedEuler_apply]
  exact hf.sum_weight_X_mul_pderiv

/-- Any derivation with the prescribed diagonal action on generators is Euler. -/
theorem derivation_eq_weightedEuler (w : σ → ℕ)
    (N : Derivation R (MvPolynomial σ R) (MvPolynomial σ R))
    (hN : ∀ i, N (X i) = w i • X i) : N = weightedEuler w := by
  apply MvPolynomial.derivation_ext
  intro i
  rw [hN, weightedEuler_X]

/-- A homogeneous polynomial is an eigenvector for its weighted Euler derivation. -/
theorem derivation_homogeneous_eigenvalue (w : σ → ℕ)
    (N : Derivation R (MvPolynomial σ R) (MvPolynomial σ R))
    (hN : ∀ i, N (X i) = w i • X i)
    {n : ℕ} {f : MvPolynomial σ R} (hf : f.IsWeightedHomogeneous w n) :
    N f = n • f := by
  rw [derivation_eq_weightedEuler w N hN]
  exact weightedEuler_of_homogeneous w hf

section Blocks

variable {β ι : Type*} [Fintype β] [Fintype ι] [DecidableEq β]

/-- Weight one on one coordinate block, and zero on all spectator blocks. -/
def blockWeight (u : β) (ki : β × ι) : ℕ := if ki.1 = u then 1 else 0

/-- A polynomial is homogeneous of the specified degree in one block. -/
def IsBlockHomogeneous (u : β) (f : MvPolynomial (β × ι) R) (n : ℕ) : Prop :=
  f.IsWeightedHomogeneous (blockWeight u) n

omit [Fintype β] [Fintype ι] in
@[simp] theorem blockWeight_apply (u k : β) (i : ι) :
    blockWeight u (k, i) = if k = u then 1 else 0 := rfl

theorem block_euler_eigenvalue (u : β)
    (N : Derivation R (MvPolynomial (β × ι) R) (MvPolynomial (β × ι) R))
    (hN : ∀ k i, N (X (k, i)) = if k = u then X (k, i) else 0)
    {n : ℕ} {f : MvPolynomial (β × ι) R} (hf : IsBlockHomogeneous u f n) :
    N f = n • f := by
  apply derivation_homogeneous_eigenvalue (blockWeight u) N _ hf
  rintro ⟨k, i⟩
  simp only [hN, blockWeight_apply]
  split_ifs <;> simp

/-- The difference of block counting operators has the difference of the block degrees
as eigenvalue. This is the weight used by the positive-weight shift lemma. -/
theorem block_difference_eigenvalue (u v : β)
    (Nu Nv : Derivation ℂ (MvPolynomial (β × ι) ℂ) (MvPolynomial (β × ι) ℂ))
    (hu : ∀ k i, Nu (X (k, i)) = if k = u then X (k, i) else 0)
    (hv : ∀ k i, Nv (X (k, i)) = if k = v then X (k, i) else 0)
    {p q : ℕ} {f : MvPolynomial (β × ι) ℂ}
    (hp : IsBlockHomogeneous u f p) (hq : IsBlockHomogeneous v f q) :
    (Nu - Nv) f = ((p : ℂ) - (q : ℂ)) • f := by
  change Nu f - Nv f = _
  rw [block_euler_eigenvalue u Nu hu hp, block_euler_eigenvalue v Nv hv hq]
  rw [sub_smul]
  simp only [Nat.cast_smul_eq_nsmul]

theorem block_difference_nat_eigenvalue (u v : β)
    (Nu Nv : Derivation ℂ (MvPolynomial (β × ι) ℂ) (MvPolynomial (β × ι) ℂ))
    (hu : ∀ k i, Nu (X (k, i)) = if k = u then X (k, i) else 0)
    (hv : ∀ k i, Nv (X (k, i)) = if k = v then X (k, i) else 0)
    {p q : ℕ} (hpq : q ≤ p) {f : MvPolynomial (β × ι) ℂ}
    (hp : IsBlockHomogeneous u f p) (hq : IsBlockHomogeneous v f q) :
    (Nu - Nv) f = ((p - q : ℕ) : ℂ) • f := by
  rw [Nat.cast_sub hpq]
  exact block_difference_eigenvalue u v Nu Nv hu hv hp hq

omit [Fintype β] [Fintype ι] in
/-- Differentiating in a block lowers its degree by one, provided that degree is positive. -/
theorem block_pderiv_source {u : β} {n : ℕ} {f : MvPolynomial (β × ι) R}
    (hf : IsBlockHomogeneous u f n) (hn : 0 < n) (i : ι) :
    IsBlockHomogeneous u (pderiv (u, i) f) (n - 1) := by
  apply IsWeightedHomogeneous.pderiv hf
  simp only [blockWeight_apply]
  exact Nat.sub_add_cancel hn

omit [Fintype β] [Fintype ι] in
/-- Differentiating in another block leaves the indicated block degree unchanged. -/
theorem block_pderiv_other {u k : β} (hku : k ≠ u) {n : ℕ}
    {f : MvPolynomial (β × ι) R} (hf : IsBlockHomogeneous u f n) (i : ι) :
    IsBlockHomogeneous u (pderiv (k, i) f) n := by
  apply IsWeightedHomogeneous.pderiv hf
  simp [blockWeight_apply, hku]

omit [Fintype β] in
/-- A directional shift lowers its source block degree by one. -/
theorem block_shift_degree_source {u v : β} (huv : u ≠ v) {n : ℕ}
    {f : MvPolynomial (β × ι) R} (hf : IsBlockHomogeneous u f n) (hn : 0 < n) :
    IsBlockHomogeneous u (∑ i : ι, X (v, i) * pderiv (u, i) f) (n - 1) := by
  apply (weightedHomogeneousSubmodule R (blockWeight u) (n - 1)).sum_mem
  intro i hi
  have hx : (X (v, i) : MvPolynomial (β × ι) R).IsWeightedHomogeneous
      (blockWeight u) 0 := by
    simpa [blockWeight_apply, Ne.symm huv] using
      (isWeightedHomogeneous_X (R := R) (blockWeight u) (v, i))
  simpa using hx.mul (block_pderiv_source hf hn i)

omit [Fintype β] in
/-- A directional shift raises its destination block degree by one. -/
theorem block_shift_degree_destination {u v : β} (huv : u ≠ v) {n : ℕ}
    {f : MvPolynomial (β × ι) R} (hf : IsBlockHomogeneous v f n) :
    IsBlockHomogeneous v (∑ i : ι, X (v, i) * pderiv (u, i) f) (n + 1) := by
  apply (weightedHomogeneousSubmodule R (blockWeight v) (n + 1)).sum_mem
  intro i hi
  have hx : (X (v, i) : MvPolynomial (β × ι) R).IsWeightedHomogeneous
      (blockWeight v) 1 := by
    simpa [blockWeight_apply] using
      (isWeightedHomogeneous_X (R := R) (blockWeight v) (v, i))
  simpa [Nat.add_comm] using hx.mul (block_pderiv_other huv hf i)

omit [Fintype β] in
/-- A directional shift leaves every spectator block degree unchanged. -/
theorem block_shift_degree_spectator {u v k : β} (huk : u ≠ k) (hvk : v ≠ k)
    {n : ℕ} {f : MvPolynomial (β × ι) R} (hf : IsBlockHomogeneous k f n) :
    IsBlockHomogeneous k (∑ i : ι, X (v, i) * pderiv (u, i) f) n := by
  apply (weightedHomogeneousSubmodule R (blockWeight k) n).sum_mem
  intro i hi
  have hx : (X (v, i) : MvPolynomial (β × ι) R).IsWeightedHomogeneous
      (blockWeight k) 0 := by
    simpa [blockWeight_apply, hvk] using
      (isWeightedHomogeneous_X (R := R) (blockWeight k) (v, i))
  simpa using hx.mul (block_pderiv_other huk hf i)

end Blocks

end PolynomialWeights
end Problem346

end

end OAI
