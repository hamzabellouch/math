import OAI.Algebra.DepthFive.FactorialPositive
import OAI.Algebra.DepthFive.OccupationExpansion

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335.FactorialExpansion

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Uniform weak-composition mean of an actual natural-valued function. -/
def uniformMean (f : (σ → ℕ) → ℕ) (t : ℕ) : ℝ :=
  (∑ M ∈ Finset.finsuppAntidiag (Finset.univ : Finset σ) t, (f M : ℝ)) /
    (Finset.finsuppAntidiag (Finset.univ : Finset σ) t).card

/-- Product-geometric evaluation of a nonnegative factorial expansion. -/
def geometricMean {f : (σ → ℕ) → ℕ} {S : Finset σ} {D : ℕ}
    (F : FactorialExpansion f S D) (G : ℝ) : ℝ :=
  geometricExpansionValue Finset.univ (fun j => (F.coeff j : ℝ)) F.degree G

theorem uniformMean_eq {f : (σ → ℕ) → ℕ} {S : Finset σ} {D : ℕ}
    (F : FactorialExpansion f S D) (t : ℕ) :
    uniformMean f t = compositionExpansionMean Finset.univ
      (fun j => (F.coeff j : ℝ)) F.degree t := by
  unfold uniformMean compositionExpansionMean
  congr 1
  apply Finset.sum_congr rfl
  intro M hM
  simpa [factorialExpansionValue, factorialMonomial, Nat.cast_prod] using F.eval_real M

theorem uniformMean_le_geometric [Nonempty σ] {f : (σ → ℕ) → ℕ}
    {S : Finset σ} {D : ℕ} (F : FactorialExpansion f S D) (t : ℕ) :
    uniformMean f t ≤ F.geometricMean ((t : ℝ) / Fintype.card σ) := by
  rw [F.uniformMean_eq]
  exact compositionExpansionMean_le_geometric _ _ _ _ (by intros; positivity)

theorem exp_mul_geometric_le_uniformMean [Nonempty σ] {f : (σ → ℕ) → ℕ}
    {S : Finset σ} {D t : ℕ} (F : FactorialExpansion f S D)
    (ht : 0 < t) (hD : 2 * D ≤ t) :
    Real.exp (-(D : ℝ) ^ 2 / t - (D : ℝ) ^ 2 / (2 * Fintype.card σ)) *
      F.geometricMean ((t : ℝ) / Fintype.card σ) ≤ uniformMean f t := by
  rw [F.uniformMean_eq]
  exact exp_mul_geometric_le_compositionExpansionMean _ _ _ ht hD
    (by intros; positivity) (by intro j hj; exact F.order_le j)

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Independent uniform means, keeping the two occupation totals fixed separately. -/
def twoGroupMean (f : ((ι ⊕ κ) → ℕ) → ℕ) (a b : ℕ) : ℝ :=
  (∑ M ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) a,
    (∑ N ∈ Finset.finsuppAntidiag (Finset.univ : Finset κ) b,
      (f (Sum.elim M N) : ℝ)) /
      (Finset.finsuppAntidiag (Finset.univ : Finset κ) b).card) /
    (Finset.finsuppAntidiag (Finset.univ : Finset ι) a).card

def twoGroupGeometricMean {f : ((ι ⊕ κ) → ℕ) → ℕ} {S : Finset (ι ⊕ κ)} {D : ℕ}
    (F : FactorialExpansion f S D) (A B : ℝ) : ℝ :=
  twoGroupGeometricExpansionValue Finset.univ (fun j => (F.coeff j : ℝ))
    (fun j i => F.degree j (.inl i)) (fun j i => F.degree j (.inr i)) A B

theorem twoGroupMean_eq {f : ((ι ⊕ κ) → ℕ) → ℕ} {S : Finset (ι ⊕ κ)} {D : ℕ}
    (F : FactorialExpansion f S D) (a b : ℕ) :
    twoGroupMean f a b = twoGroupCompositionExpansionMean Finset.univ
      (fun j => (F.coeff j : ℝ)) (fun j i => F.degree j (.inl i))
      (fun j i => F.degree j (.inr i)) a b := by
  unfold twoGroupMean twoGroupCompositionExpansionMean compositionExpansionMean
  congr 1
  apply Finset.sum_congr rfl
  intro M hM
  congr 1
  apply Finset.sum_congr rfl
  intro N hN
  simpa [factorialExpansionValue, factorialMonomial, Fintype.prod_sum_type,
    Nat.cast_prod, Nat.cast_mul, mul_assoc] using F.eval_real (Sum.elim M N)

theorem twoGroupMean_le_geometric [Nonempty ι] [Nonempty κ]
    {f : ((ι ⊕ κ) → ℕ) → ℕ} {S : Finset (ι ⊕ κ)} {D : ℕ}
    (F : FactorialExpansion f S D) (a b : ℕ) :
    twoGroupMean f a b ≤ F.twoGroupGeometricMean
      ((a : ℝ) / Fintype.card ι) ((b : ℝ) / Fintype.card κ) := by
  rw [F.twoGroupMean_eq]
  exact twoGroupCompositionExpansionMean_le_geometric _ _ _ _ _ _
    (by intros; positivity)

theorem exp_mul_geometric_le_twoGroupMean [Nonempty ι] [Nonempty κ]
    {f : ((ι ⊕ κ) → ℕ) → ℕ} {S : Finset (ι ⊕ κ)} {D a b : ℕ}
    (F : FactorialExpansion f S D) (ha : 0 < a) (hb : 0 < b)
    (hDa : 2 * D ≤ a) (hDb : 2 * D ≤ b) :
    Real.exp ((-(D : ℝ) ^ 2 / a - (D : ℝ) ^ 2 / (2 * Fintype.card ι)) +
        (-(D : ℝ) ^ 2 / b - (D : ℝ) ^ 2 / (2 * Fintype.card κ))) *
      F.twoGroupGeometricMean ((a : ℝ) / Fintype.card ι) ((b : ℝ) / Fintype.card κ) ≤
        twoGroupMean f a b := by
  rw [F.twoGroupMean_eq]
  apply exp_mul_geometric_le_twoGroupCompositionExpansionMean _ _ _ _ ha hb hDa hDb
    (by intros; positivity)
  · intro j hj
    have h := F.order_le j
    rw [Fintype.sum_sum_type] at h
    omega
  · intro j hj
    have h := F.order_le j
    rw [Fintype.sum_sum_type] at h
    omega

end Problem335.FactorialExpansion

end

end OAI
