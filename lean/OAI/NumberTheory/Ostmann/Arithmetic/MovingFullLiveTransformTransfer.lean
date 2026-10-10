import OAI.NumberTheory.Ostmann.Arithmetic.MovingFullTransformTransfer
import OAI.NumberTheory.Ostmann.Arithmetic.MovingRegularLiveOffDiagonal
import OAI.NumberTheory.Ostmann.Construction.SmoothGiantSupportedTransfer

namespace OAI

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

local instance liveFullTransferSum_neZero {J H : Type*} (Q : J → ℕ) (L : H → ℕ)
    [∀ j, NeZero (Q j)] [∀ i, NeZero (L i)] (i : J ⊕ H) :
    NeZero (Sum.elim Q L i) := by
  cases i <;> dsimp only [Sum.elim] <;> infer_instance

theorem smoothGiantPrior_full_transform_transfer_on_live
    {Y A J H : Type*} [Fintype Y] [Fintype A] [Fintype J] [Fintype H]
    (P I : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hPI : P ⊆ I)
    (hI : ∀ p ∈ I, 0 < p)
    (φ : ℝ → ℝ) (G : ℝ) (hφ : ∀ x, 0 ≤ φ x)
    (hpos : 0 < smoothGiantMass P φ G)
    (μ : Y → ℝ) (hμ : ∀ y, 0 ≤ μ y) (hμmass : ∑ y, μ y = 1)
    (U : Y → ℕ) (hU : ∀ y, 0 < U y)
    (Q : Y → P → J → ℕ) [∀ y p j, Fact (Q y p j).Prime]
    (gQ : ∀ y p j, ZMod (Q y p j) → ℂ)
    (hQprod : ∀ y p, (∏ j, Q y p j) = (p : ℕ) * U y)
    (giant : J) (S : ∀ y p j, Finset (ZMod (Q y p j)))
    (hgQ : ∀ y p x, ‖gQ y p giant x‖ ≤ 1)
    (hregular : ∀ y p j, j ≠ giant → gQ y p j = normalizedResidueTransform (S y p j))
    (hS : ∀ y p j, j ≠ giant → (S y p j).Nonempty)
    (hSp : ∀ y p j, j ≠ giant → (S y p j).card < Q y p j)
    (L : Y → A → H → ℕ) [∀ y a i, Fact (L y a i).Prime]
    (gL : ∀ y a i, ZMod (L y a i) → ℂ)
    (hgL : ∀ y a i x, gL y a i (-x) = conj (gL y a i x))
    (D : Y → ℕ) (v : Y → A → ℤ) (W : Y → ℕ → A → ℂ)
    (hrowSupport : ∀ y (p : P) a, W y p a ≠ 0 →
      Pairwise (fun i j => (Q y p i).Coprime (Q y p j)) ∧
      ∀ j, (D y).Coprime (Q y p j))
    (hsupport : ∀ y p, p ∈ I → ∀ a, W y p a ≠ 0 →
      Pairwise (fun i j => (L y a i).Coprime (L y a j)) ∧
      (∏ i, L y a i).Coprime (p * U y) ∧ ∀ i, (D y).Coprime (L y a i))
    (N B V : ℕ)
    (hv : ∀ y p, p ∈ I → ∀ a, W y p a ≠ 0 → (v y a).natAbs ≤ N)
    (hL : ∀ y, μ y ≠ 0 → ∀ p, p ∈ I → ∀ a, W y p a ≠ 0 → (∏ i, L y a i) ≤ B)
    (hscale : ∀ y, μ y ≠ 0 → ∀ p, p ∈ I → 2 * N * B ≤ V * (p * U y))
    (hlarge : ∀ y p, p ∈ I → ∀ a, W y p a ≠ 0 →
      ∀ q, q.Prime → q ∣ ∏ i, L y a i → V < q) :
    Real.exp (-smoothGiantLogNormalizer P φ G) *
      ‖∑ y, (μ y : ℂ) * ∑ p : P, (smoothGiantPrior P φ G p : ℂ) *
        ∑ a, W y p a * movingRegularTransform (Sum.elim (Q y p) (L y a))
          (movingSumFactors (Q y p) (L y a) (gQ y p) (gL y a)) (D y) (v y a)‖ ^ 2 ≤
      (∑ y, μ y * (U y : ℝ) * ∑ p ∈ I, φ (Real.log p - G) *
        (pivotDiagonal (fun a => ∏ i, L y a i) (v y)
          (movingRegularCoefficient (L y) (gL y) (D y) (U y) (v y) (W y) p)).re) +
      ‖∑ y, ((μ y * (U y : ℝ) : ℝ) : ℂ) *
        ∑ s ∈ transferFrequencyRange V, ∑ a, ∑ b,
          if validTransferredPivot I
              (v y a * (∏ i, L y b i) - v y b * (∏ i, L y a i)) (s * U y) then
            let p := reconstructedPivot
              (v y a * (∏ i, L y b i) - v y b * (∏ i, L y a i)) (s * U y)
            (φ (Real.log p - G) : ℂ) * W y p a * conj (W y p b) *
              movingRegularTransform (Sum.elim (L y a) (L y b))
                (movingSumFactors (L y a) (L y b) (gL y a) (gL y b)) (D y) s
          else 0‖ := by
  let c := fun y => movingRegularCoefficient (L y) (gL y) (D y) (U y) (v y) (W y)
  have hc (y : Y) (p : ℕ) (a : A) (h : c y p a ≠ 0) : W y p a ≠ 0 := by
    intro hz
    apply h
    simp only [c, movingRegularCoefficient, hz, zero_mul]
  have ht := smoothGiantPrior_transfer_on_prior P I hP hPI hI φ G hφ hpos μ hμ hμmass U hU
    (fun y p => movingGuardedRow (Q y p) (gQ y p) (D y))
    (fun y p => by
      simpa only [Nat.cast_mul] using
        movingGuardedRow_energy (Q y p) (gQ y p) (D y) ((p : ℕ) * U y)
          (hQprod y p) giant (S y p) (hgQ y p) (hregular y p) (hS y p) (hSp y p))
    (fun y a => ∏ i, L y a i) v c
    (fun y p hp a h => (hsupport y p hp a (hc y p a h)).2.1) N B V
    (fun y p hp a h => hv y p hp a (hc y p a h))
    (fun y hy p hp a h => hL y hy p hp a (hc y p a h)) hscale
  have hsum : (∑ y, (μ y : ℂ) * ∑ p : P, (smoothGiantPrior P φ G p : ℂ) *
      ∑ a, movingGuardedRow (Q y p) (gQ y p) (D y)
        (positiveIntegerPivotKey ((p : ℕ) * U y)
          (Nat.mul_pos (hP p p.property).pos (hU y)) (∏ i, L y a i) (v y a)) * c y p a) =
      ∑ y, (μ y : ℂ) * ∑ p : P, (smoothGiantPrior P φ G p : ℂ) *
        ∑ a, W y p a * movingRegularTransform (Sum.elim (Q y p) (L y a))
          (movingSumFactors (Q y p) (L y a) (gQ y p) (gL y a)) (D y) (v y a) := by
    apply Finset.sum_congr rfl
    intro y _
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    by_cases hz : W y p a = 0
    · simp only [c, movingRegularCoefficient, hz, zero_mul, mul_zero]
    · have hs := hrowSupport y p a hz
      rw [moving_full_transform_guarded (Q y p) (L y a) (gQ y p) (gL y a)
        (D y) ((p : ℕ) * U y) (hQprod y p)
        (Nat.mul_pos (hP p p.property).pos (hU y)) (v y a) hs.1 hs.2
        (hsupport y p (hPI p.property) a hz).2.1]
      dsimp only [c, movingRegularCoefficient]
      ring
  rw [hsum] at ht
  convert ht using 1
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  dsimp only [c]
  rw [movingGiantOffDiagonal_regular_on_live (L y) (gL y) (hgL y) I V (U y) (D y)
    (v y) (fun p => φ (Real.log p - G)) (W y) (hsupport y) (hlarge y)]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs
  · congr 1
    congr 1
    funext i
    cases i <;> rfl
  · rfl

end Ostmann

end OAI
