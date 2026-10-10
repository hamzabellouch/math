import OAI.NumberTheory.Ostmann.Construction.InitialConstituentPoisson
import OAI.NumberTheory.Ostmann.Construction.FullAtomRangeSupport

namespace OAI

/-! # Initial guarded expectation under the unchanged harmonic product law -/

namespace Ostmann
open scoped BigOperators Classical SchwartzMap FourierTransform

theorem initial_guarded_expectation {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) [Nonempty (Σ i, Fin (size i))]
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (hχ : ∀ i p, p ∈ P → χ i p ≠ 1)
    (pivot : ℕ → (Σ i, Fin (size i))) (center : ∀ p : ℕ, ZMod p)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hX : 0 < X)
    (heven : ∀ t : ℝ, 𝓕 ψ (-t) = 𝓕 ψ t) (N : ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (hwindow : ∀ x : (Σ i, Fin (size i)) → P,
      (∏ i, primeSubsetPrior P (Q i) (x i)) ≠ 0 →
      (∀ r ∈ ranges 0, r.Holds (fun a => ∏ k, (x ⟨a.val, k⟩ : ℕ))) →
      ((∏ i, (x i : ℕ) : ℕ) : ℝ) / X ∈ Set.Icc lo hi) :
    constituentPrimeGuardedAmplitude role size (χ) (fun i => primeGaussMultiplier (χ i))
      pivot 0 P hP Q childBound pivotBound ranges (scheduleFourierLeaf role ψ X lo hi)
      (fun v : Finset.Icc (-(N : ℤ)) (N : ℤ) => (v : ℤ)) center =
    ∑ x : (Σ i, Fin (size i)) → P,
      ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) *
      (if Pairwise (fun i j => (x i : ℕ).Coprime (x j : ℕ)) ∧
          (∀ r ∈ ranges 0, r.Holds (fun a => ∏ k, (x ⟨a.val, k⟩ : ℕ))) then
        sampledTupleAmplitude P hP χ center ψ X N x else 0) := by
  have hk (i) (p : P) : primeGaussMultiplier (χ i) p =
      @primitiveGaussPhase p.val ⟨(hP p p.property).ne_zero⟩ (χ i p) :=
    primeGaussMultiplier_eq (χ i) p (hP p p.property) (hχ i p p.property)
  rw [constituentPrimeGuardedAmplitude_zero role size χ (fun i => primeGaussMultiplier (χ i))
    pivot P hP Q hk childBound pivotBound ranges (scheduleFourierLeaf role ψ X lo hi)
    (fun v : Finset.Icc (-(N : ℤ)) (N : ℤ) => (v : ℤ)) center]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hz : (∏ i, primeSubsetPrior P (Q i) (x i)) = 0
  · simp only [hz, Complex.ofReal_zero, zero_mul]
  apply congrArg (fun z : ℂ => ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) * z)
  by_cases hp : Pairwise (fun i j => (x i : ℕ).Coprime (x j : ℕ))
  · simp only [hp, ite_true, true_and]
    by_cases hr : ∀ r ∈ ranges 0, r.Holds (fun a => ∏ k, (x ⟨a.val, k⟩ : ℕ))
    · rw [ite_eq_left hr]
      have hs := Finset.sum_coe_sort (Finset.Icc (-(N : ℤ)) (N : ℤ))
        (fun v : ℤ => fullAtomTransferWeight role childBound pivotBound ranges
          (scheduleFourierLeaf role ψ X lo hi) 0 (fun a => ∏ k, (x ⟨a.val, k⟩ : ℕ)) v *
          sampledTuplePhase P hP χ center v x)
      exact hs.trans (initial_constituent_poisson_sum role size χ P hP x center ψ X lo hi hX heven N
        childBound pivotBound ranges hp hr (hwindow x hz hr))
    · rw [ite_eq_right hr]
      apply Finset.sum_eq_zero
      intro v _
      have hz : fullAtomTransferWeight role childBound pivotBound ranges
          (scheduleFourierLeaf role ψ X lo hi) 0 (fun a => ∏ k, (x ⟨a.val, k⟩ : ℕ)) (v : ℤ) = 0 := by
        by_contra h
        exact hr (fun r hr => fullAtomTransferWeight_top_range role childBound pivotBound ranges
          (scheduleFourierLeaf role ψ X lo hi) 0 _ (v : ℤ) h r hr)
      rw [hz, zero_mul]
  · simp only [hp, ite_false, false_and, mul_zero, Finset.sum_const_zero]

end Ostmann

end OAI
