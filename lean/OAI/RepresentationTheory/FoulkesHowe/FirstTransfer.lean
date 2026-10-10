import OAI.RepresentationTheory.FoulkesHowe.FirstPolynomial
import OAI.RepresentationTheory.FoulkesHowe.BlockInjectivity
import OAI.RepresentationTheory.FoulkesHowe.BackwardCancellation
import OAI.RepresentationTheory.FoulkesHowe.TransferDerivative
import OAI.RepresentationTheory.FoulkesHowe.TransferEndpoints

namespace OAI

noncomputable section

namespace Problem346

universe u v
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable {κ : Type v} [Fintype κ]

/-- Cancel the first transfer sequence from its zero endpoint. The homogeneous
and derivative identities are kept separate from this zero-reflection argument. -/
theorem firstPolynomial_zero_of_chain {r m : ℕ}
    (T : SymmetricMultilinearForm (r+1) (r+m) V) (e : κ → V)
    (ht : ∀ k < m, PolynomialWeights.IsBlockHomogeneous (some none)
      (firstPolynomial T e k) (r+m-k))
    (hy : ∀ (k : ℕ) (hk : k < m), PolynomialWeights.IsBlockHomogeneous
      (some (some (⟨k,hk⟩ : Fin m))) (firstPolynomial T e k) r)
    (hD : ∀ (k : ℕ) (hk : k < m),
      PolynomialShift.shift (some none) (some (some (⟨k,hk⟩ : Fin m)))
        (firstPolynomial T e k) = ((r+m-k : ℕ) : ℂ) • firstPolynomial T e (k+1))
    (hm : firstPolynomial T e m = 0) : firstPolynomial T e 0 = 0 := by
  classical
  apply eq_zero_of_backward_chain (firstPolynomial T e) m _ hm
  intro k hk hz
  apply PolynomialShift.eq_zero_of_shift_eq_zero
    (some none) (some (some (⟨k,hk⟩ : Fin m))) (by simp)
    (show r < r+m-k by omega) (ht k hk) (hy k hk)
  rw [hD k hk, hz, smul_zero]

/-- Every terminal-zero polynomial in the concrete first-transfer family is zero
at the initial stage. All degree counts and derivative identities are discharged. -/
theorem firstPolynomial_zero_of_final {r m : ℕ}
    (T : SymmetricMultilinearForm (r+1) (r+m) V) (e : κ → V)
    (hm : firstPolynomial T e m = 0) : firstPolynomial T e 0 = 0 := by
  classical
  apply firstPolynomial_zero_of_chain T e _ _ _ hm
  · intro k hk
    simpa only [firstLabel_card_t r m k (Nat.le_of_lt hk)] using
      firstPolynomial_blockHomogeneous T e k (some none)
  · intro k hk
    simpa only [firstLabel_card_y_next r m k hk] using
      firstPolynomial_blockHomogeneous T e k (some (some (⟨k,hk⟩ : Fin m)))
  · intro k hk
    simpa only [firstPolynomial, PolynomialShift.shift_apply] using
      (firstLabel_derivative r m k hk V κ T e
        (PolynomialShift.derivation (some none) (some (some (⟨k,hk⟩ : Fin m))))
        (fun q j => by simp))

/-- The first transfer in the stabilization argument: the common product can be
removed from the distinguished argument, while the other arguments remain fixed.
No outer symmetry or positive-degree assumptions are needed for this step. -/
theorem first_transfer [FiniteDimensional ℂ V] {r m : ℕ}
    (T : SymmetricMultilinearForm (r+1) (r+m) V)
    (h : ∀ (x t : V) (y : Fin m → V),
      T (Fin.cons (symPowMul r m (symMonomial r V (fun _ => t)) (symMonomial m V y))
        (fun _ => symPowMul r m (symMonomial r V (fun _ => x)) (symMonomial m V y))) = 0) :
    ∀ (x t : V) (y : Fin m → V),
      T (Fin.cons (symMonomial (r+m) V (fun _ => t))
        (fun _ => symPowMul r m (symMonomial r V (fun _ => x)) (symMonomial m V y))) = 0 := by
  let e := Module.finBasis ℂ V
  have hm := firstPolynomial_final_eq_zero T e h
  have hzero := firstPolynomial_zero_of_final T e hm
  exact firstPolynomial_initial_vanishing T e hzero

end Problem346

end

end OAI
