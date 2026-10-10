import OAI.Probability.InvariantIsing.Cavity.CavityRetainedFrame

namespace OAI

/-! Assemble the retained group frames without imposing equal group
sizes. The separate group projector identities give completeness. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

def cavityRetainedStack {r m : ℕ} (k : Fin m → ℕ)
    (R : (a : Fin m) → Matrix (Fin r) (Fin (k a)) ℝ) :
    Matrix (Fin r) ((a : Fin m) × Fin (k a)) ℝ := fun i j => R j.1 i j.2

theorem cavityRetainedStack_gram {r m : ℕ} (k : Fin m → ℕ)
    (R : (a : Fin m) → Matrix (Fin r) (Fin (k a)) ℝ)
    (hR : ∀ a, (R a).transpose * R a = 1)
    (hcross : ∀ a b, a ≠ b → (R a).transpose * R b = 0) :
    (cavityRetainedStack k R).transpose * cavityRetainedStack k R = 1 := by
  classical
  ext ⟨a, i⟩ ⟨b, j⟩
  change ((R a).transpose * R b) i j = if (⟨a, i⟩ : Sigma fun a => Fin (k a)) = ⟨b, j⟩ then 1 else 0
  by_cases hab : a = b
  · subst b
    rw [hR, Matrix.one_apply]
    simp
  · rw [hcross a b hab, Matrix.zero_apply]
    have hij : (⟨a, i⟩ : Sigma fun a => Fin (k a)) ≠ ⟨b, j⟩ := fun h => hab (congrArg Sigma.fst h)
    simp only [hij, ite_false]

theorem cavityRetainedStack_outer {r m : ℕ} (k : Fin m → ℕ)
    (R : (a : Fin m) → Matrix (Fin r) (Fin (k a)) ℝ) :
    cavityRetainedStack k R * (cavityRetainedStack k R).transpose =
      ∑ a, R a * (R a).transpose := by
  ext i j
  change (∑ a : Sigma fun a => Fin (k a), R a.1 i a.2 * R a.1 j a.2) = _
  simp only [Fintype.sum_sigma, Matrix.sum_apply, Matrix.mul_apply, Matrix.transpose_apply]

theorem cavityEigenspaceFrame_outer {r m n : ℕ}
    (X : Fin m → Matrix (Fin r) (Fin n) ℝ) :
    cavityEigenspaceFrame X * (cavityEigenspaceFrame X).transpose =
      ∑ a, cavityNormalizeFrame (X a) * (cavityNormalizeFrame (X a)).transpose := by
  ext i j
  change (∑ k : Fin (m * n), cavityNormalizeFrame (X (finProdFinEquiv.symm k).1)
    i (finProdFinEquiv.symm k).2 * cavityNormalizeFrame (X (finProdFinEquiv.symm k).1)
      j (finProdFinEquiv.symm k).2) = _
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n))]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type,
    Matrix.sum_apply, Matrix.mul_apply, Matrix.transpose_apply]

theorem cavityRetainedStack_complete {r m n : ℕ} (g : Fin r → Fin m)
    (A : Matrix (Fin r) (Fin n) ℝ) (k : Fin m → ℕ)
    (R : (a : Fin m) → Matrix (Fin r) (Fin (k a)) ℝ)
    (hR : ∀ a, R a * (R a).transpose +
      cavityNormalizeFrame (cavitySpectralImage g A a) *
        (cavityNormalizeFrame (cavitySpectralImage g A a)).transpose =
          Matrix.diagonal (fun i => if g i = a then (1 : ℝ) else 0)) :
    cavityRetainedStack k R * (cavityRetainedStack k R).transpose +
      cavityEigenspaceFrame (cavitySpectralImage g A) *
        (cavityEigenspaceFrame (cavitySpectralImage g A)).transpose = 1 := by
  rw [cavityRetainedStack_outer, cavityEigenspaceFrame_outer, ← Finset.sum_add_distrib]
  simp only [hR]
  exact cavitySpectralProjectors_sum g

end InvariantIsing

end

end OAI
