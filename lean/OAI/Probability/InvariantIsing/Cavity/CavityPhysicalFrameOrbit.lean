import OAI.Probability.InvariantIsing.Cavity.CavityReservoirFrame

namespace OAI

/-! A single reservoir rotation represents both the base interaction
and its selected special axes, as needed for the fresh-frame law. -/

noncomputable section
open scoped Matrix BigOperators

namespace InvariantIsing

lemma cavityReservoir_spectral_eq {N n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι ≃ Fin N) (F : Matrix (Fin (N + n)) ι ℝ) (lam : ι → ℝ)
    (V : Orthogonal N)
    (hV : ∀ i j, (V : Matrix (Fin N) (Fin N) ℝ) i j = cavityReservoirRows F i (e.symm j)) :
    cavityReservoirRows F * Matrix.diagonal lam * (cavityReservoirRows F).transpose =
      (V : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal (fun j => lam (e.symm j)) *
        (V : Matrix (Fin N) (Fin N) ℝ).transpose := by
  ext i j
  change (∑ k : ι, (∑ t : ι, cavityReservoirRows F i t *
      (if t = k then lam t else 0)) * cavityReservoirRows F j k) =
    ∑ k : Fin N, (∑ t : Fin N, (V : Matrix (Fin N) (Fin N) ℝ) i t *
      (if t = k then lam (e.symm t) else 0)) * (V : Matrix (Fin N) (Fin N) ℝ) j k
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, hV]
  exact (Equiv.sum_comp e.symm (fun k : ι =>
    cavityReservoirRows F i k * lam k * cavityReservoirRows F j k)).symm

def cavityCanonicalSpecial {N d : ℕ} {ι : Type*} (e : (ι ⊕ Fin d) ≃ Fin N) :
    Matrix (Fin N) (Fin d) ℝ := fun i j => if i = e (Sum.inr j) then 1 else 0

lemma cavityCanonicalSpecial_mul {N d : ℕ} {ι : Type*} (e : (ι ⊕ Fin d) ≃ Fin N)
    (V : Matrix (Fin N) (Fin N) ℝ) (i : Fin N) (j : Fin d) :
    (V * cavityCanonicalSpecial e) i j = V i (e (Sum.inr j)) := by
  simp only [Matrix.mul_apply, cavityCanonicalSpecial, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem cavityBaseReplacement_physical_joint_orbit {N n s d : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (e : (ι ⊕ Fin d) ≃ Fin N)
    (U : Orthogonal (N + n)) (J : Matrix (Fin (N + n)) (Fin (N + n)) ℝ)
    (R : Matrix (Fin (N + n)) ι ℝ) (W : Matrix (Fin (N + n)) (Fin s) ℝ)
    (D : Matrix (Fin s) (Fin s) ℝ) (B : Matrix (Fin s) (Fin d) ℝ)
    (T : Matrix (Fin s) (Fin n) ℝ) (lam : ι → ℝ) (lam₀ : Fin d → ℝ)
    (hR : R.transpose * R = 1) (hW : W.transpose * W = 1)
    (hRW : R.transpose * W = 0) (hB : B.transpose * B = 1)
    (hBT : B.transpose * T = 0)
    (hWT : W * T = fun i j => (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ)
      i (Fin.natAdd N j))
    (hJR : J * R = R * Matrix.diagonal lam) (hJW : J * W = W * D)
    (hcomplete : R * R.transpose + W * W.transpose = 1) :
    ∃ V : Orthogonal N,
      ((U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ).transpose *
        cavityBaseReplacement J W D B (Matrix.diagonal lam₀) *
          (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ)).submatrix
            (Fin.castAdd n) (Fin.castAdd n) =
        (V : Matrix (Fin N) (Fin N) ℝ) *
          Matrix.diagonal (fun j => Sum.elim lam lam₀ (e.symm j)) *
            (V : Matrix (Fin N) (Fin N) ℝ).transpose ∧
      cavityReservoirRows ((U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ).transpose * (W * B)) =
        (V : Matrix (Fin N) (Fin N) ℝ) * cavityCanonicalSpecial e := by
  let F := Matrix.fromCols R (W * B)
  let P := (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ).transpose * F
  have hFG : F.transpose * F = 1 := cavityBaseFrame_gram R W B hR hW hRW hB
  have hPG : P.transpose * P = 1 := (cavityPhysicalFrame_gram U F).trans hFG
  have hPF : ∀ i : Fin n, ∀ j, P (Fin.natAdd N i) j = 0 := by
    apply cavityPhysicalFrame_lastRows _ F
    rw [← hWT]
    exact cavityBaseFrame_cavity_perp R W B T hW hRW hBT
  have hJ : cavityBaseReplacement J W D B (Matrix.diagonal lam₀) =
      F * Matrix.diagonal (Sum.elim lam lam₀) * F.transpose := by
    rw [cavityBaseReplacement_spectral_sum J W D B _ R _ hJR hJW hcomplete]
    exact (cavityBaseFrame_spectral_sum R (W * B) lam lam₀).symm
  have hP : (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ).transpose *
      cavityBaseReplacement J W D B (Matrix.diagonal lam₀) *
        (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ) =
      P * Matrix.diagonal (Sum.elim lam lam₀) * P.transpose := by
    rw [hJ]
    simp only [P, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  obtain ⟨V, hV⟩ := cavityReservoirRows_orthogonal e P hPG hPF
  refine ⟨V, ?_, ?_⟩
  · rw [hP, cavityReservoirRows_conjugate]
    exact cavityReservoir_spectral_eq e P (Sum.elim lam lam₀) V hV
  · ext i j
    rw [cavityCanonicalSpecial_mul, hV]
    simp only [Equiv.symm_apply_apply]
    rfl

end InvariantIsing

end

end OAI
