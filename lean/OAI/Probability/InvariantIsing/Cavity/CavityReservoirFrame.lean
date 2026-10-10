import OAI.Probability.InvariantIsing.Cavity.CavityBaseSpectralSum

namespace OAI

/-! An orthonormal base frame perpendicular to the physical cavity
coordinates gives an orthogonal eigenbasis of the reservoir. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

lemma cavityBaseFrame_gram {r s d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Matrix (Fin r) ι ℝ) (W : Matrix (Fin r) (Fin s) ℝ)
    (B : Matrix (Fin s) (Fin d) ℝ)
    (hR : R.transpose * R = 1) (hW : W.transpose * W = 1)
    (hRW : R.transpose * W = 0) (hB : B.transpose * B = 1) :
    (Matrix.fromCols R (W * B)).transpose * Matrix.fromCols R (W * B) = 1 := by
  have hRV : R.transpose * (W * B) = 0 := by rw [← Matrix.mul_assoc, hRW, Matrix.zero_mul]
  have hVR : (W * B).transpose * R = 0 := by
    have h := congrArg Matrix.transpose hRV
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] using h
  have hVV : (W * B).transpose * (W * B) = 1 := by
    rw [Matrix.transpose_mul]
    calc
      _ = B.transpose * (W.transpose * W) * B := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hW, Matrix.mul_one, hB]
  rw [Matrix.transpose_fromCols, Matrix.fromRows_mul_fromCols, hR, hRV, hVR, hVV,
    Matrix.fromBlocks_one]

lemma cavityBaseFrame_cavity_perp {r s d n : ℕ} {ι : Type*} [Fintype ι]
    (R : Matrix (Fin r) ι ℝ) (W : Matrix (Fin r) (Fin s) ℝ)
    (B : Matrix (Fin s) (Fin d) ℝ) (E : Matrix (Fin s) (Fin n) ℝ)
    (hW : W.transpose * W = 1) (hRW : R.transpose * W = 0)
    (hBE : B.transpose * E = 0) :
    (W * E).transpose * Matrix.fromCols R (W * B) = 0 := by
  have hWR : W.transpose * R = 0 := by
    have h := congrArg Matrix.transpose hRW
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] using h
  have hEB : E.transpose * B = 0 := by
    have h := congrArg Matrix.transpose hBE
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] using h
  have hER : (W * E).transpose * R = 0 := by
    rw [Matrix.transpose_mul, Matrix.mul_assoc, hWR, Matrix.mul_zero]
  have hEV : (W * E).transpose * (W * B) = 0 := by
    rw [Matrix.transpose_mul]
    calc
      _ = E.transpose * (W.transpose * W) * B := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hW, Matrix.mul_one, hEB]
  rw [Matrix.mul_fromCols, hER, hEV, Matrix.fromCols_zero]

lemma cavityBaseFrame_spectral_sum {r d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Matrix (Fin r) ι ℝ) (V : Matrix (Fin r) (Fin d) ℝ)
    (lam : ι → ℝ) (lam₀ : Fin d → ℝ) :
    Matrix.fromCols R V * Matrix.diagonal (Sum.elim lam lam₀) *
      (Matrix.fromCols R V).transpose =
        R * Matrix.diagonal lam * R.transpose + V * Matrix.diagonal lam₀ * V.transpose := by
  rw [← Matrix.fromBlocks_diagonal, Matrix.fromCols_mul_fromBlocks, Matrix.transpose_fromCols]
  simp only [Matrix.mul_zero, add_zero, zero_add,
    Matrix.fromCols_mul_fromRows]

def cavityReservoirRows {N n : ℕ} {ι : Type*}
    (F : Matrix (Fin (N + n)) ι ℝ) : Matrix (Fin N) ι ℝ :=
  fun i j => F (i.castAdd n) j

lemma cavityReservoirRows_conjugate {N n : ℕ} {ι : Type*} [Fintype ι]
    (F : Matrix (Fin (N + n)) ι ℝ) (L : Matrix ι ι ℝ) :
    (F * L * F.transpose).submatrix (Fin.castAdd n) (Fin.castAdd n) =
      cavityReservoirRows F * L * (cavityReservoirRows F).transpose := by
  ext i j
  rfl

lemma cavityReservoirRows_gram {N n : ℕ} {ι : Type*} [Fintype ι]
    (F : Matrix (Fin (N + n)) ι ℝ)
    (hF : ∀ i : Fin n, ∀ j, F (Fin.natAdd N i) j = 0) :
    (cavityReservoirRows F).transpose * cavityReservoirRows F = F.transpose * F := by
  ext i j
  change (∑ k : Fin N, F (k.castAdd n) i * F (k.castAdd n) j) =
    ∑ k : Fin (N + n), F k i * F k j
  rw [Fin.sum_univ_add]
  simp only [hF, zero_mul, Finset.sum_const_zero, add_zero]

lemma cavityReservoirRows_orthogonal {N n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι ≃ Fin N) (F : Matrix (Fin (N + n)) ι ℝ)
    (hG : F.transpose * F = 1)
    (hF : ∀ i : Fin n, ∀ j, F (Fin.natAdd N i) j = 0) :
    ∃ U : Orthogonal N, ∀ i j, (U : Matrix (Fin N) (Fin N) ℝ) i j =
      cavityReservoirRows F i (e.symm j) := by
  let A : Matrix (Fin N) (Fin N) ℝ := fun i j => cavityReservoirRows F i (e.symm j)
  have hA : A.transpose * A = 1 := by
    ext i j
    have hh := congrArg (fun M : Matrix ι ι ℝ => M (e.symm i) (e.symm j))
      ((cavityReservoirRows_gram F hF).trans hG)
    change (∑ k : Fin N, cavityReservoirRows F k (e.symm i) *
      cavityReservoirRows F k (e.symm j)) = if i = j then 1 else 0
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
      Equiv.apply_eq_iff_eq] using hh
  exact ⟨⟨A, (Matrix.mem_orthogonalGroup_iff' (Fin N) ℝ).mpr hA⟩, fun _ _ => rfl⟩

lemma cavityPhysicalFrame_lastRows {N n : ℕ} {ι : Type*} [Fintype ι]
    (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ)
    (F : Matrix (Fin (N + n)) ι ℝ)
    (hF : (show Matrix (Fin (N + n)) (Fin n) ℝ from
      fun i j => U i (Fin.natAdd N j)).transpose * F = 0) :
    ∀ i : Fin n, ∀ j, (U.transpose * F) (Fin.natAdd N i) j = 0 := by
  intro i j
  exact congrArg (fun M : Matrix (Fin n) ι ℝ => M i j) hF

lemma cavityPhysicalFrame_gram {r : ℕ} {ι : Type*} [Fintype ι]
    (U : Orthogonal r) (F : Matrix (Fin r) ι ℝ) :
    ((U : Matrix (Fin r) (Fin r) ℝ).transpose * F).transpose *
      ((U : Matrix (Fin r) (Fin r) ℝ).transpose * F) = F.transpose * F := by
  have hU : (U : Matrix (Fin r) (Fin r) ℝ) *
      (U : Matrix (Fin r) (Fin r) ℝ).transpose = 1 :=
    (Matrix.mem_orthogonalGroup_iff (Fin r) ℝ).mp U.property
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  calc
    _ = F.transpose * ((U : Matrix (Fin r) (Fin r) ℝ) *
        (U : Matrix (Fin r) (Fin r) ℝ).transpose) * F := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hU, Matrix.mul_one]

lemma cavityReservoir_spectral_orbit {N n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι ≃ Fin N) (F : Matrix (Fin (N + n)) ι ℝ) (lam : ι → ℝ)
    (hG : F.transpose * F = 1)
    (hF : ∀ i : Fin n, ∀ j, F (Fin.natAdd N i) j = 0) :
    ∃ U : Orthogonal N,
      cavityReservoirRows F * Matrix.diagonal lam * (cavityReservoirRows F).transpose =
        (U : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal (fun j => lam (e.symm j)) *
          (U : Matrix (Fin N) (Fin N) ℝ).transpose := by
  obtain ⟨U, hU⟩ := cavityReservoirRows_orthogonal e F hG hF
  refine ⟨U, ?_⟩
  ext i j
  change (∑ k : ι, (∑ t : ι, cavityReservoirRows F i t *
      (if t = k then lam t else 0)) * cavityReservoirRows F j k) =
    ∑ k : Fin N, (∑ t : Fin N, (U : Matrix (Fin N) (Fin N) ℝ) i t *
      (if t = k then lam (e.symm t) else 0)) * (U : Matrix (Fin N) (Fin N) ℝ) j k
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, hU]
  exact (Equiv.sum_comp e.symm (fun k : ι =>
    cavityReservoirRows F i k * lam k * cavityReservoirRows F j k)).symm

theorem cavityBaseReplacement_physical_orbit {N n s d : ℕ} {ι : Type*}
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
            (V : Matrix (Fin N) (Fin N) ℝ).transpose := by
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
  obtain ⟨V, hV⟩ := cavityReservoir_spectral_orbit e P (Sum.elim lam lam₀) hPG hPF
  refine ⟨V, ?_⟩
  rw [hP, cavityReservoirRows_conjugate]
  exact hV

end InvariantIsing

end

end OAI
