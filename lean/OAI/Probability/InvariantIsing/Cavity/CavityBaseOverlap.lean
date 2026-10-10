import OAI.Probability.InvariantIsing.Cavity.CavityRetainedNorm
import OAI.Probability.InvariantIsing.Cavity.CavityConcreteFrameOrbit

namespace OAI

/-! A single physical base eigenframe identifies every retained group
overlap with the corresponding projected spin overlap. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

lemma cavity_physical_frame_coordinates {N n : ℕ} {ι : Type*} [Fintype ι]
    (e : ι ≃ Fin N) (U : SpecialOrthogonal (N + n))
    (F : Matrix (Fin (N + n)) ι ℝ)
    (hF : ∀ i : Fin n, ∀ j,
      ((U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ).transpose * F) (Fin.natAdd N i) j = 0)
    (V : Orthogonal N)
    (hV : ∀ i j, (V : Matrix (Fin N) (Fin N) ℝ) i j =
      cavityReservoirRows ((U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ).transpose * F)
        i (e.symm j))
    (σ : Spin (N + n)) (j : ι) :
    matrixRotation V⁻¹ (spinVector (fun i => σ (Fin.castAdd n i))) (e j) =
      (F.transpose *ᵥ (specialRotation U (spinVector σ)).ofLp) j := by
  let P := (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ).transpose * F
  have he : F.transpose *ᵥ (specialRotation U (spinVector σ)).ofLp =
      P.transpose *ᵥ (spinVector σ).ofLp := by
    change F.transpose *ᵥ ((U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ) *ᵥ
      (spinVector σ).ofLp) = _
    simp only [P, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mulVec_mulVec]
  rw [he]
  change (∑ i : Fin N, (V : Matrix (Fin N) (Fin N) ℝ) i (e j) *
    spinValue (σ (Fin.castAdd n i))) = ∑ i : Fin (N + n), P i j * spinValue (σ i)
  rw [Fin.sum_univ_add]
  simp only [hF, zero_mul, Finset.sum_const_zero, add_zero, hV,
    Equiv.symm_apply_apply, cavityReservoirRows, P]

def cavityBaseGroup {N m d : ℕ} (k : Fin m → ℕ)
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (a₀ : Fin d → Fin m) (a : Fin m) : Finset (Fin N) :=
  Finset.univ.filter (fun j => Sum.elim (fun v => v.1) a₀ (e.symm j) = a)

theorem cavity_base_group_overlap {N n m d : ℕ}
    (g : Fin (N + n) → Fin m) (U : SpecialOrthogonal (N + n))
    (B : Matrix (Fin (m * n)) (Fin d) ℝ)
    (k : Fin m → ℕ) (R : (a : Fin m) → Matrix (Fin (N + n)) (Fin (k a)) ℝ)
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (a₀ : Fin d → Fin m)
    (hF : ∀ i : Fin n, ∀ j,
      ((U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ).transpose *
        Matrix.fromCols (cavityRetainedStack k R)
          (cavityEigenspaceFrame (cavitySpectralImage g
            (cavityColumns (cavitySpecialOrthogonal U))) * B)) (Fin.natAdd N i) j = 0)
    (V : Orthogonal N)
    (hV : ∀ i j, (V : Matrix (Fin N) (Fin N) ℝ) i j =
      cavityReservoirRows ((U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ).transpose *
        Matrix.fromCols (cavityRetainedStack k R)
          (cavityEigenspaceFrame (cavitySpectralImage g
            (cavityColumns (cavitySpecialOrthogonal U))) * B)) i (e.symm j))
    (a : Fin m) (σ τ : Spin (N + n)) :
    projectedOverlap (matrixRotation V⁻¹) (cavityBaseGroup k e a₀ a)
      (fun i => σ (Fin.castAdd n i)) (fun i => τ (Fin.castAdd n i)) =
      cavityRetainedBaseOverlap g U B k R
        (fun a => Finset.univ.filter (fun j => a₀ j = a)) a σ τ := by
  let F := Matrix.fromCols (cavityRetainedStack k R)
    (cavityEigenspaceFrame (cavitySpectralImage g (cavityColumns (cavitySpecialOrthogonal U))) * B)
  let z := fun σ : Spin (N + n) => F.transpose *ᵥ (specialRotation U (spinVector σ)).ofLp
  have hc (σ : Spin (N + n)) (j) :
      matrixRotation V⁻¹ (spinVector (fun i => σ (Fin.castAdd n i))) (e j) = z σ j :=
    cavity_physical_frame_coordinates e U F hF V hV σ j
  have hr (σ : Spin (N + n)) (b : Fin m) (i : Fin (k b)) :
      z σ (Sum.inl ⟨b, i⟩) =
        ((R b).transpose *ᵥ (specialRotation U (spinVector σ)).ofLp) i := rfl
  have hy (σ : Spin (N + n)) (i : Fin d) :
      z σ (Sum.inr i) = cavityFullSpecialCoordinates g B U σ i := rfl
  rw [projectedOverlap, cavityBaseGroup, Finset.sum_filter]
  rw [← Equiv.sum_comp e]
  simp only [Equiv.symm_apply_apply, hc, Fintype.sum_sum_type, Fintype.sum_sigma,
    Sum.elim_inl, Sum.elim_inr, hr, hy]
  simp only [Finset.sum_ite_irrel]
  rw [cavityRetainedBaseOverlap, Finset.sum_filter, div_eq_inv_mul]
  simp only [Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, dotProduct]

end InvariantIsing

end

end OAI
