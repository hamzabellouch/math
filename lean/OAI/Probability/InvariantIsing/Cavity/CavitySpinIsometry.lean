import OAI.Probability.InvariantIsing.Spectral.SpectralPermutation
import OAI.Probability.InvariantIsing.Cavity.CavityActualCovariance

namespace OAI

/-! Signed site permutations act on the actual Ising cube and its
projected overlaps. Their pair-spin observables have no sign factor. -/

noncomputable section
open IsingPerceptron
open scoped BigOperators Matrix

namespace InvariantIsing

@[simp] lemma spinValue_not (b : Bool) : spinValue (!b) = -spinValue b := by
  cases b <;> norm_num [spinValue]

def cavitySignedSpinPermutation {N : ℕ} (p : Equiv.Perm (Fin N))
    (flip : Fin N → Bool) : Equiv.Perm (Spin N) where
  toFun σ i := if flip i then !(σ (p i)) else σ (p i)
  invFun σ i := if flip (p.symm i) then !(σ (p.symm i)) else σ (p.symm i)
  left_inv σ := by
    funext i
    cases h : flip (p.symm i) <;> simp_all
  right_inv σ := by
    funext i
    cases h : flip i <;> simp_all

lemma cavitySignedSpinPermutation_pair {N : ℕ} (p : Equiv.Perm (Fin N))
    (flip : Fin N → Bool) (σ τ : Spin N) (i : Fin N) :
    spinValue (cavitySignedSpinPermutation p flip σ i) *
      spinValue (cavitySignedSpinPermutation p flip τ i) =
        spinValue (σ (p i)) * spinValue (τ (p i)) := by
  change spinValue (if flip i then _ else _) * spinValue (if flip i then _ else _) = _
  cases h : flip i <;> simp_all

def cavityPermutationFlip {N : ℕ} (hN : 0 < N) (p : Equiv.Perm (Fin N))
    (i : Fin N) : Bool := decide (i = ⟨0, hN⟩ ∧ (p.permMatrix ℝ).det = -1)

lemma cavityPermutationSpin_vector {N : ℕ} (hN : 0 < N)
    (p : Equiv.Perm (Fin N)) (σ : Spin N) :
    spinVector (cavitySignedSpinPermutation p (cavityPermutationFlip hN p) σ) =
      specialRotation (spectralPermutation hN p) (spinVector σ) := by
  ext i
  change spinValue (if cavityPermutationFlip hN p i then !(σ (p i)) else σ (p i)) =
    ((permutationSignDiagonal hN p * p.permMatrix ℝ) *ᵥ (spinVector σ).ofLp) i
  rw [← Matrix.mulVec_mulVec, Matrix.permMatrix_mulVec]
  simp only [permutationSignDiagonal, Matrix.mulVec_diagonal, Function.comp_apply,
    spinVector_apply]
  have hd := orthogonal_det_eq_one_or_neg_one
    (⟨p.permMatrix ℝ, permutationMatrix_orthogonal p⟩ : Orthogonal N)
  rcases hd with hd | hd <;> change (p.permMatrix ℝ).det = _ at hd
  · norm_num [cavityPermutationFlip, hd]
  · by_cases hi : i = (⟨0, hN⟩ : Fin N) <;> simp [cavityPermutationFlip, hd, hi]

lemma cavity_specialRotation_mul_apply {N : ℕ} (U V : SpecialOrthogonal N)
    (x : EuclideanSpace ℝ (Fin N)) :
    specialRotation (U * V) x = specialRotation U (specialRotation V x) := by
  ext i
  change (((U : Matrix (Fin N) (Fin N) ℝ) * (V : Matrix (Fin N) (Fin N) ℝ)) *ᵥ x.ofLp) i =
    ((U : Matrix (Fin N) (Fin N) ℝ) *ᵥ ((V : Matrix (Fin N) (Fin N) ℝ) *ᵥ x.ofLp)) i
  rw [Matrix.mulVec_mulVec]

lemma cavityPermutationSpin_cancel {N : ℕ} (hN : 0 < N)
    (p : Equiv.Perm (Fin N)) (U : SpecialOrthogonal N) (σ : Spin N) :
    specialRotation (U * (spectralPermutation hN p)⁻¹)
      (spinVector (cavitySignedSpinPermutation p (cavityPermutationFlip hN p) σ)) =
        specialRotation U (spinVector σ) := by
  rw [cavityPermutationSpin_vector, ← cavity_specialRotation_mul_apply]
  simp only [inv_mul_cancel_right]

lemma projectedOverlap_cavityPermutation {N : ℕ} (hN : 0 < N)
    (p : Equiv.Perm (Fin N)) (U : SpecialOrthogonal N)
    (I : Finset (Fin N)) (σ τ : Spin N) :
    projectedOverlap (specialRotation (U * (spectralPermutation hN p)⁻¹)) I
      (cavitySignedSpinPermutation p (cavityPermutationFlip hN p) σ)
      (cavitySignedSpinPermutation p (cavityPermutationFlip hN p) τ) =
        projectedOverlap (specialRotation U) I σ τ := by
  simp only [projectedOverlap, cavityPermutationSpin_cancel]

lemma rotatedEnergy_cavityPermutation {N : ℕ} (hN : 0 < N)
    (p : Equiv.Perm (Fin N)) (eig : Fin N → ℝ) (U : SpecialOrthogonal N) (σ : Spin N) :
    rotatedEnergy eig (specialRotation (U * (spectralPermutation hN p)⁻¹))
      (cavitySignedSpinPermutation p (cavityPermutationFlip hN p) σ) =
        rotatedEnergy eig (specialRotation U) σ := by
  simp only [rotatedEnergy, cavityPermutationSpin_cancel]

lemma projectedOverlap_spin_isometry {N : ℕ} (U V : Rotation N)
    (e : Spin N → Spin N) (he : ∀ σ, spinVector (e σ) = V (spinVector σ))
    (I : Finset (Fin N)) (σ τ : Spin N) :
    projectedOverlap U I (e σ) (e τ) =
      projectedOverlap (V.trans U) I σ τ := by
  simp only [projectedOverlap, he, LinearIsometryEquiv.trans_apply]

lemma rotatedEnergy_spin_isometry {N : ℕ} (U V : Rotation N)
    (e : Spin N → Spin N) (he : ∀ σ, spinVector (e σ) = V (spinVector σ))
    (eig : Fin N → ℝ) (σ : Spin N) :
    rotatedEnergy eig U (e σ) = rotatedEnergy eig (V.trans U) σ := by
  simp only [rotatedEnergy, he, LinearIsometryEquiv.trans_apply]

lemma cavityPerturbationCovariance_spin_isometry {N m depth : ℕ}
    (U V : Rotation N) (e : Spin N → Spin N)
    (he : ∀ σ, spinVector (e σ) = V (spinVector σ))
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (x y : Spin N × LabeledLeaf depth) :
    cylinderCross (cavityPerturbationCoefficients U I u depth (e x.1, x.2))
      (cavityPerturbationCoefficients U I u depth (e y.1, y.2)) =
    cylinderCross (cavityPerturbationCoefficients (V.trans U) I u depth x)
      (cavityPerturbationCoefficients (V.trans U) I u depth y) := by
  simp only [cavityPerturbationCoefficients_cross, cavityWeightedKernel,
    cavityPerturbationKernel, projectedOverlap_spin_isometry U V e he]

end InvariantIsing

end

end OAI
