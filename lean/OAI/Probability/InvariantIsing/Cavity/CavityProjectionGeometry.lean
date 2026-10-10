import OAI.Probability.InvariantIsing.Cavity.CavityProjectionControl
import OAI.Probability.InvariantIsing.Cavity.CavityPhysicalBase
import OAI.Probability.InvariantIsing.Cavity.CavityPhysicalProjection

namespace OAI

/-! The unnormalized cavity-column projections are precisely physical
spectral projections at the added sites. -/

noncomputable section
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

def cavitySpecialOrthogonal {N : ℕ} (U : SpecialOrthogonal N) : Orthogonal N :=
  ⟨U.val, (Matrix.mem_specialOrthogonalGroup_iff.mp U.property).1⟩

def cavitySpectralGroup {N m : ℕ} (g : Fin N → Fin m) (a : Fin m) : Finset (Fin N) :=
  Finset.univ.filter (fun i => g i = a)

lemma cavity_spectral_image_projection {N n m : ℕ}
    (g : Fin (N + n) → Fin m) (U : SpecialOrthogonal (N + n))
    (x : EuclideanSpace ℝ (Fin (N + n))) (a : Fin m) (j : Fin n) :
    ((cavitySpectralImage g (cavityColumns (cavitySpecialOrthogonal U)) a).transpose *ᵥ
      (specialRotation U x).ofLp) j =
    cavitySpectralProjection (specialRotation U) (cavitySpectralGroup g a) x (Fin.natAdd N j) := by
  rw [cavitySpectralProjection, cavity_specialRotation_symm]
  change (∑ i : Fin (N + n),
    (if g i = a then (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ) i (Fin.natAdd N j) else 0) *
      specialRotation U x i) =
    ∑ i : Fin (N + n),
      (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ) i (Fin.natAdd N j) *
        (if i ∈ cavitySpectralGroup g a then specialRotation U x i else 0)
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : g i = a <;> simp [cavitySpectralGroup, hi]

def cavityFullSpecialCoordinates {N n m d : ℕ} (g : Fin (N + n) → Fin m)
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (U : SpecialOrthogonal (N + n))
    (σ : Spin (N + n)) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 ((cavityEigenspaceFrame
    (cavitySpectralImage g (cavityColumns (cavitySpecialOrthogonal U))) * B).transpose *ᵥ
      (specialRotation U (spinVector σ)).ofLp)

theorem cavity_full_special_coordinates_control {N n m d : ℕ}
    (g : Fin (N + n) → Fin m) (B : Matrix (Fin (m * n)) (Fin d) ℝ)
    (hB : B.transpose * B = 1) (U : SpecialOrthogonal (N + n))
    (σ : Spin (N + n)) {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ a, ‖(CFC.sqrt (cavityCompressionGrams g (cavitySpecialOrthogonal U) a))⁻¹‖ ≤ L) :
    ‖cavityFullSpecialCoordinates g B U σ‖ ^ 2 ≤ L ^ 2 *
      ∑ a, ∑ j : Fin n,
        (cavitySpectralProjection (specialRotation U) (cavitySpectralGroup g a)
          (spinVector σ) (Fin.natAdd N j)) ^ 2 := by
  have h := cavity_special_projection_control
    (cavitySpectralImage g (cavityColumns (cavitySpecialOrthogonal U))) B hB
    (specialRotation U (spinVector σ)) hL hbound
  simpa only [cavityFullSpecialCoordinates, EuclideanSpace.real_norm_sq_eq,
    PiLp.toLp_apply, cavity_spectral_image_projection] using h

end InvariantIsing

end

end OAI
