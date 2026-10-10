import OAI.Analysis.KadisonKastler.RegularCoreBasis
import OAI.Analysis.KadisonKastler.RegularCoreGap
import OAI.Analysis.KadisonKastler.CanonicalAmplificationGap

namespace OAI

/-! # Complete matrix bounds control the regular tensor gap

The scalar Hilbert coordinates identify the actual regular tensor algebra
with the canonical countable amplification. Uniform finite-matrix
approximation, or actual common countable matrix units, therefore bounds
its gap. No ordinary-gap amplification principle is assumed.
-/

namespace KadisonKastler

open MeasureTheory
open scoped Topology CStarAlgebra

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem spatialTransportAlgebra_commutant (e : H ≃ₗᵢ[ℂ] K)
    (M : VonNeumannAlgebra H) :
    (spatialTransportAlgebra e M).commutant = spatialTransportAlgebra e M.commutant := by
  apply SetLike.coe_injective
  rw [VonNeumannAlgebra.coe_commutant]
  change Set.centralizer (e.conjStarAlgEquiv '' (M : Set (H →L[ℂ] H))) =
    e.conjStarAlgEquiv '' (M.commutant : Set (H →L[ℂ] H))
  rw [VonNeumannAlgebra.coe_commutant]
  exact centralizer_image_spatial e _

theorem mem_canonicalAmplifiedAlgebra_iff (M : VonNeumannAlgebra H)
    (T : CountableHilbertSum H →L[ℂ] CountableHilbertSum H) :
    T ∈ canonicalAmplifiedAlgebra H M ↔
      ∀ S ∈ M.commutant, l2Diagonal S * T = T * l2Diagonal S := by
  change T ∈ (canonicalMatrixCorner H).amplifiedAlgebra (canonicalCornerAlgebra H M) ↔ _
  rw [(canonicalMatrixCorner H).mem_amplifiedAlgebra_iff_commute]
  change (∀ S ∈ (spatialTransportAlgebra (canonicalInitialEquiv H) M).commutant,
    Commute ((canonicalMatrixCorner H).inflateHom S) T) ↔ _
  rw [spatialTransportAlgebra_commutant]
  constructor
  · intro h S hS
    have hh := h ((canonicalInitialEquiv H).conjStarAlgEquiv S) ⟨S, hS, rfl⟩
    simpa only [canonicalMatrixCorner_inflate] using hh.eq
  · rintro h S ⟨R, hR, rfl⟩
    change (canonicalMatrixCorner H).inflateHom ((canonicalInitialEquiv H).conjStarAlgEquiv R) * T =
      T * (canonicalMatrixCorner H).inflateHom ((canonicalInitialEquiv H).conjStarAlgEquiv R)
    simpa only [canonicalMatrixCorner_inflate] using h R hR

/-- The actual regular tensor algebra in scalar Hilbert coordinates. -/
theorem spatialTransport_regularTensorAlgebra (M : VonNeumannAlgebra H) :
    spatialTransportAlgebra (regularHilbertCoordinates (H := H) regularScalarBasis)
      (regularTensorAlgebra M) = canonicalAmplifiedAlgebra H M := by
  let e := regularHilbertCoordinates (H := H) regularScalarBasis
  have hc (S : H →L[ℂ] H) : e.conjStarAlgEquiv
      (regularConstantHom (volume : Measure ℝ) S) = l2Diagonal S :=
    regularHilbertCoordinates_constant regularScalarBasis S
  ext T
  rw [mem_spatialTransportAlgebra, mem_regularTensorAlgebra_iff,
    mem_canonicalAmplifiedAlgebra_iff]
  constructor
  · intro h S hS
    have he := congrArg e.conjStarAlgEquiv (h S hS)
    rw [map_mul, map_mul] at he
    change e.conjStarAlgEquiv ((regularConstantHom volume) S) *
        e.conjStarAlgEquiv (e.conjStarAlgEquiv.symm T) =
      e.conjStarAlgEquiv (e.conjStarAlgEquiv.symm T) *
        e.conjStarAlgEquiv ((regularConstantHom volume) S) at he
    rwa [hc, e.conjStarAlgEquiv.apply_symm_apply] at he
  · intro h S hS
    apply e.conjStarAlgEquiv.injective
    rw [map_mul, map_mul]
    change e.conjStarAlgEquiv ((regularConstantHom volume) S) *
        e.conjStarAlgEquiv (e.conjStarAlgEquiv.symm T) =
      e.conjStarAlgEquiv (e.conjStarAlgEquiv.symm T) *
        e.conjStarAlgEquiv ((regularConstantHom volume) S)
    rw [hc, e.conjStarAlgEquiv.apply_symm_apply]
    exact h S hS

/-- The regular tensor gap is exactly the canonical amplification gap. -/
theorem kkDistance_regularTensorAlgebra (M N : VonNeumannAlgebra H) :
    kkDistance (regularTensorAlgebra M) (regularTensorAlgebra N) =
      kkDistance (canonicalAmplifiedAlgebra H M) (canonicalAmplifiedAlgebra H N) := by
  rw [← spatialTransport_regularTensorAlgebra M, ← spatialTransport_regularTensorAlgebra N]
  exact (kkDistance_spatialTransportAlgebra
    (regularHilbertCoordinates (H := H) regularScalarBasis) _ _).symm

local instance regularTensorGapOrder {J : Type*} [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] : PartialOrder (J →L[ℂ] J) :=
  CStarAlgebra.spectralOrder _
local instance regularTensorGapStarOrder {J : Type*} [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] : StarOrderedRing (J →L[ℂ] J) :=
  CStarAlgebra.spectralOrderedRing _

/-- Finite-matrix approximation transports across an actual Hilbert isometry. -/
theorem matrixApprox_spatialTransport (e : H ≃ₗᵢ[ℂ] K)
    (M N : VonNeumannAlgebra H) {r : ℝ}
    (hnear : ∀ (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H)),
      (∀ i j, X i j ∈ M) → ‖X‖ ≤ 1 →
      ∃ Y : CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H),
        (∀ i j, Y i j ∈ N) ∧ ‖Y‖ ≤ 1 ∧ ‖X - Y‖ ≤ r)
    (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) (K →L[ℂ] K))
    (hX : ∀ i j, X i j ∈ spatialTransportAlgebra e M) (hn : ‖X‖ ≤ 1) :
    ∃ Y : CStarMatrix (Fin n) (Fin n) (K →L[ℂ] K),
      (∀ i j, Y i j ∈ spatialTransportAlgebra e N) ∧ ‖Y‖ ≤ 1 ∧ ‖X - Y‖ ≤ r := by
  let φ := e.conjStarAlgEquiv.toStarAlgHom
  let ψ := e.conjStarAlgEquiv.symm.toStarAlgHom
  let X₀ := CStarMatrix.mapₗ ψ.toAlgHom.toLinearMap X
  have hX₀ : ∀ i j, X₀ i j ∈ M := fun i j =>
    (mem_spatialTransportAlgebra e M (X i j)).mp (hX i j)
  have hX₀n : ‖X₀‖ ≤ 1 :=
    (injective_starAlgHom_matrix_norm ψ e.conjStarAlgEquiv.symm.injective X).le.trans hn
  obtain ⟨Y₀, hY₀, hY₀n, hclose⟩ := hnear n X₀ hX₀ hX₀n
  refine ⟨CStarMatrix.mapₗ φ.toAlgHom.toLinearMap Y₀, ?_, ?_, ?_⟩
  · intro i j
    exact ⟨Y₀ i j, hY₀ i j, rfl⟩
  · exact (injective_starAlgHom_matrix_norm φ e.conjStarAlgEquiv.injective Y₀).le.trans hY₀n
  · have he : X = CStarMatrix.mapₗ φ.toAlgHom.toLinearMap X₀ := by
      apply Matrix.ext
      intro i j
      change X i j = e.conjStarAlgEquiv (e.conjStarAlgEquiv.symm (X i j))
      exact (e.conjStarAlgEquiv.apply_symm_apply (X i j)).symm
    rw [he, ← map_sub]
    exact (injective_starAlgHom_matrix_norm φ e.conjStarAlgEquiv.injective (X₀ - Y₀)).le.trans
      hclose

/-- Two-sided complete matrix approximation controls the regular tensor gap. -/
theorem kkDistance_regularTensorAlgebra_le_of_matrix_approx
    (M N : VonNeumannAlgebra H) {r : ℝ} (hr : 0 ≤ r)
    (hMN : ∀ (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H)),
      (∀ i j, X i j ∈ M) → ‖X‖ ≤ 1 →
      ∃ Y : CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H),
        (∀ i j, Y i j ∈ N) ∧ ‖Y‖ ≤ 1 ∧ ‖X - Y‖ ≤ r)
    (hNM : ∀ (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H)),
      (∀ i j, X i j ∈ N) → ‖X‖ ≤ 1 →
      ∃ Y : CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H),
        (∀ i j, Y i j ∈ M) ∧ ‖Y‖ ≤ 1 ∧ ‖X - Y‖ ≤ r) :
    kkDistance (regularTensorAlgebra M) (regularTensorAlgebra N) ≤ r := by
  rw [kkDistance_regularTensorAlgebra]
  apply Metric.hausdorffDist_le_of_mem_dist hr
  · intro T hT
    obtain ⟨S, hS, hn⟩ := (canonicalMatrixCorner H).exists_amplified_approx_of_matrix_approx
      (canonicalCornerAlgebra H M) (canonicalCornerAlgebra H N) hr
      (matrixApprox_spatialTransport (canonicalInitialEquiv H) M N hMN) T hT
    exact ⟨S, hS, by simpa only [dist_eq_norm] using hn⟩
  · intro T hT
    obtain ⟨S, hS, hn⟩ := (canonicalMatrixCorner H).exists_amplified_approx_of_matrix_approx
      (canonicalCornerAlgebra H N) (canonicalCornerAlgebra H M) hr
      (matrixApprox_spatialTransport (canonicalInitialEquiv H) N M hNM) T hT
    exact ⟨S, hS, by simpa only [dist_eq_norm] using hn⟩

/-- Actual common matrix units are sufficient for the tensor gap bound. -/
theorem kkDistance_regularTensorAlgebra_le_of_common_matrix_units
    (M N : VonNeumannAlgebra H) (D : Submodule ℂ H) [CompleteSpace D]
    (F : FullMatrixCorner D) (hM : ∀ i j, F.entry i j ∈ M)
    (hN : ∀ i j, F.entry i j ∈ N) :
    kkDistance (regularTensorAlgebra M) (regularTensorAlgebra N) ≤ kkDistance M N := by
  rw [kkDistance_regularTensorAlgebra]
  exact kkDistance_canonicalAmplifiedAlgebra_le_of_common_matrix_units M N F hM hN

end

end KadisonKastler

end OAI
