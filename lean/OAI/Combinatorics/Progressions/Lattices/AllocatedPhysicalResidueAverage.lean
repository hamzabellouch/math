import OAI.Combinatorics.Progressions.Probability.AllocatedPhysicalPointMixture
import OAI.Combinatorics.Progressions.Probability.WeightedSupportedComplexMixture

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]

variable (q : ℕ) [NeZero q] (hq : 0 < q)
variable (hsize : (Fintype.card α + 1) * q ≤ S.value)
variable (j : Fin m) (i : Fin (n j))
variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
variable (rows : Finset (Finset α)) (x : G → IntegerScalarCubeBox α S.value)

local notation "tuples" => principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)
local notation "axisLaw" => fun y => integerMatrixImagePMF (boundedCoefficientJetMatrix
  (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
  (allocatedPhysicalCubeDirections B U basis S x y) (j.val + 1)
  (fun t : rows => (t : Finset α))) (allocatedLayerIntegerPMFs B U basis hR hσ S j i)
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "torus" => blockTorusFactor (Fintype.card α) (j.val + 1)
  (Fintype.card (B (Sigma.mk j (Sum.inr i)))) (4 * gamma)

theorem allocatedPhysicalResiduePoint_test_error
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ)
    (hcP : scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    {ε : ℝ} {M : ℕ} [NeZero M] (hM : M = torus * basisAxisScale (basis j) i)
    (hrows : ∀ t ∈ rows, t.card ≤ j.val + 1)
    (hB : positiveModerateSpectrumBlockCount j.val rows.card
      ((layerTailDegree m + 1) * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (test : (PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q) → ℂ)
    (htest : ∀ r, ‖test r‖ ≤ 1) (z : rows → ℤ) :
    ‖(tuples).complexMean (fun y => test (principalResidueLabel q y) *
        (((basisAxisScale (basis j) i : ℝ) ^ rows.card * ((axisLaw y) z).toReal : ℝ) : ℂ)) -
      ((tuples).fiberLaw (principalResidueLabel q)).complexMean (fun r => test r *
        allocatedSupportedPhysicalPointApproximation B U basis hR hσ S q r j i hactive hq hsize
          P ε M rows z)‖ ≤ ε := by
  apply (tuples).complexMean_supported_fiber_mul_error (principalResidueLabel q)
    _ _ test hε.le htest
  intro r hr
  have hc := ((tuples).condition
      (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hr).toPMF_bind_scaled_complexMean
    (axisLaw) ((basisAxisScale (basis j) i : ℝ) ^ rows.card) z
  have he := allocatedSupportedPhysicalPointApproximation_error B U basis hR hσ S q r hr j i
    hactive hq hsize hgrid A hA P hcP hsP hM rows hrows hB hε hε1 x z
  exact (congrArg (fun w : ℂ => ‖w -
    allocatedSupportedPhysicalPointApproximation B U basis hR hσ S q r j i hactive hq hsize
      P ε M rows z‖) hc).trans_le he

theorem allocatedPhysicalResiduePoint_mass_error
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ)
    (hcP : scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    {ε : ℝ} {M : ℕ} [NeZero M] (hM : M = torus * basisAxisScale (basis j) i)
    (hrows : ∀ t ∈ rows, t.card ≤ j.val + 1)
    (hB : positiveModerateSpectrumBlockCount j.val rows.card
      ((layerTailDegree m + 1) * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (hε : 0 < ε) (hε1 : ε ≤ 1) (z : rows → ℤ) :
    ‖(((basisAxisScale (basis j) i : ℝ) ^ rows.card *
        (((tuples).toPMF.bind (axisLaw)) z).toReal : ℝ) : ℂ) -
      ((tuples).fiberLaw (principalResidueLabel q)).complexMean (fun r =>
        allocatedSupportedPhysicalPointApproximation B U basis hR hσ S q r j i hactive hq hsize
          P ε M rows z)‖ ≤ ε := by
  have h := allocatedPhysicalResiduePoint_test_error B U basis hR hσ S q hq hsize j i hactive rows x
    hgrid A hA P hcP hsP hM hrows hB hε hε1 (fun _ => 1) (fun _ => by simp) z
  simp only [one_mul] at h
  rw [(tuples).toPMF_bind_scaled_complexMean] at h
  exact h

end Erdos3.VectorPolynomial

end

end OAI
