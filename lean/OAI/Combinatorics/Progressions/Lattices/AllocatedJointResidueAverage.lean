import OAI.Combinatorics.Progressions.Estimates.AllocatedJointPointApproximation

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
variable (q : ℕ) [NeZero q]

local notation "tuples" => principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)

variable {A : Type*} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (rows : A → Finset (Finset α)) (x : G → IntegerScalarCubeBox α S.value)

variable (P : ℝ)

local notation "axisK" => fun a : A => basisAxisScale (basis (Sigma.fst (selected a))) (Sigma.snd (selected a))
local notation "axisGamma" => fun a : A => principalProfileSize (R (Sigma.fst (selected a)))
  (Finset.card (layerIntegerPrincipalSlots (G := G) B (Sigma.fst (selected a)) (Sigma.snd (selected a))))
local notation "axisTorus" => fun a : A => blockTorusFactor (Fintype.card α) ((Fin.val (Sigma.fst (selected a))) + 1)
  (Fintype.card (B (Sigma.mk (Sigma.fst (selected a)) (Sum.inr (Sigma.snd (selected a)))))) (4 * (axisGamma) a)
local notation "axisCap" => fun a : A => positiveModerateSpectrumCardBudget (Fin.val (Sigma.fst (selected a)))
  (Finset.card (rows a)) ((layerTailDegree m + 1) * (Finset.card (rows a))) P
  (((axisTorus) a : ℝ) / (2 * (axisGamma) a)) (((axisTorus) a : ℝ) ^ (Finset.card (rows a))) 1 + 1

local notation "jointLaw" => fun y => dependentProductPMF (fun a =>
  integerMatrixImagePMF (boundedCoefficientJetMatrix
    (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
    (allocatedPhysicalCubeDirections B U basis S x y) ((Fin.val (Sigma.fst (selected a))) + 1)
    (fun t : rows a => (t : Finset α)))
    (allocatedLayerIntegerPMFs B U basis hR hσ S (Sigma.fst (selected a)) (Sigma.snd (selected a))))

theorem allocatedJointResiduePoint_test_error
    (hselected : Function.Injective selected)
    (hgrid : ∀ a, allocatedGridAxis (I := I) U basis S.value
      ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (hactive : ∀ a, S.value ^ ((selected a).1.val + 1) < (axisK) a)
    (hq : 0 < q) (hsize : (Fintype.card α + 1) * q ≤ S.value)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hcP : scalarCubePrimitiveEnvelope Empty L 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α L 1 0 q ≤ P)
    (M : A → ℕ) [∀ a, NeZero (M a)] (hM : ∀ a, M a = (axisTorus) a * (axisK) a)
    (hrows : ∀ a t, t ∈ rows a → t.card ≤ (selected a).1.val + 1)
    (hB : ∀ a, positiveModerateSpectrumBlockCount (selected a).1.val (rows a).card
      ((layerTailDegree m + 1) * (rows a).card) ≤
        Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (test : (PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q) → ℂ)
    (htest : ∀ r, ‖test r‖ ≤ 1) (z : ∀ a, rows a → ℤ) :
    let C := ∑ a, (axisCap) a
    ‖(tuples).complexMean (fun y => test (principalResidueLabel q y) *
        (((∏ a, ((axisK) a : ℝ) ^ (rows a).card) * ((jointLaw y) z).toReal : ℝ) : ℂ)) -
      ((tuples).fiberLaw (principalResidueLabel q)).complexMean (fun r => test r *
        ∏ a, allocatedSupportedPhysicalPointApproximation B U basis hR hσ S q r
          (selected a).1 (selected a).2 (hactive a) hq hsize P ε (M a) (rows a) (z a))‖ ≤
      Fintype.card A * ε * (1 + C + ε) ^ Fintype.card A := by
  intro C
  have hC0 : 0 ≤ C := by
    apply Finset.sum_nonneg
    intro a _
    have hc := allocatedSupportedPhysicalPointApproximation_norm_le B U basis hR hσ S q
      (fun _ _ => 0) (selected a).1 (selected a).2 (hactive a) hq hsize (hgrid a)
      L hL P hcP hsP (hM a) (rows a) (hrows a) (hB a) ε (z a)
    exact (norm_nonneg _).trans hc
  have hE : 0 ≤ (Fintype.card A : ℝ) * ε * (1 + C + ε) ^ Fintype.card A := by positivity
  apply (tuples).complexMean_supported_fiber_mul_error (principalResidueLabel q) _ _ test hE htest
  intro r hr
  have hc := ((tuples).condition
      (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hr).toPMF_bind_scaled_complexMean
    (jointLaw) (∏ a, ((axisK) a : ℝ) ^ (rows a).card) z
  have he := allocatedSupportedJointPoint_error B U basis hR hσ S q r hr selected rows x P
    hselected hgrid hactive hq hsize L hL hcP hsP M hM hrows hB hε hε1 z
  exact (congrArg (fun w : ℂ => ‖w -
    ∏ a, allocatedSupportedPhysicalPointApproximation B U basis hR hσ S q r
      (selected a).1 (selected a).2 (hactive a) hq hsize P ε (M a) (rows a) (z a)‖) hc).trans_le he

theorem allocatedJointResiduePoint_mass_error
    (hselected : Function.Injective selected)
    (hgrid : ∀ a, allocatedGridAxis (I := I) U basis S.value
      ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (hactive : ∀ a, S.value ^ ((selected a).1.val + 1) < (axisK) a)
    (hq : 0 < q) (hsize : (Fintype.card α + 1) * q ≤ S.value)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hcP : scalarCubePrimitiveEnvelope Empty L 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α L 1 0 q ≤ P)
    (M : A → ℕ) [∀ a, NeZero (M a)] (hM : ∀ a, M a = (axisTorus) a * (axisK) a)
    (hrows : ∀ a t, t ∈ rows a → t.card ≤ (selected a).1.val + 1)
    (hB : ∀ a, positiveModerateSpectrumBlockCount (selected a).1.val (rows a).card
      ((layerTailDegree m + 1) * (rows a).card) ≤
        Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (z : ∀ a, rows a → ℤ) :
    let C := ∑ a, (axisCap) a
    ‖(((∏ a, ((axisK) a : ℝ) ^ (rows a).card) *
        (((tuples).toPMF.bind (jointLaw)) z).toReal : ℝ) : ℂ) -
      ((tuples).fiberLaw (principalResidueLabel q)).complexMean (fun r =>
        ∏ a, allocatedSupportedPhysicalPointApproximation B U basis hR hσ S q r
          (selected a).1 (selected a).2 (hactive a) hq hsize P ε (M a) (rows a) (z a))‖ ≤
      Fintype.card A * ε * (1 + C + ε) ^ Fintype.card A := by
  intro C
  have h := allocatedJointResiduePoint_test_error B U basis hR hσ S q selected rows x P
    hselected hgrid hactive hq hsize L hL hcP hsP M hM hrows hB hε hε1
    (fun _ => 1) (fun _ => by simp) z
  simp only [one_mul] at h
  rw [(tuples).toPMF_bind_scaled_complexMean] at h
  exact h

end Erdos3.VectorPolynomial

end

end OAI
