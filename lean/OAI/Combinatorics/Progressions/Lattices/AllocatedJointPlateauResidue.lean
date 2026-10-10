import OAI.Combinatorics.Progressions.Estimates.AllocatedJointWindowIntegral

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

variable (rowFamily : (Σ j : Fin m, Fin (n j)) → Finset (Finset α))
variable {A : Type*} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j)) (x : G → IntegerScalarCubeBox α S.value)
variable (P δ : ℝ)

local notation "rows" => fun a : A => rowFamily (selected a)
local notation "axisK" => fun a : A => basisAxisScale (basis (Sigma.fst (selected a))) (Sigma.snd (selected a))
local notation "axisN" => fun a : A => allocatedPrincipalGridScale (G := G) B U basis (R := R)
  (Sigma.fst (selected a)) (Sigma.snd (selected a))
local notation "axisGamma" => fun a : A => principalProfileSize (R (Sigma.fst (selected a)))
  (Finset.card (layerIntegerPrincipalSlots (G := G) B (Sigma.fst (selected a)) (Sigma.snd (selected a))))
local notation "accuracy" => allocatedGridFamilyAccuracy B rowFamily P δ

local notation "jointLaw" => fun y => dependentProductPMF (fun a : A =>
  integerMatrixImagePMF (boundedCoefficientJetMatrix
    (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
    (allocatedPhysicalCubeDirections B U basis S x y) ((Fin.val (Sigma.fst (selected a))) + 1)
    (fun t : (rows) a => (t : Finset α)))
    (allocatedLayerIntegerPMFs B U basis hR hσ S (Sigma.fst (selected a)) (Sigma.snd (selected a))))

theorem allocatedJointPlateau_residue_weighted_error
    (hP : 1 ≤ P) (hδ : 0 < δ) (hselected : Function.Injective selected)
    (hgrid : ∀ a, allocatedGridAxis (I := I) U basis S.value
      ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (hactive : ∀ a, S.value ^ ((selected a).1.val + 1) < (axisK) a)
    (hgamma : ∀ a, (axisGamma) a ≤ S.value)
    (hq : 0 < q) (hsize : (Fintype.card α + 1) * q ≤ S.value)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hcP : scalarCubePrimitiveEnvelope Empty L 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α L 1 0 q ≤ P)
    (M : A → ℕ) [∀ a, NeZero (M a)]
    (hM : ∀ a, M a = allocatedGridTorusFactor B α (selected a) * (axisN) a)
    (hrows : ∀ a t, t ∈ (rows) a → t.card ≤ (selected a).1.val + 1)
    (hB : ∀ a, positiveModerateSpectrumBlockCount (selected a).1.val ((rows) a).card
      ((layerTailDegree m + 2) * ((rows) a).card) ≤
        Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))
    (test : (PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q) → ℂ)
    (z : ∀ a, (rows) a → ℤ) :
    ‖(tuples).complexMean (fun y => test (principalResidueLabel q y) *
        (((∏ a, ((axisN) a : ℝ) ^ ((rows) a).card) * ((jointLaw y) z).toReal : ℝ) : ℂ)) -
      ((tuples).fiberLaw (principalResidueLabel q)).complexMean (fun r => test r *
        ∏ a, allocatedBudgetedPlateauApproximation B U basis hR hσ S q r
          (selected a).1 (selected a).2 (hactive a) hq hsize P accuracy (M a) ((rows) a) (z a))‖ ≤
      δ * ((tuples).fiberLaw (principalResidueLabel q)).mean (fun r => ‖test r‖) := by
  apply (tuples).complexMean_supported_fiber_weighted_error (principalResidueLabel q)
  intro r hr
  have hc := ((tuples).condition
      (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hr).toPMF_bind_scaled_complexMean
    (jointLaw) (∏ a, ((axisN) a : ℝ) ^ ((rows) a).card) z
  have he := allocatedJointPlateau_family_error B U basis hR hσ S q r hr rowFamily selected x P δ
    hP hδ hselected hgrid hactive hgamma hq hsize L hL hcP hsP M hM hrows hB z
  exact (congrArg (fun w : ℂ => ‖w -
    ∏ a, allocatedBudgetedPlateauApproximation B U basis hR hσ S q r
      (selected a).1 (selected a).2 (hactive a) hq hsize P accuracy (M a) ((rows) a) (z a)‖) hc).trans_le he

theorem allocatedJointPlateau_residue_test_error
    (hP : 1 ≤ P) (hδ : 0 < δ) (hselected : Function.Injective selected)
    (hgrid : ∀ a, allocatedGridAxis (I := I) U basis S.value
      ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (hactive : ∀ a, S.value ^ ((selected a).1.val + 1) < (axisK) a)
    (hgamma : ∀ a, (axisGamma) a ≤ S.value)
    (hq : 0 < q) (hsize : (Fintype.card α + 1) * q ≤ S.value)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hcP : scalarCubePrimitiveEnvelope Empty L 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α L 1 0 q ≤ P)
    (M : A → ℕ) [∀ a, NeZero (M a)]
    (hM : ∀ a, M a = allocatedGridTorusFactor B α (selected a) * (axisN) a)
    (hrows : ∀ a t, t ∈ (rows) a → t.card ≤ (selected a).1.val + 1)
    (hB : ∀ a, positiveModerateSpectrumBlockCount (selected a).1.val ((rows) a).card
      ((layerTailDegree m + 2) * ((rows) a).card) ≤
        Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))
    (test : (PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q) → ℂ)
    (htest : ∀ r, ‖test r‖ ≤ 1) (z : ∀ a, (rows) a → ℤ) :
    ‖(tuples).complexMean (fun y => test (principalResidueLabel q y) *
        (((∏ a, ((axisN) a : ℝ) ^ ((rows) a).card) * ((jointLaw y) z).toReal : ℝ) : ℂ)) -
      ((tuples).fiberLaw (principalResidueLabel q)).complexMean (fun r => test r *
        ∏ a, allocatedBudgetedPlateauApproximation B U basis hR hσ S q r
          (selected a).1 (selected a).2 (hactive a) hq hsize P accuracy (M a) ((rows) a) (z a))‖ ≤ δ := by
  have he := allocatedJointPlateau_residue_weighted_error B U basis hR hσ S q rowFamily selected x P δ
    hP hδ hselected hgrid hactive hgamma hq hsize L hL hcP hsP M hM hrows hB test z
  have hm : ((tuples).fiberLaw (principalResidueLabel q)).mean (fun r => ‖test r‖) ≤ 1 :=
    (((tuples).fiberLaw (principalResidueLabel q)).mean_mono htest).trans_eq
      (((tuples).fiberLaw (principalResidueLabel q)).mean_const 1)
  exact he.trans (mul_le_of_le_one_right hδ.le hm)

theorem allocatedJointPlateau_residue_mass_error
    (hP : 1 ≤ P) (hδ : 0 < δ) (hselected : Function.Injective selected)
    (hgrid : ∀ a, allocatedGridAxis (I := I) U basis S.value
      ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (hactive : ∀ a, S.value ^ ((selected a).1.val + 1) < (axisK) a)
    (hgamma : ∀ a, (axisGamma) a ≤ S.value)
    (hq : 0 < q) (hsize : (Fintype.card α + 1) * q ≤ S.value)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hcP : scalarCubePrimitiveEnvelope Empty L 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α L 1 0 q ≤ P)
    (M : A → ℕ) [∀ a, NeZero (M a)]
    (hM : ∀ a, M a = allocatedGridTorusFactor B α (selected a) * (axisN) a)
    (hrows : ∀ a t, t ∈ (rows) a → t.card ≤ (selected a).1.val + 1)
    (hB : ∀ a, positiveModerateSpectrumBlockCount (selected a).1.val ((rows) a).card
      ((layerTailDegree m + 2) * ((rows) a).card) ≤
        Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))
    (z : ∀ a, (rows) a → ℤ) :
    ‖(((∏ a, ((axisN) a : ℝ) ^ ((rows) a).card) *
        (((tuples).toPMF.bind (jointLaw)) z).toReal : ℝ) : ℂ) -
      ((tuples).fiberLaw (principalResidueLabel q)).complexMean (fun r =>
        ∏ a, allocatedBudgetedPlateauApproximation B U basis hR hσ S q r
          (selected a).1 (selected a).2 (hactive a) hq hsize P accuracy (M a) ((rows) a) (z a))‖ ≤ δ := by
  have he := allocatedJointPlateau_residue_test_error B U basis hR hσ S q rowFamily selected x P δ
    hP hδ hselected hgrid hactive hgamma hq hsize L hL hcP hsP M hM hrows hB
    (fun _ => 1) (fun _ => by simp) z
  simp only [one_mul] at he
  rw [(tuples).toPMF_bind_scaled_complexMean] at he
  exact he

end Erdos3.VectorPolynomial

end

end OAI
