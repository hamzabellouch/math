import OAI.Combinatorics.Progressions.Linear.ContainedSupportedProgressionKernels

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

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
variable (q : ℕ)
variable (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable {A : Type*} [Fintype A] (j : A → Fin m) (i : ∀ a, Fin (n (j a)))
variable (hdistinct : Function.Injective
  (fun a : A => (⟨j a, Sum.inr (i a)⟩ : LayerSamplerAxis I n)))
variable (hgrid : ∀ a, allocatedGridAxis (I := I) U basis S.value ⟨j a, Sum.inr (i a)⟩)
variable {O : A → Type*} [∀ a, Fintype (O a)] (rows : ∀ a, O a → Finset α)
variable (x : G → IntegerScalarCubeBox α S.value)

local notation "conditioned" => FiniteProbabilityWeights.condition
  (principalTupleWeights B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S))
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell
local notation "physical" => fun y a => integerMatrixImagePMF
  (boundedCoefficientJetMatrix (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
    (allocatedPhysicalCubeDirections B U basis S x y) (Fin.val (j a) + 1) (rows a))
  (allocatedLayerIntegerPMFs B U basis hR hσ S (j a) (i a))

include hdistinct hgrid in
theorem allocatedPhysicalGrid_joint_residue_law :
    (conditioned).toPMF.bind (fun y => dependentProductPMF ((physical) y)) =
      dependentProductPMF (fun a => (conditioned).toPMF.bind (fun y => (physical) y a)) := by
  let F (a : A)
      (v : ∀ b : B ⟨j a, Sum.inr (i a)⟩, ∀ t : Fin ((j a).val + 1),
        IntegerScalarCubeBox α (allocatedPrincipalSides B U basis S ⟨⟨j a, Sum.inr (i a)⟩, b, t⟩)) :
      PMF (O a → ℤ) :=
    (independentProductPMF (fun s : Option (B ⟨j a, Sum.inr (i a)⟩) =>
      allocatedLayerIntegerPMFs B U basis hR hσ S (j a) (i a)
        (principalCoefficientChoice (G := G) (layerSamplerDegree I n) ⟨j a, Sum.inr (i a)⟩ s))).map
      (fun c o => booleanCoefficient (fun _ => c none) (rows a o) +
        ∑ b, c (some b) * integerBooleanBlockJet (fun t k => (v b t k : ℤ)) (rows a o))
  have hpoint y a : (physical) y a = F a (fun b t => y ⟨⟨j a, Sum.inr (i a)⟩, b, t⟩) :=
    allocatedPhysicalGridJetPMF_principal B U basis hR hσ S (j a) (i a) (hgrid a) x y (rows a)
  simp_rw [hpoint]
  exact principalSupportedResidue_selected_kernels B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)
    q r hcell (fun a => ⟨j a, Sum.inr (i a)⟩) hdistinct F

include hdistinct hgrid in
theorem allocatedPhysicalGrid_joint_point_mass (K : A → ℝ) (z : ∀ a, O a → ℤ) :
    (conditioned).mean (fun y => ∏ a, K a * ((physical) y a (z a)).toReal) =
      ∏ a, K a * (((conditioned).toPMF.bind (fun y => (physical) y a)) (z a)).toReal := by
  exact FiniteProbabilityWeights.mean_prod_point_mass (conditioned) (physical)
    (allocatedPhysicalGrid_joint_residue_law B U basis hR hσ S q r hcell j i
      hdistinct hgrid rows x) K z

include hdistinct hgrid in
theorem allocatedPhysicalGrid_joint_point_error
    (K : A → ℝ) (z : ∀ a, O a → ℤ) (g : A → ℂ)
    {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hg : ∀ a, ‖g a‖ ≤ C)
    (herr : ∀ a, ‖((K a * (((conditioned).toPMF.bind
      (fun y => (physical) y a)) (z a)).toReal : ℝ) : ℂ) - g a‖ ≤ ε) :
    ‖((conditioned).mean (fun y => ∏ a, K a * ((physical) y a (z a)).toReal) : ℂ) -
      ∏ a, g a‖ ≤ Fintype.card A * ε * (C + 1) ^ Fintype.card A := by
  rw [allocatedPhysicalGrid_joint_point_mass B U basis hR hσ S q r hcell
    j i hdistinct hgrid rows x K z, Complex.ofReal_prod]
  have hcap a : ‖((K a * (((conditioned).toPMF.bind
      (fun y => (physical) y a)) (z a)).toReal : ℝ) : ℂ)‖ ≤ C + 1 := by
    calc
      _ = ‖(((K a * (((conditioned).toPMF.bind
          (fun y => (physical) y a)) (z a)).toReal : ℝ) : ℂ) - g a) + g a‖ := by
            rw [sub_add_cancel]
      _ ≤ ‖((K a * (((conditioned).toPMF.bind
          (fun y => (physical) y a)) (z a)).toReal : ℝ) : ℂ) - g a‖ + ‖g a‖ := norm_add_le _ _
      _ ≤ C + 1 := by linarith [herr a, hg a]
  simpa only [Finset.card_univ] using norm_finset_prod_sub_prod_le Finset.univ
    (fun a => ((K a * (((conditioned).toPMF.bind
      (fun y => (physical) y a)) (z a)).toReal : ℝ) : ℂ)) g
    (by linarith : 1 ≤ C + 1) hε (fun a _ => hcap a)
    (fun a _ => (hg a).trans (by linarith)) (fun a _ => herr a)

end Erdos3.VectorPolynomial

end

end OAI
