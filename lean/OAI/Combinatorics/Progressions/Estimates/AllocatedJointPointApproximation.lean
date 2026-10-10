import OAI.Combinatorics.Progressions.Fourier.AllocatedPointSpectrumCap
import OAI.Combinatorics.Progressions.Sampling.ForecastInactiveSlicedFixedProduct

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
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

local notation "conditioned" => FiniteProbabilityWeights.condition
  (principalTupleWeights B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S))
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell

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

theorem allocatedSupportedJointPoint_error
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
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (z : ∀ a, rows a → ℤ) :
    let C := ∑ a, (axisCap) a
    ‖(((∏ a, ((axisK) a : ℝ) ^ (rows a).card) *
        (allocatedSupportedPhysicalJointPMF B U basis hR hσ S q r hcell selected rows x z).toReal : ℝ) : ℂ) -
      ∏ a, allocatedSupportedPhysicalPointApproximation B U basis hR hσ S q r
        (selected a).1 (selected a).2 (hactive a) hq hsize P ε (M a) (rows a) (z a)‖ ≤
      Fintype.card A * ε * (1 + C + ε) ^ Fintype.card A := by
  intro C
  let f (a : A) : ℂ := allocatedSupportedPhysicalPointApproximation B U basis hR hσ S q r
    (selected a).1 (selected a).2 (hactive a) hq hsize P ε (M a) (rows a) (z a)
  let g (a : A) : ℂ := (((axisK) a : ℝ) ^ (rows a).card *
    (allocatedSupportedPhysicalGridPMF B U basis hR hσ S q r hcell
      (selected a).1 (selected a).2 (rows a) x (z a)).toReal : ℝ)
  have hcap (a : A) : ‖f a‖ ≤ (axisCap) a :=
    allocatedSupportedPhysicalPointApproximation_norm_le B U basis hR hσ S q r
      (selected a).1 (selected a).2 (hactive a) hq hsize (hgrid a)
      L hL P hcP hsP (hM a) (rows a) (hrows a) (hB a) ε (z a)
  have hcap0 (a : A) : 0 ≤ (axisCap) a := (norm_nonneg _).trans (hcap a)
  have hC0 : 0 ≤ C := Finset.sum_nonneg (fun a _ => hcap0 a)
  have hfa (a : A) : ‖f a‖ ≤ C := (hcap a).trans
    (Finset.single_le_sum (fun a _ => hcap0 a) (Finset.mem_univ a))
  have herr (a : A) : ‖g a - f a‖ ≤ ε :=
    allocatedSupportedPhysicalPointApproximation_error B U basis hR hσ S q r hcell
      (selected a).1 (selected a).2 (hactive a) hq hsize (hgrid a)
      L hL P hcP hsP (hM a) (rows a) (hrows a) (hB a) hε hε1 x (z a)
  have hga (a : A) : ‖g a‖ ≤ 1 + C + ε := by
    have hn : ‖g a‖ ≤ ‖g a - f a‖ + ‖f a‖ := by
      simpa only [sub_add_cancel] using norm_add_le (g a - f a) (f a)
    exact (hn.trans (add_le_add (herr a) (hfa a))).trans (by linarith)
  have hp := norm_finset_prod_sub_prod_le Finset.univ g f
    (show 1 ≤ 1 + C + ε by linarith) hε.le
    (fun a _ => hga a) (fun a _ => (hfa a).trans (by linarith)) (fun a _ => herr a)
  have hj := allocatedSupportedPhysicalGrid_joint_scaled_mass B U basis hR hσ S q r hcell
    selected rows x hselected hgrid z
  have hjc : (((∏ a, ((axisK) a : ℝ) ^ (rows a).card) *
      (allocatedSupportedPhysicalJointPMF B U basis hR hσ S q r hcell selected rows x z).toReal : ℝ) : ℂ) =
      ∏ a, g a := by
    rw [hj, Complex.ofReal_prod]
  exact (congrArg (fun v : ℂ => ‖v - ∏ a, f a‖) hjc).trans_le
    (by simpa only [Finset.card_univ] using hp)

end Erdos3.VectorPolynomial

end

end OAI
