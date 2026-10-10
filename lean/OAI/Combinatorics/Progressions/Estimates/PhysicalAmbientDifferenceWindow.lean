import OAI.Combinatorics.Progressions.Sampling.AllocatedTranslatedCutoffSampling

namespace OAI

section

namespace Erdos3.BooleanCubeKernel
open MeasureTheory VectorPolynomial
open scoped BigOperators Classical NNReal

theorem physicalAmbientRowsKernelSampling_weighted_difference.{uX, uJ}
    {m dim K : ℕ} {O : Fin m → Type} [∀ j, Fintype (O j)]
    (rows : ∀ j, O j → Finset (Fin dim))
    (hSampling : PhysicalAmbientRowsKernelSampling.{uX, uJ, 0} m dim K O rows)
    {X : Type uX} [Fintype X] [DecidableEq X]
    {Ksp : Type*} [Fintype Ksp]
    {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
    {P : ℝ} (hP : 0 ≤ P) (hn : (Fintype.card X : ℝ) ≤ P)
    (hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    (d : ℕ) [NeZero d] (stride : X → ℕ) (hs : ∀ x, 0 < stride x)
    {R S₀ ρ ε : ℝ} (hS : 0 ≤ S₀) (hSP : S₀ ≤ Real.exp P) (hρ : 0 < ρ) (hε : 0 < ε)
    (hρP : 1 / ρ ≤ Real.exp P) (hεP : 1 / ε ≤ Real.exp P)
    (hstride : ∀ x, (stride x : ℝ) ≤ S₀)
    (H₀ : X → ℝ) (hsize : ∀ x, Real.exp ((P + K) ^ K) ≤ H₀ x)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H₀ R (U j) (p j))
    (hR : Real.exp ((P + K) ^ K) ≤ R)
    (root : Ksp → ℤ) (D : Matrix (Fin dim) Ksp ℤ) (base : X → ℤ)
    (cells : Finset (ColumnResiduePattern (Option Ksp) X stride))
    (W₀ : Option Ksp × X → ℝ) (hW₀ : ∀ z, 0 < W₀ z)
    (hZ₀ : 0 < ∑' z, selectedResidueSmoothWeight stride cells W₀ z)
    (H T : X → ℝ) (hH : ∀ x, 0 < H x) (hT : ∀ x, 0 < T x)
    {Wsp Lsp : ℝ} (hLsp : 0 < Lsp) (hsc : ∀ x, H x = (1 + Wsp) * T x)
    (hrows : ∀ x i, (∑ k, |(physicalCubeCoefficient root D i k : ℝ)|) ≤ H x)
    (hwidth : ∀ x, ρ * H₀ x ≤ 20 * (stride x : ℝ) * H x)
    (hprofile : ∀ x, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H x)
    (ψ : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ) {Cψ : ℝ} (hCψ : 0 ≤ Cψ)
    (hψ : ∀ w ∈ spatialWindow H 4, ‖ψ w‖ ≤ Cψ)
    (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ) (htest : ∀ w, ‖test w‖ ≤ 1)
    (f g : (JetAmbientIndex O J → UnitAddCircle) → ℂ)
    {Kf Kg Cf Cg : ℝ≥0} (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (hfb : ∀ y, ‖f y‖ ≤ Cf) (hgb : ∀ y, ‖g y‖ ≤ Cg)
    {δ L E : ℝ} (hδ : 0 < δ) (hL : 0 ≤ L)
    (hambient : (Fintype.card (JetAmbientIndex O J) : ℝ) ≤ L)
    (hlip : ((Kf + Kg : ℝ≥0) : ℝ) ≤ Real.exp L) (hδL : δ⁻¹ ≤ Real.exp L)
    (hfreqP : Real.exp ((2 * L + 2) ^ 4) ≤ Real.exp P)
    (hcoeffP : Real.exp (2 * L * (2 * L + 2) ^ 4) * (Cf + Cg : ℝ≥0) ≤ Real.exp P)
    (hmass : (∫ y, ‖f (coveredJetAmbientTorus U 1 y) - g (coveredJetAmbientTorus U 1 y)‖
      ∂Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) ≤ E) :
    let volumeFactor := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + Wsp) / Lsp) ^ dim) ^ Fintype.card X
    let scale := ∏ x, ∏ i, physicalSpatialOutputScale (Fin dim) (H x) (T x) Lsp i
    let window := spatialWindow H 4
    let reconstruct := fun a : cells => physicalResidueReconstruction root D base
      (boundedColumnResidueRepresentative stride a.val) stride
    ‖∑ t : cells × window,
      (selectedResidueCellWeight stride cells W₀ t.1 : ℂ) * (ψ t.2.val / (scale : ℂ)) *
        test (reconstruct t.1 t.2.val) *
          (f (coveredJetAmbientTorus U d (physicalCubeRowSample U d rows p hm (reconstruct t.1 t.2.val))) -
           g (coveredJetAmbientTorus U d (physicalCubeRowSample U d rows p hm (reconstruct t.1 t.2.val))))‖ ≤
      Cψ * (volumeFactor * (E + 2 * δ + ε)) := by
  intro volumeFactor scale window reconstruct
  let error := fun y => ‖f (coveredJetAmbientTorus U d y) - g (coveredJetAmbientTorus U d y)‖
  let p₀ := fun j => translate (fun x => (base x : ℝ)) (p j)
  have hp₀ (j) : DegreeLE (1 : X → ℕ) (j.val + 1) (p₀ j) :=
    degreeLE_translate (1 : X → ℕ) (fun _ => by norm_num) _ (p j) (hp j)
  have hm₀ (j e) : coefficients (p₀ j) e ∈ U j :=
    coefficients_translate_mem (U j) (fun x => (base x : ℝ)) (p j) (hm j) e
  have hrank₀ (j) : HasLayerSamplingRank (j.val + 1) H₀ R (U j) (p₀ j) :=
    (hasLayerSamplingRank_translate_iff _ _ H₀ R (U j) (p j) (hp j)).mpr (hrank j)
  let V₁ := referenceJetEnvelopeWidths (q := dim) stride H
  have hV₁ := referenceJetEnvelopeWidths_pos (q := dim) stride hs H hH
  have hscale : 0 < scale := Finset.prod_pos (fun x _ => Finset.prod_pos (fun i _ =>
    physicalSpatialOutputScale_pos (Fin dim) (hH x) (hT x) hLsp i))
  have hmassWindow (a : cells) :
      (∑ w ∈ window, error (physicalCubeRowSample U d rows p hm (reconstruct a w))) ≤
        (volumeFactor * (E + 2 * δ + ε)) * scale := by
    let r := boundedColumnResidueRepresentative stride a.val
    let target := columnResiduePattern stride
      (standardPhysicalCubeFrame (physicalCubeRootDifferences root D 0 r))
    obtain ⟨hZ, hmean⟩ := physicalAmbientRowsKernelSampling_difference rows hSampling
      hP hn hdim U μ ν p₀ hp₀ hm₀ d stride hs hS hSP hρ hε hρP hεP hstride H₀ hsize hrank₀ hR
      {target} (Finset.singleton_nonempty _) V₁ hV₁ (fun z => hwidth z.2)
      f g hf hg hfb hgb hδ hL hambient hlip hδL hfreqP hcoeffP hmass
    let F := fun w => error (physicalCubeRowSample U d rows p₀ hm₀ w)
    have hraw := physicalReconstruction_sum_le_sampled_mass stride hs root D a.val
      H hH hrows hprofile F (fun _ => norm_nonneg _) hZ
    have hvol : ((3 / 2 : ℝ) ^ Fintype.card (Option (Fin dim) × X) *
        (∏ i, residueProfileWidth stride V₁ i) /
        (smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X)) = volumeFactor * scale :=
      referenceJetEnvelope_anisotropic_volume stride hs H T hLsp.ne' hsc
    have hvol0 : 0 ≤ (3 / 2 : ℝ) ^ Fintype.card (Option (Fin dim) × X) *
        (∏ i, residueProfileWidth stride V₁ i) /
        (smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) := by
      exact div_nonneg (mul_nonneg (pow_nonneg (by norm_num) _)
        (Finset.prod_nonneg (fun i _ => (residueProfileWidth_pos stride V₁ hs hV₁ i).le)))
        (pow_pos smoothProbabilityProfile_pos_zero _).le
    have hfinal := hraw.trans (mul_le_mul_of_nonneg_left hmean hvol0)
    rw [hvol] at hfinal
    dsimp only [F, p₀] at hfinal
    simp_rw [physicalCubeRowSample_translate U d rows p hm base,
      ← physicalResidueReconstruction_translate root D base] at hfinal
    exact hfinal.trans_eq (by ring)
  have ht := selectedResidue_coefficient_tail_of_window_mass stride cells W₀ hW₀ hZ₀ window ψ
    (fun a w => test (reconstruct a w))
    (fun a w => error (physicalCubeRowSample U d rows p hm (reconstruct a w)))
    hscale hCψ hψ (fun _ w => htest _) (fun _ _ => norm_nonneg _) hmassWindow
  refine (norm_sum_le _ _).trans ?_
  simpa only [norm_mul] using ht

end Erdos3.BooleanCubeKernel

end

end OAI
