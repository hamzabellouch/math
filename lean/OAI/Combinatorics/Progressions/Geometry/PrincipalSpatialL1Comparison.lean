import OAI.Combinatorics.Progressions.Estimates.PrincipalJointL1Comparison
import OAI.Combinatorics.Progressions.Sampling.PrincipalGridMixture

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem principalJointCoefficient_spatial_comparison {Q Z K D α : Type*}
    [Fintype Q] [DecidableEq Q] [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
    {I J N : Q → Type*} [∀ q, Fintype (I q)] [∀ q, DecidableEq (I q)]
    [∀ q, Fintype (J q)] [∀ q, DecidableEq (J q)] [∀ q, Fintype (N q)] [∀ q, DecidableEq (N q)]
    (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
    (A : ∀ q, Matrix (I q) (J q) ℤ) (s : ∀ q, I q ↪ J q)
    (hA : ∀ q, ((A q).submatrix id (s q)).det ≠ 0)
    (S : ∀ q, J q → ℝ) (hS : ∀ q j, 0 < S q j) (H ℓ C U : Q → ℝ) (G : ℝ)
    (hH : ∀ q, 0 < H q) (hH1 : ∀ q, 1 ≤ H q) (hℓ : ∀ q, 0 < ℓ q)
    (hC0 : ∀ q, 0 ≤ C q) (hU0 : ∀ q, 0 ≤ U q) (hG0 : 0 ≤ G)
    (e : ∀ q, N q → K →₀ ℕ) (input : K → Option α → Z ⊕ JointBlockParameter B h α)
    (zi : Z → ℤ) (zr : Z → ℝ) (hz : ∀ j, |zr j| ≤ 1) (T : K → ℝ) (hT : ∀ k, 0 < T k)
    (rows : ∀ q, I q → Finset α) (degree : Q → ℕ)
    (hd : ∀ q n, (e q n).sum (fun _ k => k) ≤ degree q)
    (c w : ∀ q, J q ⊕ N q → ℝ) (hw : ∀ q j, 0 < w q j) (δ R : Q → ℝ≥0)
    (hδ : ∀ q, 0 < δ q) (hwidth : ∀ q j, (δ q : ℝ) ≤ w q j)
    (hsupport : ∀ q j, |c q j| + w q j ≤ R q)
    (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)
    (m : ℕ) [NeZero m] (hm : 0 < m)
    (hsize : ∀ j, (Fintype.card α+1)*m ≤ L j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant α * ((m : ℝ)/L j) < volume.real (scalarCubeDomain α))
    (hn : ∀ (y : PrincipalIntegerTuples B h α L) k a,
      ((Sum.elim zi (principalTupleIntegers y) (input k a) : ℤ) : ℝ)/T k =
        Sum.elim zr (principalTupleNormalized L y) (input k a))
    (ctrl : ∀ q y, (principalTupleWeights (α := α) B h L hL).weight y ≠ 0 →
      CoefficientFiberControl
        (Matrix.fromCols (A q) (integerMappedJetMatrix (e q) input zi (rows q) (principalTupleIntegers y)))
        ((s q).trans Function.Embedding.inl) (Sum.elim (S q) (fun n => H q/monomialScale T (e q n)))
        (H q) (ℓ q) (degree q) (C q) (U q) G)
    (hperiod : ∀ q, integerScalarLattice (I q) (m : ℤ) ≤ (A q).mulVecLin.range)
    (b t ε : Q → ℝ) (hb : ∀ q, 0 ≤ b q) (ht : ∀ q, 0 ≤ t q) (hε : ∀ q, 0 < ε q)
    (hG : ∀ q, G ≤ Real.exp (b q)) (hU : ∀ q, U q ≤ Real.exp (b q))
    (hC : ∀ q, C q ≤ Real.exp (b q)) (hR : ∀ q, (R q : ℝ) ≤ Real.exp (b q))
    (hi : ∀ q, (δ q : ℝ)⁻¹ ≤ Real.exp (t q))
    (hlarge : ∀ q, coefficientGridReplacementScale (J := J q ⊕ N q)
      ((s q).trans Function.Embedding.inl) (C q) (R q) (b q) (t q) (ε q) (ℓ q) (degree q) ≤ H q)
    (hεsum : (∑ q, ε q) ≤ 1)
    (Cap Lip Ro : ℝ≥0) (hCap : 1 ≤ Cap) {mesh : ℝ}
    (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1) (hmesh : ∀ q, 1 / H q ≤ mesh)
    (grid : Finset ((Σ q, I q) → ℤ))
    (spatial : PrincipalIntegerTuples B h α L → ((Σ q, I q) → ℤ) → ℂ)
    (sites : (PrincipalTupleIndex B h → Option α → ZMod m) → ((Σ q, I q) → ℤ) → ℂ)
    (Msite : (PrincipalTupleIndex B h → Option α → ZMod m) → ℝ)
    (hMsite : ∀ rr, 0 < Msite rr) (hsites : ∀ rr v, v ∈ grid → ‖sites rr v‖ ≤ Msite rr)
    {spatialError : ℝ} (hspatialError : 0 ≤ spatialError)
    (hspatial : ∀ y, (principalTupleWeights (α := α) B h L hL).weight y ≠ 0 →
      ∀ v ∈ grid, ‖spatial y v - sites (principalResidueLabel m y) v‖ ≤ spatialError)
    (φ : ((Σ q, I q) → ℤ) → ℂ)
    (hφ : ∀ v ∈ grid, ‖φ v‖ ≤ 1) :
    let E := fun q => normalizedPivotEquiv ((A q).submatrix id (s q)) (hA q)
      (fun i => S q (s q i)) (fun _ => H q) (fun i => hS q (s q i)) (fun _ => hH q)
    let F := fun q => matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns (A q) (s q))
      (fun j => S q j.val) (fun _ => H q))
    let mask := fun (rr : PrincipalTupleIndex B h → Option α → ZMod m) q =>
      coefficientResidueMultiplier (A q)
        (integerResidueMatrix (integerMappedJetMatrix (e q) input zi (rows q) (principalResidueLift m rr)) m)
    let ρ := fun x => jointAffineJetDensity s E F e input zr rows c w x ∘ sigmaAxisCoordinates I
    let KT := ∑ q, affineJetL1Cost (JointBlockParameter B h α) α (J q) (N q) (E q) (degree q) (δ q) (R q)
    let KO := Fintype.card Q * Lip * Cap^Fintype.card Q
    let ET := (2 * scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) + KT) *
      ∑ j, (m : ℝ)/L j
    let Err := 2 * ∑ q, ε q + G^Fintype.card Q *
      (ET + (2 * (Ro : ℝ) + 2)^Fintype.card (Σ q, I q) * ((KO : ℝ) + KO) * mesh)
    let source := principalTupleWeights (α := α) B h L hL
    let residues := source.fiberLaw (principalResidueLabel m)
    (∀ q, pivotKernelCap (UnselectedColumn (s q)) (E q) (R q) ((δ q)⁻¹^Fintype.card (J q)) ≤ Cap) →
    (∀ q, pivotKernelLip (UnselectedColumn (s q)) (E q) (R q) (affineProductProfileLip (J q) (δ q)) ≤ Lip) →
    (∀ q, normalizedJetOutputRadius α (N q) (E q) (F q) (degree q) (R q) (R q) ≤ Ro) →
    ∃ hZ : ∀ q, 0 < coefficientWeightSum (affineProductProfile (c q) (w q))
        (Sum.elim (S q) (fun n => H q/monomialScale T (e q n))),
      ‖source.complexMean (fun y => ∑ v ∈ grid, ((∏ q,
          (coefficientImagePMF
            (Matrix.fromCols (A q) (integerMappedJetMatrix (e q) input zi (rows q) (principalTupleIntegers y)))
            (affineProductProfile (c q) (w q)) (affineProductProfile_nonneg (c q) (w q) (hw q))
            (Sum.elim (S q) (fun n => H q/monomialScale T (e q n)))
            (Sum.rec (hS q) (fun n => div_pos (hH q) (monomialScale_pos T hT (e q n))))
            (affineProductProfile_zero_outside (c q) (w q) (hw q) (R q).coe_nonneg (hsupport q))
            (hZ q) (fun i => v ⟨q, i⟩)).toReal : ℝ) : ℂ) * spatial y v * φ v) -
        residues.complexMean (fun rr => gridDensityTest (densityMixture (jointBooleanSource h) ρ)
          0 (fun j => H j.1) grid (fun v => ∏ q, mask rr q (fun i => v ⟨q, i⟩))
            (fun v => sites rr v * φ v))‖ ≤
          spatialError + residues.mean (fun rr => Msite rr * Err) := by
  dsimp only
  intro hcap hlip hRo
  let E := fun q => normalizedPivotEquiv ((A q).submatrix id (s q)) (hA q)
    (fun i => S q (s q i)) (fun _ => H q) (fun i => hS q (s q i)) (fun _ => hH q)
  let F := fun q => matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns (A q) (s q))
    (fun j => S q j.val) (fun _ => H q))
  let ρ := fun x => jointAffineJetDensity s E F e input zr rows c w x ∘ sigmaAxisCoordinates I
  have hcomp (rr : PrincipalTupleIndex B h → Option α → ZMod m)
      (ψ : ((Σ q, I q) → ℤ) → ℂ) (hψ : ∀ v ∈ grid, ‖ψ v‖ ≤ 1) :=
    principalJointCoefficient_grid_comparison B h A s hA S hS H ℓ C U G hH hH1 hℓ hC0 hU0 hG0
      e input zi zr hz T hT rows degree hd c w hw δ R hδ hwidth hsupport L hL m hm rr hsize hsmall hn
      (fun q y hy => ctrl q y (principalResidueWeights_nonzero_source B h L hL m hm rr hsize y hy))
      hperiod (principalResidueLift m rr) (principalResidueLift_spec m rr)
      b t ε hb ht hε hG hU hC hR hi hlarge hεsum Cap Lip Ro hCap hmesh0 hmesh1 hmesh
      grid ψ hψ hcap hlip hRo
  obtain ⟨hZ, _⟩ := hcomp 0 (fun _ => 0) (fun _ _ => by simp)
  let P : PrincipalIntegerTuples B h α L → ∀ q, PMF (I q → ℤ) := fun y q => coefficientImagePMF
    (Matrix.fromCols (A q) (integerMappedJetMatrix (e q) input zi (rows q) (principalTupleIntegers y)))
    (affineProductProfile (c q) (w q)) (affineProductProfile_nonneg (c q) (w q) (hw q))
    (Sum.elim (S q) (fun n => H q/monomialScale T (e q n)))
    (Sum.rec (hS q) (fun n => div_pos (hH q) (monomialScale_pos T hT (e q n))))
    (affineProductProfile_zero_outside (c q) (w q) (hw q) (R q).coe_nonneg (hsupport q)) (hZ q)
  refine ⟨hZ, ?_⟩
  refine principal_jointPMF_grid_mixture B h L hL m hm hsize I P grid spatial sites
    (fun _ => densityMixture (jointBooleanSource h) ρ) 0 (fun j => H j.1)
    (fun rr v => ∏ q, coefficientResidueMultiplier (A q)
      (integerResidueMatrix (integerMappedJetMatrix (e q) input zi (rows q) (principalResidueLift m rr)) m)
        (fun i => v ⟨q, i⟩)) Msite _ hMsite hsites hspatialError hspatial ?_ φ hφ
  intro rr ψ hψ
  obtain ⟨_, he⟩ := hcomp rr ψ hψ
  exact he

end Erdos3

end

end OAI
