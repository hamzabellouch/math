import OAI.Combinatorics.Progressions.Sampling.ControlledJointGrid
import OAI.Combinatorics.Progressions.Sampling.JointTupleGrid
import OAI.Combinatorics.Progressions.Sampling.PrincipalCoefficientGridFamily

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem principalJointCoefficient_grid_comparison {Q Z K D α : Type*}
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
    (m : ℕ) (hm : 0 < m) (r : PrincipalTupleIndex B h → Option α → ZMod m)
    (hsize : ∀ j, (Fintype.card α+1)*m ≤ L j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant α * ((m : ℝ)/L j) < volume.real (scalarCubeDomain α))
    (hn : ∀ (y : PrincipalIntegerTuples B h α L) k a,
      ((Sum.elim zi (principalTupleIntegers y) (input k a) : ℤ) : ℝ)/T k =
        Sum.elim zr (principalTupleNormalized L y) (input k a))
    (ctrl : ∀ q y, (principalResidueWeights B h L hL m hm r hsize).weight y ≠ 0 →
      CoefficientFiberControl
        (Matrix.fromCols (A q) (integerMappedJetMatrix (e q) input zi (rows q) (principalTupleIntegers y)))
        ((s q).trans Function.Embedding.inl) (Sum.elim (S q) (fun n => H q/monomialScale T (e q n)))
        (H q) (ℓ q) (degree q) (C q) (U q) G)
    (hperiod : ∀ q, integerScalarLattice (I q) (m : ℤ) ≤ (A q).mulVecLin.range)
    (ref : JointBlockParameter B h α → ℤ) (href : integerResidueMap _ m ref = principalTupleResidues r)
    (b t ε : Q → ℝ) (hb : ∀ q, 0 ≤ b q) (ht : ∀ q, 0 ≤ t q) (hε : ∀ q, 0 < ε q)
    (hG : ∀ q, G ≤ Real.exp (b q)) (hU : ∀ q, U q ≤ Real.exp (b q))
    (hC : ∀ q, C q ≤ Real.exp (b q)) (hR : ∀ q, (R q : ℝ) ≤ Real.exp (b q))
    (hi : ∀ q, (δ q : ℝ)⁻¹ ≤ Real.exp (t q))
    (hlarge : ∀ q, coefficientGridReplacementScale (J := J q ⊕ N q)
      ((s q).trans Function.Embedding.inl) (C q) (R q) (b q) (t q) (ε q) (ℓ q) (degree q) ≤ H q)
    (hεsum : (∑ q, ε q) ≤ 1)
    (Cap Lip Ro : ℝ≥0) (hCap : 1 ≤ Cap) {mesh : ℝ}
    (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1) (hmesh : ∀ q, 1 / H q ≤ mesh)
    (grid : Finset ((Σ q, I q) → ℤ)) (φ : ((Σ q, I q) → ℤ) → ℂ)
    (hφ : ∀ v ∈ grid, ‖φ v‖ ≤ 1) :
    let E := fun q => normalizedPivotEquiv ((A q).submatrix id (s q)) (hA q)
      (fun i => S q (s q i)) (fun _ => H q) (fun i => hS q (s q i)) (fun _ => hH q)
    let F := fun q => matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns (A q) (s q))
      (fun j => S q j.val) (fun _ => H q))
    let mask := fun q => coefficientResidueMultiplier (A q)
      (integerResidueMatrix (integerMappedJetMatrix (e q) input zi (rows q) ref) m)
    let ρ := fun x => jointAffineJetDensity s E F e input zr rows c w x ∘ sigmaAxisCoordinates I
    let KT := ∑ q, affineJetL1Cost (JointBlockParameter B h α) α (J q) (N q) (E q) (degree q) (δ q) (R q)
    let KO := Fintype.card Q * Lip * Cap^Fintype.card Q
    let ET := (2 * scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) + KT) *
      ∑ j, (m : ℝ)/L j
    (∀ q, pivotKernelCap (UnselectedColumn (s q)) (E q) (R q) ((δ q)⁻¹^Fintype.card (J q)) ≤ Cap) →
    (∀ q, pivotKernelLip (UnselectedColumn (s q)) (E q) (R q) (affineProductProfileLip (J q) (δ q)) ≤ Lip) →
    (∀ q, normalizedJetOutputRadius α (N q) (E q) (F q) (degree q) (R q) (R q) ≤ Ro) →
    ∃ hZ : ∀ q, 0 < coefficientWeightSum (affineProductProfile (c q) (w q))
        (Sum.elim (S q) (fun n => H q/monomialScale T (e q n))),
      ‖(principalResidueWeights B h L hL m hm r hsize).complexMean
          (fun y => ∑ v ∈ grid, ((∏ q,
            (coefficientImagePMF
              (Matrix.fromCols (A q) (integerMappedJetMatrix (e q) input zi (rows q) (principalTupleIntegers y)))
              (affineProductProfile (c q) (w q)) (affineProductProfile_nonneg (c q) (w q) (hw q))
              (Sum.elim (S q) (fun n => H q/monomialScale T (e q n)))
              (Sum.rec (hS q) (fun n => div_pos (hH q) (monomialScale_pos T hT (e q n))))
              (affineProductProfile_zero_outside (c q) (w q) (hw q) (R q).coe_nonneg (hsupport q))
              (hZ q) (fun i => v ⟨q, i⟩)).toReal : ℝ) : ℂ) * φ v) -
        gridDensityTest (densityMixture (jointBooleanSource h) ρ) 0 (fun j => H j.1)
          grid (fun v => ∏ q, mask q (fun i => v ⟨q, i⟩)) φ‖ ≤
        2 * ∑ q, ε q + G^Fintype.card Q *
          (ET + (2 * (Ro : ℝ) + 2)^Fintype.card (Σ q, I q) * ((KO : ℝ) + KO) * mesh) := by
  dsimp only
  intro hcap hlip hRo
  let E := fun q => normalizedPivotEquiv ((A q).submatrix id (s q)) (hA q)
    (fun i => S q (s q i)) (fun _ => H q) (fun i => hS q (s q i)) (fun _ => hH q)
  let F := fun q => matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns (A q) (s q))
    (fun j => S q j.val) (fun _ => H q))
  let mask := fun q => coefficientResidueMultiplier (A q)
    (integerResidueMatrix (integerMappedJetMatrix (e q) input zi (rows q) ref) m)
  let ρ := fun x => jointAffineJetDensity s E F e input zr rows c w x ∘ sigmaAxisCoordinates I
  let p := principalResidueWeights B h L hL m hm r hsize
  have hfamily (q) := principalCoefficientGrid_family B h (A q) (s q) (hA q) (S q) (hS q)
    (hH q) (hH1 q) (hℓ q) (hC0 q) (hU0 q) hG0 (e q) input zi zr T hT (rows q) (degree q)
    (c q) (w q) (hw q) (hδ q) (hwidth q) (R q) (hsupport q) L hL m hm r hsize hn (ctrl q)
    (hperiod q) ref href (hb q) (ht q) (hε q) (hG q) (hU q) (hC q) (hR q) (hi q) (hlarge q)
  choose hZ hmask herr using hfamily
  let P : PrincipalIntegerTuples B h α L → ∀ q, PMF (I q → ℤ) := fun y q => coefficientImagePMF
    (Matrix.fromCols (A q) (integerMappedJetMatrix (e q) input zi (rows q) (principalTupleIntegers y)))
    (affineProductProfile (c q) (w q)) (affineProductProfile_nonneg (c q) (w q) (hw q))
    (Sum.elim (S q) (fun n => H q/monomialScale T (e q n)))
    (Sum.rec (hS q) (fun n => div_pos (hH q) (monomialScale_pos T hT (e q n))))
    (affineProductProfile_zero_outside (c q) (w q) (hw q) (R q).coe_nonneg (hsupport q)) (hZ q)
  have hfirst : ‖p.complexMean (fun y => ∑ v ∈ grid,
      ((∏ q, (P y q (fun i => v ⟨q, i⟩)).toReal : ℝ) : ℂ) * φ v) -
      p.complexMean (fun y => gridDensityTest (ρ (principalTupleNormalized L y)) 0 (fun j => H j.1)
        grid (fun v => ∏ q, mask q (fun i => v ⟨q, i⟩)) φ)‖ ≤ 2 * ∑ q, ε q := by
    apply (p.norm_complexMean_sub_le _ _ (fun _ => 2 * ∑ q, ε q) ?_).trans_eq (p.mean_const _)
    intro y hy
    apply independentPMF_grid_test_error I (P y)
      (fun q => affineSelectedJetDensity (s q) (E q) (F q) (e q) input zr (rows q) (c q) (w q)
        (principalTupleNormalized L y)) H mask ε (fun q => (herr q y hy).1) _
      (fun q => (herr q y hy).2) hεsum grid φ hφ
    intro q v
    apply div_nonneg (mul_nonneg (hmask q v).1 _) (pow_nonneg (hH q).le _)
    exact (affineSelectedJetDensity_probability_data (s q) (E q) (F q) (e q) input zr (rows q)
      (c q) (w q) (hw q) (R q) (hsupport q) (principalTupleNormalized L y)).1 _
  have hmaskprod (v : (Σ q, I q) → ℤ) :
      |∏ q, mask q (fun i => v ⟨q, i⟩)| ≤ G^Fintype.card Q := by
    rw [Finset.abs_prod]
    calc
      _ ≤ ∏ _q : Q, G := Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun q _ => by
        rw [abs_of_nonneg (hmask q _).1]
        exact (hmask q _).2)
      _ = G^Fintype.card Q := by simp
  have hsecond := jointAffineJetDensity_principalTuple_grid B h s E F e input zr hz rows degree hd
    c w hw δ R hδ (fun q j => hwidth q (.inl j)) hsupport L hL m hm r hsize hsmall
    Cap Lip Ro hCap hcap hlip hRo 0 (fun j => H j.1) (fun j => hH j.1)
    hmesh0 hmesh1 (fun j => hmesh j.1) grid (fun v => ∏ q, mask q (fun i => v ⟨q, i⟩)) φ
    (pow_nonneg hG0 _) (fun v _ => hmaskprod v) hφ
  exact ⟨hZ, (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hfirst hsecond)⟩

end Erdos3

end

end OAI
