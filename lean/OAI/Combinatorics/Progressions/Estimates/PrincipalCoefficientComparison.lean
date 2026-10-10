import OAI.Combinatorics.Progressions.Lattices.ResidueCoefficientFamily

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

noncomputable def principalCoefficientQuadratureError {D α I J : Type*}
    [Fintype D] [Fintype α] [DecidableEq α] [Fintype I] [Fintype J]
    (B : D → Type*) [∀ d, Fintype (B d)] (h : D → ℕ) (s : I ↪ J)
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (N : Type*) [Fintype N]
    (degree : ℕ) (δ R : ℝ≥0) (L : PrincipalTupleIndex B h → ℕ) (m : ℕ) : ℝ :=
  (2 * (pivotKernelCap (UnselectedColumn s) A R (δ⁻¹^Fintype.card J) : ℝ) *
      scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) +
    ((pivotKernelLip (UnselectedColumn s) A R (affineProductProfileLip J δ) *
      (Fintype.card N * polynomialBoxLip (Fintype.card (JointBlockParameter B h α)) degree
        (normalizedJetMass α degree)) * R : ℝ≥0) : ℝ)) *
    ∑ j, (m : ℝ)/L j

theorem kernelCoefficient_principalTuple_riemann {Z K D α I J N : Type*}
    [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
    (A : Matrix I J ℤ) (s : I ↪ J) (hA : (A.submatrix id s).det ≠ 0)
    (S : J → ℝ) (hS : ∀ j, 0 < S j) {H : ℝ} (hH : 0 < H)
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ JointBlockParameter B h α)
    (zi : Z → ℤ) (zr : Z → ℝ) (hz : ∀ j, |zr j| ≤ 1) (T : K → ℝ)
    (rows : I → Finset α) {degree : ℕ} (hd : ∀ n, (e n).sum (fun _ k => k) ≤ degree)
    (c w : J ⊕ N → ℝ) (hw : ∀ j, 0 < w j) {δ : ℝ≥0} (hδ : 0 < δ)
    (hwidth : ∀ j, (δ : ℝ) ≤ w (.inl j)) (R : ℝ≥0) (hsupport : ∀ j, |c j|+w j ≤ R)
    (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)
    (m : ℕ) (hm : 0 < m) (r : PrincipalTupleIndex B h → Option α → ZMod m)
    (hsize : ∀ j, (Fintype.card α+1)*m ≤ L j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant α * ((m : ℝ)/L j) < volume.real (scalarCubeDomain α))
    (hn : ∀ (y : PrincipalIntegerTuples B h α L) k a,
      ((Sum.elim zi (principalTupleIntegers y) (input k a) : ℤ) : ℝ)/T k =
        Sum.elim zr (principalTupleNormalized L y) (input k a)) (v : I → ℝ) :
    let E := normalizedPivotEquiv (A.submatrix id s) hA (fun i => S (s i)) (fun _ => H)
      (fun i => hS (s i)) (fun _ => hH)
    let F := matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns A s) (fun j => S j.val) (fun _ => H))
    |(principalResidueWeights B h L hL m hm r hsize).mean
      (fun y => kernelCoefficientDensity A s hA S (fun _ => H) hS (fun _ => hH)
        (integerMappedJetMatrix e input zi rows (principalTupleIntegers y))
        (fun n => H/monomialScale T (e n)) c w v) -
      ∫ x, affineSelectedJetDensity s E F e input zr rows c w x v ∂jointBooleanSource h| ≤
        principalCoefficientQuadratureError (α := α) B h s E N degree δ R L m := by
  dsimp only
  have he (y : PrincipalIntegerTuples B h α L) := kernelCoefficientDensity_eq_jet A s hA S hS hH
    e input zr rows (principalTupleNormalized L y)
    (integerMappedCubeTuple input zi (principalTupleIntegers y)) T
    (integerMappedCubeTuple_normalized input zi (principalTupleIntegers y) zr
      (principalTupleNormalized L y) T (hn y)) c w
  change |(principalResidueWeights B h L hL m hm r hsize).mean
    (fun y => kernelCoefficientDensity A s hA S (fun _ => H) hS (fun _ => hH)
      (integerMappedJetMatrix e input zi rows (principalTupleIntegers y)) _ c w v) - _| ≤ _
  simp_rw [integerMappedJetMatrix, he]
  exact affineSelectedJetDensity_principalTuple_riemann B h s
    (normalizedPivotEquiv (A.submatrix id s) hA (fun i => S (s i)) (fun _ => H)
      (fun i => hS (s i)) (fun _ => hH))
    (matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns A s) (fun j => S j.val) (fun _ => H)))
    e input zr hz rows hd
    c w hw hδ hwidth R hsupport L (fun _ => m) hL (fun _ _ => m) r (fun _ _ => hm)
    (fun _ _ => le_rfl) hsize hsmall v

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem principalCoefficientImage_comparison {Z K D α I J N : Type*}
    [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
    (A : Matrix I J ℤ) (s : I ↪ J) (hA : (A.submatrix id s).det ≠ 0)
    (S : J → ℝ) (hS : ∀ j, 0 < S j) {H ℓ C U G : ℝ} (hH : 0 < H) (hℓ : 0 < ℓ)
    (hC0 : 0 ≤ C) (hU0 : 0 ≤ U) (hG0 : 0 ≤ G)
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ JointBlockParameter B h α)
    (zi : Z → ℤ) (zr : Z → ℝ) (hz : ∀ j, |zr j| ≤ 1) (T : K → ℝ) (hT : ∀ k, 0 < T k)
    (rows : I → Finset α) (degree : ℕ) (hd : ∀ n, (e n).sum (fun _ k => k) ≤ degree)
    (c w : J ⊕ N → ℝ) (hw : ∀ j, 0 < w j) {δ : ℝ≥0} (hδ : 0 < δ)
    (hwidth : ∀ j, (δ : ℝ) ≤ w j) (R : ℝ≥0) (hsupport : ∀ j, |c j|+w j ≤ R)
    (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)
    (m : ℕ) (hm : 0 < m) (r : PrincipalTupleIndex B h → Option α → ZMod m)
    (hsize : ∀ j, (Fintype.card α+1)*m ≤ L j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant α * ((m : ℝ)/L j) < volume.real (scalarCubeDomain α))
    (hn : ∀ (y : PrincipalIntegerTuples B h α L) k a,
      ((Sum.elim zi (principalTupleIntegers y) (input k a) : ℤ) : ℝ)/T k =
        Sum.elim zr (principalTupleNormalized L y) (input k a))
    (ctrl : ∀ y, (principalResidueWeights B h L hL m hm r hsize).weight y ≠ 0 →
      CoefficientFiberControl
        (Matrix.fromCols A (integerMappedJetMatrix e input zi rows (principalTupleIntegers y)))
        (s.trans Function.Embedding.inl) (Sum.elim S (fun n => H/monomialScale T (e n)))
        H ℓ degree C U G)
    (hperiod : integerScalarLattice I (m : ℤ) ≤ A.mulVecLin.range)
    (ref : JointBlockParameter B h α → ℤ) (href : integerResidueMap _ m ref = principalTupleResidues r)
    {b t ε : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t) (hε : 0 < ε)
    (hG : G ≤ Real.exp b) (hU : U ≤ Real.exp b) (hC : C ≤ Real.exp b) (hR : (R : ℝ) ≤ Real.exp b)
    (hi : (δ : ℝ)⁻¹ ≤ Real.exp t)
    (hlarge : coefficientReplacementScale (J := J ⊕ N) (s.trans Function.Embedding.inl) b t ε ℓ degree ≤ H) :
    let E := normalizedPivotEquiv (A.submatrix id s) hA (fun i => S (s i)) (fun _ => H)
      (fun i => hS (s i)) (fun _ => hH)
    let F := matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns A s) (fun j => S j.val) (fun _ => H))
    ∃ hZ : 0 < coefficientWeightSum (affineProductProfile c w)
        (Sum.elim S (fun n => H/monomialScale T (e n))), ∀ v,
      |(principalResidueWeights B h L hL m hm r hsize).mean (fun y => H ^ Fintype.card I *
        (coefficientImagePMF
          (Matrix.fromCols A (integerMappedJetMatrix e input zi rows (principalTupleIntegers y)))
          (affineProductProfile c w) (affineProductProfile_nonneg c w hw)
          (Sum.elim S (fun n => H/monomialScale T (e n)))
          (Sum.rec hS (fun n => div_pos hH (monomialScale_pos T hT (e n))))
          (affineProductProfile_zero_outside c w hw R.coe_nonneg hsupport) hZ v).toReal) -
        coefficientResidueMultiplier A (integerResidueMatrix (integerMappedJetMatrix e input zi rows ref) m) v *
          (∫ x, affineSelectedJetDensity s E F e input zr rows c w x (fun i => (v i : ℝ)/H)
            ∂jointBooleanSource h)| ≤
        ε + G * principalCoefficientQuadratureError (α := α) B h s E N degree δ R L m := by
  dsimp only
  have hquad (v : I → ℝ) := kernelCoefficient_principalTuple_riemann B h A s hA S hS hH
    e input zi zr hz T rows hd c w hw hδ (fun j => hwidth (.inl j)) R hsupport
    L hL m hm r hsize hsmall hn v
  have hη := (abs_nonneg _).trans (hquad 0)
  exact affineCoefficientImage_residue_average (principalResidueWeights B h L hL m hm r hsize)
    A s hA (fun y => integerMappedJetMatrix e input zi rows (principalTupleIntegers y))
    S (fun n => H/monomialScale T (e n)) hS (fun n => div_pos hH (monomialScale_pos T hT (e n)))
    degree ctrl hℓ hH hC0 hU0 hG0 c w hw hδ hwidth R hsupport hb ht hε hη hG hU hC hR hi hlarge
    m (integerResidueMatrix (integerMappedJetMatrix e input zi rows ref) m) hperiod
    (principalResidueWeights_matrix B h L hL m hm r hsize e input zi rows ref href)
    (fun v => ∫ x, affineSelectedJetDensity s _ _ e input zr rows c w x v ∂jointBooleanSource h)
    (fun v => hquad (fun i => (v i : ℝ)/H))

end Erdos3

end

end OAI
