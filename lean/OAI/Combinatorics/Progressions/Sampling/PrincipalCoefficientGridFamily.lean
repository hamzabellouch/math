import OAI.Combinatorics.Progressions.Estimates.JointPrincipalCoefficientComparison

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem principalCoefficientGrid_family {Z K D α I J N : Type*}
    [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
    (A : Matrix I J ℤ) (s : I ↪ J) (hA : (A.submatrix id s).det ≠ 0)
    (S : J → ℝ) (hS : ∀ j, 0 < S j) {H ℓ C U G : ℝ} (hH : 0 < H) (hH1 : 1 ≤ H) (hℓ : 0 < ℓ)
    (hC0 : 0 ≤ C) (hU0 : 0 ≤ U) (hG0 : 0 ≤ G)
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ JointBlockParameter B h α)
    (zi : Z → ℤ) (zr : Z → ℝ) (T : K → ℝ) (hT : ∀ k, 0 < T k)
    (rows : I → Finset α) (degree : ℕ)
    (c w : J ⊕ N → ℝ) (hw : ∀ j, 0 < w j) {δ : ℝ≥0} (hδ : 0 < δ)
    (hwidth : ∀ j, (δ : ℝ) ≤ w j) (R : ℝ≥0) (hsupport : ∀ j, |c j| + w j ≤ R)
    (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)
    (m : ℕ) (hm : 0 < m) (r : PrincipalTupleIndex B h → Option α → ZMod m)
    (hsize : ∀ j, (Fintype.card α+1)*m ≤ L j)
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
    (hlarge : coefficientGridReplacementScale (J := J ⊕ N) (s.trans Function.Embedding.inl)
      C R b t ε ℓ degree ≤ H) :
    let E := normalizedPivotEquiv (A.submatrix id s) hA (fun i => S (s i)) (fun _ => H)
      (fun i => hS (s i)) (fun _ => hH)
    let F := matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns A s) (fun j => S j.val) (fun _ => H))
    let mask := coefficientResidueMultiplier A (integerResidueMatrix (integerMappedJetMatrix e input zi rows ref) m)
    let g := fun y v => mask v * affineSelectedJetDensity s E F e input zr rows c w
      (principalTupleNormalized L y) (fun i => (v i : ℝ)/H) / H^Fintype.card I
    ∃ hZ : 0 < coefficientWeightSum (affineProductProfile c w) (Sum.elim S (fun n => H/monomialScale T (e n))),
      (∀ v, 0 ≤ mask v ∧ mask v ≤ G) ∧
      ∀ y, (principalResidueWeights B h L hL m hm r hsize).weight y ≠ 0 →
        Integrable (g y) Measure.count ∧
          (∫ v, |(coefficientImagePMF
            (Matrix.fromCols A (integerMappedJetMatrix e input zi rows (principalTupleIntegers y)))
            (affineProductProfile c w) (affineProductProfile_nonneg c w hw)
            (Sum.elim S (fun n => H/monomialScale T (e n)))
            (Sum.rec hS (fun n => div_pos hH (monomialScale_pos T hT (e n))))
            (affineProductProfile_zero_outside c w hw R.coe_nonneg hsupport) hZ v).toReal - g y v|
            ∂Measure.count) ≤ ε := by
  dsimp only
  let p := principalResidueWeights B h L hL m hm r hsize
  have hrow (y) (hy : p.weight y ≠ 0) := affineCoefficientGrid_tolerance
    (Matrix.fromCols A (integerMappedJetMatrix e input zi rows (principalTupleIntegers y)))
    (s.trans Function.Embedding.inl) (Sum.elim S (fun n => H/monomialScale T (e n)))
    (Sum.rec hS (fun n => div_pos hH (monomialScale_pos T hT (e n)))) degree (ctrl y hy)
    hℓ hH hH1 hC0 hU0 hG0 c w hw hδ hwidth R.coe_nonneg hsupport
    hb ht hε hG hU hC hR hi hlarge
  obtain ⟨y₀, hy₀⟩ := finiteProbability_exists_nonzero_weight p
  obtain ⟨hZ, _⟩ := hrow y₀ hy₀
  refine ⟨hZ, ?_, ?_⟩
  · exact coefficientResidueMultiplier_bounds A _ m _ hperiod
      (principalResidueWeights_matrix B h L hL m hm r hsize e input zi rows ref href y₀ hy₀)
      (ctrl y₀ hy₀).index_bound
  · intro y hy
    have hid := kernelCoefficientDensity_eq_jet A s hA S hS hH e input zr rows
      (principalTupleNormalized L y) (integerMappedCubeTuple input zi (principalTupleIntegers y)) T
      (integerMappedCubeTuple_normalized input zi (principalTupleIntegers y) zr
        (principalTupleNormalized L y) T (hn y)) c w
    have hproxy (v) : coefficientGridProxy
        (Matrix.fromCols A (integerMappedJetMatrix e input zi rows (principalTupleIntegers y)))
        (s.trans Function.Embedding.inl) (ctrl y hy).det_ne_zero
        (Sum.elim S (fun n => H/monomialScale T (e n))) (fun _ => H)
        (Sum.rec hS (fun n => div_pos hH (monomialScale_pos T hT (e n)))) (fun _ => hH)
        (affineProductProfile c w) v =
          coefficientResidueMultiplier A (integerResidueMatrix (integerMappedJetMatrix e input zi rows ref) m) v *
            affineSelectedJetDensity s
              (normalizedPivotEquiv (A.submatrix id s) hA (fun i => S (s i)) (fun _ => H)
                (fun i => hS (s i)) (fun _ => hH))
              (matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns A s) (fun j => S j.val) (fun _ => H)))
              e input zr rows c w (principalTupleNormalized L y) (fun i => (v i : ℝ)/H) / H^Fintype.card I := by
      rw [coefficientGridProxy, coefficientImageMask_eq_multiplier,
        selectedCoefficientDensity_eq_kernel A s hA S (fun _ => H) hS (fun _ => hH) _ _
          (fun n => div_pos hH (monomialScale_pos T hT (e n))) (ctrl y hy).det_ne_zero c w hδ hwidth R hsupport,
        coefficientImageMultiplier_eq_residue A _ m _ hperiod
          (principalResidueWeights_matrix B h L hL m hm r hsize e input zi rows ref href y hy)]
      simp only [integerMappedJetMatrix, hid, Finset.prod_const, Finset.card_univ]
    obtain ⟨_, he⟩ := hrow y hy
    have hg := coefficientGridProxy_integrable_of_control _ _ _
      (Sum.rec hS (fun n => div_pos hH (monomialScale_pos T hT (e n)))) degree (ctrl y hy)
      hH hC0 (affineProductProfile c w) R.coe_nonneg
      (affineProductProfile_zero_outside c w hw R.coe_nonneg hsupport)
    constructor
    · exact hg.congr (Filter.Eventually.of_forall hproxy)
    · simpa only [hproxy] using he

end Erdos3

end

end OAI
