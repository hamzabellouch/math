import OAI.Combinatorics.Progressions.Geometry.PrincipalSpatialJointTest
import OAI.Combinatorics.Progressions.Geometry.PrincipalSpatialL1Comparison
import OAI.Combinatorics.Progressions.Linear.KernelComparisonScales
import OAI.Combinatorics.Progressions.Linear.KernelFamilyOutputBounds

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem principalJoint_spatial_grid_comparison {Q Z K D α Ax Jx Nx : Type*}
    [Fintype Ax] [Fintype Jx] [DecidableEq Jx] [Fintype Nx] [DecidableEq Nx]
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
    {ℓx Mx : ℕ} {rhoX xiX rX : ℝ} (sx : α ↪ Jx)
    (x : Jx → IntegerScalarCubeBox α ℓx) (root : Jx → ℤ)
    (hMx : 0 < Mx) (hℓx : 0 < ℓx) (hx : GoodScalarKernelTuple sx (1/(Mx : ℝ)) Mx x)
    (hroot : ∀ j, |root j| ≤ (ℓx : ℤ))
    (hpX : integerScalarLattice (Unit ⊕ α) (m : ℤ) ≤
      pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) sx)
        (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) sx))
    (cX : Ax → Nx → ℤ) (indexX : Ax → Nx → PrincipalTupleIndex B h)
    (HX : Ax → ℝ) (QX : Ax → Nx → ℝ) (hHX : ∀ a, 0 < HX a) (hQX : ∀ a n, 0 < QX a n)
    (hxi0 : 0 ≤ xiX) (hxi1 : xiX ≤ 1)
    (hwidthX : ∀ a n, ((|cX a n| : ℤ)+(L (indexX a n) : ℤ) : ℝ)*QX a n ≤ xiX*HX a)
    (hrho : 0 < rhoX) (hscaleX : ∀ a, rhoX ≤ HX a/ℓx) (hscaleQX : ∀ a n, rhoX ≤ QX a n)
    (hlargeX : smoothSpatialMeshThreshold α Jx Nx ℓx ≤ rhoX) (hrX : 0 < rX)
    (spatialGrid : Finset (Ax → (Unit ⊕ α) → ℤ))
    (hbox : ∀ v ∈ spatialGrid, ∀ a i, |((spatialStar (v a) i : ℤ) : ℝ)/HX a| ≤ 1)
    (φ : (Ax → (Unit ⊕ α) → ℤ) → ((Σ q, I q) → ℤ) → ℂ)
    (hφ : ∀ v ∈ spatialGrid, ∀ w ∈ grid, ‖φ v w‖ ≤ 1) :
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
    let PX := selectedSpatialPivot root (scalarCubeDifferenceMatrix x) sx
    let FX := selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) sx
    let hPX := goodScalarKernelTuple_spatial_det_ne_zero sx x root
      (one_div_pos.mpr (by exact_mod_cast hMx)) hx
    let fX := fun a => smoothSpatialKernelDensity sx root (scalarCubeDifferenceMatrix x) hPX
      (HX a) ℓx (hHX a) (by exact_mod_cast hℓx)
    let GX := (m : ℝ)^Fintype.card (Unit ⊕ α)
    let EX := smoothSpatialError Nx sx Mx ℓx rhoX xiX
    let spatialScale := ∏ a, ∏ _i : Unit ⊕ α, HX a
    let spatialError := Fintype.card Ax * (EX + 4 * GX * smoothSpatialDensityLip sx Mx * rX) *
      (1 + GX * smoothSpatialDensityCap sx Mx + EX)^Fintype.card Ax
    let Δ := spatialError / spatialScale * spatialGrid.card
    let site := fun rr v => ∏ a, spatialSiteApprox PX
      (Matrix.fromCols FX (liftResidueMatrix (principalSpatialResidueColumns m (cX a) (indexX a) rr)))
      m (fX a) (HX a) 1 rX (v a)
    let source := principalTupleWeights (α := α) B h L hL
    let residues := source.fiberLaw (principalResidueLabel m)
    (∀ q, pivotKernelCap (UnselectedColumn (s q)) (E q) (R q) ((δ q)⁻¹^Fintype.card (J q)) ≤ Cap) →
    (∀ q, pivotKernelLip (UnselectedColumn (s q)) (E q) (R q) (affineProductProfileLip (J q) (δ q)) ≤ Lip) →
    (∀ q, normalizedJetOutputRadius α (N q) (E q) (F q) (degree q) (R q) (R q) ≤ Ro) →
    ∃ hZ : ∀ q, 0 < coefficientWeightSum (affineProductProfile (c q) (w q))
        (Sum.elim (S q) (fun n => H q/monomialScale T (e q n))),
      ‖source.complexMean (fun y => ∑ v ∈ spatialGrid,
        ((smoothVectorSpatialOutputLaw root (scalarCubeDifferenceMatrix x)
          (fun a => principalSpatialColumns (cX a) (indexX a) y) HX ℓx QX hHX
          (by exact_mod_cast hℓx) hQX v).toReal : ℂ) *
        (∑ z ∈ grid, ((∏ q,
          (coefficientImagePMF
            (Matrix.fromCols (A q) (integerMappedJetMatrix (e q) input zi (rows q) (principalTupleIntegers y)))
            (affineProductProfile (c q) (w q)) (affineProductProfile_nonneg (c q) (w q) (hw q))
            (Sum.elim (S q) (fun n => H q/monomialScale T (e q n)))
            (Sum.rec (hS q) (fun n => div_pos (hH q) (monomialScale_pos T hT (e q n))))
            (affineProductProfile_zero_outside (c q) (w q) (hw q) (R q).coe_nonneg (hsupport q))
            (hZ q) (fun i => z ⟨q, i⟩)).toReal : ℝ) : ℂ) * φ v z)) -
        residues.complexMean (fun rr => ∑ v ∈ spatialGrid, (site rr v / (spatialScale : ℂ)) *
          gridDensityTest (densityMixture (jointBooleanSource h) ρ)
            0 (fun j => H j.1) grid (fun z => ∏ q, mask rr q (fun i => z ⟨q, i⟩)) (φ v))‖ ≤
          Δ + (1 + Δ) * Err := by
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
  obtain ⟨hZ, hzero⟩ := hcomp 0 (fun _ => 0) (fun _ _ => by simp)
  let P : PrincipalIntegerTuples B h α L → ∀ q, PMF (I q → ℤ) := fun y q => coefficientImagePMF
    (Matrix.fromCols (A q) (integerMappedJetMatrix (e q) input zi (rows q) (principalTupleIntegers y)))
    (affineProductProfile (c q) (w q)) (affineProductProfile_nonneg (c q) (w q) (hw q))
    (Sum.elim (S q) (fun n => H q/monomialScale T (e q n)))
    (Sum.rec (hS q) (fun n => div_pos (hH q) (monomialScale_pos T hT (e q n))))
    (affineProductProfile_zero_outside (c q) (w q) (hw q) (R q).coe_nonneg (hsupport q)) (hZ q)
  refine ⟨hZ, ?_⟩
  apply principalSpatial_joint_test B h L hL sx x root hMx hℓx hx hroot m hm hsize hpX
    cX indexX HX QX hHX hQX hxi0 hxi1 hwidthX hrho hscaleX hscaleQX hlargeX hrX
    ((norm_nonneg _).trans hzero) spatialGrid grid
    (fun y z => ∏ q, (P y q (fun i => z ⟨q, i⟩)).toReal)
    (fun rr ψ => gridDensityTest (densityMixture (jointBooleanSource h) ρ)
      0 (fun j => H j.1) grid (fun z => ∏ q, coefficientResidueMultiplier (A q)
        (integerResidueMatrix (integerMappedJetMatrix (e q) input zi (rows q) (principalResidueLift m rr)) m)
          (fun i => z ⟨q, i⟩)) ψ)
    (fun _ _ _ _ => Finset.prod_nonneg (fun _ _ => ENNReal.toReal_nonneg))
    (fun y _ => independentPMF_grid_mass_le_one I (P y) grid) hbox _ φ hφ
  intro rr ψ hψ
  obtain ⟨_, he⟩ := hcomp rr ψ hψ
  exact he

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem goodKernel_joint_grid_comparison {Q Z K D α Ax Jx Nx : Type*}
    [Fintype Q] [DecidableEq Q] [Fintype D] [DecidableEq D]
    [Fintype α] [DecidableEq α] [Fintype Ax]
    [Fintype Jx] [DecidableEq Jx] [Fintype Nx] [DecidableEq Nx]
    {I N : Q → Type*} [∀ q, Fintype (I q)] [∀ q, DecidableEq (I q)]
    [∀ q, Fintype (N q)] [∀ q, DecidableEq (N q)]
    (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
    {ℓx Mx : ℕ} (hℓx : 0 < ℓx) (hMx : 0 < Mx) (sx : α ↪ Jx)
    (x : Jx → IntegerScalarCubeBox α ℓx) (hx : GoodScalarKernelTuple sx (1/(Mx : ℝ)) Mx x)
    (smax : ℕ) (hsmax : 1 ≤ smax) (degree : Q → ℕ) (hdegree : ∀ q, degree q ≤ smax)
    (rows : ∀ q, I q → Finset α) (hinj : ∀ q, Function.Injective (rows q))
    (hrows : ∀ q i, (rows q i).card ≤ degree q) (δ R : Q → ℝ≥0) :
    ∃ (m : ℕ) (hm : 0 < m), m ≤ Mx^smax ∧
      letI : NeZero m := ⟨hm.ne'⟩
      ∃ s : ∀ q, I q ↪ BoundedIntegerExponent Jx (degree q),
      ∃ hA : ∀ q, ((scalarKernelIntegerJet x (degree q) (rows q)).submatrix id (s q)).det ≠ 0,
      ∃ Cap Lip Ro : ℝ≥0, 1 ≤ Cap ∧
      ∀ (H : Q → ℝ) (hH : ∀ q, 0 < H q) (hH1 : ∀ q, 1 ≤ H q)
        (G : ℝ) (hG0 : 0 ≤ G)
        (hIndex : ∀ q, (((Mx^degree q)^Fintype.card (I q) : ℕ) : ℝ) ≤ G)
        (e : ∀ q, N q → K →₀ ℕ) (input : K → Option α → Z ⊕ JointBlockParameter B h α)
        (zi : Z → ℤ) (zr : Z → ℝ) (hz : ∀ j, |zr j| ≤ 1)
        (T : K → ℝ) (hT : ∀ k, 0 < T k) (hTℓ : ∀ k, T k ≤ (ℓx : ℝ))
        (hd : ∀ q n, (e q n).sum (fun _ k => k) ≤ degree q)
        (c w : ∀ q, BoundedIntegerExponent Jx (degree q) ⊕ N q → ℝ)
        (hw : ∀ q j, 0 < w q j) (hδ : ∀ q, 0 < δ q)
        (hwidth : ∀ q j, (δ q : ℝ) ≤ w q j) (hsupport : ∀ q j, |c q j| + w q j ≤ R q)
        (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)
        (hsize : ∀ j, (Fintype.card α+1)*m ≤ L j)
        (hsmall : ∀ j, scalarCubeGridBoundaryConstant α * ((m : ℝ)/L j) < volume.real (scalarCubeDomain α))
        (hn : ∀ (y : PrincipalIntegerTuples B h α L) k a,
          ((Sum.elim zi (principalTupleIntegers y) (input k a) : ℤ) : ℝ)/T k =
            Sum.elim zr (principalTupleNormalized L y) (input k a))
        (b t ε : Q → ℝ) (hb : ∀ q, 0 ≤ b q) (ht : ∀ q, 0 ≤ t q) (hε : ∀ q, 0 < ε q)
        (hG : ∀ q, G ≤ Real.exp (b q))
        (hU : ∀ q, kernelJetInverseAllowance (Fintype.card α) (Fintype.card Jx)
          (Fintype.card (I q)) (degree q) (1/(Mx : ℝ)) ≤ Real.exp (b q))
        (hC : ∀ q, kernelJetEntryAllowance (Fintype.card α) (degree q) ≤ Real.exp (b q))
        (hR : ∀ q, (R q : ℝ) ≤ Real.exp (b q))
        (hi : ∀ q, (δ q : ℝ)⁻¹ ≤ Real.exp (t q))
        (hlarge : ∀ q, coefficientGridReplacementScale
          (J := BoundedIntegerExponent Jx (degree q) ⊕ N q) ((s q).trans Function.Embedding.inl)
          (kernelJetEntryAllowance (Fintype.card α) (degree q)) (R q) (b q) (t q) (ε q) ℓx (degree q) ≤ H q)
        (hεsum : (∑ q, ε q) ≤ 1)
        (mesh : ℝ) (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1) (hmesh : ∀ q, 1 / H q ≤ mesh)
        (grid : Finset ((Σ q, I q) → ℤ))
        (rhoX xiX rX : ℝ) (root : Jx → ℤ) (hroot : ∀ j, |root j| ≤ (ℓx : ℤ))
        (cX : Ax → Nx → ℤ) (indexX : Ax → Nx → PrincipalTupleIndex B h)
        (HX : Ax → ℝ) (QX : Ax → Nx → ℝ) (hHX : ∀ a, 0 < HX a) (hQX : ∀ a n, 0 < QX a n)
        (hxi0 : 0 ≤ xiX) (hxi1 : xiX ≤ 1)
        (hwidthX : ∀ a n, ((|cX a n| : ℤ)+(L (indexX a n) : ℤ) : ℝ)*QX a n ≤ xiX*HX a)
        (hrho : 0 < rhoX) (hscaleX : ∀ a, rhoX ≤ HX a/ℓx) (hscaleQX : ∀ a n, rhoX ≤ QX a n)
        (hlargeX : smoothSpatialMeshThreshold α Jx Nx ℓx ≤ rhoX) (hrX : 0 < rX)
        (spatialGrid : Finset (Ax → (Unit ⊕ α) → ℤ))
        (hbox : ∀ v ∈ spatialGrid, ∀ a i, |((spatialStar (v a) i : ℤ) : ℝ)/HX a| ≤ 1)
        (φ : (Ax → (Unit ⊕ α) → ℤ) → ((Σ q, I q) → ℤ) → ℂ)
        (hφ : ∀ v ∈ spatialGrid, ∀ z ∈ grid, ‖φ v z‖ ≤ 1),
    let A := fun q => scalarKernelIntegerJet x (degree q) (rows q)
    let S := fun q => kernelJetCoefficientScale Jx (degree q) ℓx (H q)
    let hS := fun q j => kernelJetCoefficientScale_pos Jx (degree q) (by exact_mod_cast hℓx) (hH q) j
    let E := fun q => normalizedPivotEquiv ((A q).submatrix id (s q)) (hA q)
      (fun i => S q (s q i)) (fun _ => H q) (fun i => hS q (s q i)) (fun _ => hH q)
    let F := fun q => matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns (A q) (s q))
      (fun j => S q j.val) (fun _ => H q))
    let mask := fun (rr : PrincipalTupleIndex B h → Option α → ZMod m) q =>
      coefficientResidueMultiplier (A q)
        (integerResidueMatrix (integerMappedJetMatrix (e q) input zi (rows q) (principalResidueLift m rr)) m)
    let ρ := fun x => jointAffineJetDensity s E F e input zr rows c w x ∘ sigmaAxisCoordinates I
    let KT := ∑ q, affineJetL1Cost (JointBlockParameter B h α) α (BoundedIntegerExponent Jx (degree q)) (N q) (E q) (degree q) (δ q) (R q)
    let KO := Fintype.card Q * Lip * Cap^Fintype.card Q
    let ET := (2 * scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) + KT) *
      ∑ j, (m : ℝ)/L j
    let Err := 2 * ∑ q, ε q + G^Fintype.card Q *
      (ET + (2 * (Ro : ℝ) + 2)^Fintype.card (Σ q, I q) * ((KO : ℝ) + KO) * mesh)
    let PX := selectedSpatialPivot root (scalarCubeDifferenceMatrix x) sx
    let FX := selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) sx
    let hPX := goodScalarKernelTuple_spatial_det_ne_zero sx x root
      (one_div_pos.mpr (by exact_mod_cast hMx)) hx
    let fX := fun a => smoothSpatialKernelDensity sx root (scalarCubeDifferenceMatrix x) hPX
      (HX a) ℓx (hHX a) (by exact_mod_cast hℓx)
    let GX := (m : ℝ)^Fintype.card (Unit ⊕ α)
    let EX := smoothSpatialError Nx sx Mx ℓx rhoX xiX
    let spatialScale := ∏ a, ∏ _i : Unit ⊕ α, HX a
    let spatialError := Fintype.card Ax * (EX + 4 * GX * smoothSpatialDensityLip sx Mx * rX) *
      (1 + GX * smoothSpatialDensityCap sx Mx + EX)^Fintype.card Ax
    let Δ := spatialError / spatialScale * spatialGrid.card
    let site := fun rr v => ∏ a, spatialSiteApprox PX
      (Matrix.fromCols FX (liftResidueMatrix (principalSpatialResidueColumns m (cX a) (indexX a) rr)))
      m (fX a) (HX a) 1 rX (v a)
    let source := principalTupleWeights (α := α) B h L hL
    let residues := source.fiberLaw (principalResidueLabel m)
    ∃ hZ : ∀ q, 0 < coefficientWeightSum (affineProductProfile (c q) (w q))
        (Sum.elim (S q) (fun n => H q/monomialScale T (e q n))),
      ‖source.complexMean (fun y => ∑ v ∈ spatialGrid,
        ((smoothVectorSpatialOutputLaw root (scalarCubeDifferenceMatrix x)
          (fun a => principalSpatialColumns (cX a) (indexX a) y) HX ℓx QX hHX
          (by exact_mod_cast hℓx) hQX v).toReal : ℂ) *
        (∑ z ∈ grid, ((∏ q,
          (coefficientImagePMF
            (Matrix.fromCols (A q) (integerMappedJetMatrix (e q) input zi (rows q) (principalTupleIntegers y)))
            (affineProductProfile (c q) (w q)) (affineProductProfile_nonneg (c q) (w q) (hw q))
            (Sum.elim (S q) (fun n => H q/monomialScale T (e q n)))
            (Sum.rec (hS q) (fun n => div_pos (hH q) (monomialScale_pos T hT (e q n))))
            (affineProductProfile_zero_outside (c q) (w q) (hw q) (R q).coe_nonneg (hsupport q))
            (hZ q) (fun i => z ⟨q, i⟩)).toReal : ℝ) : ℂ) * φ v z)) -
        residues.complexMean (fun rr => ∑ v ∈ spatialGrid, (site rr v / (spatialScale : ℂ)) *
          gridDensityTest (densityMixture (jointBooleanSource h) ρ)
            0 (fun j => H j.1) grid (fun z => ∏ q, mask rr q (fun i => z ⟨q, i⟩)) (φ v))‖ ≤
          Δ + (1 + Δ) * Err := by
  have hκ : 0 < 1/(Mx : ℝ) := one_div_pos.mpr (by exact_mod_cast hMx)
  obtain ⟨m, hm, hmB, hpX, hperiod⟩ := goodKernel_common_period sx x hx smax hsmax degree hdegree rows hinj hrows
  obtain ⟨s, hA, hctrl⟩ := goodKernel_mapped_pivots
    (K := K) (Z := Z) (X := JointBlockParameter B h α) (N := N) hℓx sx hκ x hx degree rows hinj hrows
  obtain ⟨Cap, Lip, Ro, hCap, hbounds⟩ := exists_kernelFamily_output_bounds
    (N := N) hℓx x degree rows s hA δ R
  refine ⟨m, hm, hmB, ?_⟩
  let : NeZero m := ⟨hm.ne'⟩
  refine ⟨s, hA, Cap, Lip, Ro, hCap, ?_⟩
  intro H hH hH1 G hG0 hIndex e input zi zr hz T hT hTℓ hd c w hw hδ hwidth hsupport
    L hL hsize hsmall hn b t ε hb ht hε hG hU hC hR hi hlarge hεsum mesh hmesh0 hmesh1 hmesh
    grid rhoX xiX rX root hroot cX indexX HX QX hHX hQX hxi0 hxi1 hwidthX hrho hscaleX hscaleQX
    hlargeX hrX spatialGrid hbox φ hφ
  dsimp only
  have hcontrol (q) (y : PrincipalIntegerTuples B h α L) :=
    hctrl H hH e input zi (principalTupleIntegers y) T hT hTℓ hd
      (mappedPrincipal_normalized_bound B h L hL input zi zr hz T y (hn y)) G hIndex q
  obtain ⟨hcap, hlip, hRo⟩ := hbounds H hH
  exact principalJoint_spatial_grid_comparison B h
    (fun q => scalarKernelIntegerJet x (degree q) (rows q)) s hA
    (fun q => kernelJetCoefficientScale Jx (degree q) ℓx (H q))
    (fun q j => kernelJetCoefficientScale_pos Jx (degree q) (by exact_mod_cast hℓx) (hH q) j)
    H (fun _ => (ℓx : ℝ))
    (fun q => kernelJetEntryAllowance (Fintype.card α) (degree q))
    (fun q => kernelJetInverseAllowance (Fintype.card α) (Fintype.card Jx)
      (Fintype.card (I q)) (degree q) (1/(Mx : ℝ)))
    G hH hH1 (fun _ => by exact_mod_cast hℓx)
    (fun q => (kernelJetEntryAllowance_pos _ _).le)
    (fun q => kernelJetInverseAllowance_nonneg _ _ _ _ hκ) hG0
    e input zi zr hz T hT rows degree hd c w hw δ R hδ hwidth hsupport
    L hL m hm hsize hsmall hn (fun q y _ => hcontrol q y) hperiod
    b t ε hb ht hε hG hU hC hR hi hlarge hεsum Cap Lip Ro hCap hmesh0 hmesh1 hmesh
    grid sx x root hMx hℓx hx hroot (hpX root) cX indexX HX QX hHX hQX hxi0 hxi1 hwidthX
    hrho hscaleX hscaleQX hlargeX hrX spatialGrid hbox φ hφ hcap hlip hRo

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem quantitativeKernel_joint_grid_comparison {Q Z K D α Ax Jx Nx : Type*}
    [Fintype Q] [DecidableEq Q] [Fintype D] [DecidableEq D]
    [Fintype α] [DecidableEq α] [Fintype Ax]
    [Fintype Jx] [DecidableEq Jx] [Fintype Nx] [DecidableEq Nx]
    {I N : Q → Type*} [∀ q, Fintype (I q)] [∀ q, DecidableEq (I q)]
    [∀ q, Fintype (N q)] [∀ q, DecidableEq (N q)]
    (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
    {ℓx Mx : ℕ} (hℓx : 0 < ℓx) (hMx : 0 < Mx) (sx : α ↪ Jx)
    (x : Jx → IntegerScalarCubeBox α ℓx) (hx : GoodScalarKernelTuple sx (1/(Mx : ℝ)) Mx x)
    (smax : ℕ) (hsmax : 1 ≤ smax) (degree : Q → ℕ) (hdegree : ∀ q, degree q ≤ smax)
    (rows : ∀ q, I q → Finset α) (hinj : ∀ q, Function.Injective (rows q))
    (hrows : ∀ q i, (rows q i).card ≤ degree q) (δ R : Q → ℝ≥0)
    (p : ℝ) (hp : 0 ≤ p) (hMxp : (Mx : ℝ) ≤ Real.exp p)
    (hδ : ∀ q, 0 < δ q) (hRp : ∀ q, (R q : ℝ) ≤ Real.exp p)
    (hδp : ∀ q, (δ q : ℝ)⁻¹ ≤ Real.exp p) :
    ∃ (m : ℕ) (hm : 0 < m), m ≤ Mx^smax ∧
      letI : NeZero m := ⟨hm.ne'⟩
      ∃ s : ∀ q, I q ↪ BoundedIntegerExponent Jx (degree q),
      ∃ hA : ∀ q, ((scalarKernelIntegerJet x (degree q) (rows q)).submatrix id (s q)).det ≠ 0,
      let Cap : ℝ≥0 := ⟨Real.exp (kernelFamilyOutputLog (α := α) (J := Jx) I N degree p), (Real.exp_pos _).le⟩
      let Lip := Cap
      let Ro := Cap
      let G := Real.exp (kernelFamilyIndexLog I smax p)
      let b := fun q => kernelCoefficientLog (Fintype.card α) (Fintype.card Jx) (Fintype.card (I q))
        (Fintype.card (BoundedIntegerExponent Jx (degree q))) (degree q) p (kernelFamilyIndexLog I smax p)
      let t := fun _ : Q => p
      ∀ (H : Q → ℝ) (hH : ∀ q, 0 < H q) (hH1 : ∀ q, 1 ≤ H q)
        (e : ∀ q, N q → K →₀ ℕ) (input : K → Option α → Z ⊕ JointBlockParameter B h α)
        (zi : Z → ℤ) (zr : Z → ℝ) (hz : ∀ j, |zr j| ≤ 1)
        (T : K → ℝ) (hT : ∀ k, 0 < T k) (hTℓ : ∀ k, T k ≤ (ℓx : ℝ))
        (hd : ∀ q n, (e q n).sum (fun _ k => k) ≤ degree q)
        (c w : ∀ q, BoundedIntegerExponent Jx (degree q) ⊕ N q → ℝ)
        (hw : ∀ q j, 0 < w q j)
        (hwidth : ∀ q j, (δ q : ℝ) ≤ w q j) (hsupport : ∀ q j, |c q j| + w q j ≤ R q)
        (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)
        (hsize : ∀ j, (Fintype.card α+1)*m ≤ L j)
        (hsmall : ∀ j, scalarCubeGridBoundaryConstant α * ((m : ℝ)/L j) < volume.real (scalarCubeDomain α))
        (hn : ∀ (y : PrincipalIntegerTuples B h α L) k a,
          ((Sum.elim zi (principalTupleIntegers y) (input k a) : ℤ) : ℝ)/T k =
            Sum.elim zr (principalTupleNormalized L y) (input k a))
        (ε : Q → ℝ) (hε : ∀ q, 0 < ε q)
        (hlarge : ∀ q, coefficientGridReplacementScale
          (J := BoundedIntegerExponent Jx (degree q) ⊕ N q) ((s q).trans Function.Embedding.inl)
          (kernelJetEntryAllowance (Fintype.card α) (degree q)) (R q) (b q) (t q) (ε q) ℓx (degree q) ≤ H q)
        (hεsum : (∑ q, ε q) ≤ 1)
        (mesh : ℝ) (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1) (hmesh : ∀ q, 1 / H q ≤ mesh)
        (grid : Finset ((Σ q, I q) → ℤ))
        (rhoX xiX rX : ℝ) (root : Jx → ℤ) (hroot : ∀ j, |root j| ≤ (ℓx : ℤ))
        (cX : Ax → Nx → ℤ) (indexX : Ax → Nx → PrincipalTupleIndex B h)
        (HX : Ax → ℝ) (QX : Ax → Nx → ℝ) (hHX : ∀ a, 0 < HX a) (hQX : ∀ a n, 0 < QX a n)
        (hxi0 : 0 ≤ xiX) (hxi1 : xiX ≤ 1)
        (hwidthX : ∀ a n, ((|cX a n| : ℤ)+(L (indexX a n) : ℤ) : ℝ)*QX a n ≤ xiX*HX a)
        (hrho : 0 < rhoX) (hscaleX : ∀ a, rhoX ≤ HX a/ℓx) (hscaleQX : ∀ a n, rhoX ≤ QX a n)
        (hlargeX : smoothSpatialMeshThreshold α Jx Nx ℓx ≤ rhoX) (hrX : 0 < rX)
        (spatialGrid : Finset (Ax → (Unit ⊕ α) → ℤ))
        (hbox : ∀ v ∈ spatialGrid, ∀ a i, |((spatialStar (v a) i : ℤ) : ℝ)/HX a| ≤ 1)
        (φ : (Ax → (Unit ⊕ α) → ℤ) → ((Σ q, I q) → ℤ) → ℂ)
        (hφ : ∀ v ∈ spatialGrid, ∀ z ∈ grid, ‖φ v z‖ ≤ 1),
    let A := fun q => scalarKernelIntegerJet x (degree q) (rows q)
    let S := fun q => kernelJetCoefficientScale Jx (degree q) ℓx (H q)
    let hS := fun q j => kernelJetCoefficientScale_pos Jx (degree q) (by exact_mod_cast hℓx) (hH q) j
    let E := fun q => normalizedPivotEquiv ((A q).submatrix id (s q)) (hA q)
      (fun i => S q (s q i)) (fun _ => H q) (fun i => hS q (s q i)) (fun _ => hH q)
    let F := fun q => matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns (A q) (s q))
      (fun j => S q j.val) (fun _ => H q))
    let mask := fun (rr : PrincipalTupleIndex B h → Option α → ZMod m) q =>
      coefficientResidueMultiplier (A q)
        (integerResidueMatrix (integerMappedJetMatrix (e q) input zi (rows q) (principalResidueLift m rr)) m)
    let ρ := fun x => jointAffineJetDensity s E F e input zr rows c w x ∘ sigmaAxisCoordinates I
    let KT := ∑ q, affineJetL1Cost (JointBlockParameter B h α) α (BoundedIntegerExponent Jx (degree q)) (N q) (E q) (degree q) (δ q) (R q)
    let KO := Fintype.card Q * Lip * Cap^Fintype.card Q
    let ET := (2 * scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) + KT) *
      ∑ j, (m : ℝ)/L j
    let Err := 2 * ∑ q, ε q + G^Fintype.card Q *
      (ET + (2 * (Ro : ℝ) + 2)^Fintype.card (Σ q, I q) * ((KO : ℝ) + KO) * mesh)
    let PX := selectedSpatialPivot root (scalarCubeDifferenceMatrix x) sx
    let FX := selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) sx
    let hPX := goodScalarKernelTuple_spatial_det_ne_zero sx x root
      (one_div_pos.mpr (by exact_mod_cast hMx)) hx
    let fX := fun a => smoothSpatialKernelDensity sx root (scalarCubeDifferenceMatrix x) hPX
      (HX a) ℓx (hHX a) (by exact_mod_cast hℓx)
    let GX := (m : ℝ)^Fintype.card (Unit ⊕ α)
    let EX := smoothSpatialError Nx sx Mx ℓx rhoX xiX
    let spatialScale := ∏ a, ∏ _i : Unit ⊕ α, HX a
    let spatialError := Fintype.card Ax * (EX + 4 * GX * smoothSpatialDensityLip sx Mx * rX) *
      (1 + GX * smoothSpatialDensityCap sx Mx + EX)^Fintype.card Ax
    let Δ := spatialError / spatialScale * spatialGrid.card
    let site := fun rr v => ∏ a, spatialSiteApprox PX
      (Matrix.fromCols FX (liftResidueMatrix (principalSpatialResidueColumns m (cX a) (indexX a) rr)))
      m (fX a) (HX a) 1 rX (v a)
    let source := principalTupleWeights (α := α) B h L hL
    let residues := source.fiberLaw (principalResidueLabel m)
    ∃ hZ : ∀ q, 0 < coefficientWeightSum (affineProductProfile (c q) (w q))
        (Sum.elim (S q) (fun n => H q/monomialScale T (e q n))),
      ‖source.complexMean (fun y => ∑ v ∈ spatialGrid,
        ((smoothVectorSpatialOutputLaw root (scalarCubeDifferenceMatrix x)
          (fun a => principalSpatialColumns (cX a) (indexX a) y) HX ℓx QX hHX
          (by exact_mod_cast hℓx) hQX v).toReal : ℂ) *
        (∑ z ∈ grid, ((∏ q,
          (coefficientImagePMF
            (Matrix.fromCols (A q) (integerMappedJetMatrix (e q) input zi (rows q) (principalTupleIntegers y)))
            (affineProductProfile (c q) (w q)) (affineProductProfile_nonneg (c q) (w q) (hw q))
            (Sum.elim (S q) (fun n => H q/monomialScale T (e q n)))
            (Sum.rec (hS q) (fun n => div_pos (hH q) (monomialScale_pos T hT (e q n))))
            (affineProductProfile_zero_outside (c q) (w q) (hw q) (R q).coe_nonneg (hsupport q))
            (hZ q) (fun i => z ⟨q, i⟩)).toReal : ℝ) : ℂ) * φ v z)) -
        residues.complexMean (fun rr => ∑ v ∈ spatialGrid, (site rr v / (spatialScale : ℂ)) *
          gridDensityTest (densityMixture (jointBooleanSource h) ρ)
            0 (fun j => H j.1) grid (fun z => ∏ q, mask rr q (fun i => z ⟨q, i⟩)) (φ v))‖ ≤
          Δ + (1 + Δ) * Err := by
  have hκ : 0 < 1/(Mx : ℝ) := one_div_pos.mpr (by exact_mod_cast hMx)
  obtain ⟨m, hm, hmB, hpX, hperiod⟩ := goodKernel_common_period sx x hx smax hsmax degree hdegree rows hinj hrows
  obtain ⟨s, hA, hinv⟩ := goodKernel_fixed_pivots hℓx sx hκ x hx degree rows hinj hrows
  refine ⟨m, hm, hmB, ?_⟩
  let : NeZero m := ⟨hm.ne'⟩
  refine ⟨s, hA, ?_⟩
  dsimp only
  intro H hH hH1 e input zi zr hz T hT hTℓ hd c w hw hwidth hsupport
    L hL hsize hsmall hn ε hε hlarge hεsum mesh hmesh0 hmesh1 hmesh
    grid rhoX xiX rX root hroot cX indexX HX QX hHX hQX hxi0 hxi1 hwidthX hrho hscaleX hscaleQX
    hlargeX hrX spatialGrid hbox φ hφ
  let g := kernelFamilyIndexLog I smax p
  let G := Real.exp g
  let b := fun q => kernelCoefficientLog (Fintype.card α) (Fintype.card Jx) (Fintype.card (I q))
    (Fintype.card (BoundedIntegerExponent Jx (degree q))) (degree q) p g
  let Cap : ℝ≥0 := ⟨Real.exp (kernelFamilyOutputLog (α := α) (J := Jx) I N degree p), (Real.exp_pos _).le⟩
  have hg : 0 ≤ g := kernelFamilyIndexLog_nonneg I smax hp
  have hcost (q) := kernelCoefficientLog_bounds (Fintype.card α) (Fintype.card Jx) (Fintype.card (I q))
    (Fintype.card (BoundedIntegerExponent Jx (degree q))) (degree q) hMx hp hg hMxp
  have hIndex (q) : (((Mx^degree q)^Fintype.card (I q) : ℕ) : ℝ) ≤ G :=
    kernelFamilyIndexLog_row I smax degree hdegree hp hMxp q
  have hcontrol (q) (y : PrincipalIntegerTuples B h α L) :=
    fixedKernel_mapped_control hℓx sx x hx (degree q) (rows q) (hinj q) (hrows q) (s q) (hA q)
      (hinv q) (hH q) (e q) input zi (principalTupleIntegers y) T hT hTℓ (hd q)
      (mappedPrincipal_normalized_bound B h L hL input zi zr hz T y (hn y)) (hIndex q)
  obtain ⟨hCap, hcap, hlip, hRo⟩ := fixedKernel_family_output_bound (N := N)
    hℓx hMx x degree rows s hA hinv δ R hδ hp hMxp hRp hδp H hH
  exact principalJoint_spatial_grid_comparison B h
    (fun q => scalarKernelIntegerJet x (degree q) (rows q)) s hA
    (fun q => kernelJetCoefficientScale Jx (degree q) ℓx (H q))
    (fun q j => kernelJetCoefficientScale_pos Jx (degree q) (by exact_mod_cast hℓx) (hH q) j)
    H (fun _ => (ℓx : ℝ))
    (fun q => kernelJetEntryAllowance (Fintype.card α) (degree q))
    (fun q => kernelJetInverseAllowance (Fintype.card α) (Fintype.card Jx)
      (Fintype.card (I q)) (degree q) (1/(Mx : ℝ)))
    G hH hH1 (fun _ => by exact_mod_cast hℓx)
    (fun q => (kernelJetEntryAllowance_pos _ _).le)
    (fun q => kernelJetInverseAllowance_nonneg _ _ _ _ hκ) (Real.exp_pos _).le
    e input zi zr hz T hT rows degree hd c w hw δ R hδ hwidth hsupport
    L hL m hm hsize hsmall hn (fun q y _ => hcontrol q y) hperiod
    b (fun _ => p) ε (fun q => (hcost q).1) (fun _ => hp) hε
    (fun q => (hcost q).2.1) (fun q => (hcost q).2.2.1) (fun q => (hcost q).2.2.2.1)
    (fun q => (hRp q).trans (hcost q).2.2.2.2) hδp hlarge hεsum
    Cap Cap Cap hCap hmesh0 hmesh1 hmesh
    grid sx x root hMx hℓx hx hroot (hpX root) cX indexX HX QX hHX hQX hxi0 hxi1 hwidthX
    hrho hscaleX hscaleQX hlargeX hrX spatialGrid hbox φ hφ hcap hlip hRo

end Erdos3

end

end OAI
