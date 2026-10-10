import OAI.Combinatorics.Progressions.Sampling.QuantitativeKernelJointGrid

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem kernel_joint_grid_tolerance {Q Z K D α Ax Jx Nx : Type*}
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
    (hδp : ∀ q, (δ q : ℝ)⁻¹ ≤ Real.exp p)
    (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
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
      let K₀ := 2*scalarCubeGridBoundaryConstant α/volume.real (scalarCubeDomain α) +
        Real.exp (kernelFamilyTupleLog (P := JointBlockParameter B h α) (α := α) (J := Jx) I N degree p)
      let KO : ℝ≥0 := Fintype.card Q * Lip * Cap^Fintype.card Q
      let DO := (2*(Ro : ℝ)+2)^Fintype.card (Σ q, I q) * ((KO : ℝ)+KO)
      let ε := coefficientRowAccuracy (Fintype.card Q) η
      let mesh := outputGridAccuracy (G^Fintype.card Q) DO (η/2)
      let Lmin := scalarTupleToleranceCutoff α (PrincipalTupleIndex B h) (Mx^smax) K₀
        (mixedCoefficientAccuracy (G^Fintype.card Q) (η/2))
      ∀ (H : Q → ℝ) (hH : ∀ q, 0 < H q) (hH1 : ∀ q, 1 ≤ H q)
        (e : ∀ q, N q → K →₀ ℕ) (input : K → Option α → Z ⊕ JointBlockParameter B h α)
        (zi : Z → ℤ) (zr : Z → ℝ) (hz : ∀ j, |zr j| ≤ 1)
        (T : K → ℝ) (hT : ∀ k, 0 < T k) (hTℓ : ∀ k, T k ≤ (ℓx : ℝ))
        (hd : ∀ q n, (e q n).sum (fun _ k => k) ≤ degree q)
        (c w : ∀ q, BoundedIntegerExponent Jx (degree q) ⊕ N q → ℝ)
        (hw : ∀ q j, 0 < w q j)
        (hwidth : ∀ q j, (δ q : ℝ) ≤ w q j) (hsupport : ∀ q j, |c q j| + w q j ≤ R q)
        (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)
        (hLlarge : ∀ j, Lmin ≤ L j)
        (hn : ∀ (y : PrincipalIntegerTuples B h α L) k a,
          ((Sum.elim zi (principalTupleIntegers y) (input k a) : ℤ) : ℝ)/T k =
            Sum.elim zr (principalTupleNormalized L y) (input k a))
        (hHlarge : ∀ q, coefficientToleranceScale
          (J := BoundedIntegerExponent Jx (degree q) ⊕ N q) ((s q).trans Function.Embedding.inl)
          (b q) (t q) ε ℓx mesh (degree q) ≤ H q)
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
          Δ + (1 + Δ) * η := by
  have hκ : 0 < 1/(Mx : ℝ) := one_div_pos.mpr (by exact_mod_cast hMx)
  obtain ⟨m, hm, hmB, hpX, hperiod⟩ := goodKernel_common_period sx x hx smax hsmax degree hdegree rows hinj hrows
  obtain ⟨s, hA, hinv⟩ := goodKernel_fixed_pivots hℓx sx hκ x hx degree rows hinj hrows
  refine ⟨m, hm, hmB, ?_⟩
  let : NeZero m := ⟨hm.ne'⟩
  refine ⟨s, hA, ?_⟩
  dsimp only
  intro H hH hH1 e input zi zr hz T hT hTℓ hd c w hw hwidth hsupport
    L hL hLlarge hn hHlarge
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
  let K₀ := 2*scalarCubeGridBoundaryConstant α/volume.real (scalarCubeDomain α) +
    Real.exp (kernelFamilyTupleLog (P := JointBlockParameter B h α) (α := α) (J := Jx) I N degree p)
  let KO : ℝ≥0 := Fintype.card Q * Cap * Cap^Fintype.card Q
  let DO := (2*(Cap : ℝ)+2)^Fintype.card (Σ q, I q) * ((KO : ℝ)+KO)
  let ε := coefficientRowAccuracy (Fintype.card Q) η
  let mesh := outputGridAccuracy (G^Fintype.card Q) DO (η/2)
  have hε : 0 < ε := coefficientRowAccuracy_pos _ hη
  have hεsum : (∑ _q : Q, ε) ≤ 1 := by
    have hh := coefficientRowAccuracy_sum Q hη.le
    change 2 * (∑ _q : Q, ε) ≤ η/2 at hh
    linarith
  have hG0 : 0 ≤ G^Fintype.card Q := by positivity
  have hDO : 0 ≤ DO := by dsimp only [DO]; positivity
  have hmesh0 : 0 < mesh := outputGridAccuracy_pos hG0 hDO (half_pos hη)
  have hmesh1 : mesh ≤ 1 := (outputGridAccuracy_le hG0 hDO (half_pos hη).le).trans (by linarith)
  have hK₀ : 0 ≤ K₀ := by
    have hB := (scalarCubeGridBoundaryConstant_pos α).le
    have hV := (scalarCubeDomain_volumeReal_pos α).le
    dsimp only [K₀]
    positivity
  have hmodulus := scalarTupleToleranceCutoff_mono_modulus α (PrincipalTupleIndex B h)
    hmB hK₀ (mixedCoefficientAccuracy_pos hG0 (half_pos hη)).le
  have htuple := scalarTupleToleranceCutoff_spec α (PrincipalTupleIndex B h)
    (mixedCoefficientAccuracy_pos hG0 (half_pos hη)) (fun j => hmodulus.trans (hLlarge j))
  have hsize := htuple.2.1
  have hsmall := htuple.2.2.1
  have hHspec (q) := coefficientToleranceScale_spec
    (J := BoundedIntegerExponent Jx (degree q) ⊕ N q) ((s q).trans Function.Embedding.inl)
    (degree q) (hcost q).1 (kernelJetEntryAllowance_pos (Fintype.card α) (degree q)).le
    (R q).coe_nonneg hε (show (0 : ℝ) ≤ ℓx by positivity) (hcost q).2.2.2.1
    ((hRp q).trans (hcost q).2.2.2.2) hmesh0 (hHlarge q)
  have hKT := fixedKernel_family_tuple_bound (P := JointBlockParameter B h α) (N := N)
    hℓx hMx x degree rows s hA hinv δ R hp hMxp hRp hδp H hH
  have herr := coefficientComparisonError_le Q (PrincipalTupleIndex B h)
    hη hG0 hDO (add_le_add le_rfl hKT) htuple.2.2.2 (le_refl mesh)
  obtain ⟨hZ, he⟩ := principalJoint_spatial_grid_comparison B h
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
    b (fun _ => p) (fun _ => ε) (fun q => (hcost q).1) (fun _ => hp) (fun _ => hε)
    (fun q => (hcost q).2.1) (fun q => (hcost q).2.2.1) (fun q => (hcost q).2.2.2.1)
    (fun q => (hRp q).trans (hcost q).2.2.2.2) hδp (fun q => (hHspec q).2.2.2) hεsum
    Cap Cap Cap hCap hmesh0.le hmesh1 (fun q => (hHspec q).2.2.1)
    grid sx x root hMx hℓx hx hroot (hpX root) cX indexX HX QX hHX hQX hxi0 hxi1 hwidthX
    hrho hscaleX hscaleQX hlargeX hrX spatialGrid hbox φ hφ hcap hlip hRo

  refine ⟨hZ, he.trans ?_⟩
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left
  · simpa only [NNReal.coe_sum] using herr
  · have hEX := smoothSpatialError_nonneg Nx sx Mx ℓx hrho.le hxi0
    have hCX := smoothSpatialDensityCap_nonneg sx Mx
    have hLX := smoothSpatialDensityLip_nonneg sx Mx
    have hscale0 : 0 < ∏ a, ∏ _i : Unit ⊕ α, HX a :=
      Finset.prod_pos (fun a _ => Finset.prod_pos (fun _ _ => hHX a))
    positivity

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem kernel_joint_prescribed_error {Q Z K D α Ax Jx Nx : Type*}
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
    (hδp : ∀ q, (δ q : ℝ)⁻¹ ≤ Real.exp p)
    (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    ∃ (m : ℕ) (hm : 0 < m), m ≤ Mx^smax ∧
      letI : NeZero m := ⟨hm.ne'⟩
      ∃ s : ∀ q, I q ↪ BoundedIntegerExponent Jx (degree q),
      ∃ hA : ∀ q, ((scalarKernelIntegerJet x (degree q) (rows q)).submatrix id (s q)).det ≠ 0,
      let η := τ/4
      let Cap : ℝ≥0 := ⟨Real.exp (kernelFamilyOutputLog (α := α) (J := Jx) I N degree p), (Real.exp_pos _).le⟩
      let Lip := Cap
      let Ro := Cap
      let G := Real.exp (kernelFamilyIndexLog I smax p)
      let b := fun q => kernelCoefficientLog (Fintype.card α) (Fintype.card Jx) (Fintype.card (I q))
        (Fintype.card (BoundedIntegerExponent Jx (degree q))) (degree q) p (kernelFamilyIndexLog I smax p)
      let t := fun _ : Q => p
      let K₀ := 2*scalarCubeGridBoundaryConstant α/volume.real (scalarCubeDomain α) +
        Real.exp (kernelFamilyTupleLog (P := JointBlockParameter B h α) (α := α) (J := Jx) I N degree p)
      let KO : ℝ≥0 := Fintype.card Q * Lip * Cap^Fintype.card Q
      let DO := (2*(Ro : ℝ)+2)^Fintype.card (Σ q, I q) * ((KO : ℝ)+KO)
      let ε := coefficientRowAccuracy (Fintype.card Q) η
      let mesh := outputGridAccuracy (G^Fintype.card Q) DO (η/2)
      let Lmin := scalarTupleToleranceCutoff α (PrincipalTupleIndex B h) (Mx^smax) K₀
        (mixedCoefficientAccuracy (G^Fintype.card Q) (η/2))
      let rhoX := smoothJointResolution Nx (Fintype.card Ax) sx Mx ℓx smax τ
      let xiX := smoothJointWidth Nx (Fintype.card Ax) sx Mx smax τ
      let rX := smoothJointRadius (Fintype.card Ax) sx Mx smax τ
      ∀ (H : Q → ℝ) (hH : ∀ q, 0 < H q) (hH1 : ∀ q, 1 ≤ H q)
        (e : ∀ q, N q → K →₀ ℕ) (input : K → Option α → Z ⊕ JointBlockParameter B h α)
        (zi : Z → ℤ) (zr : Z → ℝ) (hz : ∀ j, |zr j| ≤ 1)
        (T : K → ℝ) (hT : ∀ k, 0 < T k) (hTℓ : ∀ k, T k ≤ (ℓx : ℝ))
        (hd : ∀ q n, (e q n).sum (fun _ k => k) ≤ degree q)
        (c w : ∀ q, BoundedIntegerExponent Jx (degree q) ⊕ N q → ℝ)
        (hw : ∀ q j, 0 < w q j)
        (hwidth : ∀ q j, (δ q : ℝ) ≤ w q j) (hsupport : ∀ q j, |c q j| + w q j ≤ R q)
        (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)
        (hLlarge : ∀ j, Lmin ≤ L j)
        (hn : ∀ (y : PrincipalIntegerTuples B h α L) k a,
          ((Sum.elim zi (principalTupleIntegers y) (input k a) : ℤ) : ℝ)/T k =
            Sum.elim zr (principalTupleNormalized L y) (input k a))
        (hHlarge : ∀ q, coefficientToleranceScale
          (J := BoundedIntegerExponent Jx (degree q) ⊕ N q) ((s q).trans Function.Embedding.inl)
          (b q) (t q) ε ℓx mesh (degree q) ≤ H q)
        (grid : Finset ((Σ q, I q) → ℤ))
        (root : Jx → ℤ) (hroot : ∀ j, |root j| ≤ (ℓx : ℤ))
        (cX : Ax → Nx → ℤ) (indexX : Ax → Nx → PrincipalTupleIndex B h)
        (HX : Ax → ℝ) (QX : Ax → Nx → ℝ) (hHX : ∀ a, 0 < HX a) (hQX : ∀ a n, 0 < QX a n)
        (hHX1 : ∀ a, 1 ≤ HX a)
        (hwidthX : ∀ a n, ((|cX a n| : ℤ)+(L (indexX a n) : ℤ) : ℝ)*QX a n ≤ xiX*HX a)
        (hscaleX : ∀ a, rhoX ≤ HX a/ℓx) (hscaleQX : ∀ a n, rhoX ≤ QX a n)
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
    let PX := selectedSpatialPivot root (scalarCubeDifferenceMatrix x) sx
    let FX := selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) sx
    let hPX := goodScalarKernelTuple_spatial_det_ne_zero sx x root
      (one_div_pos.mpr (by exact_mod_cast hMx)) hx
    let fX := fun a => smoothSpatialKernelDensity sx root (scalarCubeDifferenceMatrix x) hPX
      (HX a) ℓx (hHX a) (by exact_mod_cast hℓx)
    let spatialScale := ∏ a, ∏ _i : Unit ⊕ α, HX a
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
          τ := by
  obtain ⟨m, hm, hmB, hdata⟩ := kernel_joint_grid_tolerance (Z := Z) (K := K) (Ax := Ax) (Nx := Nx) (N := N) B h hℓx hMx sx x hx
    smax hsmax degree hdegree rows hinj hrows δ R p hp hMxp hδ hRp hδp
    (τ/4) (by positivity) (by linarith)
  refine ⟨m, hm, hmB, ?_⟩
  let : NeZero m := ⟨hm.ne'⟩
  obtain ⟨s, hA, hmain⟩ := hdata
  refine ⟨s, hA, ?_⟩
  dsimp only
  intro H hH hH1 e input zi zr hz T hT hTℓ hd c w hw hwidth hsupport
    L hL hLlarge hn hHlarge grid root hroot cX indexX HX QX hHX hQX hHX1
    hwidthX hscaleX hscaleQX spatialGrid hbox φ hφ
  let rhoX := smoothJointResolution Nx (Fintype.card Ax) sx Mx ℓx smax τ
  let xiX := smoothJointWidth Nx (Fintype.card Ax) sx Mx smax τ
  let rX := smoothJointRadius (Fintype.card Ax) sx Mx smax τ
  obtain ⟨hrho, hlargeX, hxi, hxi1, hrX, _, herr⟩ :=
    smoothSpatial_grid_tolerance (N := Nx) sx Mx ℓx smax hτ hτ1 hmB HX hHX1 spatialGrid hbox
  obtain ⟨hZ, he⟩ := hmain H hH hH1 e input zi zr hz T hT hTℓ hd c w hw hwidth hsupport
    L hL hLlarge hn hHlarge grid rhoX xiX rX root hroot cX indexX HX QX hHX hQX
    hxi.le hxi1 hwidthX hrho hscaleX hscaleQX hlargeX hrX spatialGrid hbox φ hφ
  exact ⟨hZ, he.trans herr⟩

end Erdos3

end

end OAI
