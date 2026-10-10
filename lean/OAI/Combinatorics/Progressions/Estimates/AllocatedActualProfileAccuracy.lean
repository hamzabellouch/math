import OAI.Combinatorics.Progressions.Probability.AllocatedProfileErrorSampledMass

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped ContDiff NNReal Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] [∀ j, Nonempty (O j)]

local notation "hLayer" => layerSamplerDegree I n

theorem exists_allocated_actual_profile_majorant
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧
      (δ : ℝ) = booleanRegularizationRadius (B := B)
        (O := fun a : LayerSamplerAxis I n => O a.1) (α := α) hLayer
        (unitProfilePrincipalSize (B := B)) (fun d => 2 * unitProfilePrincipalSize (B := B) d)
        A T (ε / 2) ∧
      let t := booleanMassPerturbationScale (B := B)
        (O := fun a : LayerSamplerAxis I n => O a.1) (α := α)
        ((G × Option α) ⊕ (Σ d, SamplerCoefficientSlot G B hLayer d)) hLayer
        (unitProfilePrincipalSize (B := B)) (fun d => 2 * unitProfilePrincipalSize (B := B) d)
        A T m 1 (ε / 2)
      0 < t ∧ t ≤ 1 ∧
      ∀ {J : Fin m → Type*} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
        {R : Fin m → ℝ} (hR : ∀ j, 0 < R j)
        {σ : Fin m → ℝ} (_hσ : ∀ j, 0 < σ j) (_hσt : ∀ j, σ j ≤ t)
        (S : LayerSamplerScale (G := G) B U basis R σ)
        (x : G → IntegerScalarCubeBox α S.value)
        (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
          (allocatedPrincipalSides B U basis S))
        (rows : ∀ j, O j → Finset α)
        (_hrows : ∀ j, Function.Injective (rows j))
        (_hcard : ∀ j o, (rows j o).card ≤ j.val + 1)
        (_block : ∀ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1 ↪ B a.val)
        (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
        (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
        {M : ℕ} (_hM : 0 < M)
        (_hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val + 1) (rows j) (s j) (hA j) (1 / (M : ℝ)))
        {P : ℝ} (_hP : 0 ≤ P) (_hMP : (M : ℝ) ≤ Real.exp P)
        (_hRP : ∀ j, R j ≤ Real.exp P) (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
        (_hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
        (_hcount : ∀ j : Fin m, (Fintype.card
          (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)
        {mesh : ℝ} (_hmesh0 : 0 ≤ mesh) (_hmesh1 : mesh ≤ 1)
        (_hmesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh),
      let ideal := physicalActiveProfileIdeal (G := G) (B := B) (G × Option α) hLayer
        (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1)
        (fun a => R a.1) (fun a => hR a.1) δ
      let Q := {q : (Σ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1) //
        allocatedLongIntegerCoordinate B U basis S q}
      let select := allocatedLongIntegerSelect B U basis S (O := O)
      let bound : ℝ≥0 := ⟨Real.exp (allocatedDensityLog (G := G) B α O P), (Real.exp_pos _).le⟩
      let Kp : ℝ≥0 := (Fintype.card (LayerSamplerAxis I n) : ℝ≥0) * bound *
        bound ^ Fintype.card (LayerSamplerAxis I n)
      let Ki : ℝ≥0 := ‖(∏ q : (Σ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1),
        R q.1.val.1)⁻¹‖₊ *
        (affineProductProfileLip (Σ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1) δ *
          (NNReal.mk (Real.exp P) (Real.exp_pos P).le))
      let Ro := Real.toNNReal (max (Real.exp (allocatedJetSupportLog (G := G) B α O P))
        (Real.exp P * (partitionedIdealRadius α m + 1)))
      let proxy := allocatedContinuousLongJetProxy B U basis S x u rows s hA
      ∀ (v₀ : PrincipalAxisTuples (α := α)
          (fun a => ¬allocatedGridAxis (I := I) U basis S.value a) (allocatedPrincipalSides B U basis S))
        (Kcov : Fin m → Type*) [∀ j, Fintype (Kcov j)]
        [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
        (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
        (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
        (bW : ∀ j, Module.Basis (Kcov j) ℤ
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
        (d : ℕ) [NeZero d]
        (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
        [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
        (period : ℕ) [NeZero period]
        (_hperiod : ∀ j, integerScalarLattice (O j) (period : ℤ) ≤
          (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
        (modulus : ℕ)
        (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
        (Cm : ℝ≥0) (_hCm : 1 ≤ (Cm : ℝ))
        (_hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ∧
          allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ≤ Cm)
        (C V : Fin m → ℝ≥0)
        (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
        (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
          mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j),
      let gain := Real.toNNReal (coefficientDeckPeriodCap O Kcov period) *
        Cm ^ Fintype.card (LayerSamplerAxis I n)
      let majorant := allocatedProfileErrorMajorant B U basis S o hR _hσ x u v₀ rows gain proxy ideal d
      let covered := fun f => allocatedCoveredProfileDensity B U basis hR _hσ S x u v₀ rows hb o bW d
        (fun j _ => standardLatticeClosedQuarterBox (J j)) (allocatedLongProfileDensity B U basis S x rows modulus residue f)
      let law := Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))
      (∀ y, |covered proxy y - covered ideal y| ≤ majorant y) ∧
        Integrable majorant law ∧
        (∫ y, majorant y ∂law) ≤ (gain : ℝ) *
          (ε + (2 * (Ro : ℝ)) ^ Fintype.card (UnselectedColumn select) *
            ((2 * (Ro : ℝ) + 2) ^ Fintype.card Q * ((Kp : ℝ) + Ki) * mesh)) := by
  obtain ⟨δ, hδ, hδ1, hδeq, ht, ht1, hcompare⟩ := exists_allocated_actual_profile_control
    (G := G) (α := α) (O := O) B ψ hψ hrange hzero hone A T hLip hTransition hε
  refine ⟨δ, hδ, hδ1, hδeq, ht, ht1, ?_⟩
  intro J _ U basis R hR σ hσ hσt S x u rows hrows hcard block s hA
    M hM hi P hP hMP hRP hRi hσi hcount mesh hmesh0 hmesh1 hmesh
  obtain ⟨hpLip, hiLip, hpb, hib, hdiff, herr⟩ := hcompare U basis hR hσ hσt S x u rows hrows hcard block s hA
    hM hi hP hMP hRP hRi hσi hcount hmesh0 hmesh1 hmesh
  dsimp only
  intro v₀ Kcov _ _ hb o bW d _ ν _ _ period _ hperiod modulus residue Cm hCm hm C V hC hV
  let gain := Real.toNNReal (coefficientDeckPeriodCap O Kcov period) *
    Cm ^ Fintype.card (LayerSamplerAxis I n)
  have hmass := allocatedProfileErrorMajorant_integrable_mass B U basis S o hR hσ x u v₀ rows
    hb bW d ν gain _ _ hdiff hpLip hiLip hpb hib C V hC hV
  refine ⟨?_, hmass.1, hmass.2.trans (mul_le_mul_of_nonneg_left herr gain.coe_nonneg)⟩
  intro y
  exact allocatedProfileDifference_le_period_majorant B U basis S o hR hσ x u v₀ rows hb bW d
    period hperiod modulus residue Cm hCm hm _ _ y

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped ContDiff NNReal Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] [∀ j, Nonempty (O j)]

local notation "hLayer" => layerSamplerDegree I n

theorem exists_allocated_actual_profile_accuracy
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    {D E p₀ w : ℝ} (hdim : AllocatedComparisonDimensions (G := G) B α O D)
    (hE : 0 ≤ E) (hp₀ : 0 ≤ p₀) (hw : 0 ≤ w) :
    let gainLog := allocatedProfileGainLog m D p₀ w
    let ε := physicalIdealErrorShare E gainLog
    let e := physicalIdealSmoothingLog (B := B) (O := fun a : LayerSamplerAxis I n => O a.1)
      (α := α) hLayer A T E gainLog
    ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧
      (δ : ℝ) = booleanRegularizationRadius (B := B)
        (O := fun a : LayerSamplerAxis I n => O a.1) (α := α) hLayer
        (unitProfilePrincipalSize (B := B)) (fun d => 2 * unitProfilePrincipalSize (B := B) d)
        A T (ε / 2) ∧
      (δ : ℝ)⁻¹ ≤ Real.exp e ∧
      let t := booleanMassPerturbationScale (B := B)
        (O := fun a : LayerSamplerAxis I n => O a.1) (α := α)
        ((G × Option α) ⊕ (Σ d, SamplerCoefficientSlot G B hLayer d)) hLayer
        (unitProfilePrincipalSize (B := B)) (fun d => 2 * unitProfilePrincipalSize (B := B) d)
        A T m 1 (ε / 2)
      0 < t ∧ t ≤ 1 ∧
      ∀ {J : Fin m → Type*} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
        {R : Fin m → ℝ} (hR : ∀ j, 0 < R j)
        {σ : Fin m → ℝ} (_hσ : ∀ j, 0 < σ j) (_hσt : ∀ j, σ j ≤ t)
        (S : LayerSamplerScale (G := G) B U basis R σ)
        (x : G → IntegerScalarCubeBox α S.value)
        (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
          (allocatedPrincipalSides B U basis S))
        (rows : ∀ j, O j → Finset α)
        (_hrows : ∀ j, Function.Injective (rows j))
        (_hcard : ∀ j o, (rows j o).card ≤ j.val + 1)
        (_block : ∀ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1 ↪ B a.val)
        (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
        (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
        {M : ℕ} (_hM : 0 < M)
        (_hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val + 1) (rows j) (s j) (hA j) (1 / (M : ℝ)))
        {P : ℝ} (_hP : 0 ≤ P) (_hMP : (M : ℝ) ≤ Real.exp P)
        (_hRP : ∀ j, R j ≤ Real.exp P) (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
        (_hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
        (_hcount : ∀ j : Fin m, (Fintype.card
          (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)
        {mesh : ℝ} (_hmesh0 : 0 ≤ mesh) (_hmesh1 : mesh ≤ 1)
        (_hmesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh)
        (_hmeshBudget : mesh ≤ physicalIdealErrorShare E (gainLog + allocatedIdealMeshEnvelope m D P e)),
      let ideal := physicalActiveProfileIdeal (G := G) (B := B) (G × Option α) hLayer
        (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1)
        (fun a => R a.1) (fun a => hR a.1) δ
      let proxy := allocatedContinuousLongJetProxy B U basis S x u rows s hA
      ∀ (v₀ : PrincipalAxisTuples (α := α)
          (fun a => ¬allocatedGridAxis (I := I) U basis S.value a) (allocatedPrincipalSides B U basis S))
        (Kcov : Fin m → Type*) [∀ j, Fintype (Kcov j)]
        [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
        (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
        (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
        (bW : ∀ j, Module.Basis (Kcov j) ℤ
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
        (d : ℕ) [NeZero d]
        (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
        [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
        (period : ℕ) [NeZero period]
        (_hperiodM : period ≤ M ^ (m + 1)) (_hM₀ : (M : ℝ) ≤ Real.exp p₀)
        (_hKcov : ∀ j, (Fintype.card (Kcov j) : ℝ) ≤ D)
        (_hperiod : ∀ j, integerScalarLattice (O j) (period : ℤ) ≤
          (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
        (modulus : ℕ)
        (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
        (Cm : ℝ≥0) (_hCm : 1 ≤ (Cm : ℝ)) (_hCmw : (Cm : ℝ) ≤ Real.exp w)
        (_hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ∧
          allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ≤ Cm)
        (C V : Fin m → ℝ≥0)
        (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
        (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
          mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j),
      let gain := Real.toNNReal (coefficientDeckPeriodCap O Kcov period) *
        Cm ^ Fintype.card (LayerSamplerAxis I n)
      let majorant := allocatedProfileErrorMajorant B U basis S o hR _hσ x u v₀ rows gain proxy ideal d
      let covered := fun f => allocatedCoveredProfileDensity B U basis hR _hσ S x u v₀ rows hb o bW d
        (fun j _ => standardLatticeClosedQuarterBox (J j)) (allocatedLongProfileDensity B U basis S x rows modulus residue f)
      let law := Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))
      (∀ y, |covered proxy y - covered ideal y| ≤ majorant y) ∧
        Integrable (allocatedUnmaskedLongProfileDensity B U basis S (fun v => |proxy v - ideal v|))
          (allocatedLongJetReference B U basis S O) ∧
        (gain : ℝ) * (∫ z, allocatedUnmaskedLongProfileDensity B U basis S (fun v => |proxy v - ideal v|) z
          ∂allocatedLongJetReference B U basis S O) ≤ Real.exp (-E) ∧
        Integrable majorant law ∧
        (∫ y, majorant y ∂law) ≤ Real.exp (-E) := by
  dsimp only
  let gainLog := allocatedProfileGainLog m D p₀ w
  have hgainLog : 0 ≤ gainLog := allocatedProfileGainLog_nonneg m hdim.nonneg hp₀ hw
  let e := physicalIdealSmoothingLog (B := B) (O := fun a : LayerSamplerAxis I n => O a.1)
    (α := α) hLayer A T E gainLog
  have he : 0 ≤ e := physicalIdealSmoothingLog_nonneg hLayer A T hE hgainLog
  obtain ⟨δ, hδ, hδ1, hδeq, ht, ht1, hcompare⟩ := exists_allocated_actual_profile_control
    (G := G) (α := α) (O := O) B ψ hψ hrange hzero hone A T hLip hTransition
    (physicalIdealErrorShare_pos E gainLog)
  have hδe : (δ : ℝ)⁻¹ ≤ Real.exp e := by
    rw [hδeq]
    exact physicalIdeal_smoothing_inverse_le_exp hLayer (fun a => Nat.succ_pos _)
      A T hE hgainLog
  refine ⟨δ, hδ, hδ1, hδeq, hδe, ht, ht1, ?_⟩
  intro J _ U basis R hR σ hσ hσt S x u rows hrows hcard block s hA
    M hM hi P hP hMP hRP hRi hσi hcount mesh hmesh0 hmesh1 hmesh hmeshBudget
  obtain ⟨hpLip, hiLip, hpb, hib, hdiff, herr⟩ := hcompare U basis hR hσ hσt S x u rows hrows hcard block s hA
    hM hi hP hMP hRP hRi hσi hcount hmesh0 hmesh1 hmesh
  intro v₀ Kcov _ _ hb o bW d _ ν _ _ period _ hperiodM hM₀ hKcov hperiod
    modulus residue Cm hCm hCmw hm C V hC hV
  let gain := Real.toNNReal (coefficientDeckPeriodCap O Kcov period) *
    Cm ^ Fintype.card (LayerSamplerAxis I n)
  have hgain := allocatedProfileGain_le_exp B hdim hKcov M period hperiodM Cm hp₀ hw hM₀ hCmw
  have hbudget := allocatedProfileError_mass_budget B hdim
    (allocatedGridAxis (I := I) U basis S.value) (allocatedLongIntegerSelect B U basis S (O := O))
    R (fun j => (hR j).le) hP he gain.coe_nonneg hRi hδe hgain le_rfl hmeshBudget
  have hmass := (mul_le_mul_of_nonneg_left herr gain.coe_nonneg).trans hbudget
  have hmajorant := allocatedProfileErrorMajorant_integrable_mass B U basis S o hR hσ x u v₀ rows
    hb bW d ν gain _ _ hdiff hpLip hiLip hpb hib C V hC hV
  refine ⟨?_, hdiff, hmass, hmajorant.1, hmajorant.2.trans hmass⟩
  intro y
  exact allocatedProfileDifference_le_period_majorant B U basis S o hR hσ x u v₀ rows hb bW d
    period hperiod modulus residue Cm hCm hm _ _ y

end Erdos3.VectorPolynomial

end

end OAI
