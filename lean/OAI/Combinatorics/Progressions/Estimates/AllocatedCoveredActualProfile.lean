import OAI.Combinatorics.Progressions.Estimates.AllocatedActualHaarComparison

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

theorem exists_allocated_covered_ideal_comparison
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
        (modulus : ℕ)
        (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
        {mesh C : ℝ} (_hmesh0 : 0 ≤ mesh) (_hmesh1 : mesh ≤ 1)
        (_hmesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh) (_hC : 1 ≤ C)
        (_hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ∧
          allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ≤ C),
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
      let proxy := allocatedLongProfileDensity B U basis S x rows modulus residue
        (allocatedContinuousLongJetProxy B U basis S x u rows s hA)
      let target := allocatedLongProfileDensity B U basis S x rows modulus residue ideal
      ∀ (v₀ : PrincipalAxisTuples (α := α)
          (fun a => ¬allocatedGridAxis (I := I) U basis S.value a) (allocatedPrincipalSides B U basis S))
        (Kcov : Fin m → Type*) [∀ j, Fintype (Kcov j)]
        (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
        (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
        (bW : ∀ j, Module.Basis (Kcov j) ℤ
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
        (d : ℕ) [NeZero d]
        (F : AllocatedFrozenCoefficients B U basis S × EuclideanJetLayers U O → ℂ),
        Measurable F → (∀ p, ‖F p‖ ≤ 1) →
      ‖(∫ a₀, ∫ z, (proxy z : ℂ) *
          allocatedCoveredFixedTest B U basis S x u v₀ rows Kcov hb o bW d F a₀ z
          ∂allocatedLongJetReference B U basis S O
          ∂allocatedFrozenCoefficientSource B U basis hR _hσ S) -
        (∫ a₀, ∫ z, (target z : ℂ) *
          allocatedCoveredFixedTest B U basis S x u v₀ rows Kcov hb o bW d F a₀ z
          ∂allocatedLongJetReference B U basis S O
          ∂allocatedFrozenCoefficientSource B U basis hR _hσ S)‖ ≤
        C ^ Fintype.card (LayerSamplerAxis I n) *
          (ε + (2 * (Ro : ℝ)) ^ Fintype.card (UnselectedColumn select) *
            ((2 * (Ro : ℝ) + 2) ^ Fintype.card Q * ((Kp : ℝ) + Ki) * mesh)) := by
  obtain ⟨δ, hδ, hδ1, hδeq, ht, ht1, hcompare⟩ := exists_allocated_long_actual_l1
    (G := G) (α := α) (O := O) B ψ hψ hrange hzero hone A T hLip hTransition hε
  refine ⟨δ, hδ, hδ1, hδeq, ht, ht1, ?_⟩
  intro J _ U basis R hR σ hσ hσt S x u rows hrows hcard block s hA
    M hM hi P hP hMP hRP hRi hσi hcount modulus residue mesh C hmesh0 hmesh1 hmesh hC hm
  have hdata := hcompare U basis hR hσ hσt S x u rows hrows hcard block s hA
    hM hi hP hMP hRP hRi hσi hcount modulus residue hmesh0 hmesh1 hmesh hC hm
  dsimp only
  intro v₀ Kcov _ hb o bW d _ F hF hFb
  exact allocatedCoveredProfile_test_comparison B U basis hR hσ S x u v₀ rows Kcov hb o bW d
    _ _ hdata.1 hdata.2.1 hdata.2.2 F hF hFb

end Erdos3.VectorPolynomial

end

end OAI
