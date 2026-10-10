import OAI.Combinatorics.Progressions.Estimates.AllocatedCoveredSiteBuffer

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory Module Submodule VectorPolynomial
open scoped BigOperators Classical NNReal

theorem exists_allocated_site_envelope_sampled_mass (m q : ℕ) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ {X : Type*} [Fintype X] [DecidableEq X]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (Fin q) × X) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := Fin q) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin q) U)] [BorelSpace (CoefficientTorus (K := Fin q) U)]
    (μ : Measure (CoefficientTorus (K := Fin q) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    (d : ℕ) [NeZero d]
    (stride : X → ℕ) (_hs : ∀ x, 0 < stride x)
    {R S₀ ρ ε : ℝ} (_hS : 0 ≤ S₀) (_hSP : S₀ ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ x, (stride x : ℝ) ≤ S₀)
    (H : X → ℝ) (_hsize : ∀ x, Real.exp ((P + K) ^ K) ≤ H x)
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H R (U j) (p j))
    (_hR : Real.exp ((P + K) ^ K) ≤ R)
    (cells : Finset (ColumnResiduePattern (Option (Fin q)) X stride)) (_hcells : cells.Nonempty)
    (W : Option (Fin q) × X → ℝ) (_hW : ∀ z, 0 < W z) (_hwidth : ∀ z, ρ * H z.2 ≤ W z)
    {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R₀ σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R₀ σ)
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR₀ : ∀ j, 0 < R₀ j) (hσ : ∀ j, 0 < σ j) (_hσ1 : ∀ j, σ j ≤ 1)
    (x : G → IntegerScalarCubeBox (Fin q) S.value)
    (u : PrincipalAxisTuples (α := Fin q) (allocatedGridAxis (I := I) U b S.value)
      (allocatedPrincipalSides B U b S))
    (v : PrincipalAxisTuples (α := Fin q) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
      (allocatedPrincipalSides B U b S))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (_hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
    (_bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (A : ℝ≥0)
    (M : ℝ≥0) (_hInv : ∀ j, (R₀ j)⁻¹ ≤ M)
    (modulus : ℕ)
    (residue : ∀ j : Fin m, Matrix (BoundedBooleanJet (Fin q) (j.val + 1))
      (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    {δ L : ℝ} (_hδ : 0 < δ) (_hL : 0 ≤ L)
    (_hamb : (Fintype.card (JetAmbientIndex (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) J) : ℝ) ≤ L)
    (_hδL : δ⁻¹ ≤ Real.exp L),
    let O := fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)
    let rows := fun j => (Subtype.val : O j → Finset (Fin q))
    let buffer := allocatedSiteBuffer (α := Fin q) B U b S
    let cap : ℝ≥0 := ‖(∏ t : (Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a}, O a.val.1), R₀ t.1.val.1)⁻¹‖₊
    (∀ (z : AllocatedLongJetRows B U b S O) (r : ∀ j, O j → Q j → ZMod d),
      |∏ a, allocatedLongJetMask B U b S x rows modulus residue a (z a)| *
        coefficientDeckJetDensity
          (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x
            (principalAxisJoin (allocatedGridAxis (I := I) U b S.value) u v))
          (allocatedPhysicalCubeDirections B U b S x
            (principalAxisJoin (allocatedGridAxis (I := I) U b S.value) u v)) rows d r ≤ A) →
    (allocatedProfileErrorLip B U b S (O := O) A cap 0
      (allocatedSiteBufferLip (α := Fin q) B U b S M) 0 C V : ℝ) ≤ Real.exp L →
    Real.exp ((2 * L + 2) ^ 4) ≤ Real.exp P →
    Real.exp (2 * L * (2 * L + 2) ^ 4) * allocatedProfileErrorCap B U b S (O := O) A cap 0 V ≤ Real.exp P →
    let majorant := allocatedProfileErrorMajorant B U b S o hR₀ hσ x u v rows A buffer (fun _ => 0) d
    ∃ _hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells W z,
      selectedResidueDensityMass stride cells W
        (fun z => majorant (physicalCubeEuclideanSample U d p hm (standardPhysicalCubeOutput z))) ≤
          (A : ℝ) * Real.exp ((Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) : ℝ) *
            (((m : ℝ) + 3) * Fintype.card (Fin q) + 6)) + 2 * δ + ε ∧
      selectedResidueDensityMass stride cells W
        (fun z => |allocatedCoveredProfileDensity B U b hR₀ hσ S x u v rows _hb o _bW d
          (fun j _ => standardLatticeClosedQuarterBox (J j))
          (allocatedMaskedSiteEnvelope B U b S x modulus residue)
          (physicalCubeEuclideanSample U d p hm (standardPhysicalCubeOutput z))|) ≤
            (A : ℝ) * Real.exp ((Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) : ℝ) *
              (((m : ℝ) + 3) * Fintype.card (Fin q) + 6)) + 2 * δ + ε := by
  obtain ⟨K, hK, htest⟩ := exists_allocated_profile_error_sampled_mass m q
  refine ⟨K, hK, ?_⟩
  intro X _ _ J _ P hP hn hdim U _ _ _ μ _ _ ν _ _ p hp hm d _ stride hs R S₀ ρ ε
    hS hSP hρ hε hρP hεP hstride H hsize hrank hR cells hcells W hW hwidth
    G _ I _ n B _ b R₀ σ S o hR₀ hσ hσ1 x u v _ hb Q _ bW
    A M hInv modulus residue C V hC hV δ L hδ hL hamb hδL O rows buffer cap hA
    hLip hfreqP hcoeffP majorant
  have heq : (fun w => |buffer w - 0|) = buffer := by
    funext w
    rw [sub_zero, abs_of_nonneg (allocatedSiteBuffer_range B U b S hR₀ w).1]
  have hi : Integrable (allocatedUnmaskedLongProfileDensity B U b S (fun w => |buffer w - 0|))
      (allocatedLongJetReference B U b S O) := by
    rw [heq]
    exact (allocatedSiteBuffer_integrable_mass B U b S hR₀ hσ1).1
  have hmass : (A : ℝ) * (∫ z, allocatedUnmaskedLongProfileDensity B U b S (fun w => |buffer w - 0|) z
      ∂allocatedLongJetReference B U b S O) ≤
      (A : ℝ) * Real.exp ((Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) : ℝ) *
        (((m : ℝ) + 3) * Fintype.card (Fin q) + 6)) := by
    rw [heq]
    exact mul_le_mul_of_nonneg_left (allocatedSiteBuffer_integral_le_exp B U b S hR₀ hσ1) A.coe_nonneg
  obtain ⟨hZ, hbound, hdom⟩ := htest hP hn hdim U μ ν p hp hm d stride hs
    hS hSP hρ hε hρP hεP hstride H hsize hrank hR cells hcells W hW hwidth
    B b S o hR₀ hσ x u v rows hb bW A buffer (fun _ => 0)
    (allocatedSiteBuffer_lipschitz B U b S hR₀ M hInv) (LipschitzWith.const 0)
    (allocatedSiteBuffer_abs_le B U b S hR₀) (by intro w; simp) C V hC hV
    hδ hL hamb hδL hLip hfreqP hcoeffP hi _ hmass
  refine ⟨hZ, hbound, ?_⟩
  apply hdom (fun y => |allocatedCoveredProfileDensity B U b hR₀ hσ S x u v rows hb o bW d
    (fun j _ => standardLatticeClosedQuarterBox (J j))
    (allocatedMaskedSiteEnvelope B U b S x modulus residue) y|)
  intro y
  exact allocatedCoveredSiteEnvelope_le_buffer_majorant B U b S hR₀ hσ x u v hb o bW d
    modulus residue A hA y

end Erdos3.BooleanCubeKernel

end

end OAI
