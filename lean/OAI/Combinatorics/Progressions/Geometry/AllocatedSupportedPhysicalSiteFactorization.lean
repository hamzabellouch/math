import OAI.Combinatorics.Progressions.Estimates.AllocatedBufferedPhysicalFactorization
import OAI.Combinatorics.Progressions.Estimates.AllocatedCoveredSiteBuffer

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "jets" => (fun j : Fin m => BoundedBooleanJet α ((j : ℕ) + 1))
local notation "rows" => (fun j => (Subtype.val : jets j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit jets I n grid
local notation "quarter" => (fun j (_ : jets j) => standardLatticeClosedQuarterBox (J j))
local notation "chart" => mixedCoveredJetChart (O := jets) U o b hb bW d
local notation "region" => mixedCoveredJetRegion (O := jets) (E := Q) U o b d quarter

theorem allocatedCoveredSiteTerm_supported_factorization
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j w, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm w‖ ≤ C j * ‖w‖)
    (hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B α C (allocatedSiteRootAllowance α m) j)
    (modulus : ℕ)
    (residue : ∀ j : Fin m, Matrix (BoundedBooleanJet α (j.val + 1))
      (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (f : Finset α → (LayerSamplerAxis I n → ℝ) → ℂ)
    (hsupport : ∀ s w, (∃ a, 2 * idealSiteBoxRadius α m < |w a|) → f s w = 0)
    (y : EuclideanJetLayers U jets) :
    allocatedCoveredComplexProfileDensity B U b hR hσ S x u v rows hb o bW d quarter
        (allocatedSiteTermDensity B U b S x modulus residue f) y =
      (allocatedCoveredProfileDensity B U b hR hσ S x u v rows hb o bW d quarter
        (allocatedMaskedSiteEnvelope B U b S x modulus residue) y : ℂ) *
        ∏ s, allocatedIdealSiteChartFactor B U b S o hb bW d (f s) (coveredBooleanSiteValue U y s) := by
  by_cases hy : y ∈ chart '' region
  · obtain ⟨z, hz, rfl⟩ := hy
    have hinj := mixedCoveredJetChart_injOn U o b hb bW d quarter
      (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))
    rw [allocatedCoveredComplexProfileDensity, allocatedCoveredProfileDensity,
      restrictedComplexChartDensity_apply _ _ _ _ hinj hz,
      restrictedChartDensity_apply _ _ _ _ hinj hz, Complex.ofReal_one, one_mul, one_mul]
    by_cases hg : allocatedGridJetDensity B U b hR hσ S x u v rows
        (fun a => coefficientJetAxisEquiv jets I n z.1 a.val) = 0
    · simp only [allocatedCoveredFixedFactor, hg, zero_mul, zero_div, Complex.ofReal_zero]
    · by_cases hs : ∀ s a, |allocatedIdealSiteCoordinates B U b S (split z.1).2 s a| ≤ 2 * idealSiteBoxRadius α m
      · have hsites := mixedCoveredBooleanSiteValue_mem_quarter U o b d z
          (fun j => C j * (((Fintype.card (I j) : ℝ) + 1) * (allocatedSiteJetSize (G := G) B α j * R j)))
          (fun j => mul_nonneg (hC j) (mul_nonneg (by positivity)
            (mul_nonneg (allocatedSiteJetSize_nonneg B α j) (hR j).le)))
          (allocatedSiteBox_mixed_point_bound B U b hR hσ S x u v hσ1 o d z hg hs C hC hchart)
          (allocatedSiteChartRadius_budget B α C hC (fun j => (hR j).le) hsmall)
        rw [allocatedIdealSiteChartFactor_product B U b S o hb bW d f z hsites]
        simp only [allocatedMaskedSiteEnvelope, allocatedIdealSiteEnvelope, ite_eq_left hs,
          allocatedSiteTermDensity, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_inv]
        ring
      · obtain ⟨s, a, ha⟩ : ∃ s a, 2 * idealSiteBoxRadius α m <
            |allocatedIdealSiteCoordinates B U b S (split z.1).2 s a| := by
          simpa only [not_forall, not_le] using hs
        have hp : (∏ s, f s (allocatedIdealSiteCoordinates B U b S (split z.1).2 s)) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ s) (hsupport s _ ⟨a, ha⟩)
        simp only [allocatedSiteTermDensity, hp, zero_div, mul_zero, allocatedMaskedSiteEnvelope,
          allocatedIdealSiteEnvelope, ite_eq_right hs, Complex.ofReal_zero, zero_mul]
  · rw [allocatedCoveredComplexProfileDensity, allocatedCoveredProfileDensity,
      restrictedComplexChartDensity_zero _ _ _ _ hy, restrictedChartDensity_zero _ _ _ _ hy,
      Complex.ofReal_zero, zero_mul]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.BooleanCubeKernel

open Module Submodule _root_.Set _root_.OAI.Set VectorPolynomial
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (u : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := Fin dim) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1))
local notation "rows" => (fun j => (Subtype.val : jets j → Finset (Fin dim)))
local notation "quarter" => (fun j (_ : jets j) => standardLatticeClosedQuarterBox (J j))

theorem allocatedCoveredSiteTerm_supported_physical_factorization
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j w, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm w‖ ≤ C j * ‖w‖)
    (hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B (Fin dim) C
      (allocatedSiteRootAllowance (Fin dim) m) j)
    (modulus : ℕ)
    (residue : ∀ j : Fin m, Matrix (BoundedBooleanJet (Fin dim) (j.val + 1))
      (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (f : Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)
    (hsupport : ∀ s w, (∃ a, 2 * idealSiteBoxRadius (Fin dim) m < |w a|) → f s w = 0)
    {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    (cube : X → (Unit ⊕ Fin dim) → ℤ) :
    allocatedCoveredComplexProfileDensity B U b hR hσ S x u v rows hb o bW d quarter
        (allocatedSiteTermDensity B U b S x modulus residue f) (physicalCubeEuclideanSample U d p hm cube) =
      (allocatedCoveredProfileDensity B U b hR hσ S x u v rows hb o bW d quarter
        (allocatedMaskedSiteEnvelope B U b S x modulus residue) (physicalCubeEuclideanSample U d p hm cube) : ℂ) *
        ∏ s, allocatedIdealSiteChartFactor B U b S o hb bW d (f s)
          (physicalSingleSiteValue U d p hm (fun a => (physicalCubeVertexValue cube s a : ℝ))) := by
  have h := allocatedCoveredSiteTerm_supported_factorization B U b hR hσ S x u v hb o bW d
    hσ1 C hC hchart hsmall modulus residue f hsupport (physicalCubeEuclideanSample U d p hm cube)
  simpa only [coveredBooleanSiteValue_physical U d p hm hp cube] using h

end Erdos3.BooleanCubeKernel

end

end OAI
