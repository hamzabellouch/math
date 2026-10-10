import OAI.Combinatorics.Progressions.Geometry.AllocatedSupportedPhysicalSiteFactorization

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

local notation "single" => (fun _ : Fin m => Unit)
local notation "ambient" => JetAmbientIndex single J

theorem exists_allocated_ambient_site_factor (hR : ∀ j, 0 < R j)
    (C : Fin m → ℝ≥0)
    (hC : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ C j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (f : (LayerSamplerAxis I n → ℝ) → ℂ) (L : ℝ≥0)
    (hL : LipschitzWith L f) (hf : ∀ v, ‖f v‖ ≤ 1) :
    ∃ g : (ambient → UnitAddCircle) → ℂ,
      LipschitzWith (2 * (L * (K * ∑ j, C j * Fintype.card (J j)))) g ∧
      (∀ z, ‖g z‖ ≤ 2) ∧
      ∀ v : ambient → ℝ, (∀ i, |v i| ≤ 1 / 4) →
        g (fun i => (v i : UnitAddCircle)) = f (allocatedAmbientSiteCoordinates B U b S o v) := by
  obtain ⟨g, hg, hgb, hgv⟩ := exists_quarter_torus_extension
    (fun v => f (allocatedAmbientSiteCoordinates B U b S o v))
    (L * (K * ∑ j, C j * Fintype.card (J j))) 1
    (hL.comp (allocatedAmbientSiteCoordinates_lipschitz B U b S o hR C hC K hK)) (fun v => hf _)
  exact ⟨g, hg, by simpa only [NNReal.coe_one, mul_one] using hgb, hgv⟩

theorem allocatedAmbientSiteFactor_chart
    (f : (LayerSamplerAxis I n → ℝ) → ℂ) (g : (ambient → UnitAddCircle) → ℂ)
    (hvalue : ∀ v : ambient → ℝ, (∀ i, |v i| ≤ 1 / 4) →
      g (fun i => (v i : UnitAddCircle)) = f (allocatedAmbientSiteCoordinates B U b S o v))
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d] (z : MixedCoveredJetSource I single Q n d)
    (hz : z ∈ mixedCoveredJetRegion U o b d (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))) :
    g (coveredJetAmbientTorus U d (mixedCoveredJetChart U o b hb bW d z)) =
      f (allocatedNormalizedMixedSiteValue B U b S (fun j => mixedArrayRegroup _ _ _ (z.1 j) ())) := by
  rw [coveredJetAmbientTorus_chart U b hb o bW d z]
  have hsmall : ∀ a, |mixedJetAmbientPoint U b o z.1 a| ≤ 1 / 4 := by
    rintro ⟨j, t, i⟩
    exact (hz j (Set.mem_univ j) t (Set.mem_univ t)).1 i
  rw [hvalue _ hsmall, allocatedAmbientSiteCoordinates_point]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

theorem exists_allocated_unit_ambient_site_factor (hR : ∀ j, 0 < R j)
    (C : Fin m → ℝ≥0)
    (hC : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ C j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (f : (LayerSamplerAxis I n → ℝ) → ℂ) (L : ℝ≥0)
    (hL : LipschitzWith L f) (hf : ∀ v, ‖f v‖ ≤ 1) :
    ∃ g : (JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) → ℂ,
      LipschitzWith (L * (K * ∑ j, C j * Fintype.card (J j))) g ∧
      (∀ z, ‖g z‖ ≤ 1) ∧
      ∀ v : JetAmbientIndex (fun _ : Fin m => Unit) J → ℝ, (∀ i, |v i| ≤ 1 / 4) →
        2 * g (fun i => (v i : UnitAddCircle)) = f (allocatedAmbientSiteCoordinates B U b S o v) := by
  obtain ⟨g, hg, hgb, hgv⟩ := exists_allocated_ambient_site_factor B U b S o hR C hC K hK f L hL hf
  refine ⟨fun z => g z / 2, lipschitz_complex_half g _ hg,
    fun z => complex_half_norm_le_one (hgb z), ?_⟩
  intro v hv
  calc
    2 * (g (fun i => (v i : UnitAddCircle)) / 2) = g (fun i => (v i : UnitAddCircle)) := by ring
    _ = _ := hgv v hv

end Erdos3.VectorPolynomial

end

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

theorem allocatedCoveredSiteTerm_ambient_factorization
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j w, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm w‖ ≤ C j * ‖w‖)
    (hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B α C (allocatedSiteRootAllowance α m) j)
    (modulus : ℕ)
    (residue : ∀ j : Fin m, Matrix (BoundedBooleanJet α (j.val + 1))
      (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (f : Finset α → (LayerSamplerAxis I n → ℝ) → ℂ)
    (hsupport : ∀ s w, (∃ a, 2 * idealSiteBoxRadius α m < |w a|) → f s w = 0)
    (g : Finset α → (JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) → ℂ)
    (hvalue : ∀ s (w : JetAmbientIndex (fun _ : Fin m => Unit) J → ℝ),
      (∀ i, |w i| ≤ 1 / 4) → g s (fun i => (w i : UnitAddCircle)) =
        f s (allocatedAmbientSiteCoordinates B U b S o w))
    (y : EuclideanJetLayers U jets) :
    allocatedCoveredComplexProfileDensity B U b hR hσ S x u v rows hb o bW d quarter
        (allocatedSiteTermDensity B U b S x modulus residue f) y =
      (allocatedCoveredProfileDensity B U b hR hσ S x u v rows hb o bW d quarter
        (allocatedMaskedSiteEnvelope B U b S x modulus residue) y : ℂ) *
        ∏ s, g s (coveredJetAmbientTorus U d (coveredBooleanSiteValue U y s)) := by
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
        have hprod : (∏ s, g s (coveredJetAmbientTorus U d (coveredBooleanSiteValue U (chart z) s))) =
            ∏ s, f s (allocatedIdealSiteCoordinates B U b S (split z.1).2 s) := by
          apply Finset.prod_congr rfl
          intro s _
          rw [← mixedCoveredBooleanSiteValue_chart U o b hb bW d z s,
            allocatedAmbientSiteFactor_chart B U b S o (f s) (g s) (hvalue s) hb bW d
              (mixedCoveredBooleanSiteValue d z s) (hsites s)]
          change f s (allocatedNormalizedMixedSiteValue B U b S (mixedBooleanSiteValue z.1 s)) = _
          rw [allocatedIdealSiteCoordinates_mixed_value]
        rw [hprod]
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

theorem allocatedCoveredSiteTerm_physical_ambient_factorization
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j w, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm w‖ ≤ C j * ‖w‖)
    (hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B (Fin dim) C
      (allocatedSiteRootAllowance (Fin dim) m) j)
    (modulus : ℕ)
    (residue : ∀ j : Fin m, Matrix (BoundedBooleanJet (Fin dim) (j.val + 1))
      (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (f : Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)
    (hsupport : ∀ s w, (∃ a, 2 * idealSiteBoxRadius (Fin dim) m < |w a|) → f s w = 0)
    (g : Finset (Fin dim) → (JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) → ℂ)
    (hvalue : ∀ s (w : JetAmbientIndex (fun _ : Fin m => Unit) J → ℝ),
      (∀ i, |w i| ≤ 1 / 4) → g s (fun i => (w i : UnitAddCircle)) =
        f s (allocatedAmbientSiteCoordinates B U b S o w))
    {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    (cube : X → (Unit ⊕ Fin dim) → ℤ) :
    allocatedCoveredComplexProfileDensity B U b hR hσ S x u v rows hb o bW d quarter
        (allocatedSiteTermDensity B U b S x modulus residue f) (physicalCubeEuclideanSample U d p hm cube) =
      (allocatedCoveredProfileDensity B U b hR hσ S x u v rows hb o bW d quarter
        (allocatedMaskedSiteEnvelope B U b S x modulus residue) (physicalCubeEuclideanSample U d p hm cube) : ℂ) *
        ∏ s, g s (fun a : JetAmbientIndex (fun _ : Fin m => Unit) J =>
          ((eval (fun t => (physicalCubeVertexValue cube s t : ℝ)) (p a.1)) a.2.2 : UnitAddCircle)) := by
  have h := allocatedCoveredSiteTerm_ambient_factorization B U b hR hσ S x u v hb o bW d
    hσ1 C hC hchart hsmall modulus residue f hsupport g hvalue (physicalCubeEuclideanSample U d p hm cube)
  simpa only [coveredBooleanSiteValue_physical U d p hm hp cube, physicalSingleSiteValue_ambient U d p hm] using h

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped Classical BigOperators NNReal

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

theorem allocatedCoveredSiteTerm_unit_ambient_factorization
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j w, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm w‖ ≤ C j * ‖w‖)
    (hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B α C (allocatedSiteRootAllowance α m) j)
    (modulus : ℕ)
    (residue : ∀ j : Fin m, Matrix (BoundedBooleanJet α (j.val + 1))
      (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (f : Finset α → (LayerSamplerAxis I n → ℝ) → ℂ)
    (hsupport : ∀ s w, (∃ a, 2 * idealSiteBoxRadius α m < |w a|) → f s w = 0)
    (g : Finset α → (JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) → ℂ)
    (hvalue : ∀ s (w : JetAmbientIndex (fun _ : Fin m => Unit) J → ℝ),
      (∀ i, |w i| ≤ 1 / 4) → 2 * g s (fun i => (w i : UnitAddCircle)) =
        f s (allocatedAmbientSiteCoordinates B U b S o w))
    (y : EuclideanJetLayers U jets) :
    allocatedCoveredComplexProfileDensity B U b hR hσ S x u v rows hb o bW d quarter
        (allocatedSiteTermDensity B U b S x modulus residue f) y =
      (2 : ℂ) ^ Fintype.card (Finset α) *
      (allocatedCoveredProfileDensity B U b hR hσ S x u v rows hb o bW d quarter
        (allocatedMaskedSiteEnvelope B U b S x modulus residue) y : ℂ) *
        ∏ s, g s (coveredJetAmbientTorus U d (coveredBooleanSiteValue U y s))  := by
  have h := allocatedCoveredSiteTerm_ambient_factorization B U b hR hσ S x u v hb o bW d
    hσ1 C hC hchart hsmall modulus residue f hsupport (fun s z => 2 * g s z) hvalue y
  rw [h, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  ring

include hR in
omit [Fintype α] [DecidableEq α] in
theorem exists_allocated_unit_site_family {T : Type*}
    (f : T → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ)
    (C : Fin m → ℝ≥0)
    (hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K) (L : ℝ≥0)
    (hL : ∀ i s, LipschitzWith L (f i s)) (hf : ∀ i s w, ‖f i s w‖ ≤ 1) :
    ∃ g : T → Finset α → (JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) → ℂ,
      (∀ i s, LipschitzWith (L * (K * ∑ j, C j * Fintype.card (J j))) (g i s)) ∧
      (∀ i s z, ‖g i s z‖ ≤ 1) ∧
      ∀ i s (w : JetAmbientIndex (fun _ : Fin m => Unit) J → ℝ), (∀ a, |w a| ≤ 1 / 4) →
        2 * g i s (fun a => (w a : UnitAddCircle)) = f i s (allocatedAmbientSiteCoordinates B U b S o w) := by
  choose g hgl hgb hgv using fun i s =>
    exists_allocated_unit_ambient_site_factor B U b S o hR C hC K hK (f i s) L (hL i s) (hf i s)
  exact ⟨g, hgl, hgb, hgv⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.BooleanCubeKernel

open Module Submodule _root_.Set _root_.OAI.Set VectorPolynomial
open scoped Classical BigOperators NNReal

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

theorem exists_allocated_physical_lipschitz_site_factors
    (hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hinv : ∀ j w, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm w‖ ≤ Cinv j * ‖w‖)
    (hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B (Fin dim) Cinv
      (allocatedSiteRootAllowance (Fin dim) m) j)
    (modulus : ℕ)
    (residue : ∀ j : Fin m, Matrix (BoundedBooleanJet (Fin dim) (j.val + 1))
      (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (f : Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)
    (hsupport : ∀ s w, (∃ a, 2 * idealSiteBoxRadius (Fin dim) m < |w a|) → f s w = 0)
    (C : Fin m → ℝ≥0)
    (hforward : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K) (L : ℝ≥0)
    (hL : ∀ s, LipschitzWith L (f s)) (hf : ∀ s w, ‖f s w‖ ≤ 1)
    {X : Type*} :
    ∃ g : Finset (Fin dim) → (JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) → ℂ,
      (∀ s, LipschitzWith (2 * (L * (K * ∑ j, C j * Fintype.card (J j)))) (g s)) ∧
      (∀ s z, ‖g s z‖ ≤ 2) ∧
      ∀ (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
        (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
        (hm : ∀ j e, coefficients (p j) e ∈ U j) (cube : X → (Unit ⊕ Fin dim) → ℤ),
      allocatedCoveredComplexProfileDensity B U b hR hσ S x u v rows hb o bW d quarter
          (allocatedSiteTermDensity B U b S x modulus residue f) (physicalCubeEuclideanSample U d p hm cube) =
        (allocatedCoveredProfileDensity B U b hR hσ S x u v rows hb o bW d quarter
          (allocatedMaskedSiteEnvelope B U b S x modulus residue) (physicalCubeEuclideanSample U d p hm cube) : ℂ) *
          ∏ s, g s (fun a : JetAmbientIndex (fun _ : Fin m => Unit) J =>
            ((eval (fun t => (physicalCubeVertexValue cube s t : ℝ)) (p a.1)) a.2.2 : UnitAddCircle)) := by
  choose g hg hgb hgv using fun s => exists_allocated_ambient_site_factor B U b S o hR C hforward K hK
    (f s) L (hL s) (hf s)
  refine ⟨g, hg, hgb, ?_⟩
  intro p hp hm cube
  exact allocatedCoveredSiteTerm_physical_ambient_factorization B U b hR hσ S x u v hb o bW d
    hσ1 Cinv hCinv hinv hsmall modulus residue f hsupport g hgv p hp hm cube

end Erdos3.BooleanCubeKernel

end

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

theorem allocatedCoveredSiteTerm_unit_factorization
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j w, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm w‖ ≤ C j * ‖w‖)
    (hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B α C (allocatedSiteRootAllowance α m) j)
    (modulus : ℕ)
    (residue : ∀ j : Fin m, Matrix (BoundedBooleanJet α (j.val + 1))
      (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (f : Finset α → (LayerSamplerAxis I n → ℝ) → ℂ)
    (hsupport : ∀ s w, (∃ a, 2 * idealSiteBoxRadius α m < |w a|) → f s w = 0)
    (g : Finset α → (JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) → ℂ)
    (hvalue : ∀ s (w : JetAmbientIndex (fun _ : Fin m => Unit) J → ℝ),
      (∀ i, |w i| ≤ 1 / 4) → 2 * g s (fun i => (w i : UnitAddCircle)) =
        f s (allocatedAmbientSiteCoordinates B U b S o w))
    (y : EuclideanJetLayers U jets) :
    allocatedCoveredComplexProfileDensity B U b hR hσ S x u v rows hb o bW d quarter
        (allocatedSiteTermDensity B U b S x modulus residue f) y =
      (2 : ℂ) ^ Fintype.card (Finset α) *
      (allocatedCoveredProfileDensity B U b hR hσ S x u v rows hb o bW d quarter
        (allocatedMaskedSiteEnvelope B U b S x modulus residue) y : ℂ) *
        ∏ s, g s (coveredJetAmbientTorus U d (coveredBooleanSiteValue U y s)) := by
  exact allocatedCoveredSiteTerm_unit_ambient_factorization B U b hR hσ S x u v hb o bW d
    hσ1 C hC hchart hsmall modulus residue f hsupport g hvalue y

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.BooleanCubeKernel

open Module Submodule _root_.Set _root_.OAI.Set VectorPolynomial
open scoped Classical BigOperators NNReal

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

theorem exists_allocated_physical_unit_site_factors
    (hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hinv : ∀ j w, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm w‖ ≤ Cinv j * ‖w‖)
    (hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B (Fin dim) Cinv
      (allocatedSiteRootAllowance (Fin dim) m) j)
    (modulus : ℕ)
    (residue : ∀ j : Fin m, Matrix (BoundedBooleanJet (Fin dim) (j.val + 1))
      (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (f : Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)
    (hsupport : ∀ s w, (∃ a, 2 * idealSiteBoxRadius (Fin dim) m < |w a|) → f s w = 0)
    (C : Fin m → ℝ≥0)
    (hforward : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K) (L : ℝ≥0)
    (hL : ∀ s, LipschitzWith L (f s)) (hf : ∀ s w, ‖f s w‖ ≤ 1)
    {X : Type*} :
    ∃ g : Finset (Fin dim) → (JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) → ℂ,
      (∀ s, LipschitzWith (L * (K * ∑ j, C j * Fintype.card (J j))) (g s)) ∧
      (∀ s z, ‖g s z‖ ≤ 1) ∧
      ∀ (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
        (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
        (hm : ∀ j e, coefficients (p j) e ∈ U j) (cube : X → (Unit ⊕ Fin dim) → ℤ),
      allocatedCoveredComplexProfileDensity B U b hR hσ S x u v rows hb o bW d quarter
          (allocatedSiteTermDensity B U b S x modulus residue f) (physicalCubeEuclideanSample U d p hm cube) =
        (2 : ℂ) ^ Fintype.card (Finset (Fin dim)) *
        (allocatedCoveredProfileDensity B U b hR hσ S x u v rows hb o bW d quarter
          (allocatedMaskedSiteEnvelope B U b S x modulus residue) (physicalCubeEuclideanSample U d p hm cube) : ℂ) *
          ∏ s, g s (fun a : JetAmbientIndex (fun _ : Fin m => Unit) J =>
            ((eval (fun t => (physicalCubeVertexValue cube s t : ℝ)) (p a.1)) a.2.2 : UnitAddCircle)) := by
  obtain ⟨g, hg, hgb, hgv⟩ := exists_allocated_physical_lipschitz_site_factors B U b hR hσ S x u v hb o bW d
    hσ1 Cinv hCinv hinv hsmall modulus residue f hsupport C hforward K hK L hL hf (X := X)
  refine ⟨fun s z => g s z / 2, ?_, ?_, ?_⟩
  · exact fun s => lipschitz_complex_half (g s) (L * (K * ∑ j, C j * Fintype.card (J j))) (hg s)
  · exact fun s z => complex_half_norm_le_one (hgb s z)
  · intro p hp hm cube
    rw [hgv p hp hm cube, complex_prod_halves]
    ring

end Erdos3.BooleanCubeKernel

end

end OAI
