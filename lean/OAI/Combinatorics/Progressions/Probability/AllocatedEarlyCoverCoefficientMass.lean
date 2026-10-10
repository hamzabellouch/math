import OAI.Combinatorics.Progressions.Geometry.AllocatedSpatialIdealCoverExpansion
import OAI.Combinatorics.Progressions.Probability.AllocatedProbabilityWindowMesh

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem integral_prefactor_finite_expansion {Y T : Type*} [MeasurableSpace Y] [Fintype T]
    (μ : Measure Y) (φ : Y → ℂ) (c : T → ℂ) (F : T → Y → ℂ)
    (hφ : Integrable φ μ) (hF : ∀ t, AEStronglyMeasurable (F t) μ)
    {K : ℝ} (hbound : ∀ t y, ‖F t y‖ ≤ K) :
    (∫ y, φ y * ∑ t, c t * F t y ∂μ) =
      ∑ t, c t * ∫ y, φ y * F t y ∂μ := by
  have hi (t : T) : Integrable (fun y => c t * (φ y * F t y)) μ :=
    (hφ.mul_bdd (hF t) (Filter.Eventually.of_forall (hbound t))).const_mul _
  calc
    _ = ∫ y, ∑ t, c t * (φ y * F t y) ∂μ := by
      congr 1
      funext y
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ = ∑ t, ∫ y, c t * (φ y * F t y) ∂μ :=
      integral_finsetSum _ (fun t _ => hi t)
    _ = _ := by simp only [integral_const_mul]

theorem norm_integral_prefactor_le {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)
    {φ F : Y → ℂ} {K M : ℝ} (hφ : Integrable φ μ) (hK : 0 ≤ K)
    (hmass : (∫ y, ‖φ y‖ ∂μ) ≤ M)
    (hF : ∀ y, φ y ≠ 0 → ‖F y‖ ≤ K) :
    ‖∫ y, φ y * F y ∂μ‖ ≤ K * M := by
  have hb (y : Y) : ‖φ y * F y‖ ≤ K * ‖φ y‖ := by
    by_cases hy : φ y = 0
    · simp only [hy, zero_mul, norm_zero, mul_zero, le_refl]
    · rw [norm_mul, mul_comm K]
      exact mul_le_mul_of_nonneg_left (hF y hy) (norm_nonneg _)
  calc
    _ ≤ ∫ y, K * ‖φ y‖ ∂μ :=
      norm_integral_le_of_norm_le (hφ.norm.const_mul K) (Filter.Eventually.of_forall hb)
    _ = K * ∫ y, ‖φ y‖ ∂μ := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hmass hK

theorem norm_integrated_sum_le {Y T : Type*} [MeasurableSpace Y] [Fintype T]
    (μ : Measure Y) (φ : Y → ℂ) (c : T → ℂ) (F : T → Y → ℂ)
    {K M : ℝ} (hφ : Integrable φ μ) (hK : 0 ≤ K)
    (hmass : (∫ y, ‖φ y‖ ∂μ) ≤ M)
    (hF : ∀ t, c t ≠ 0 → ∀ y, φ y ≠ 0 → ‖F t y‖ ≤ K) :
    ‖∑ t, c t * ∫ y, φ y * F t y ∂μ‖ ≤ K * M * ∑ t, ‖c t‖ := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ t, (K * M) * ‖c t‖ := by
      apply Finset.sum_le_sum
      intro t _
      by_cases ht : c t = 0
      · simp only [ht, zero_mul, norm_zero, mul_zero, le_refl]
      · rw [norm_mul, mul_comm (K * M)]
        exact mul_le_mul_of_nonneg_left
          (norm_integral_prefactor_le μ hφ hK hmass (hF t ht)) (norm_nonneg _)
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem norm_integrated_mixture_le {Y I : Type*} [MeasurableSpace Y] [Fintype I]
    {T : I → Type*} [∀ i, Fintype (T i)]
    (μ : Measure Y) (law : FiniteProbabilityWeights I)
    (φ : I → Y → ℂ) (c : ∀ i, T i → ℂ) (F : ∀ i, T i → Y → ℂ)
    {K M : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ i, 0 < law.weight i → Integrable (φ i) μ)
    (hmass : ∀ i, 0 < law.weight i → (∫ y, ‖φ i y‖ ∂μ) ≤ M)
    (hF : ∀ i, 0 < law.weight i → ∀ t, c i t ≠ 0 → ∀ y, φ i y ≠ 0 → ‖F i t y‖ ≤ K) :
    ‖law.complexMean (fun i => ∑ t, c i t * ∫ y, φ i y * F i t y ∂μ)‖ ≤
      K * M * law.mean (fun i => ∑ t, ‖c i t‖) := by
  apply (law.norm_complexMean_le_mean_norm _).trans
  calc
    _ ≤ law.mean (fun i => K * M * ∑ t, ‖c i t‖) := by
      apply law.mean_mono_on_support
      intro i hi
      have hpos : 0 < law.weight i := lt_of_le_of_ne (law.nonneg i) (Ne.symm hi)
      exact norm_integrated_sum_le μ (φ i) (c i) (F i) (hφ i hpos) hK
        (hmass i hpos) (hF i hpos)
    _ = _ := by
      unfold FiniteProbabilityWeights.mean
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem exists_large_integrated_mixture_term {Y I : Type*} [MeasurableSpace Y] [Fintype I]
    {T : I → Type*} [∀ i, Fintype (T i)]
    (μ : Measure Y) (law : FiniteProbabilityWeights I)
    (φ : I → Y → ℂ) (c : ∀ i, T i → ℂ) (F : ∀ i, T i → Y → ℂ)
    {δ M C : ℝ} (hδ : 0 < δ) (hM : 0 < M) (hC : 0 < C)
    (hφ : ∀ i, 0 < law.weight i → Integrable (φ i) μ)
    (hmass : ∀ i, 0 < law.weight i → (∫ y, ‖φ i y‖ ∂μ) ≤ M)
    (hc : law.mean (fun i => ∑ t, ‖c i t‖) ≤ C)
    (hlower : δ ≤ ‖law.complexMean (fun i => ∑ t, c i t * ∫ y, φ i y * F i t y ∂μ)‖) :
    ∃ i, 0 < law.weight i ∧ ∃ t, c i t ≠ 0 ∧ ∃ y, φ i y ≠ 0 ∧
      δ / (2 * M * C) ≤ ‖F i t y‖ := by
  classical
  by_contra h
  push Not at h
  let K := δ / (2 * M * C)
  have hK : 0 ≤ K := (div_pos hδ (by positivity)).le
  have hb := norm_integrated_mixture_le μ law φ c F hK hφ hmass
    (fun i hi t ht y hy => (h i hi t ht y hy).le)
  have hupper : K * M * law.mean (fun i => ∑ t, ‖c i t‖) ≤ K * M * C :=
    mul_le_mul_of_nonneg_left hc (mul_nonneg hK hM.le)
  have heq : K * M * C = δ / 2 := by
    dsimp only [K]
    field_simp
  have hbad := hlower.trans (hb.trans hupper)
  rw [heq] at hbad
  linarith only [hbad, hδ]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] activeAmbientAxisDecidableEq fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ) (q : ℕ) [NeZero q]
variable (W : (r : AllocatedPositiveResidue (dim := dim) B U b S q) →
  AllocatedResidueSiteWitness (dim := dim) B U b S q r.val)

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "O" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
local notation "pos" => AllocatedPositiveResidue (dim := dim) B U b S q
abbrev allocatedResidueCoverTerms (r : pos) := ∀ a, ((W r).expansion a).Term

local notation "terms" => allocatedResidueCoverTerms B U b S q W
local notation "tuples" => principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
local notation "residueLaw" => FiniteProbabilityWeights.fiberLaw (tuples) (principalResidueLabel q)

noncomputable def allocatedPositiveResidueLaw : FiniteProbabilityWeights pos :=
  (residueLaw).positiveRestriction
    (fun r => 0 < (tuples).mass (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
    (fun r => by rw [FiniteProbabilityWeights.fiberLaw_weight_eq_mass])

theorem allocatedPositiveResidueLaw_mean (F : pos → ℝ) :
    (allocatedPositiveResidueLaw (dim := dim) B U b S q).mean F =
      (residueLaw).mean (fun r =>
        if hr : 0 < (tuples).mass (Finset.univ.filter (fun y => principalResidueLabel q y = r))
        then F ⟨r, hr⟩ else 0) :=
  (residueLaw).positiveRestriction_mean _ _ F

theorem allocatedPositiveResidueLaw_complexMean (F : pos → ℂ) :
    (allocatedPositiveResidueLaw (dim := dim) B U b S q).complexMean F =
      (residueLaw).complexMean (fun r =>
        if hr : 0 < (tuples).mass (Finset.univ.filter (fun y => principalResidueLabel q y = r))
        then F ⟨r, hr⟩ else 0) :=
  (residueLaw).positiveRestriction_complexMean _ _ F

theorem allocatedPositiveResidueLaw_coverMass :
    (allocatedPositiveResidueLaw (dim := dim) B U b S q).mean
      (fun r => ∑ k, ‖coverSiteCoefficient (W r).expansion k‖) =
        allocatedResidueCoverCoefficientMass B U b S q W :=
  allocatedPositiveResidueLaw_mean B U b S q _

theorem allocatedPositiveResidueLaw_jointMass_le (T : pos → Type*) [∀ r, Fintype (T r)]
    (a : ∀ r, T r → ℂ) {Cs Cc : ℝ} (hCs : 0 ≤ Cs)
    (ha : ∀ r, (∑ t, ‖a r t‖) ≤ Cs)
    (hc : allocatedResidueCoverCoefficientMass B U b S q W ≤ Cc) :
    (allocatedPositiveResidueLaw (dim := dim) B U b S q).mean
      (fun r => ∑ t : T r × terms r, ‖a r t.1 * coverSiteCoefficient (W r).expansion t.2‖) ≤ Cs * Cc := by
  have heq (r : pos) :
      (∑ t : T r × terms r, ‖a r t.1 * coverSiteCoefficient (W r).expansion t.2‖) =
        (∑ t, ‖a r t‖) * ∑ k, ‖coverSiteCoefficient (W r).expansion k‖ := by
    rw [Fintype.sum_prod_type]
    simp_rw [norm_mul, ← Finset.mul_sum]
    exact (Finset.sum_mul _ _ _).symm
  calc
    _ ≤ (allocatedPositiveResidueLaw (dim := dim) B U b S q).mean
        (fun r => Cs * ∑ k, ‖coverSiteCoefficient (W r).expansion k‖) := by
      apply FiniteProbabilityWeights.mean_mono
      intro r
      rw [heq]
      exact mul_le_mul_of_nonneg_right (ha r) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    _ = Cs * allocatedResidueCoverCoefficientMass B U b S q W := by
      rw [FiniteProbabilityWeights.mean_const_mul, allocatedPositiveResidueLaw_coverMass]
    _ ≤ _ := mul_le_mul_of_nonneg_left hc hCs

variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (x : G → IntegerScalarCubeBox (Fin dim) S.value)

noncomputable def allocatedResidueIdealWindowPrefactor (δ : ℝ≥0) (r : pos) : EuclideanJetLayers U O → ℂ :=
  allocatedGlobalWindowPrefactor B U b hR hσ S rowSets d x q
    (W r).representative (W r).positive hb o bW
    (allocatedPhysicalLongIdeal B U b hR S rowSets δ)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "residue" => (fun (r : pos) j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
  (principalAxisRestrict grid (AllocatedResidueSiteWitness.representative (W r))) rows j
  (principalAxisRestrict (fun a => ¬grid a) (AllocatedResidueSiteWitness.representative (W r)))) q)

noncomputable def allocatedWindowCoverMixture (δ : ℝ≥0)
    (T : pos → Type*) [∀ r, Fintype (T r)] (a : ∀ r, T r → ℂ)
    (F : ∀ r, T r × terms r → EuclideanJetLayers U O → ℂ) : ℂ :=
  (residueLaw).complexMean (fun r =>
    if hr : 0 < (tuples).mass (Finset.univ.filter (fun y => principalResidueLabel q y = r)) then
      let rr : pos := ⟨r, hr⟩
      ∫ y, allocatedResidueIdealWindowPrefactor B U b hR hσ S q W hb o bW d x δ rr y *
        ∑ t : T rr × terms rr, (a rr t.1 * coverSiteCoefficient (W rr).expansion t.2) * F rr t y ∂haar
    else 0)

theorem allocatedIdealWindow_mixture_selection {p c P e : ℝ}
    (hp : 0 ≤ p) (hc : 0 ≤ c) (hP : 0 ≤ P) (he : 0 ≤ e) (hdim : dim ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (hR1 : ∀ j, R j ≤ 1) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp c)
    (δ : ℝ≥0) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδe : (δ : ℝ)⁻¹ ≤ Real.exp e)
    (hmask : ∀ (r : pos) j z, 0 ≤ allocatedIntegerKernelMask B U b S x rows j q (residue r j) z ∧
      allocatedIntegerKernelMask B U b S x rows j q (residue r j) z ≤ Real.exp (allocatedSiteKernelMaskLog m P))
    (T : pos → Type*) [∀ r, Fintype (T r)] (a : ∀ r, T r → ℂ)
    (F : ∀ r, T r × terms r → EuclideanJetLayers U O → ℂ)
    (hF : ∀ r t, Measurable (F r t)) (hFbound : ∀ r t y, ‖F r t y‖ ≤ 1)
    {η Cs Cc : ℝ} (hη : 0 < η) (hCs : 0 < Cs) (hCc : 0 < Cc)
    (ha : ∀ r, (∑ t, ‖a r t‖) ≤ Cs)
    (hcover : allocatedResidueCoverCoefficientMass B U b S q W ≤ Cc)
    (hlower : η ≤ ‖allocatedWindowCoverMixture B U b hR hσ S q W hb o bW d x ν δ T a F‖) :
    ∃ (r : pos) (t : T r) (k : terms r) (y : EuclideanJetLayers U O),
      a r t ≠ 0 ∧ coverSiteCoefficient (W r).expansion k ≠ 0 ∧
      allocatedResidueIdealWindowPrefactor B U b hR hσ S q W hb o bW d x δ r y ≠ 0 ∧
      η / (2 * Real.exp (allocatedIdealWindowMassLog m dim p c P e) * (Cs * Cc)) ≤ ‖F r (t, k) y‖ := by
  let φ := allocatedResidueIdealWindowPrefactor B U b hR hσ S q W hb o bW d x δ
  let coeff := fun (r : pos) (t : T r × terms r) => a r t.1 * coverSiteCoefficient (W r).expansion t.2
  let law := allocatedPositiveResidueLaw (dim := dim) B U b S q
  have hmass (r : pos) : Integrable (φ r) haar ∧
      (∫ y, ‖φ r y‖ ∂haar) ≤ Real.exp (allocatedIdealWindowMassLog m dim p c P e) :=
    allocatedIdealGlobalWindow_mass B U b hR hσ S rowSets d x q (W r).representative
      (W r).positive hb o bW ν hp hc hP he hdim hvars hI hn hR1 hRi δ hδ hδ1 hδe (hmask r)
  have horiginal : allocatedWindowCoverMixture B U b hR hσ S q W hb o bW d x ν δ T a F =
      law.complexMean (fun r => ∫ y, φ r y * ∑ t, coeff r t * F r t y ∂haar) := by
    unfold allocatedWindowCoverMixture
    exact (allocatedPositiveResidueLaw_complexMean B U b S q
      (fun r => ∫ y, φ r y * ∑ t, coeff r t * F r t y ∂haar)).symm
  have hexpand : law.complexMean (fun r => ∫ y, φ r y * ∑ t, coeff r t * F r t y ∂haar) =
      law.complexMean (fun r => ∑ t, coeff r t * ∫ y, φ r y * F r t y ∂haar) := by
    apply congrArg law.complexMean
    funext r
    exact integral_prefactor_finite_expansion haar (φ r) (coeff r) (F r) (hmass r).1
      (fun t => (hF r t).aestronglyMeasurable) (hFbound r)
  rw [horiginal, hexpand] at hlower
  have hcoeff := allocatedPositiveResidueLaw_jointMass_le B U b S q W T a hCs.le ha hcover
  obtain ⟨r, _hr, t, ht, y, hy, hgain⟩ := exists_large_integrated_mixture_term haar law φ coeff F
    hη (Real.exp_pos _) (mul_pos hCs hCc) (fun r _ => (hmass r).1) (fun r _ => (hmass r).2) hcoeff hlower
  have hparts := mul_ne_zero_iff.mp ht
  exact ⟨r, t.1, t.2, y, hparts.1, hparts.2, hy, hgain⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] activeAmbientAxisDecidableEq fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ) (q : ℕ) [NeZero q]
variable (W : (r : AllocatedPositiveResidue (dim := dim) B U b S q) →
  AllocatedResidueSiteWitness (dim := dim) B U b S q r.val)

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "O" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
local notation "terms" => allocatedResidueCoverTerms B U b S q W

variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (x : G → IntegerScalarCubeBox (Fin dim) S.value)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "residue" => (fun (r : AllocatedPositiveResidue (dim := dim) B U b S q) j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
  (principalAxisRestrict grid (AllocatedResidueSiteWitness.representative (W r))) rows j
  (principalAxisRestrict (fun a => ¬grid a) (AllocatedResidueSiteWitness.representative (W r)))) q)

theorem allocatedIdealWindow_probability_selection {D p P e : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin dim) O D)
    (hp : 0 ≤ p) (hP : 0 ≤ P) (he : 0 ≤ e)
    (hRP : ∀ j, R j ≤ Real.exp p) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp p)
    (δ : ℝ≥0) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδe : (δ : ℝ)⁻¹ ≤ Real.exp e)
    (hmesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤
      physicalIdealErrorShare 0 (allocatedIdealMeshEnvelope m D p e))
    (hmask : ∀ (r : AllocatedPositiveResidue (dim := dim) B U b S q) j z,
      0 ≤ allocatedIntegerKernelMask B U b S x rows j q (residue r j) z ∧
      allocatedIntegerKernelMask B U b S x rows j q (residue r j) z ≤ Real.exp (allocatedSiteKernelMaskLog m P))
    (T : AllocatedPositiveResidue (dim := dim) B U b S q → Type*) [∀ r, Fintype (T r)]
    (a : ∀ r, T r → ℂ) (F : ∀ r, T r × terms r → EuclideanJetLayers U O → ℂ)
    (hF : ∀ r t, Measurable (F r t)) (hFbound : ∀ r t y, ‖F r t y‖ ≤ 1)
    {η C : ℝ} (hη : 0 < η) (hC : 0 < C)
    (hcoeff : (allocatedPositiveResidueLaw (dim := dim) B U b S q).mean
      (fun r => ∑ t : T r × terms r, ‖a r t.1 * coverSiteCoefficient (W r).expansion t.2‖) ≤ C)
    (hlower : η ≤ ‖allocatedWindowCoverMixture B U b hR hσ S q W hb o bW d x ν δ T a F‖) :
    ∃ (r : AllocatedPositiveResidue (dim := dim) B U b S q) (t : T r) (k : terms r)
      (y : EuclideanJetLayers U O),
      a r t ≠ 0 ∧ coverSiteCoefficient (W r).expansion k ≠ 0 ∧
      allocatedResidueIdealWindowPrefactor B U b hR hσ S q W hb o bW d x δ r y ≠ 0 ∧
      η / (2 * Real.exp (allocatedSiteFamilyWindowLog D + D * allocatedSiteKernelMaskLog m P + 1) * C) ≤
        ‖F r (t, k) y‖ := by
  let φ := allocatedResidueIdealWindowPrefactor B U b hR hσ S q W hb o bW d x δ
  let coeff := fun (r : AllocatedPositiveResidue (dim := dim) B U b S q) (t : T r × terms r) =>
    a r t.1 * coverSiteCoefficient (W r).expansion t.2
  let law := allocatedPositiveResidueLaw (dim := dim) B U b S q
  have hmass (r : AllocatedPositiveResidue (dim := dim) B U b S q) : Integrable (φ r) haar ∧
      (∫ y, ‖φ r y‖ ∂haar) ≤
        Real.exp (allocatedSiteFamilyWindowLog D + D * allocatedSiteKernelMaskLog m P + 1) :=
    allocatedIdealGlobalWindow_probability_mass B U b hR S rowSets hσ d x q (W r).representative
      (W r).positive hb o bW ν hdim hp he hP hRP hRi δ hδ hδ1 hδe hmesh (hmask r)
  have horiginal : allocatedWindowCoverMixture B U b hR hσ S q W hb o bW d x ν δ T a F =
      law.complexMean (fun r => ∫ y, φ r y * ∑ t, coeff r t * F r t y ∂haar) := by
    unfold allocatedWindowCoverMixture
    exact (allocatedPositiveResidueLaw_complexMean B U b S q
      (fun r => ∫ y, φ r y * ∑ t, coeff r t * F r t y ∂haar)).symm
  have hexpand : law.complexMean (fun r => ∫ y, φ r y * ∑ t, coeff r t * F r t y ∂haar) =
      law.complexMean (fun r => ∑ t, coeff r t * ∫ y, φ r y * F r t y ∂haar) := by
    apply congrArg law.complexMean
    funext r
    exact integral_prefactor_finite_expansion haar (φ r) (coeff r) (F r) (hmass r).1
      (fun t => (hF r t).aestronglyMeasurable) (hFbound r)
  rw [horiginal, hexpand] at hlower
  obtain ⟨r, _hr, t, ht, y, hy, hgain⟩ := exists_large_integrated_mixture_term haar law φ coeff F
    hη (Real.exp_pos _) hC (fun r _ => (hmass r).1) (fun r _ => (hmass r).2) hcoeff hlower
  have hparts := mul_ne_zero_iff.mp ht
  exact ⟨r, t.1, t.2, y, hparts.1, hparts.2, hy, hgain⟩

theorem allocatedIdealWindow_probability_volume_selection {D p P e : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin dim) O D)
    (hp : 0 ≤ p) (hP : 0 ≤ P) (he : 0 ≤ e)
    (hRP : ∀ j, R j ≤ Real.exp p) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp p)
    (δ : ℝ≥0) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδe : (δ : ℝ)⁻¹ ≤ Real.exp e)
    (hmesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤
      physicalIdealErrorShare 0 (allocatedIdealMeshEnvelope m D p e))
    (hmask : ∀ (r : AllocatedPositiveResidue (dim := dim) B U b S q) j z,
      0 ≤ allocatedIntegerKernelMask B U b S x rows j q (residue r j) z ∧
      allocatedIntegerKernelMask B U b S x rows j q (residue r j) z ≤ Real.exp (allocatedSiteKernelMaskLog m P))
    (T : AllocatedPositiveResidue (dim := dim) B U b S q → Type*) [∀ r, Fintype (T r)]
    (a : ∀ r, T r → ℂ) (F : ∀ r, T r × terms r → EuclideanJetLayers U O → ℂ)
    (hF : ∀ r t, Measurable (F r t)) (hFbound : ∀ r t y, ‖F r t y‖ ≤ 1)
    {η V Qc : ℝ} (hη : 0 < η) (hV : 0 < V)
    (hcoeff : (allocatedPositiveResidueLaw (dim := dim) B U b S q).mean
      (fun r => ∑ t : T r × terms r, ‖a r t.1 * coverSiteCoefficient (W r).expansion t.2‖) ≤ Real.exp Qc / V)
    (hlower : η ≤ ‖allocatedWindowCoverMixture B U b hR hσ S q W hb o bW d x ν δ T a F‖) :
    ∃ (r : AllocatedPositiveResidue (dim := dim) B U b S q) (t : T r) (k : terms r)
      (y : EuclideanJetLayers U O),
      a r t ≠ 0 ∧ coverSiteCoefficient (W r).expansion k ≠ 0 ∧
      allocatedResidueIdealWindowPrefactor B U b hR hσ S q W hb o bW d x δ r y ≠ 0 ∧
      η * V / (2 * Real.exp (allocatedSiteFamilyWindowLog D + D * allocatedSiteKernelMaskLog m P + 1 + Qc)) ≤
        ‖F r (t, k) y‖ := by
  obtain ⟨r, t, k, y, ht, hk, hy, hgain⟩ := allocatedIdealWindow_probability_selection
    B U b hR hσ S q W hb o bW d x ν hdim hp hP he hRP hRi δ hδ hδ1 hδe hmesh hmask
    T a F hF hFbound hη (div_pos (Real.exp_pos _) hV) hcoeff hlower
  refine ⟨r, t, k, y, ht, hk, hy, ?_⟩
  convert hgain using 1
  rw [Real.exp_add]
  field_simp

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] activeAmbientAxisDecidableEq fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (X : Type*) [Fintype X] (modulus : ℕ) [NeZero modulus] (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))

variable (coverWitness : (r : (AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q))) →
  AllocatedResidueSiteWitness (dim := dim) B U b S (residueRefinedPeriod modulus q) r.val)
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ : ℝ} (hW : 0 ≤ W)

noncomputable def allocatedRecenteredCoverCoefficientMass (mesh volume : ℝ) : ℝ :=
  (allocatedPositiveResidueLaw (dim := dim) B U b S (residueRefinedPeriod modulus q)).mean (fun r =>
    ∑ t : (X → SpatialSiteLabel (Fin dim) modulus 4 mesh) ×
        allocatedResidueCoverTerms B U b S (residueRefinedPeriod modulus q) coverWitness r,
      ‖(allocatedSpatialExpansionCoefficient B U b S x X hM selection hx modulus hW mesh
        (principalResidueLabel modulus (wholeReference r.val)) t.1 / ((volume : ℝ) : ℂ)) *
        coverSiteCoefficient (coverWitness r).expansion t.2‖)

theorem allocatedEarlyCoverCoefficient_mass
    {p E : ℝ} (hp : 0 ≤ p) (hE : 0 ≤ E)
    (hG : (Fintype.card G : ℝ) ≤ p) (hX : (Fintype.card X : ℝ) ≤ p)
    (hMP : (M : ℝ) ≤ Real.exp p) (hmod : modulus ≤ M ^ (m + 1))
    (hq : ∀ z, 0 < q z) (hN : ∀ z, 0 < N z) (hτ : 0 < τ)
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ))
          (scalarCubeDifferenceMatrix x) selection))
    {Qcover : ℝ}
    (hcover : allocatedResidueCoverCoefficientMass B U b S (residueRefinedPeriod modulus q) coverWitness ≤
      Real.exp Qcover) :
    let mesh : ℝ := allocatedEarlyRecenteredMesh X selection M modulus p E;
    let costLog : ℝ := coarseSpatialPartitionLog (allocatedEarlyCoarseInput m dim (p + E));
    let volume : ℝ := ∏ z, ∏ i, physicalSpatialOutputScale (Fin dim)
      (trimmedSpatialRootScale τ N q z) (trimmedSpatialSlopeScale W τ N q z) S.value i;
    allocatedRecenteredCoverCoefficientMass B U b S X modulus q wholeReference coverWitness
      x hM selection hx hW mesh volume ≤
      Real.exp (costLog + Qcover) / volume := by
  intro mesh costLog volume
  have hscales (z : X) : 0 < trimmedSpatialRootScale τ N q z ∧
      0 < trimmedSpatialSlopeScale W τ N q z := trimmedSpatial_scales_pos hW hτ N q z (hN z) (hq z)
  have hvolume : 0 < volume := Finset.prod_pos (fun z _ => Finset.prod_pos (fun i _ =>
    physicalSpatialOutputScale_pos (Fin dim) (hscales z).1 (hscales z).2 (Nat.cast_pos.mpr S.positive) i))
  have hcost := allocatedEarlyRecenteredMesh_partition_budget m X selection hp hE hG hX hM hMP hmod
  have hspatial (r : (AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q))) :
      (∑ t : X → SpatialSiteLabel (Fin dim) modulus 4 mesh,
        ‖allocatedSpatialExpansionCoefficient B U b S x X hM selection hx modulus hW mesh
          (principalResidueLabel modulus (wholeReference r.val)) t / ((volume : ℝ) : ℂ)‖) ≤
      Real.exp costLog / volume := by
    exact (allocatedRecenteredSpatialCoefficient_sum_le B U b S X modulus q wholeReference x N mesh
      hM selection hx hW hq hN hτ hbudget hperiod r.val).trans
      (div_le_div_of_nonneg_right hcost.2.2.2 hvolume.le)
  have hfactor : 0 ≤ Real.exp costLog / volume := div_nonneg (Real.exp_pos _).le hvolume.le
  have hmass := allocatedPositiveResidueLaw_jointMass_le B U b S (residueRefinedPeriod modulus q) coverWitness
    (fun _ => X → SpatialSiteLabel (Fin dim) modulus 4 mesh)
    (fun r t => allocatedSpatialExpansionCoefficient B U b S x X hM selection hx modulus hW mesh
      (principalResidueLabel modulus (wholeReference r.val)) t / ((volume : ℝ) : ℂ))
    hfactor hspatial hcover
  apply hmass.trans_eq
  rw [Real.exp_add]
  ring

end Erdos3.VectorPolynomial

end

end OAI
