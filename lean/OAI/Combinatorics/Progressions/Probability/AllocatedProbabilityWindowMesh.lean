import OAI.Combinatorics.Progressions.Estimates.AllocatedIdealPhysicalCover
import OAI.Combinatorics.Progressions.Estimates.CanonicalSiteBlocks

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators Classical NNReal

universe uα

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] activeAmbientAxisDecidableEq

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)] (d : ℕ) [NeZero d]
variable (x : G → IntegerScalarCubeBox α S.value) (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "O" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "activeAxes" => {a : {a // grid a} // allocatedActiveGrid B U b S a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "siteH" => (fun a : activeAxes => allocatedNaturalSiteRadius (G := G) B
  (Sigma.fst (ig (Subtype.val a))) (Sigma.snd (ig (Subtype.val a)))
  (rowSets (Sigma.fst (ig (Subtype.val a)))) + 1 / 4)
local notation "chart" => mixedCoveredJetChart U o b hb bW d

variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)
variable (e : {a : {a // allocatedGridAxis (I := I) U b S.value a} // allocatedActiveGrid B U b S a} →
  ScalarSiteExpansion.{uα,uα} (Finset α))

local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j))

omit [Fintype α] [DecidableEq α] [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedComplexGridMultiplier_real_div
    (g : AllocatedFrozenJetRows B U b S O → ℝ) (N : ℝ) (y : EuclideanJetLayers U O) :
    allocatedComplexGridMultiplier B U b S O hb o bW d (fun z => (g z : ℂ) / (N : ℂ)) y =
      ((allocatedChartGridMultiplier B U b S O hb o bW d g y : ℝ) : ℂ) / (N : ℂ) := by
  by_cases hy : y ∈ chart '' region
  · obtain ⟨z, hz, rfl⟩ := hy
    rw [allocatedComplexGridMultiplier_apply B U b S O hb o bW d _ z hz,
      allocatedChartGridMultiplier_apply B U b S O hb o bW d _ z hz]
  · rw [allocatedComplexGridMultiplier_zero B U b S O hb o bW d _ y hy,
      allocatedChartGridMultiplier, restrictedChartDensity_zero _ _ _ _ hy,
      Complex.ofReal_zero, zero_div]

local notation "laws" => allocatedSupportedGridJetPMF B U b hR hσ S x rows q (principalResidueLabel q y₀) hcell
local notation "windows" => allocatedGridSiteWindow B rowSets U b S
local notation "weight" => allocatedGridWindowWeight B U b S O (allocatedActiveGrid B U b S) windows laws
local notation "χ" => allocatedChartGridMultiplier B U b S O hb o bW d weight
local notation "profile" => allocatedWholeMaskedGridlessProfile B U b S x y₀ rows hb o bW d q f
local notation "volumeN" => allocatedActiveNaturalVolume B U b S rowSets
local notation "globalPrefactor" => allocatedGlobalWindowPrefactor B U b hR hσ S rowSets d x q y₀ hcell hb o bW f

theorem allocatedGlobalWindowPrefactor_eq_weight (y : EuclideanJetLayers U O) :
    globalPrefactor y = ((χ y * profile y : ℝ) : ℂ) / (volumeN : ℂ) := by
  have he : allocatedSelectedGridExtension B U b hR hσ S x rows q (principalResidueLabel q y₀) hcell
      (allocatedActiveGrid B U b S)
      (fun z => if ∀ a, z a ∈ windows a.val then 1 else 0) volumeN =
      fun z => (weight z : ℂ) / (volumeN : ℂ) := by
    funext z
    exact selectedProductExtension_windowIndicator (allocatedActiveGrid B U b S)
      (fun a v => (laws a v).toReal) windows volumeN z
  rw [allocatedGlobalWindowPrefactor, he,
    allocatedComplexGridMultiplier_real_div B U b S rowSets d hb o bW weight volumeN y]
  rw [Complex.ofReal_mul]
  ring

theorem allocatedGlobalWindowPrefactor_norm (y : EuclideanJetLayers U O) :
    ‖globalPrefactor y‖ = |χ y * profile y| / volumeN := by
  rw [allocatedGlobalWindowPrefactor_eq_weight B U b hR hσ S rowSets d x q y₀ hcell hb o bW f,
    norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (allocatedActiveNaturalVolume_pos B U b hR S rowSets)]

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))
local notation "residue" => (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
  (principalAxisRestrict grid y₀) rows j (principalAxisRestrict (fun a => ¬grid a) y₀)) q)

theorem allocatedGlobalWindowPrefactor_mass
    (hf : Measurable f) {T C Cf : ℝ} (hT : 0 ≤ T) (hs : ∀ v, T < ‖v‖ → f v = 0)
    (hC : 1 ≤ C) (hCf : 0 ≤ Cf) (hfb : ∀ v, |f v| ≤ Cf)
    (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x rows j q (residue j) z ∧
      allocatedIntegerKernelMask B U b S x rows j q (residue j) z ≤ C) :
    Integrable globalPrefactor haar ∧
      (∫ y, ‖globalPrefactor y‖ ∂haar) ≤ allocatedSiteFamilyWindowVolume (G := G) B rowSets *
        ((C ^ Fintype.card (LayerSamplerAxis I n) * Cf) *
          (2 * T + 1) ^ Fintype.card (Σ a : LayerSamplerAxis I n, O (Sigma.fst a))) := by
  have hχ := fun z hz => allocatedChartGridMultiplier_apply B U b S O hb o bW d weight z hz
  have hmass := allocatedWholeMaskedGridlessProfile_window_mass B U b S x y₀ rows hb o bW d ν q
    (allocatedActiveGrid B U b S) windows laws χ hχ f hf hT hs hC hCf hfb hm
  have heq : globalPrefactor = fun y => ((χ y * profile y : ℝ) : ℂ) / (volumeN : ℂ) :=
    funext (allocatedGlobalWindowPrefactor_eq_weight B U b hR hσ S rowSets d x q y₀ hcell hb o bW f)
  constructor
  · rw [heq]
    exact hmass.1.ofReal.div_const _
  · simp_rw [allocatedGlobalWindowPrefactor_norm B U b hR hσ S rowSets d x q y₀ hcell hb o bW f]
    rw [integral_div]
    apply (div_le_iff₀ (allocatedActiveNaturalVolume_pos B U b hR S rowSets)).mpr
    have hC0 : 0 ≤ C := zero_le_one.trans hC
    have hb0 : 0 ≤ (C ^ Fintype.card (LayerSamplerAxis I n) * Cf) *
        (2 * T + 1) ^ Fintype.card (Σ a : LayerSamplerAxis I n, O (Sigma.fst a)) := by positivity
    apply hmass.2.trans
    have hwin := mul_le_mul_of_nonneg_right (allocatedActiveSiteWindow_volume B rowSets U b S hR) hb0
    convert hwin using 1
    ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators Classical NNReal

universe uα

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] activeAmbientAxisDecidableEq

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)] (d : ℕ) [NeZero d]
variable (x : G → IntegerScalarCubeBox α S.value) (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "O" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "activeAxes" => {a : {a // grid a} // allocatedActiveGrid B U b S a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "siteH" => (fun a : activeAxes => allocatedNaturalSiteRadius (G := G) B
  (Sigma.fst (ig (Subtype.val a))) (Sigma.snd (ig (Subtype.val a)))
  (rowSets (Sigma.fst (ig (Subtype.val a)))) + 1 / 4)
local notation "chart" => mixedCoveredJetChart U o b hb bW d

variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)
variable (e : {a : {a // allocatedGridAxis (I := I) U b S.value a} // allocatedActiveGrid B U b S a} →
  ScalarSiteExpansion.{uα,uα} (Finset α))

local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j))

local notation "laws" => allocatedSupportedGridJetPMF B U b hR hσ S x rows q (principalResidueLabel q y₀) hcell
local notation "windows" => allocatedGridSiteWindow B rowSets U b S
local notation "weight" => allocatedGridWindowWeight B U b S O (allocatedActiveGrid B U b S) windows laws
local notation "χ" => allocatedChartGridMultiplier B U b S O hb o bW d weight
local notation "profile" => allocatedWholeMaskedGridlessProfile B U b S x y₀ rows hb o bW d q f
local notation "volumeN" => allocatedActiveNaturalVolume B U b S rowSets
local notation "globalPrefactor" => allocatedGlobalWindowPrefactor B U b hR hσ S rowSets d x q y₀ hcell hb o bW f

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))
local notation "residue" => (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
  (principalAxisRestrict grid y₀) rows j (principalAxisRestrict (fun a => ¬grid a) y₀)) q)

theorem allocatedGlobalWindowPrefactor_integral_mass
    (hf : Measurable f)
    (hi : Integrable (allocatedUnmaskedLongProfileDensity B U b S f) (allocatedLongJetReference B U b S O))
    {C Mf : ℝ} (hC : 1 ≤ C)
    (hMf : (∫ z, |allocatedUnmaskedLongProfileDensity B U b S f z| ∂allocatedLongJetReference B U b S O) ≤ Mf)
    (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x rows j q (residue j) z ∧
      allocatedIntegerKernelMask B U b S x rows j q (residue j) z ≤ C) :
    Integrable globalPrefactor haar ∧
      (∫ y, ‖globalPrefactor y‖ ∂haar) ≤ allocatedSiteFamilyWindowVolume (G := G) B rowSets *
        (C ^ Fintype.card (LayerSamplerAxis I n) * Mf) := by
  have hχ := fun z hz => allocatedChartGridMultiplier_apply B U b S O hb o bW d weight z hz
  have hmass := allocatedWholeMaskedGridlessProfile_window_integral_mass B U b S x y₀ rows hb o bW d ν q
    (allocatedActiveGrid B U b S) windows laws χ hχ f hf hi hC hMf hm
  have heq : globalPrefactor = fun y => ((χ y * profile y : ℝ) : ℂ) / (volumeN : ℂ) :=
    funext (allocatedGlobalWindowPrefactor_eq_weight B U b hR hσ S rowSets d x q y₀ hcell hb o bW f)
  constructor
  · rw [heq]
    exact hmass.1.ofReal.div_const _
  · simp_rw [allocatedGlobalWindowPrefactor_norm B U b hR hσ S rowSets d x q y₀ hcell hb o bW f]
    rw [integral_div]
    apply (div_le_iff₀ (allocatedActiveNaturalVolume_pos B U b hR S rowSets)).mpr
    have hMf0 : 0 ≤ Mf := (integral_nonneg (fun _ => abs_nonneg _)).trans hMf
    have hb0 : 0 ≤ C ^ Fintype.card (LayerSamplerAxis I n) * Mf := by
      exact mul_nonneg (pow_nonneg (zero_le_one.trans hC) _) hMf0
    apply hmass.2.trans
    have hwin := mul_le_mul_of_nonneg_right (allocatedActiveSiteWindow_volume B rowSets U b S hR) hb0
    convert hwin using 1; ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators Classical NNReal

def allocatedIdealSupportCost (m dim : ℕ) : ℕ := 2 ^ (dim + 1) * (dim + 1) ^ m + 4

theorem allocatedIdealSupportCost_bound (m dim : ℕ) :
    2 * (partitionedIdealRadius (Fin dim) m + 1) + 1 ≤
      Real.exp (allocatedIdealSupportCost m dim : ℝ) := by
  have h : 2 * (partitionedIdealRadius (Fin dim) m + 1) + 1 ≤
      (allocatedIdealSupportCost m dim : ℝ) := by
    unfold allocatedIdealSupportCost partitionedIdealRadius
    simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
      Nat.cast_one, pow_succ]
    nlinarith
  exact h.trans (by linarith [Real.add_one_le_exp (allocatedIdealSupportCost m dim : ℝ)])

noncomputable def allocatedIdealWindowMassLog {A : Type*} [Semiring A]
    (m dim : ℕ) (p c P e : A) : A :=
  let D := allocatedComparisonDimension m p
  allocatedSiteFamilyWindowLog D + D * allocatedSiteKernelMaskLog m P +
    D * (c + e) + D * (allocatedIdealSupportCost m dim : ℕ)

theorem allocatedIdealWindowMassLog_nonneg (m dim : ℕ) {p c P e : ℝ}
    (hp : 0 ≤ p) (hc : 0 ≤ c) (hP : 0 ≤ P) (he : 0 ≤ e) :
    0 ≤ allocatedIdealWindowMassLog m dim p c P e := by
  have hD := (allocatedComparisonDimension_bounds m hp).1
  have hw := allocatedSiteFamilyWindowLog_nonneg hD
  have hmask := allocatedSiteKernelMaskLog_nonneg m hP
  unfold allocatedIdealWindowMassLog
  positivity

theorem allocatedIdealWindowMassLog_mono (m dim : ℕ) {p c P e p' c' P' e' : ℝ}
    (hp : 0 ≤ p) (hc : 0 ≤ c) (hP : 0 ≤ P) (he : 0 ≤ e)
    (hpp : p ≤ p') (hcc : c ≤ c') (hPP : P ≤ P') (hee : e ≤ e') :
    allocatedIdealWindowMassLog m dim p c P e ≤ allocatedIdealWindowMassLog m dim p' c' P' e' := by
  have hD := (allocatedComparisonDimension_bounds m hp).1
  have hDD := allocatedComparisonDimension_mono m hp hpp
  have hmask := allocatedSiteKernelMaskLog_nonneg m hP
  have hmask' : allocatedSiteKernelMaskLog m P ≤ allocatedSiteKernelMaskLog m P' := by
    unfold allocatedSiteKernelMaskLog
    gcongr
  have hD' := hD.trans hDD
  have hwin : allocatedSiteFamilyWindowLog (allocatedComparisonDimension m p) ≤
      allocatedSiteFamilyWindowLog (allocatedComparisonDimension m p') := by
    unfold allocatedSiteFamilyWindowLog allocatedSiteAxisWindowLog allocatedSiteCoefficientLog
    gcongr
  exact add_le_add
    (add_le_add (add_le_add hwin (mul_le_mul hDD hmask' hmask hD'))
      (mul_le_mul hDD (add_le_add hcc hee) (add_nonneg hc he) hD'))
    (mul_le_mul_of_nonneg_right hDD (Nat.cast_nonneg _))

theorem exists_allocatedIdealWindowMassLog_bound (m dim : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ {p c P e : ℝ}, 0 ≤ p → 0 ≤ c → 0 ≤ P → 0 ≤ e →
      allocatedIdealWindowMassLog m dim p c P e ≤ (p + c + P + e + a) ^ a := by
  let poly : Polynomial ℕ := allocatedIdealWindowMassLog m dim
    Polynomial.X Polynomial.X Polynomial.X Polynomial.X
  obtain ⟨a, ha, hb⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro p c P e hp hc hP he
  apply (allocatedIdealWindowMassLog_mono m dim hp hc hP he
    (show p ≤ p + c + P + e by linarith) (show c ≤ p + c + P + e by linarith)
    (show P ≤ p + c + P + e by linarith) (show e ≤ p + c + P + e by linarith)).trans
  simpa [poly, allocatedIdealWindowMassLog, allocatedSiteFamilyWindowLog, allocatedSiteAxisWindowLog,
    allocatedSiteCoefficientLog, allocatedComparisonDimension, allocatedSiteKernelMaskLog,
    Polynomial.eval₂_pow] using hb (p + c + P + e) (by positivity)

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (rowSets : Fin m → Finset (Finset (Fin dim)))

local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
local notation "O" => (fun j : Fin m => (rowSets j : Type))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

theorem allocatedPhysicalLongIdeal_zero_outside (hR1 : ∀ j, R j ≤ 1)
    (δ : ℝ≥0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (v : (Σ a : {a // ¬grid a}, O a.val.1) → ℝ)
    (hv : partitionedIdealRadius (Fin dim) m + 1 < ‖v‖) :
    allocatedPhysicalLongIdeal B U b hR S rowSets δ v = 0 := by
  by_contra hne
  have hrad : 0 ≤ partitionedIdealRadius (Fin dim) m + 1 :=
    add_nonneg (partitionedIdealRadius_nonneg _ _) zero_le_one
  have hbnd : ‖v‖ ≤ partitionedIdealRadius (Fin dim) m + 1 := by
    apply (pi_norm_le_iff_of_nonneg hrad).mpr
    rintro ⟨a, t⟩
    rw [Real.norm_eq_abs]
    exact (allocatedPhysicalLongIdeal_relative_support B U b hR S rowSets δ hδ hδ1 v hne a t).trans
      (mul_le_of_le_one_right hrad (hR1 a.val.1))
  exact (not_lt_of_ge hbnd) hv

variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)] (d : ℕ) [NeZero d]
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value) (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (hcell : 0 < (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))
local notation "residue" => (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
  (principalAxisRestrict grid y₀) rows j (principalAxisRestrict (fun a => ¬grid a) y₀)) q)

theorem allocatedIdealGlobalWindow_mass {p c P e : ℝ}
    (hp : 0 ≤ p) (hc : 0 ≤ c) (hP : 0 ≤ P) (he : 0 ≤ e) (hdim : dim ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (hR1 : ∀ j, R j ≤ 1) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp c)
    (δ : ℝ≥0) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδe : (δ : ℝ)⁻¹ ≤ Real.exp e)
    (hmask : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x rows j q (residue j) z ∧
      allocatedIntegerKernelMask B U b S x rows j q (residue j) z ≤ Real.exp (allocatedSiteKernelMaskLog m P)) :
    let φ := allocatedGlobalWindowPrefactor B U b hR hσ S rowSets d x q y₀ hcell hb o bW
      (allocatedPhysicalLongIdeal B U b hR S rowSets δ)
    Integrable φ haar ∧ (∫ y, ‖φ y‖ ∂haar) ≤ Real.exp (allocatedIdealWindowMassLog m dim p c P e) := by
  have hd := allocatedComparisonDimensions_of_primitive B rows
    (by simpa only [Fintype.card_fin] using hdim) (fun _ => Subtype.val_injective) hp hvars hI hn
  let D := allocatedComparisonDimension m p
  have hD : 0 ≤ D := hd.nonneg
  have hw := allocatedSiteKernelMaskLog_nonneg m hP
  have hrad : 0 ≤ partitionedIdealRadius (Fin dim) m + 1 :=
    add_nonneg (partitionedIdealRadius_nonneg _ _) zero_le_one
  have hcap := allocatedPhysicalLongIdeal_exp_bound B U b hR S rowSets hc he hd.outputs hRi δ hδ hδe
  have hmass := allocatedGlobalWindowPrefactor_mass B U b hR hσ S rowSets d x q y₀ hcell hb o bW
    (allocatedPhysicalLongIdeal B U b hR S rowSets δ) ν
    (allocatedPhysicalLongIdeal_measurable B U b hR S rowSets δ) hrad
    (allocatedPhysicalLongIdeal_zero_outside B U b hR S rowSets hR1 δ hδ hδ1)
    (Real.one_le_exp hw) (Real.exp_nonneg _) hcap hmask
  refine ⟨hmass.1, hmass.2.trans ?_⟩
  have hwin := allocatedSiteFamilyWindowVolume_exp_bound B rowSets hd
  have hmaskPow := pow_le_exp_mul_of_le_exp (Real.exp_nonneg _) (le_refl _) hw
    (Fintype.card (LayerSamplerAxis I n)) hd.axes
  have hsupport := pow_le_exp_mul_of_le_exp (by positivity :
    0 ≤ 2 * (partitionedIdealRadius (Fin dim) m + 1) + 1)
    (allocatedIdealSupportCost_bound m dim) (Nat.cast_nonneg _)
    (Fintype.card (Σ a : LayerSamplerAxis I n, O a.1)) hd.outputs
  calc
    _ ≤ Real.exp (allocatedSiteFamilyWindowLog D) *
        ((Real.exp (D * allocatedSiteKernelMaskLog m P) * Real.exp (D * (c + e))) *
          Real.exp (D * (allocatedIdealSupportCost m dim : ℝ))) := by gcongr
    _ = _ := by
      simp only [← Real.exp_add]
      congr 1
      unfold allocatedIdealWindowMassLog
      dsimp only [D]
      ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

theorem allocatedPhysicalLongIdeal_reference_mass
    {D p e : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B α (fun j => {t : Finset α // t ∈ rowSets j}) D)
    (hp : 0 ≤ p) (he : 0 ≤ e)
    (hRP : ∀ j, R j ≤ Real.exp p) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp p)
    (δ : ℝ≥0) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδe : (δ : ℝ)⁻¹ ≤ Real.exp e)
    (hmesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤
      physicalIdealErrorShare 0 (allocatedIdealMeshEnvelope m D p e)) :
    Integrable (allocatedUnmaskedLongProfileDensity B U b S (allocatedPhysicalLongIdeal B U b hR S rowSets δ))
      (allocatedLongJetReference B U b S (fun j => {t : Finset α // t ∈ rowSets j})) ∧
      (∫ z, |allocatedUnmaskedLongProfileDensity B U b S
        (allocatedPhysicalLongIdeal B U b hR S rowSets δ) z|
        ∂allocatedLongJetReference B U b S (fun j => {t : Finset α // t ∈ rowSets j})) ≤ 2 := by
  let O : Fin m → Type _ := fun j => {t : Finset α // t ∈ rowSets j}
  let grid := allocatedGridAxis (I := I) U b S.value
  let output := Σ a : {a // ¬grid a}, O a.val.1
  let f := allocatedPhysicalLongIdeal B U b hR S rowSets δ
  let K : ℝ≥0 := ⟨Real.exp p, (Real.exp_pos p).le⟩
  let Ki : ℝ≥0 := ‖(∏ q : output, R q.1.val.1)⁻¹‖₊ * (affineProductProfileLip output δ * K)
  let bound : ℝ≥0 := ⟨Real.exp (allocatedDensityLog (G := G) B α O p), (Real.exp_pos _).le⟩
  let Kp : ℝ≥0 := Fintype.card (LayerSamplerAxis I n) * bound * bound ^ Fintype.card (LayerSamplerAxis I n)
  let Ro := Real.toNNReal (max (Real.exp (allocatedJetSupportLog (G := G) B α O p))
    (Real.exp p * (partitionedIdealRadius α m + 1)))
  let mesh := physicalIdealErrorShare 0 (allocatedIdealMeshEnvelope m D p e)
  have hip := physicalActiveProfileIdeal_probability (G := G) (B := B) (G × Option α)
    (layerSamplerDegree I n) grid (fun a => (Subtype.val : O a.val.1 → Finset α))
    (fun a => R a.1) (fun a => hR a.1) δ hδ
  have hil := physicalActiveProfileIdeal_lipschitz (G := G) (B := B) (G × Option α)
    (layerSamplerDegree I n) grid (fun a => (Subtype.val : O a.val.1 → Finset α))
    (fun a => R a.1) (fun a => hR a.1) δ hδ K (fun a => hRi a.1)
  have hib := physicalActiveProfileIdeal_bound (G := G) (B := B) (G × Option α)
    (layerSamplerDegree I n) grid (fun a => (Subtype.val : O a.val.1 → Finset α))
    (fun a => R a.1) (fun a => hR a.1) δ hδ
  have hRo : Real.exp p * (partitionedIdealRadius α m + 1) ≤ (Ro : ℝ) :=
    (le_max_right _ _).trans (Real.le_coe_toNNReal _)
  have hs (v : output → ℝ) (hv : (Ro : ℝ) < ‖v‖) : f v = 0 :=
    physicalActiveProfileIdeal_zero_outside (G := G) (B := B) (G × Option α)
      (layerSamplerDegree I n) grid (fun a => (Subtype.val : O a.val.1 → Finset α))
      (fun a => R a.1) (fun a => hR a.1) (fun a => Nat.succ_le_of_lt a.1.isLt)
      δ hδ hδ1 K (fun a => hRP a.1) v (hRo.trans_lt hv)
  have hgrid := allocatedIdealGridEnvelope_nonneg m hdim.nonneg hp he
  have hD : 0 ≤ D := hdim.nonneg
  have hcost : 0 ≤ allocatedIdealMeshEnvelope m D p e := by
    unfold allocatedIdealMeshEnvelope
    positivity
  have hm0 : 0 ≤ mesh := (physicalIdealErrorShare_pos 0 _).le
  have hm1 : mesh ≤ 1 := physicalIdealErrorShare_le_one (le_refl 0) hcost
  have hallow := allocatedIdealGridAllowance_le_exp B hdim hp
    (allocatedLongIntegerSelect B U b S (O := O))
    (fun q : output => R q.1.val.1) (fun q => (hR q.1.val.1).le) he
    (hdim.active_outputs B grid) (fun q => hRi q.1.val.1) hδe
  change mixedOutputGridAllowance (allocatedLongIntegerSelect B U b S (O := O)) Ro
    ((Kp : ℝ) + Ki) ≤ Real.exp (allocatedIdealMeshEnvelope m D p e) at hallow
  have hallowI : mixedOutputGridAllowance (allocatedLongIntegerSelect B U b S (O := O)) Ro Ki ≤
      Real.exp (allocatedIdealMeshEnvelope m D p e) := by
    apply le_trans _ hallow
    unfold mixedOutputGridAllowance
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by positivity) _)
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left Kp.coe_nonneg) (pow_nonneg (by positivity) _)
  have herr : mixedOutputGridAllowance (allocatedLongIntegerSelect B U b S (O := O)) Ro Ki * mesh ≤ 1 := by
    apply (mul_le_mul_of_nonneg_right hallowI hm0).trans
    change Real.exp (allocatedIdealMeshEnvelope m D p e) *
      physicalIdealErrorShare 0 (allocatedIdealMeshEnvelope m D p e) ≤ 1
    rw [exp_mul_physicalIdealErrorShare]
    exact Real.exp_le_one_iff.mpr (by norm_num)
  exact allocatedUnmaskedLongProfile_probability_mass B U b S f Ki Ro hil hip.1 hip.2.1 hip.2.2
    hs hib hm0 hm1 hmesh herr

variable (hσ : ∀ j, 0 < σ j)
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)] (d : ℕ) [NeZero d]
variable (x : G → IntegerScalarCubeBox α S.value) (modulus : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel modulus y = principalResidueLabel modulus y₀)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))
local notation "residue" => (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
  (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀) rows j
  (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) modulus)

theorem allocatedIdealGlobalWindow_probability_mass
    {D p e P : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B α (fun j => {t : Finset α // t ∈ rowSets j}) D)
    (hp : 0 ≤ p) (he : 0 ≤ e) (hP : 0 ≤ P)
    (hRP : ∀ j, R j ≤ Real.exp p) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp p)
    (δ : ℝ≥0) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδe : (δ : ℝ)⁻¹ ≤ Real.exp e)
    (hmesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤
      physicalIdealErrorShare 0 (allocatedIdealMeshEnvelope m D p e))
    (hmask : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x rows j modulus (residue j) z ∧
      allocatedIntegerKernelMask B U b S x rows j modulus (residue j) z ≤ Real.exp (allocatedSiteKernelMaskLog m P)) :
    let φ := allocatedGlobalWindowPrefactor B U b hR hσ S rowSets d x modulus y₀ hcell hb o bW
      (allocatedPhysicalLongIdeal B U b hR S rowSets δ)
    Integrable φ (Measure.pi (fun j => Measure.pi (fun _ : rowSets j => ν j))) ∧
      (∫ y, ‖φ y‖ ∂Measure.pi (fun j => Measure.pi (fun _ : rowSets j => ν j))) ≤
        Real.exp (allocatedSiteFamilyWindowLog D + D * allocatedSiteKernelMaskLog m P + 1) := by
  intro φ
  have hl := allocatedPhysicalLongIdeal_reference_mass B U b hR S rowSets hdim hp he hRP hRi
    δ hδ hδ1 hδe hmesh
  have hw := allocatedSiteKernelMaskLog_nonneg m hP
  have hbound := allocatedGlobalWindowPrefactor_integral_mass B U b hR hσ S rowSets d x modulus y₀ hcell hb o bW
    (allocatedPhysicalLongIdeal B U b hR S rowSets δ) ν
    (allocatedPhysicalLongIdeal_measurable B U b hR S rowSets δ) hl.1 (Real.one_le_exp hw) hl.2 hmask
  refine ⟨hbound.1, hbound.2.trans ?_⟩
  have hwin := allocatedSiteFamilyWindowVolume_exp_bound B rowSets hdim
  have hmaskPower := pow_le_exp_mul_of_le_exp (Real.exp_nonneg (allocatedSiteKernelMaskLog m P))
    (le_refl (Real.exp (allocatedSiteKernelMaskLog m P))) hw (Fintype.card (LayerSamplerAxis I n)) hdim.axes
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
  calc
    _ ≤ Real.exp (allocatedSiteFamilyWindowLog D) *
        (Real.exp (D * allocatedSiteKernelMaskLog m P) * Real.exp 1) := by gcongr
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule

theorem allocatedIdealProbability_mesh_of_scale {m : ℕ} {D p e E gain S : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (he : 0 ≤ e) (hE : 0 ≤ E) (hgain : 0 ≤ gain)
    (hS : Real.exp (E + (gain + allocatedIdealMeshEnvelope m D p e) + 3) ≤ S) :
    1 / S ^ (layerTailDegree m + 1) ≤ physicalIdealErrorShare 0 (allocatedIdealMeshEnvelope m D p e) := by
  have hgrid := allocatedIdealGridEnvelope_nonneg m hD hp he
  have hcost : 0 ≤ gain + allocatedIdealMeshEnvelope m D p e := by
    unfold allocatedIdealMeshEnvelope
    positivity
  have hm := physicalIdealErrorShare_scale_mesh (layerTailDegree m) hE hcost hS
  apply hm.trans
  unfold physicalIdealErrorShare
  apply Real.exp_le_exp.mpr
  linarith only [hE, hgain]

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable (rows : ∀ j, O j → Finset α)

theorem allocatedSiteScale_probability_mesh
    (hq : Fintype.card α ≤ m + 1) (hinj : ∀ j, Function.Injective (rows j))
    {p e E : ℝ} (hp : 0 ≤ p) (he : 0 ≤ e) (hE : 0 ≤ E)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p) :
    1 / ((allocatedSiteScale (G := G) B U b hR hσ p e E).value : ℝ) ^ (layerTailDegree m + 1) ≤
      physicalIdealErrorShare 0
        (allocatedIdealMeshEnvelope m (allocatedComparisonDimension m p) (allocatedSiteScaleNumeric m p) e) := by
  have hm := (allocatedSiteScale_ready B U b hR hσ rows hq hinj hp he hE hvars hI hn).2
  have hD := (allocatedComparisonDimension_bounds m hp).1
  have hw := allocatedSiteKernelMaskLog_nonneg m hp
  have hprod := mul_nonneg hD hw
  apply hm.trans
  unfold physicalIdealErrorShare
  apply Real.exp_le_exp.mpr
  linarith only [hE, hprod]

end Erdos3.VectorPolynomial

end

end OAI
