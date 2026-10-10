import OAI.Combinatorics.Progressions.Estimates.AllocatedActualProfileControl
import OAI.Combinatorics.Progressions.Linear.AllocatedProbabilityProfileKernel

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (p : ∀ a : {a // allocatedGridAxis (I := I) U b S.value a}, PMF (CoefficientJetAxisRow O a.val))

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))
local notation "scale" => (∏ a, allocatedLongJetOutputScale B U b S (O := O) a)

noncomputable def allocatedProbabilityProfileRawDensity (A : ℝ≥0) (f g : (output → ℝ) → ℝ)
    (z : ∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) : ℝ :=
  allocatedProbabilityGridDensity B U b S p (fun a => coefficientJetAxisEquiv O I n z a.val) *
    ((A : ℝ) * |f (allocatedLongJetRealCoordinates B U b S (fun a => coefficientJetAxisEquiv O I n z a.val)) -
      g (allocatedLongJetRealCoordinates B U b S (fun a => coefficientJetAxisEquiv O I n z a.val))| / scale) *
    smallBoxCutoff (mixedJetAmbientPoint U b o z)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

theorem allocatedProbabilityProfileAmbientKernel_point (A : ℝ≥0) (f g : (output → ℝ) → ℝ)
    (z : ∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) :
    allocatedProbabilityProfileAmbientKernel B U b S o p A f g (mixedJetAmbientPoint U b o z) =
      allocatedProbabilityProfileRawDensity B U b S o p A f g z /
        coveredJetArrayScale (O := O) U := by
  rw [allocatedProbabilityProfileAmbientKernel, allocatedProbabilityAmbientKernel_mixed_point,
    allocatedLongAmbientCoordinates_point]
  unfold allocatedProbabilityRawDensity allocatedProbabilityProfileRawDensity
  simp only [NNReal.coe_one, one_mul]
  ring

variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (O := O) (E := Q) U o b d
  (fun j _ => standardLatticeSmallBox (J j))
local notation "quarter" => mixedCoveredJetRegion (O := O) (E := Q) U o b d
  (fun j _ => standardLatticeClosedQuarterBox (J j))

theorem allocatedProbabilityProfileMajorant_chart (A : ℝ≥0) (f g : (output → ℝ) → ℝ) :
    allocatedProbabilityProfileMajorant B U b S o p A f g d =
      restrictedChartDensity chart region 1 (fun z =>
        allocatedProbabilityProfileRawDensity B U b S o p A f g z.1 /
          coveredJetArrayScale (O := O) U) := by
  apply restrictedChartDensity_eq_of_values chart region
    (mixedCoveredJetChart_injOn U o b hb bW d _ (fun _ _ => Subset.rfl))
  · intro z hz
    change allocatedProbabilityProfileTorusKernel B U b S o p A f g
      (coveredJetAmbientTorus U d (chart z)) = _
    rw [coveredJetAmbientTorus_chart, allocatedProbabilityProfileTorusKernel,
      smallBoxTorusKernel_local _ (allocatedProbabilityProfileAmbientKernel_support B U b S o p A f g)]
    · exact allocatedProbabilityProfileAmbientKernel_point B U b S o p A f g z.1
    · intro a
      exact (hz a.1 (mem_univ _) a.2.1 (mem_univ _)).1 a.2.2
  · intro y hy
    by_contra h
    obtain ⟨z, hz, hzn⟩ := smallBoxTorusKernel_recover
      (allocatedProbabilityProfileAmbientKernel B U b S o p A f g)
      (coveredJetAmbientTorus U d y) h
    exact hy (coveredJetAmbientTorus_smallBox_mem_chart U b hb o bW d y z hz
      (allocatedProbabilityProfileAmbientKernel_support B U b S o p A f g z hzn))

include hb bW in
theorem allocatedProbabilityProfileMajorant_nonneg (A : ℝ≥0) (f g : (output → ℝ) → ℝ)
    (y : EuclideanJetLayers U O) :
    0 ≤ allocatedProbabilityProfileMajorant B U b S o p A f g d y := by
  rw [allocatedProbabilityProfileMajorant_chart B U b S o p hb bW d]
  by_cases hy : y ∈ chart '' region
  · obtain ⟨z, hz, rfl⟩ := hy
    rw [restrictedChartDensity_apply _ _ _ _
      (mixedCoveredJetChart_injOn U o b hb bW d _ (fun _ _ => Subset.rfl)) hz, one_mul]
    apply div_nonneg _ (coveredJetArrayScale_pos U).le
    unfold allocatedProbabilityProfileRawDensity
    exact mul_nonneg (mul_nonneg (allocatedProbabilityGridDensity_nonneg B U b S p _)
      (div_nonneg (mul_nonneg A.coe_nonneg (abs_nonneg _))
        (Finset.prod_nonneg (fun a _ => (allocatedLongJetOutputScale_pos B U b S a).le))))
      (smallBoxCutoff_range _).1
  · rw [restrictedChartDensity_zero _ _ _ _ hy]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (p : ∀ a : {a // allocatedGridAxis (I := I) U b S.value a}, PMF (CoefficientJetAxisRow O a.val))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit O I n grid
local notation "scale" => (∏ a, allocatedLongJetOutputScale B U b S (O := O) a)
local notation "region" => mixedCoveredJetRegion (O := O) (E := Q) U o b d
  (fun j _ => standardLatticeSmallBox (J j))
local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))

local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))
local notation "reference" => allocatedLongJetReference B U b S O

include hb bW

theorem allocatedProbabilityProfileMajorant_lintegral_mass (A : ℝ≥0) (f g : (output → ℝ) → ℝ)
    (hi : Integrable (allocatedUnmaskedLongProfileDensity B U b S (fun v => |f v - g v|)) reference) :
    (∫⁻ y, ENNReal.ofReal (allocatedProbabilityProfileMajorant B U b S o p A f g d y) ∂haar) ≤
      ENNReal.ofReal ((A : ℝ) * ∫ z,
        allocatedUnmaskedLongProfileDensity B U b S (fun v => |f v - g v|) z ∂reference) := by
  let μf := allocatedFrozenJetReference B U b S O
  let μd := (PMF.uniformOfFintype (∀ j, O j → Q j → ZMod d)).toMeasure
  let μraw := (Measure.pi (fun j => mixedArrayReference (I j) (Fin (n j)) (O j))).prod μd
  let fg := allocatedProbabilityGridDensity B U b S p
  let k := fun z => (A : ℝ) * allocatedUnmaskedLongProfileDensity B U b S (fun v => |f v - g v|) z
  let e := MeasurableEquiv.prodCongr split (MeasurableEquiv.refl (∀ j, O j → Q j → ZMod d))
  let F := fun z : (AllocatedFrozenJetRows B U b S O × AllocatedLongJetRows B U b S O) ×
      (∀ j, O j → Q j → ZMod d) => fg z.1.1 * k z.1.2 * (1 : ℝ)
  have hfg : Integrable fg μf ∧ (∫ z, fg z ∂μf) = 1 :=
    allocatedProbabilityGridDensity_mass B U b S p
  have hfg0 (z) : 0 ≤ fg z := allocatedProbabilityGridDensity_nonneg B U b S p z
  have hk0 (z) : 0 ≤ k z := mul_nonneg A.coe_nonneg
    (div_nonneg (abs_nonneg _) (Finset.prod_nonneg (fun a _ => (allocatedLongJetOutputScale_pos B U b S a).le)))
  have hki : Integrable k reference := hi.const_mul A
  have hFi : Integrable F ((μf.prod reference).prod μd) := (hfg.1.mul_prod hki).mul_prod (integrable_const 1)
  have hF0 (z) : 0 ≤ F z := mul_nonneg (mul_nonneg (hfg0 _) (hk0 _)) zero_le_one
  have hone : (∫ _ : (∀ j, O j → Q j → ZMod d), (1 : ℝ) ∂μd) = 1 := by simp
  have hFm : (∫ z, F z ∂(μf.prod reference).prod μd) = (A : ℝ) * ∫ z,
      allocatedUnmaskedLongProfileDensity B U b S (fun v => |f v - g v|) z ∂reference := by
    dsimp only [F]
    rw [integral_prod_mul (μ := μf.prod reference) (ν := μd)
      (fun z : AllocatedFrozenJetRows B U b S O × AllocatedLongJetRows B U b S O => fg z.1 * k z.2)
      (fun _ : (∀ j, O j → Q j → ZMod d) => (1 : ℝ)),
      hone, integral_prod_mul (μ := μf) (ν := reference) fg k, hfg.2, one_mul, mul_one]
    exact integral_const_mul _ _
  have he : MeasurePreserving e μraw ((μf.prod reference).prod μd) :=
    (coefficientJetAxisSplit_measurePreserving O I n grid).prod (MeasurePreserving.id μd)
  rw [allocatedProbabilityProfileMajorant_chart B U b S o p hb bW d]
  rw [mixedCoveredJet_normalized_lintegral U o b hb bW d ν _
    (fun j _ => (standardLatticeSmallBox_isOpen (J j)).measurableSet) (fun _ _ => Subset.rfl)]
  calc
    _ ≤ ∫⁻ z in region, ENNReal.ofReal (F (e z)) ∂μraw := by
      apply lintegral_mono
      intro z
      apply ENNReal.ofReal_le_ofReal
      change fg ((split z.1).1) * ((A : ℝ) *
          |f (allocatedLongJetRealCoordinates B U b S ((split z.1).2)) -
            g (allocatedLongJetRealCoordinates B U b S ((split z.1).2))| / scale) *
          smallBoxCutoff (mixedJetAmbientPoint U b o z.1) ≤
        fg ((split z.1).1) * k ((split z.1).2) * 1
      calc
        _ = fg ((split z.1).1) * k ((split z.1).2) *
            smallBoxCutoff (mixedJetAmbientPoint U b o z.1) := by
          dsimp only [k, allocatedUnmaskedLongProfileDensity]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (smallBoxCutoff_range _).2
          (mul_nonneg (hfg0 _) (hk0 _))
    _ ≤ ∫⁻ z, ENNReal.ofReal (F (e z)) ∂μraw := lintegral_mono' Measure.restrict_le_self le_rfl
    _ = ∫⁻ z, ENNReal.ofReal (F z) ∂(μf.prod reference).prod μd :=
      he.lintegral_comp_emb e.measurableEmbedding (fun z => ENNReal.ofReal (F z))
    _ = _ := by
      rw [← ofReal_integral_eq_lintegral_ofReal hFi (Filter.Eventually.of_forall hF0), hFm]

theorem allocatedProbabilityProfileMajorant_integrable_mass (A : ℝ≥0) (f g : (output → ℝ) → ℝ)
    (hi : Integrable (allocatedUnmaskedLongProfileDensity B U b S (fun v => |f v - g v|)) reference)
    {Cf Cg Kf Kg : ℝ≥0} (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (hfb : ∀ z, |f z| ≤ Cf) (hgb : ∀ z, |g z| ≤ Cg)
    (C V : Fin m → ℝ≥0)
    (hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j) :
    Integrable (allocatedProbabilityProfileMajorant B U b S o p A f g d) haar ∧
    (∫ y, allocatedProbabilityProfileMajorant B U b S o p A f g d y ∂haar) ≤
      (A : ℝ) * ∫ z, allocatedUnmaskedLongProfileDensity B U b S (fun v => |f v - g v|) z ∂reference := by
  let majorant := allocatedProbabilityProfileMajorant B U b S o p A f g d
  have hp := allocatedProbabilityProfileTorusKernel_bounds B U b S o p A f g hf hg hfb hgb C V hC hV
  have hm0 (y) : 0 ≤ majorant y := (hp.1 (coveredJetAmbientTorus U d y)).1
  have hmc : Continuous majorant := hp.2.continuous.comp (coveredJetAmbientTorus_continuous U d)
  have hmi : Integrable majorant haar := by
    apply (integrable_const (allocatedProfileErrorCap B U b S (O := O) A Cf Cg V : ℝ)).mono'
      hmc.measurable.aestronglyMeasurable
    filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_of_nonneg (hm0 y)]
    exact (hp.1 (coveredJetAmbientTorus U d y)).2
  refine ⟨hmi, ?_⟩
  have hmass := allocatedProbabilityProfileMajorant_lintegral_mass B U b S o p hb bW d ν A f g hi
  change (∫⁻ y, ENNReal.ofReal (majorant y) ∂haar) ≤ _ at hmass
  rw [← ofReal_integral_eq_lintegral_ofReal hmi (Filter.Eventually.of_forall hm0)] at hmass
  apply (ENNReal.ofReal_le_ofReal_iff ?_).mp hmass
  exact mul_nonneg A.coe_nonneg (integral_nonneg (fun z => div_nonneg (abs_nonneg _)
    (Finset.prod_nonneg (fun a _ => (allocatedLongJetOutputScale_pos B U b S a).le))))

end Erdos3.VectorPolynomial

end

end OAI
