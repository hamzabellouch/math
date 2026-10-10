import Mathlib
import OAI.Geometry.BallPacking.Moments.ConvexWeights

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian
open Set Function Manifold MeasureTheory Classical
open scoped ContDiff Manifold Topology ENNReal

section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M]
  {I J : Type*} [Fintype I] [Fintype J] {K : Set M}

omit [T2Space M] in

theorem partitionFormMass_independent (hpos : PositivePlaneTransitions M)
    (hK : IsCompact K) (B : I → SurfaceCoordinateBox M) (C : J → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K) (ν : SmoothPartitionOfUnity J 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    (hν : ν.IsSubordinate (fun j => (C j).carrier))
    {Ω : ManifoldTwoForm Plane M} (hΩ : SmoothTwoForm Ω)
    (hskew : ∀ x u v, Ω x u v = -Ω x v u) (hz : ∀ x, x ∉ K → Ω x=0) :
    partitionFormMass B ρ Ω = partitionFormMass C ν Ω := by
  classical
  let : MulActionWithZero ℝ (Plane →L[ℝ] Plane →L[ℝ] ℝ) :=
    @Module.toMulActionWithZero ℝ (Plane →L[ℝ] Plane →L[ℝ] ℝ) inferInstance inferInstance inferInstance
  let D : I → J → ManifoldTwoForm Plane M := fun i j x => ρ i x • (ν j x • Ω x)
  let L : I → J → Set M := fun i j => K ∩ tsupport (ρ i) ∩ tsupport (ν j)
  have hL (i : I) (j : J) : IsCompact (L i j) :=
    (hK.inter_right (isClosed_tsupport (ρ i))).inter_right (isClosed_tsupport (ν j))
  have hLB (i : I) (j : J) : L i j ⊆ (extChartAt 𝓘(ℝ,Plane) (B i).center).source :=
    fun _ hx => (hρ i hx.1.2).1
  have hLC (i : I) (j : J) : L i j ⊆ (extChartAt 𝓘(ℝ,Plane) (C j).center).source :=
    fun _ hx => (hν j hx.2).1
  have hDz (i : I) (j : J) (x : M) (hx : x ∉ L i j) : D i j x=0 := by
    by_cases hk : x ∈ K
    · by_cases hi : x ∈ tsupport (ρ i)
      · have hj : x ∉ tsupport (ν j) := fun hj => hx ⟨⟨hk,hi⟩,hj⟩
        simp only [D,image_eq_zero_of_notMem_tsupport hj,zero_smul,smul_zero]
      · simp only [D,image_eq_zero_of_notMem_tsupport hi,zero_smul]
    · simp only [D,hz x hk,smul_zero]
  have hDs (i : I) (j : J) : SmoothTwoForm (D i j) :=
    (((SmoothTwoFormFamily.const (P := ℝ) hΩ).spatial_smul (ν j).contMDiff).spatial_smul
      (ρ i).contMDiff).eval 0
  have hDa (i : I) (j : J) (x : M) (u v : Plane) : D i j x u v = -D i j x v u := by
    change ρ i x * (ν j x * Ω x u v) = -(ρ i x * (ν j x * Ω x v u))
    rw [hskew x u v]; ring
  have hsumJ (i : I) : (∑ j, D i j) = fun x => ρ i x • Ω x := by
    funext x
    apply ContinuousLinearMap.ext
    intro firstVector
    apply ContinuousLinearMap.ext
    intro secondVector
    simp only [Finset.sum_apply,D,sum_apply,smul_apply,smul_eq_mul]
    rw [← Finset.mul_sum,← Finset.sum_mul]
    by_cases hx : x ∈ K
    · have hh : (∑ j, ν j x)=1 := by simpa only [finsum_eq_sum_of_fintype] using ν.sum_eq_one hx
      rw [hh,one_mul]
    · simp only [hz x hx,zero_apply,mul_zero]
  have hsumI (j : J) : (∑ i, D i j) = fun x => ν j x • Ω x := by
    funext x
    apply ContinuousLinearMap.ext
    intro firstVector
    apply ContinuousLinearMap.ext
    intro secondVector
    simp only [Finset.sum_apply,D,sum_apply,smul_apply,smul_eq_mul]
    rw [← Finset.sum_mul]
    by_cases hx : x ∈ K
    · have hh : (∑ i, ρ i x)=1 := by simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one hx
      rw [hh,one_mul]
    · simp only [hz x hx,zero_apply,mul_zero]
  have hchange (i : I) (j : J) : chartMass (B i).center (D i j)=chartMass (C j).center (D i j) := by
    apply chartMass_change (hDa i j) (hL i j) (hLB i j) (hLC i j) (hDz i j)
    rintro y ⟨x,hx,rfl⟩
    apply hpos (B i).center (C j).center _ ((extChartAt 𝓘(ℝ,Plane) (B i).center).map_source (hLB i j hx))
    simpa only [(extChartAt 𝓘(ℝ,Plane) (B i).center).left_inv (hLB i j hx)] using hLC i j hx
  unfold partitionFormMass
  calc
    (∑ i, chartMass (B i).center (fun x => ρ i x • Ω x)) =
        ∑ i, ∑ j, chartMass (B i).center (D i j) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← hsumJ i]
      exact chartMass_sum Finset.univ (B i).center (D i)
        (fun j _ => (hDs i j).coefficient_integrable _ (hL i j) (hLB i j) (hDz i j))
    _ = ∑ i, ∑ j, chartMass (C j).center (D i j) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_congr rfl (fun j _ => hchange i j)
    _ = ∑ j, ∑ i, chartMass (C j).center (D i j) := Finset.sum_comm
    _ = ∑ j, chartMass (C j).center (fun x => ν j x • Ω x) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← hsumI j]
      exact (chartMass_sum Finset.univ (C j).center (fun i => D i j)
        (fun i _ => (hDs i j).coefficient_integrable _ (hL i j) (hLC i j) (hDz i j))).symm

end

section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [MeasurableSpace M] [BorelSpace M]

def chartInverseExtension (c : M) (y : Plane) : M :=
  if y ∈ (extChartAt 𝓘(ℝ,Plane) c).target then (extChartAt 𝓘(ℝ,Plane) c).symm y else c

theorem chartInverseExtension_measurable (c : M) : Measurable (chartInverseExtension c) := by
  classical
  exact (continuousOn_extChartAt_symm (I := 𝓘(ℝ,Plane)) c).measurable_piecewise
    continuousOn_const (isOpen_extChartAt_target c).measurableSet

omit [MeasurableSpace M] [BorelSpace M] in
theorem chartInverseExtension_eq {c : M} {y : Plane}
    (hy : y∈(extChartAt 𝓘(ℝ,Plane) c).target) :
    chartInverseExtension c y=(extChartAt 𝓘(ℝ,Plane) c).symm y := ite_eq_left hy

def chartAreaMeasure (c : M) (w : Plane → ℝ) : Measure M :=
  Measure.map (chartInverseExtension c) (volume.withDensity (fun y => ENNReal.ofReal (w y)))

omit [BorelSpace M] in
theorem chartAreaMeasure_finite (c : M) {w : Plane → ℝ} (hw : Integrable w) :
    IsFiniteMeasure (chartAreaMeasure c w) := by
  have hl : (∫⁻ y, ENNReal.ofReal (w y)) < (⊤ : ℝ≥0∞) := by
    apply lt_of_le_of_lt (lintegral_mono (fun y => ENNReal.ofReal_le_ofReal (le_abs_self (w y))))
    simpa only [Real.norm_eq_abs] using (hasFiniteIntegral_iff_norm w).mp hw.hasFiniteIntegral
  let := isFiniteMeasure_withDensity hl.ne
  exact inferInstanceAs (IsFiniteMeasure (Measure.map _ _))

theorem integral_chartAreaMeasure (c : M) {w : Plane → ℝ}
    (hw : Measurable w) (hpos : ∀ y,0≤w y)
    (hz : ∀ y,y∉(extChartAt 𝓘(ℝ,Plane) c).target→w y=0)
    {f : M → ℝ} (hf : Measurable f) :
    (∫ x, f x ∂chartAreaMeasure c w)=
      ∫ y, w y*f ((extChartAt 𝓘(ℝ,Plane) c).symm y) := by
  rw [chartAreaMeasure,integral_map (chartInverseExtension_measurable c).aemeasurable
    hf.aestronglyMeasurable]
  rw [integral_withDensity_eq_integral_toReal_smul (hw.ennreal_ofReal)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [ENNReal.toReal_ofReal (hpos y)]
  change w y*f (chartInverseExtension c y)=_
  by_cases hy : y∈(extChartAt 𝓘(ℝ,Plane) c).target
  · rw [chartInverseExtension_eq hy]
  · rw [hz y hy,zero_mul,zero_mul]

theorem integrable_chartAreaMeasure (c : M) {w : Plane → ℝ}
    (hw : Measurable w) (hpos : ∀ y,0≤w y)
    (hz : ∀ y,y∉(extChartAt 𝓘(ℝ,Plane) c).target→w y=0)
    {f : M → ℝ} (hf : Measurable f) :
    Integrable f (chartAreaMeasure c w) ↔
      Integrable (fun y => w y*f ((extChartAt 𝓘(ℝ,Plane) c).symm y)) := by
  rw [chartAreaMeasure,integrable_map_measure hf.aestronglyMeasurable
    (chartInverseExtension_measurable c).aemeasurable,
    integrable_withDensity_iff_integrable_smul' hw.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integrable_congr
  filter_upwards [] with y
  rw [ENNReal.toReal_ofReal (hpos y)]
  change w y*f (chartInverseExtension c y)=_
  by_cases hy : y∈(extChartAt 𝓘(ℝ,Plane) c).target
  · rw [chartInverseExtension_eq hy]
  · rw [hz y hy,zero_mul,zero_mul]

theorem chartAreaMeasure_null (c : M) {w : Plane → ℝ}
    (hz : ∀ y,y∉(extChartAt 𝓘(ℝ,Plane) c).target→w y=0)
    {C : Set M} (hC : MeasurableSet C)
    (hnull : volume ((extChartAt 𝓘(ℝ,Plane) c).target ∩
      (extChartAt 𝓘(ℝ,Plane) c).symm ⁻¹' C)=0) :
    chartAreaMeasure c w C=0 := by
  rw [chartAreaMeasure,Measure.map_apply (chartInverseExtension_measurable c) hC,
    withDensity_apply _ ((chartInverseExtension_measurable c) hC)]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem ((chartInverseExtension_measurable c) hC),
    (ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp hnull))] with y hy hn
  have hyt : y∉(extChartAt 𝓘(ℝ,Plane) c).target := by
    intro ht
    apply hn
    refine ⟨ht,?_⟩
    simpa only [mem_preimage,chartInverseExtension_eq ht] using hy
  rw [hz y hyt,ENNReal.ofReal_zero]
  rfl

end

section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  {I : Type*} {K : Set M}

def partitionChartDensity (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (Λ : ManifoldTwoForm Plane M) (i : I) (y : Plane) : ℝ :=
  extendedChartCoefficient (B i).center (fun _ : ℝ => fun x => ρ i x • Λ x) (0,y)

theorem partitionChartDensity_off_target (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (Λ : ManifoldTwoForm Plane M) (i : I) {y : Plane}
    (hy : y∉(extChartAt 𝓘(ℝ,Plane) (B i).center).target) :
    partitionChartDensity B ρ Λ i y=0 := ite_eq_right hy

theorem partitionChartDensity_nonneg (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    {Λ : ManifoldTwoForm Plane M}
    (hΛ : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→
      0≤chartTwoForm Λ c y (1,0) (0,1)) (i : I) (y : Plane) :
    0≤partitionChartDensity B ρ Λ i y := by
  by_cases hy : y∈(extChartAt 𝓘(ℝ,Plane) (B i).center).target
  · unfold partitionChartDensity extendedChartCoefficient spatialZeroExtension
    rw [ite_eq_left hy]
    change 0 ≤ chartTwoForm (fun x => ρ i x • Λ x) (B i).center y (1,0) (0,1)
    rw [chartTwoForm_spatial_smul]
    exact mul_nonneg (ρ.nonneg i _) (hΛ _ _ hy)
  · rw [partitionChartDensity_off_target B ρ Λ i hy]

theorem partitionChartDensity_spatial_smul (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (Λ : ManifoldTwoForm Plane M) (f : M → ℝ) (i : I) (y : Plane) :
    partitionChartDensity B ρ (fun x => f x • Λ x) i y=
      partitionChartDensity B ρ Λ i y * f ((extChartAt 𝓘(ℝ,Plane) (B i).center).symm y) := by
  unfold partitionChartDensity extendedChartCoefficient spatialZeroExtension
  split_ifs
  · change chartTwoForm (fun x => ρ i x • (f x • Λ x)) (B i).center y (1,0) (0,1) =
      chartTwoForm (fun x => ρ i x • Λ x) (B i).center y (1,0) (0,1) * _
    rw [chartTwoForm_spatial_smul,chartTwoForm_spatial_smul,chartTwoForm_spatial_smul]
    simp only [smul_apply, smul_eq_mul]
    ring
  · exact (zero_mul _).symm

variable [IsManifold 𝓘(ℝ,Plane) ∞ M]

theorem partitionChartDensity_properties (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ) (i : I) :
    ContDiff ℝ ∞ (partitionChartDensity B ρ Λ i) ∧
      HasCompactSupport (partitionChartDensity B ρ Λ i) ∧
      Integrable (partitionChartDensity B ρ Λ i) := by
  let L := tsupport (ρ i)
  have hL : IsCompact L := (B i).isCompact_compactCarrier.of_isClosed_subset
    (isClosed_tsupport _) ((hρ i).trans (B i).carrier_subset_compactCarrier)
  have hLc : L⊆(extChartAt 𝓘(ℝ,Plane) (B i).center).source := fun _ hx => (hρ i hx).1
  have hs : SmoothTwoFormFamily (fun _ : ℝ => fun x => ρ i x • Λ x) :=
    (SmoothTwoFormFamily.const hΛ).spatial_smul (ρ i).contMDiff
  have hz : ∀ (p : ℝ) x,x∉L→ρ i x • Λ x=0 := by
    intro _ x hx
    rw [image_eq_zero_of_notMem_tsupport hx]
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    change (0:ℝ) * _ = 0
    exact zero_mul _
  have hfull : ContDiff ℝ ∞ (extendedChartCoefficient (B i).center
      (fun _ : ℝ => fun x => ρ i x • Λ x)) :=
    extendedChartCoefficient_smooth (Ω := fun _ : ℝ => fun x => ρ i x • Λ x)
      (c := (B i).center) (hs (B i).center) hL hLc hz
  have hsm : ContDiff ℝ ∞ (partitionChartDensity B ρ Λ i) :=
    hfull.comp (f := fun y : Plane => ((0 : ℝ),y))
      (contDiff_const.prodMk contDiff_id)
  have hc : HasCompactSupport (partitionChartDensity B ρ Λ i) := by
    apply HasCompactSupport.intro (hL.image_of_continuousOn
      ((continuousOn_extChartAt (I := 𝓘(ℝ,Plane)) (B i).center).mono hLc))
    exact fun _ hy => extendedChartCoefficient_zero hz 0 hy
  exact ⟨hsm,hc,hsm.continuous.integrable_of_hasCompactSupport hc⟩

variable [Fintype I] [MeasurableSpace M] [BorelSpace M]

def partitionAreaMeasure (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K) (Λ : ManifoldTwoForm Plane M) : Measure M :=
  ∑ i, chartAreaMeasure (B i).center (partitionChartDensity B ρ Λ i)

omit [BorelSpace M] in
theorem partitionAreaMeasure_finite (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ) :
    IsFiniteMeasure (partitionAreaMeasure B ρ Λ) := by
  have (i : I) : IsFiniteMeasure (chartAreaMeasure (B i).center (partitionChartDensity B ρ Λ i)) :=
    chartAreaMeasure_finite _ (partitionChartDensity_properties B ρ hρ hΛ i).2.2
  exact inferInstanceAs (IsFiniteMeasure (∑ i, chartAreaMeasure (B i).center (partitionChartDensity B ρ Λ i)))

theorem integral_partitionAreaMeasure (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ)
    (hpos : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→
      0≤chartTwoForm Λ c y (1,0) (0,1))
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞ f) :
    (∫ x, f x ∂partitionAreaMeasure B ρ Λ)=
      partitionFormMass B ρ (fun x => f x • Λ x) := by
  have hfp : SmoothTwoForm (fun x => f x • Λ x) :=
    ((SmoothTwoFormFamily.const (P := ℝ) hΛ).spatial_smul hf).eval 0
  have hmeas (i : I) : Measurable (partitionChartDensity B ρ Λ i) :=
    (partitionChartDensity_properties B ρ hρ hΛ i).1.continuous.measurable
  have hint (i : I) : Integrable f
      (chartAreaMeasure (B i).center (partitionChartDensity B ρ Λ i)) := by
    rw [integrable_chartAreaMeasure _ (hmeas i) (partitionChartDensity_nonneg B ρ hpos i)
      (fun _ hy => partitionChartDensity_off_target B ρ Λ i hy) hf.continuous.measurable]
    simpa only [← partitionChartDensity_spatial_smul] using
      (partitionChartDensity_properties B ρ hρ hfp i).2.2
  rw [partitionAreaMeasure,integral_finsetSum_measure (fun i _ => hint i)]
  unfold partitionFormMass chartMass
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_chartAreaMeasure _ (hmeas i) (partitionChartDensity_nonneg B ρ hpos i)
    (fun _ hy => partitionChartDensity_off_target B ρ Λ i hy) hf.continuous.measurable]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => (partitionChartDensity_spatial_smul B ρ Λ f i y).symm)

end

section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [MeasurableSpace M] [BorelSpace M]

theorem integral_chartAreaMeasure_restrict (c : M) {w : Plane → ℝ}
    (hw : Measurable w) (hpos : ∀ y,0≤w y)
    (hz : ∀ y,y∉(extChartAt 𝓘(ℝ,Plane) c).target→w y=0)
    {C : Set M} (hC : MeasurableSet C) {f : M → ℝ} (hf : Measurable f) :
    (∫ x in C, f x ∂chartAreaMeasure c w)=
      ∫ y in (extChartAt 𝓘(ℝ,Plane) c).target ∩
        (extChartAt 𝓘(ℝ,Plane) c).symm ⁻¹' C,
        w y*f ((extChartAt 𝓘(ℝ,Plane) c).symm y) := by
  rw [← integral_indicator hC, integral_chartAreaMeasure c hw hpos hz (hf.indicator hC)]
  have hD : MeasurableSet ((extChartAt 𝓘(ℝ,Plane) c).target ∩
      (extChartAt 𝓘(ℝ,Plane) c).symm ⁻¹' C) :=
    by
      have he : (extChartAt 𝓘(ℝ,Plane) c).target ∩
          (extChartAt 𝓘(ℝ,Plane) c).symm ⁻¹' C =
          (extChartAt 𝓘(ℝ,Plane) c).target ∩ chartInverseExtension c ⁻¹' C := by
        ext y
        by_cases hy : y∈(extChartAt 𝓘(ℝ,Plane) c).target
        · simp only [mem_inter_iff,mem_preimage,hy,true_and,chartInverseExtension_eq hy]
        · simp only [mem_inter_iff,hy,false_and]
      rw [he]
      exact (isOpen_extChartAt_target c).measurableSet.inter
        (chartInverseExtension_measurable c hC)
  rw [← integral_indicator hD]
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hy : y∈(extChartAt 𝓘(ℝ,Plane) c).target
  · by_cases hc : (extChartAt 𝓘(ℝ,Plane) c).symm y∈C
    · simp only [Set.indicator,mem_inter_iff,mem_preimage,hy,hc,and_self,↓reduceIte]
    · simp only [Set.indicator,mem_inter_iff,mem_preimage,hy,hc,and_false,↓reduceIte,mul_zero]
  · simp only [Set.indicator,mem_inter_iff,mem_preimage,hy,false_and,↓reduceIte,hz y hy,zero_mul]

variable {I : Type*} [Fintype I] {K : Set M}

def restrictedPartitionFormMass (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K) (C : Set M)
    (Ω : ManifoldTwoForm Plane M) : ℝ :=
  ∑ i, ∫ y in (extChartAt 𝓘(ℝ,Plane) (B i).center).target ∩
    (extChartAt 𝓘(ℝ,Plane) (B i).center).symm ⁻¹' C,
    partitionChartDensity B ρ Ω i y

variable [IsManifold 𝓘(ℝ,Plane) ∞ M]

theorem smooth_integrable_partitionAreaMeasure (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ)
    (hpos : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→
      0≤chartTwoForm Λ c y (1,0) (0,1))
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞ f) :
    Integrable f (partitionAreaMeasure B ρ Λ) := by
  have hfp : SmoothTwoForm (fun x => f x • Λ x) :=
    ((SmoothTwoFormFamily.const (P := ℝ) hΛ).spatial_smul hf).eval 0
  apply integrable_finsetSum_measure.mpr
  intro i _
  rw [integrable_chartAreaMeasure _
    (partitionChartDensity_properties B ρ hρ hΛ i).1.continuous.measurable
    (partitionChartDensity_nonneg B ρ hpos i)
    (fun _ hy => partitionChartDensity_off_target B ρ Λ i hy) hf.continuous.measurable]
  simpa only [← partitionChartDensity_spatial_smul] using
    (partitionChartDensity_properties B ρ hρ hfp i).2.2

theorem integral_partitionAreaMeasure_restrict (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ)
    (hpos : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→
      0≤chartTwoForm Λ c y (1,0) (0,1))
    {C : Set M} (hC : MeasurableSet C)
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞ f) :
    (∫ x in C, f x ∂partitionAreaMeasure B ρ Λ)=
      restrictedPartitionFormMass B ρ C (fun x => f x • Λ x) := by
  have hh := (smooth_integrable_partitionAreaMeasure B ρ hρ hΛ hpos hf).indicator hC
  have hint : ∀ i ∈ (Finset.univ : Finset I), Integrable (C.indicator f)
      (chartAreaMeasure (B i).center (partitionChartDensity B ρ Λ i)) :=
    integrable_finsetSum_measure.mp hh
  rw [← integral_indicator hC,partitionAreaMeasure,
    integral_finsetSum_measure hint]
  unfold restrictedPartitionFormMass
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_indicator hC, integral_chartAreaMeasure_restrict _
    (partitionChartDensity_properties B ρ hρ hΛ i).1.continuous.measurable
    (partitionChartDensity_nonneg B ρ hpos i)
    (fun _ hy => partitionChartDensity_off_target B ρ Λ i hy) hC hf.continuous.measurable]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => (partitionChartDensity_spatial_smul B ρ Λ f i y).symm)

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] in
theorem partitionAreaMeasure_null (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K) (Λ : ManifoldTwoForm Plane M)
    {C : Set M} (hC : MeasurableSet C)
    (hnull : ∀ i,volume ((extChartAt 𝓘(ℝ,Plane) (B i).center).target ∩
      (extChartAt 𝓘(ℝ,Plane) (B i).center).symm ⁻¹' C)=0) :
    partitionAreaMeasure B ρ Λ C=0 := by
  rw [partitionAreaMeasure,Measure.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro i _
  exact chartAreaMeasure_null _ (fun _ hy => partitionChartDensity_off_target B ρ Λ i hy)
    hC (hnull i)

omit [IsManifold 𝓘(ℝ,Plane) ∞ M]

 theorem chartRegion_measurable (c : M) {C : Set M} (hC : MeasurableSet C) :
    MeasurableSet ((extChartAt 𝓘(ℝ,Plane) c).target ∩
      (extChartAt 𝓘(ℝ,Plane) c).symm ⁻¹' C) := by
  have he : (extChartAt 𝓘(ℝ,Plane) c).target ∩
      (extChartAt 𝓘(ℝ,Plane) c).symm ⁻¹' C =
      (extChartAt 𝓘(ℝ,Plane) c).target ∩ chartInverseExtension c ⁻¹' C := by
    ext y
    by_cases hy : y∈(extChartAt 𝓘(ℝ,Plane) c).target
    · simp only [mem_inter_iff,mem_preimage,hy,true_and,chartInverseExtension_eq hy]
    · simp only [mem_inter_iff,hy,false_and]
  rw [he]
  exact (isOpen_extChartAt_target c).measurableSet.inter (chartInverseExtension_measurable c hC)

 omit [MeasurableSpace M] [BorelSpace M] in
 theorem extendedChartCoefficient_indicator (c : M) (C : Set M)
    (Ω : ManifoldTwoForm Plane M) (y : Plane) :
    extendedChartCoefficient c (fun _ : ℝ => C.indicator Ω) (0,y)=
      ((extChartAt 𝓘(ℝ,Plane) c).target ∩ (extChartAt 𝓘(ℝ,Plane) c).symm ⁻¹' C).indicator
        (fun y => extendedChartCoefficient c (fun _ : ℝ => Ω) (0,y)) y := by
  classical
  unfold extendedChartCoefficient spatialZeroExtension chartTwoForm
  by_cases hy : y∈(extChartAt 𝓘(ℝ,Plane) c).target
  · by_cases hc : (extChartAt 𝓘(ℝ,Plane) c).symm y∈C
    · simp only [Set.indicator,hy,hc,mem_inter_iff,mem_preimage,and_self,↓reduceIte]
    · simp only [Set.indicator,hy,hc,mem_inter_iff,mem_preimage,and_false,↓reduceIte]
      simp only [ContinuousLinearMap.bilinearComp_apply,zero_apply]
  · simp only [Set.indicator,hy,mem_inter_iff,false_and,↓reduceIte]

 theorem extendedChartCoefficient_indicator_integrable (c : M) {C : Set M}
    (hC : MeasurableSet C) {Ω : ManifoldTwoForm Plane M}
    (hΩ : Integrable (fun y => extendedChartCoefficient c (fun _ : ℝ => Ω) (0,y))) :
    Integrable (fun y => extendedChartCoefficient c (fun _ : ℝ => C.indicator Ω) (0,y)) := by
  simpa only [extendedChartCoefficient_indicator] using hΩ.indicator (chartRegion_measurable c hC)

 theorem restrictedPartitionFormMass_eq_indicator {I : Type*} [Fintype I] {K : Set M}
    (B : I → SurfaceCoordinateBox M) (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    {C : Set M} (hC : MeasurableSet C) (Ω : ManifoldTwoForm Plane M) :
    restrictedPartitionFormMass B ρ C Ω=partitionFormMass B ρ (C.indicator Ω) := by
  classical
  let : MulActionWithZero ℝ (Plane →L[ℝ] Plane →L[ℝ] ℝ) :=
    @Module.toMulActionWithZero ℝ (Plane →L[ℝ] Plane →L[ℝ] ℝ) inferInstance inferInstance inferInstance
  unfold restrictedPartitionFormMass partitionFormMass chartMass
  apply Finset.sum_congr rfl
  intro i _
  have he : (fun x => ρ i x • C.indicator Ω x)=C.indicator (fun x => ρ i x • Ω x) := by
    funext x
    by_cases hx : x∈C <;> simp only [Set.indicator,hx,↓reduceIte,smul_zero]
  rw [he]
  simp_rw [extendedChartCoefficient_indicator]
  rw [integral_indicator (chartRegion_measurable (B i).center hC)]
  rfl

end

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M]
  {I J : Type*} [Fintype I] [Fintype J] {K : Set M}

omit [T2Space M] in

theorem partitionFormMass_independent_integrable (hpos : PositivePlaneTransitions M)
    (hK : IsCompact K) (B : I → SurfaceCoordinateBox M) (C : J → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K) (ν : SmoothPartitionOfUnity J 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    (hν : ν.IsSubordinate (fun j => (C j).carrier))
    {Ω : ManifoldTwoForm Plane M}
    (hskew : ∀ x u v, Ω x u v = -Ω x v u) (hz : ∀ x, x ∉ K → Ω x=0)
    (hB : ∀ i j,Integrable (fun y => extendedChartCoefficient (B i).center
      (fun _ : ℝ => fun x => ρ i x • (ν j x • Ω x)) (0,y)))
    (hC : ∀ i j,Integrable (fun y => extendedChartCoefficient (C j).center
      (fun _ : ℝ => fun x => ρ i x • (ν j x • Ω x)) (0,y))) :
    partitionFormMass B ρ Ω = partitionFormMass C ν Ω := by
  classical
  let : MulActionWithZero ℝ (Plane →L[ℝ] Plane →L[ℝ] ℝ) :=
    @Module.toMulActionWithZero ℝ (Plane →L[ℝ] Plane →L[ℝ] ℝ) inferInstance inferInstance inferInstance
  let D : I → J → ManifoldTwoForm Plane M := fun i j x => ρ i x • (ν j x • Ω x)
  let L : I → J → Set M := fun i j => K ∩ tsupport (ρ i) ∩ tsupport (ν j)
  have hL (i : I) (j : J) : IsCompact (L i j) :=
    (hK.inter_right (isClosed_tsupport (ρ i))).inter_right (isClosed_tsupport (ν j))
  have hLB (i : I) (j : J) : L i j ⊆ (extChartAt 𝓘(ℝ,Plane) (B i).center).source :=
    fun _ hx => (hρ i hx.1.2).1
  have hLC (i : I) (j : J) : L i j ⊆ (extChartAt 𝓘(ℝ,Plane) (C j).center).source :=
    fun _ hx => (hν j hx.2).1
  have hDz (i : I) (j : J) (x : M) (hx : x ∉ L i j) : D i j x=0 := by
    by_cases hk : x ∈ K
    · by_cases hi : x ∈ tsupport (ρ i)
      · have hj : x ∉ tsupport (ν j) := fun hj => hx ⟨⟨hk,hi⟩,hj⟩
        simp only [D,image_eq_zero_of_notMem_tsupport hj,zero_smul,smul_zero]
      · simp only [D,image_eq_zero_of_notMem_tsupport hi,zero_smul]
    · simp only [D,hz x hk,smul_zero]
  have hDa (i : I) (j : J) (x : M) (u v : Plane) : D i j x u v = -D i j x v u := by
    change ρ i x * (ν j x * Ω x u v) = -(ρ i x * (ν j x * Ω x v u))
    rw [hskew x u v]; ring
  have hsumJ (i : I) : (∑ j, D i j) = fun x => ρ i x • Ω x := by
    funext x
    apply ContinuousLinearMap.ext
    intro firstVector
    apply ContinuousLinearMap.ext
    intro secondVector
    simp only [Finset.sum_apply,D,sum_apply,smul_apply,smul_eq_mul]
    rw [← Finset.mul_sum,← Finset.sum_mul]
    by_cases hx : x ∈ K
    · have hh : (∑ j, ν j x)=1 := by simpa only [finsum_eq_sum_of_fintype] using ν.sum_eq_one hx
      rw [hh,one_mul]
    · simp only [hz x hx,zero_apply,mul_zero]
  have hsumI (j : J) : (∑ i, D i j) = fun x => ν j x • Ω x := by
    funext x
    apply ContinuousLinearMap.ext
    intro firstVector
    apply ContinuousLinearMap.ext
    intro secondVector
    simp only [Finset.sum_apply,D,sum_apply,smul_apply,smul_eq_mul]
    rw [← Finset.sum_mul]
    by_cases hx : x ∈ K
    · have hh : (∑ i, ρ i x)=1 := by simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one hx
      rw [hh,one_mul]
    · simp only [hz x hx,zero_apply,mul_zero]
  have hchange (i : I) (j : J) : chartMass (B i).center (D i j)=chartMass (C j).center (D i j) := by
    apply chartMass_change (hDa i j) (hL i j) (hLB i j) (hLC i j) (hDz i j)
    rintro y ⟨x,hx,rfl⟩
    apply hpos (B i).center (C j).center _ ((extChartAt 𝓘(ℝ,Plane) (B i).center).map_source (hLB i j hx))
    simpa only [(extChartAt 𝓘(ℝ,Plane) (B i).center).left_inv (hLB i j hx)] using hLC i j hx
  unfold partitionFormMass
  calc
    (∑ i, chartMass (B i).center (fun x => ρ i x • Ω x)) =
        ∑ i, ∑ j, chartMass (B i).center (D i j) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← hsumJ i]
      exact chartMass_sum Finset.univ (B i).center (D i)
        (fun j _ => hB i j)
    _ = ∑ i, ∑ j, chartMass (C j).center (D i j) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_congr rfl (fun j _ => hchange i j)
    _ = ∑ j, ∑ i, chartMass (C j).center (D i j) := Finset.sum_comm
    _ = ∑ j, chartMass (C j).center (fun x => ν j x • Ω x) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← hsumI j]
      exact (chartMass_sum Finset.univ (C j).center (fun i => D i j)
        (fun i _ => hC i j)).symm

end PackingSufficiencySupport.Hamiltonian
end

end OAI
