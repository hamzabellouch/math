import OAI.Geometry.Perimeter.Regularity.GeometricHausdorff

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPI.Boundary

theorem surfaceGradient_comp {n : ℕ} {S : Set (Space n)}
    {f : Space n → ℝ} {T : ℝ → ℝ} {x : Space n}
    (hf : DifferentiableAt ℝ f x) (hT : DifferentiableAt ℝ T (f x)) :
    surfaceGradient S (T ∘ f) x = deriv T (f x) • surfaceGradient S f x := by
  have hgrad : gradient (T ∘ f) x = deriv T (f x) • gradient f x := by
    apply (InnerProductSpace.toDual ℝ (Space n)).injective
    simp only [map_smul, toDual_gradient]
    exact (hT.hasDerivAt.comp_hasFDerivAt x hf.hasFDerivAt).fderiv
  simp only [surfaceGradient, hgrad, map_smul, Submodule.coe_smul]

theorem HasSmoothTraceJetAt.comp {n : ℕ} {S : Set (Space n)}
    {h : Space n → ℝ} {G : Space n → Space n} {x : Space n}
    (hxS : x ∈ S) (hx : HasSmoothTraceJetAt S h G x)
    {T : ℝ → ℝ} (hT : ContDiff ℝ ∞ T) :
    HasSmoothTraceJetAt S (T ∘ h) (fun y ↦ deriv T (h y) • G y) x := by
  obtain ⟨U, hU, hxU, f, hf, hfh, hfG⟩ := hx
  refine ⟨U, hU, hxU, T ∘ f, hT.comp_contDiffOn hf, ?_, ?_⟩
  · intro y hy
    exact congrArg T (hfh hy)
  · rw [surfaceGradient_comp ((hf.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp))
        (hT.differentiable (by simp)).differentiableAt, hfh ⟨hxS, hxU⟩, hfG]

def truncatedGradient {n : ℕ} (W : Space n → ℝ) (D : Space n → Space n)
    (x : Space n) : Space n := if W x < 1 then D x else 0

theorem truncationSlope_smul_truncatedGradient {n : ℕ}
    (W : Space n → ℝ) (D : Space n → Space n) {ε : ℝ} (hε : 0 < ε) (x : Space n) :
    truncationSlope ε (W x) • truncatedGradient W D x = truncationSlope ε (W x) • D x := by
  unfold truncatedGradient
  split_ifs with h
  · rfl
  · simp only [truncationSlope_eq_zero hε (le_of_not_gt h), zero_smul]

theorem HasSmoothTraceJetAt.smoothTruncation {n : ℕ} {S : Set (Space n)}
    {W : Space n → ℝ} {D : Space n → Space n} {x : Space n}
    (hxS : x ∈ S) (hx : HasSmoothTraceJetAt S W D x)
    {ε : ℝ} (hε : 0 < ε) :
    HasSmoothTraceJetAt S (fun y ↦ smoothTruncation ε (W y))
      (fun y ↦ truncationSlope ε (W y) • truncatedGradient W D y) x := by
  simpa only [Function.comp_def, smoothTruncation_deriv,
    truncationSlope_smul_truncatedGradient W D hε] using hx.comp hxS (smoothTruncation_contDiff ε)

end RPI.Boundary

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPI.Boundary

theorem smoothTruncation_norm_le {ε s : ℝ} (hε : 0 < ε) (hs : 0 ≤ s) :
    ‖smoothTruncation ε s‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (smoothTruncation_nonneg _ hs)]
  exact (smoothTruncation_le_min hε hs).trans (min_le_right _ _)

theorem truncationSlope_norm_le (ε s : ℝ) : ‖truncationSlope ε s‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (truncationSlope_mem_Icc _ _).1]
  exact (truncationSlope_mem_Icc _ _).2

theorem min_one_memLp {n : ℕ} {μ : Measure (Space n)} [IsFiniteMeasure μ]
    {W : Space n → ℝ} (hW : AEStronglyMeasurable W μ) (hW0 : ∀ᵐ x ∂μ, 0 ≤ W x) :
    MemLp (fun x ↦ min (W x) 1) 2 μ := by
  apply MemLp.of_bound ((continuous_id.min continuous_const).comp_aestronglyMeasurable hW) 1
  filter_upwards [hW0] with x hx
  change ‖min (W x) 1‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg (le_min hx zero_le_one)]
  exact min_le_right _ _

theorem smoothTruncation_memLp {n : ℕ} {μ : Measure (Space n)} [IsFiniteMeasure μ]
    {W : Space n → ℝ} (hW : AEStronglyMeasurable W μ) (hW0 : ∀ᵐ x ∂μ, 0 ≤ W x)
    {ε : ℝ} (hε : 0 < ε) : MemLp (fun x ↦ smoothTruncation ε (W x)) 2 μ := by
  apply MemLp.of_bound ((smoothTruncation_contDiff ε).continuous.comp_aestronglyMeasurable hW) 1
  filter_upwards [hW0] with x hx using smoothTruncation_norm_le hε hx

theorem truncationGradient_memLp {n : ℕ} {μ : Measure (Space n)}
    {W : Space n → ℝ} {D : Space n → Space n}
    (hW : AEStronglyMeasurable W μ) (hG : MemLp (truncatedGradient W D) 2 μ) (ε : ℝ) :
    MemLp (fun x ↦ truncationSlope ε (W x) • truncatedGradient W D x) 2 μ := by
  apply hG.of_le (((truncationSlope_contDiff _).continuous.comp_aestronglyMeasurable hW).smul
    hG.aestronglyMeasurable)
  apply ae_of_all
  intro x
  change ‖truncationSlope ε (W x) • truncatedGradient W D x‖ ≤ ‖truncatedGradient W D x‖
  rw [norm_smul]
  exact mul_le_of_le_one_left (norm_nonneg _) (truncationSlope_norm_le _ _)

theorem smoothTruncation_error_energy_tendsto {n : ℕ} {μ : Measure (Space n)}
    [IsFiniteMeasure μ] {W : Space n → ℝ}
    (hW : AEStronglyMeasurable W μ) (hW0 : ∀ᵐ x ∂μ, 0 ≤ W x) :
    Tendsto (fun j ↦ vectorEnergy μ (fun x ↦ smoothTruncation (truncationParameter j) (W x) -
      min (W x) 1)) atTop (𝓝 0) := by
  have hm : AEStronglyMeasurable (fun x ↦ min (W x) 1) μ := (continuous_id.min continuous_const).comp_aestronglyMeasurable hW
  have hf : ∀ j, AEStronglyMeasurable (fun x ↦ smoothTruncation (truncationParameter j) (W x)) μ :=
    fun j ↦ (smoothTruncation_contDiff _).continuous.comp_aestronglyMeasurable hW
  have hmeas : ∀ j, AEMeasurable (fun x ↦ ENNReal.ofReal
      (‖smoothTruncation (truncationParameter j) (W x) - min (W x) 1‖ ^ 2)) μ :=
    fun j ↦ (((hf j).sub hm).norm.pow 2).aemeasurable.ennreal_ofReal
  have hlim := tendsto_lintegral_of_dominated_convergence' (μ := μ)
    (fun _ : Space n ↦ ENNReal.ofReal ((2 : ℝ) ^ 2)) (f := fun _ ↦ (0 : ℝ≥0∞))
    (F := fun j x ↦ ENNReal.ofReal (‖smoothTruncation (truncationParameter j) (W x) - min (W x) 1‖ ^ 2))
    hmeas ?_ ?_ ?_
  · simpa only [vectorEnergy, lintegral_zero] using hlim
  · intro j
    filter_upwards [hW0] with x hx
    have hm : ‖min (W x) 1‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min hx zero_le_one)]
      exact min_le_right _ _
    apply ENNReal.ofReal_le_ofReal
    apply (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mpr
    exact (norm_sub_le _ _).trans (by linarith [smoothTruncation_norm_le (truncationParameter_pos j) hx])
  · simp only [lintegral_const, ne_eq]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ _)
  · filter_upwards [hW0] with x hx
    have ht : Tendsto (fun j ↦ smoothTruncation (truncationParameter j) (W x) - min (W x) 1)
        atTop (𝓝 (0 : ℝ)) := by
      simpa only [sub_self] using (smoothTruncation_tendsto hx).sub_const (min (W x) 1)
    simpa only [norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal (ht.norm.pow 2)

theorem truncationGradient_error_energy_tendsto {n : ℕ} {μ : Measure (Space n)}
    {W : Space n → ℝ} {D : Space n → Space n}
    (hW : AEStronglyMeasurable W μ) (hG : MemLp (truncatedGradient W D) 2 μ) :
    Tendsto (fun j ↦ vectorEnergy μ (fun x ↦
      truncationSlope (truncationParameter j) (W x) • truncatedGradient W D x -
        truncatedGradient W D x)) atTop (𝓝 0) := by
  let G := truncatedGradient W D
  let F := fun j x ↦ truncationSlope (truncationParameter j) (W x) • G x
  have hF : ∀ j, MemLp (F j) 2 μ := fun j ↦ truncationGradient_memLp hW hG _
  have hfin : vectorEnergy μ G ≠ ⊤ :=
    (memLp_two_iff_vectorEnergy hG.aestronglyMeasurable).mp hG |>.ne
  have hmeas : ∀ j, AEMeasurable (fun x ↦ ENNReal.ofReal (‖F j x - G x‖ ^ 2)) μ := by
    intro j
    exact (((hF j).aestronglyMeasurable.sub hG.aestronglyMeasurable).norm.pow 2).aemeasurable.ennreal_ofReal
  have hlim := tendsto_lintegral_of_dominated_convergence' (μ := μ)
    (fun x ↦ ENNReal.ofReal (‖G x‖ ^ 2)) (f := fun _ ↦ (0 : ℝ≥0∞))
    (F := fun j x ↦ ENNReal.ofReal (‖F j x - G x‖ ^ 2)) hmeas ?_ hfin ?_
  · simpa only [vectorEnergy, Pi.sub_apply, lintegral_zero] using hlim
  · intro j
    apply ae_of_all
    intro x
    apply ENNReal.ofReal_le_ofReal
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    have he : F j x - G x = (truncationSlope (truncationParameter j) (W x) - 1) • G x := by
      rw [sub_smul, one_smul]
    rw [he, norm_smul, Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr (truncationSlope_mem_Icc _ _).2)]
    exact mul_le_of_le_one_left (norm_nonneg _) (by linarith [(truncationSlope_mem_Icc (truncationParameter j) (W x)).1])
  · apply ae_of_all
    intro x
    have ht : Tendsto (fun j ↦ F j x) atTop (𝓝 (G x)) := by
      have ht := (truncationSlope_tendsto (W x)).smul_const (G x)
      by_cases hx : W x < 1
      · simpa only [ite_eq_left hx, one_smul] using ht
      · simpa only [F, G, truncatedGradient, ite_eq_right hx, smul_zero] using ht
    have ht' : Tendsto (fun j ↦ F j x - G x) atTop (𝓝 (0 : Space n)) := by
      simpa only [sub_self] using ht.sub_const (G x)
    simpa only [norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal (ht'.norm.pow 2)

theorem smoothTruncation_pair_tendsto {n : ℕ} {μ : Measure (Space n)}
    [IsFiniteMeasure μ] {W : Space n → ℝ} {D : Space n → Space n}
    (hW : AEStronglyMeasurable W μ) (hW0 : ∀ᵐ x ∂μ, 0 ≤ W x)
    (hG : MemLp (truncatedGradient W D) 2 μ) :
    ∃ (hh : MemLp (fun x ↦ min (W x) 1) 2 μ)
      (hf : ∀ j, MemLp (fun x ↦ smoothTruncation (truncationParameter j) (W x)) 2 μ)
      (hF : ∀ j, MemLp (fun x ↦ truncationSlope (truncationParameter j) (W x) •
        truncatedGradient W D x) 2 μ),
      Tendsto (fun j ↦ ((hf j).toLp (fun x ↦ smoothTruncation (truncationParameter j) (W x)),
        (hF j).toLp (fun x ↦ truncationSlope (truncationParameter j) (W x) •
          truncatedGradient W D x))) atTop
        (𝓝 (hh.toLp (fun x ↦ min (W x) 1), hG.toLp (truncatedGradient W D))) := by
  let hh := min_one_memLp hW hW0
  let hf := fun j ↦ smoothTruncation_memLp hW hW0 (truncationParameter_pos j)
  let hF := fun j ↦ truncationGradient_memLp hW hG (truncationParameter j)
  refine ⟨hh, hf, hF, ?_⟩
  apply Filter.Tendsto.prodMk_nhds
  · apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hf _ hh).mpr
    exact tendsto_eLpNorm_two_of_vectorEnergy_zero_of_aestronglyMeasurable
      (fun index ↦ ((hf index).sub hh).aestronglyMeasurable)
      (smoothTruncation_error_energy_tendsto hW hW0)
  · apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hF _ hG).mpr
    exact tendsto_eLpNorm_two_of_vectorEnergy_zero_of_aestronglyMeasurable
      (fun index ↦ ((hF index).sub hG).aestronglyMeasurable)
      (truncationGradient_error_energy_tendsto hW hG)

end RPI.Boundary

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPI.Boundary

theorem surfaceGradient_eq_tangentialGradient_filled {n : ℕ} {E S : Set (Space n)}
    (hE : MeasurableSet E) {f g : Space n → ℝ} {x : Space n}
    (hf : ContDiffAt ℝ 1 f x) (hfx : f x = 0) (hdf : fderiv ℝ f x ≠ 0)
    (hlevel : ∀ᶠ y in 𝓝 x, y ∈ S ↔ f y = 0)
    (hfilled : ∀ᶠ y in 𝓝 x, (f y < 0 → y ∈ E) ∧ (y ∈ E → f y ≤ 0)) :
    surfaceGradient S g x = RPISingularHarnack.tangentialGradient E g x := by
  have hgrad : gradient f x ≠ 0 := by
    intro he
    apply hdf
    rw [← toDual_gradient, he, map_zero]
  have hn : ‖gradient f x‖ ≠ 0 := norm_ne_zero_iff.mpr hgrad
  rw [surfaceGradient_eq_level_formula hf hdf (by simpa only [hfx] using hlevel),
    RPISingularHarnack.tangentialGradient,
    RPISingularHarnack.approximateNormal_eq_gradient_filled hE
      (hf.differentiableAt (by norm_num)) hfx hdf hfilled,
    real_inner_smul_right, smul_smul, real_inner_comm (gradient f x) (gradient g x)]
  congr 2
  field_simp

end RPI.Boundary

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPI.Boundary

theorem surfaceGradient_ae_eq_tangentialGradient_filled {n : ℕ} (hn : 8 ≤ n)
    {E S Z : Set (Space n)} (hE : MeasurableSet E) (hS : MeasurableSet S)
    (hZd : dimH Z ≤ (n - 8 : ℕ))
    (hreg : ∀ x ∈ S \ Z, ∃ f : Space n → ℝ,
      ContDiffAt ℝ 1 f x ∧ f x = 0 ∧ fderiv ℝ f x ≠ 0 ∧
      (∀ᶠ y in 𝓝 x, y ∈ S ↔ f y = 0) ∧
      (∀ᶠ y in 𝓝 x, (f y < 0 → y ∈ E) ∧ (y ∈ E → f y ≤ 0))) (g : Space n → ℝ) :
    surfaceGradient S g =ᵐ[surfaceMeasure S]
      RPISingularHarnack.tangentialGradient E g := by
  have hz : ∀ᵐ x ∂surfaceMeasure S, x ∉ Z := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using
      surfaceMeasure_zero_of_singular_dim hn S Z hZd
  filter_upwards [ae_restrict_mem hS, hz] with x hx hzx
  obtain ⟨f, hf, hfx, hdf, hlevel, hfilled⟩ := hreg x ⟨hx, hzx⟩
  exact surfaceGradient_eq_tangentialGradient_filled hE hf hfx hdf hlevel hfilled

end RPI.Boundary

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack

theorem wholeBoundarySobolev_of_local_sobolevGraph_filled {n : ℕ} (hn : 8 ≤ n)
    {E Z : Set (Euc n)} (hE : MeasurableSet E)
    (hS : MeasurableSet (perimeterSupport E)) (hZd : dimH Z ≤ (n - 8 : ℕ))
    (hreg : ∀ x ∈ perimeterSupport E \ Z, ∃ f : Euc n → ℝ,
      ContDiffAt ℝ 1 f x ∧ f x = 0 ∧ fderiv ℝ f x ≠ 0 ∧
      (∀ᶠ y in 𝓝 x, y ∈ perimeterSupport E ↔ f y = 0) ∧
      (∀ᶠ y in 𝓝 x, (f y < 0 → y ∈ E) ∧ (y ∈ E → f y ≤ 0)))
    {h : Euc n → ℝ} {G : Euc n → Euc n}
    (hgraph : ∀ R : ℝ, 0 < R →
      ∃ (hh : MemLp h 2 ((RPI.Boundary.surfaceMeasure (perimeterSupport E)).restrict
          (Metric.ball 0 R)))
        (hG : MemLp G 2 ((RPI.Boundary.surfaceMeasure (perimeterSupport E)).restrict
          (Metric.ball 0 R))),
        (hh.toLp h, hG.toLp G) ∈ closure
          (RPI.Boundary.smoothGradientGraph (perimeterSupport E) (Metric.ball 0 R))) :
    WholeBoundarySobolev E h G := by
  intro R hR
  obtain ⟨hh, hG, hpair⟩ := hgraph R hR
  obtain ⟨φ, hφ, hlim, hDlim⟩ :=
    RPI.Boundary.exists_compact_energy_approximants_of_mem_sobolevGraph
      (perimeterSupport E) (Metric.ball 0 R) Metric.isBounded_ball
      measurableSet_ball hh hG hpair
  dsimp only
  rw [boundaryArea_eq_smul_surfaceMeasure, Measure.restrict_smul]
  refine ⟨hh.smul_measure (hausdorffNormalizationRatio_ne_top _),
    hG.smul_measure (hausdorffNormalizationRatio_ne_top _), φ, hφ, ?_, ?_⟩
  · simp_rw [lintegral_smul_measure, smul_eq_mul]
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hlim
      (Or.inr (hausdorffNormalizationRatio_ne_top (n - 1)))
  · have heq : ∀ j, RPI.Boundary.surfaceGradient (perimeterSupport E) (φ j)
        =ᵐ[(RPI.Boundary.surfaceMeasure (perimeterSupport E)).restrict (Metric.ball 0 R)]
          tangentialGradient E (φ j) := fun j ↦
      (RPI.Boundary.surfaceGradient_ae_eq_tangentialGradient_filled hn hE hS hZd hreg (φ j)).filter_mono
        (ae_mono Measure.restrict_le_self)
    have hl : Tendsto (fun j ↦ ∫⁻ x,
        ENNReal.ofReal (‖tangentialGradient E (φ j) x - G x‖ ^ 2)
        ∂(RPI.Boundary.surfaceMeasure (perimeterSupport E)).restrict (Metric.ball 0 R))
        atTop (𝓝 0) := by
      apply hDlim.congr
      intro j
      apply lintegral_congr_ae
      filter_upwards [heq j] with x hx
      rw [hx]
    simp_rw [lintegral_smul_measure, smul_eq_mul]
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hl
      (Or.inr (hausdorffNormalizationRatio_ne_top (n - 1)))

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPI.Boundary

theorem HasSmoothTraceJetAt.mul_smooth {n : ℕ} {S : Set (Space n)}
    {h : Space n → ℝ} {G : Space n → Space n} {x : Space n}
    (hxS : x ∈ S) (hx : HasSmoothTraceJetAt S h G x)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ ∞ ψ) :
    HasSmoothTraceJetAt S (fun y ↦ ψ y * h y)
      (fun y ↦ ψ y • G y + h y • surfaceGradient S ψ y) x := by
  obtain ⟨U, hU, hxU, f, hf, he, hG⟩ := hx
  refine ⟨U, hU, hxU, fun y ↦ ψ y * f y, hψ.contDiffOn.mul hf, ?_, ?_⟩
  · intro y hy
    exact congrArg (fun a ↦ ψ y * a) (he hy)
  · rw [surfaceGradient_mul (hψ.differentiable (by simp) x)
        ((hf.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)),
        hG, he ⟨hxS, hxU⟩]

theorem regular_trace_jet_mul_spatial {n : ℕ} {S Z : Set (Space n)}
    {h : Space n → ℝ} {G : Space n → Space n}
    (hreg : ∀ x ∈ S \ Z, HasSmoothTraceJetAt S h G x)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ ∞ ψ) :
    ∀ x ∈ S \ (Z ∩ tsupport ψ), HasSmoothTraceJetAt S (fun y ↦ ψ y * h y)
      (fun y ↦ ψ y • G y + h y • surfaceGradient S ψ y) x := by
  intro x hx
  by_cases hxZ : x ∈ Z
  · have hxs : x ∉ tsupport ψ := fun hxψ ↦ hx.2 ⟨hxZ, hxψ⟩
    have hloc : ψ =ᶠ[𝓝 x] (0 : Space n → ℝ) :=
      notMem_tsupport_iff_eventuallyEq.mp hxs
    obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp hloc
    have hψgrad : gradient ψ x = 0 := by
      simpa only [Pi.zero_def, gradient_fun_const] using hloc.gradient_eq
    have hψx : ψ x = 0 := hloc.self_of_nhds
    refine ⟨U, hU, hxU, fun _ ↦ 0, contDiffOn_const, ?_, ?_⟩
    · intro y hy
      have hy0 : ψ y = 0 := hUsub hy.2
      simp only [hy0, zero_mul]
    · simp only [hψx, surfaceGradient, hψgrad, gradient_fun_const,
        map_zero, Submodule.coe_zero, zero_smul, smul_zero, add_zero]
  · exact (hreg x ⟨hx.1, hxZ⟩).mul_smooth hx.1 hψ

theorem hausdorff_trace_mem_sobolevGraph_ball {n : ℕ} (hn : 8 ≤ n)
    {S Z : Set (Space n)} (hS : IsClosed S) (hZ : IsClosed Z)
    (hZd : dimH Z ≤ (n - 8 : ℕ)) {R : ℝ} (hR : 0 < R)
    {h : Space n → ℝ} {G : Space n → Space n}
    (hreg : ∀ x ∈ S \ Z, HasSmoothTraceJetAt S h G x)
    (hh : MemLp h 2 ((surfaceMeasure S).restrict (Metric.ball 0 R)))
    (hG : MemLp G 2 ((surfaceMeasure S).restrict (Metric.ball 0 R)))
    {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ᵐ x ∂(surfaceMeasure S).restrict (Metric.ball 0 R), ‖h x‖ ≤ M)
    (hgrad : ∀ f : Space n → ℝ, ContDiff ℝ ∞ f →
      AEStronglyMeasurable (surfaceGradient S f)
        ((surfaceMeasure S).restrict (Metric.ball 0 R)))
    {A r₀ : ℝ} (hA : 0 < A) (hr₀ : 0 < r₀)
    (hgrowth : ∀ c ∈ Z ∩ Metric.closedBall 0 (R + 2), ∀ r : ℝ, 0 < r → r < r₀ →
      (surfaceMeasure S).restrict (Metric.ball 0 R) (Metric.ball c r) ≤
        ENNReal.ofReal (A * r ^ (n - 1))) :
    (hh.toLp h, hG.toLp G) ∈ closure (smoothGradientGraph S (Metric.ball 0 R)) := by
  let b : ContDiffBump (0 : Space n) := ⟨R + 1, R + 2, by linarith, by linarith⟩
  let K : Set (Space n) := Z ∩ tsupport b
  have hKc : IsCompact K := b.hasCompactSupport.of_isClosed_subset
    (hZ.inter (isClosed_tsupport b)) inter_subset_right
  have hKd : dimH K ≤ (n - 8 : ℕ) :=
    (dimH_mono (show K ⊆ Z from inter_subset_left)).trans hZd
  have hb : ∀ x ∈ Metric.ball (0 : Space n) R, b =ᶠ[𝓝 x] 1 := by
    intro x hx
    apply b.eventuallyEq_one_of_mem_ball
    exact Metric.mem_ball.mpr ((Metric.mem_ball.mp hx).trans (by dsimp [b]; linarith))
  have hbG : ∀ x ∈ Metric.ball (0 : Space n) R, surfaceGradient S b x = 0 := by
    intro x hx
    have hgr : gradient b x = 0 := by
      simpa only [Pi.one_def, gradient_fun_const] using (hb x hx).gradient_eq
    simp only [surfaceGradient, hgr, map_zero, Submodule.coe_zero]
  let h' := fun x ↦ b x * h x
  let G' := fun x ↦ b x • G x + h x • surfaceGradient S b x
  have he : h' =ᵐ[(surfaceMeasure S).restrict (Metric.ball 0 R)] h := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    dsimp [h']
    rw [(hb x hx).self_of_nhds]
    simp
  have hDe : G' =ᵐ[(surfaceMeasure S).restrict (Metric.ball 0 R)] G := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    dsimp [G']
    rw [(hb x hx).self_of_nhds, hbG x hx]
    simp
  let hh' := hh.ae_eq he.symm
  let hG' := hG.ae_eq hDe.symm
  have hbound' : ∀ᵐ x ∂(surfaceMeasure S).restrict (Metric.ball 0 R), ‖h' x‖ ≤ M := by
    filter_upwards [he, hbound] with x hx hbx
    simpa only [hx] using hbx
  have hmem := hausdorff_trace_mem_sobolevGraph hn hS (Metric.ball 0 R) hKc hKd
    (regular_trace_jet_mul_spatial hreg b.contDiff) hh' hG' hM
    hbound' hgrad hA hr₀ (fun c hc r hr hrr ↦ hgrowth c
      ⟨hc.1, by simpa only [b.tsupport_eq] using hc.2⟩ r hr hrr)
  have heLp : hh'.toLp h' = hh.toLp h := hh'.toLp_congr hh he
  have hDeLp : hG'.toLp G' = hG.toLp G := hG'.toLp_congr hG hDe
  change (hh'.toLp h', hG'.toLp G') ∈ _ at hmem
  simpa only [heLp, hDeLp] using hmem

end RPI.Boundary

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPI.Boundary

theorem trace_aestronglyMeasurable_of_singular_dim {n : ℕ} (hn : 8 ≤ n)
    {S Z : Set (Space n)} (hS : MeasurableSet S) (hZ : MeasurableSet Z)
    (hdim : dimH Z ≤ (n - 8 : ℕ)) {h : Space n → ℝ} {G : Space n → Space n}
    (hreg : ∀ x ∈ S \ Z, HasSmoothTraceJetAt S h G x) :
    AEStronglyMeasurable h (surfaceMeasure S) := by
  have hc : ContinuousOn h (S \ Z) := by
    intro x hx
    obtain ⟨U, hU, hxU, f, hf, he, _⟩ := hreg x hx
    have hf' : ContinuousWithinAt f (S \ Z) x :=
      (hf.contDiffAt (hU.mem_nhds hxU)).continuousAt.continuousWithinAt
    apply hf'.congr_of_eventuallyEq _ (he ⟨hx.1, hxU⟩).symm
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hxU)] with y hy hyU
    exact (he ⟨hy.1, hyU⟩).symm
  have hs : ∀ᵐ x ∂surfaceMeasure S, x ∈ S := ae_restrict_mem hS
  have hz : ∀ᵐ x ∂surfaceMeasure S, x ∉ Z := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using
      surfaceMeasure_zero_of_singular_dim hn S Z hdim
  have hregular : ∀ᵐ x ∂surfaceMeasure S, x ∈ S \ Z := by
    filter_upwards [hs, hz] with x hx hzx
    exact ⟨hx, hzx⟩
  have hmeas := hc.aestronglyMeasurable (μ := surfaceMeasure S) (hS.diff hZ)
  rwa [Measure.restrict_eq_self_of_ae_mem hregular] at hmeas

theorem min_one_mem_sobolevGraph_ball {n : ℕ} (hn : 8 ≤ n)
    {S Z : Set (Space n)} (hS : IsClosed S) (hZ : IsClosed Z)
    (hZd : dimH Z ≤ (n - 8 : ℕ)) {R : ℝ} (hR : 0 < R)
    [IsFiniteMeasure ((surfaceMeasure S).restrict (Metric.ball 0 R))]
    {W : Space n → ℝ} {D : Space n → Space n}
    (htrace : ∀ x ∈ S \ Z, HasSmoothTraceJetAt S W D x)
    (hW0 : ∀ᵐ x ∂(surfaceMeasure S).restrict (Metric.ball 0 R), 0 ≤ W x)
    (hG : MemLp (truncatedGradient W D) 2
      ((surfaceMeasure S).restrict (Metric.ball 0 R)))
    (hgrad : ∀ f : Space n → ℝ, ContDiff ℝ ∞ f →
      AEStronglyMeasurable (surfaceGradient S f)
        ((surfaceMeasure S).restrict (Metric.ball 0 R)))
    {A r₀ : ℝ} (hA : 0 < A) (hr₀ : 0 < r₀)
    (hgrowth : ∀ c ∈ Z ∩ Metric.closedBall 0 (R + 2), ∀ r : ℝ, 0 < r → r < r₀ →
      (surfaceMeasure S).restrict (Metric.ball 0 R) (Metric.ball c r) ≤
        ENNReal.ofReal (A * r ^ (n - 1))) :
    ∃ hh : MemLp (fun x ↦ min (W x) 1) 2
        ((surfaceMeasure S).restrict (Metric.ball 0 R)),
      (hh.toLp (fun x ↦ min (W x) 1), hG.toLp (truncatedGradient W D)) ∈
        closure (smoothGradientGraph S (Metric.ball 0 R)) := by
  have hW : AEStronglyMeasurable W ((surfaceMeasure S).restrict (Metric.ball 0 R)) :=
    (trace_aestronglyMeasurable_of_singular_dim hn hS.measurableSet
    hZ.measurableSet hZd htrace).mono_measure (Measure.restrict_le_self)
  obtain ⟨hh, hf, hF, hlim⟩ := smoothTruncation_pair_tendsto hW hW0 hG
  refine ⟨hh, isClosed_closure.mem_of_tendsto hlim (Filter.Eventually.of_forall ?_)⟩
  intro j
  apply hausdorff_trace_mem_sobolevGraph_ball hn hS hZ hZd hR
    (fun x hx ↦ (htrace x hx).smoothTruncation hx.1 (truncationParameter_pos j))
    (hf j) (hF j) (M := 1) zero_le_one _ hgrad hA hr₀ hgrowth
  filter_upwards [hW0] with x hx
  exact smoothTruncation_norm_le (truncationParameter_pos j) hx

end RPI.Boundary

end

end OAI
