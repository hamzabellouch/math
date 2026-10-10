import OAI.Analysis.SignedDisk.ActualMarkTrees2

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace DiskMaximalTools

lemma strong_three_halves_norm {f : ℂ → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) [IsFiniteMeasure (volume.withDensity (fun x => ENNReal.ofReal (f x)))] :
    eLpNorm (fun x => (rationalMaximal (volume.withDensity (fun x => ENNReal.ofReal (f x))) x).toReal)
      (3/2) volume ≤ ENNReal.ofReal ((150*2^(1/2:ℝ))^(2/3:ℝ))*eLpNorm f (3/2) volume := by
  have h := strong_rationalMaximal hf hf0 (by norm_num : (1:ℝ) < 3/2)
  have hs := ENNReal.rpow_le_rpow h (by norm_num : (0:ℝ) ≤ 2/3)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2/3)] at hs
  have hp : (50*(3/2:ℝ)*2^((3/2:ℝ)-1)/((3/2:ℝ)-1)) = 150*2^(1/2:ℝ) := by
    norm_num
    ring
  rw [hp,ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)] at hs
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (3/2:ℝ≥0∞) ≠ 0)
    (ENNReal.div_ne_top (by norm_num) (by norm_num))
      (measurable_rationalMaximal _).ennreal_toReal.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (3/2:ℝ≥0∞) ≠ 0)
    (ENNReal.div_ne_top (by norm_num) (by norm_num)) hf.aestronglyMeasurable]
  norm_num only [ENNReal.toReal_div,ENNReal.toReal_ofNat,one_div_div]
  simp only [← ofReal_norm,Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg,
    abs_of_nonneg (hf0 _),ENNReal.ofReal_rpow_of_nonneg (hf0 _) (by norm_num : (0:ℝ) ≤ 3/2),
    ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num : (0:ℝ) ≤ 3/2)] at hs ⊢
  exact hs

lemma lintegral_le_three_halves_norm {f : ℂ → ℝ} (hf : AEStronglyMeasurable f volume)
    (hf0 : ∀ x, 0 ≤ f x) {Q : Set ℂ} (hQ : volume Q ≤ 1) :
    (∫⁻ x in Q, ENNReal.ofReal (f x)) ≤ eLpNorm f (3/2) volume := by
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (show (1:ℝ≥0∞) ≤ 3/2 by rw [ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)]; norm_num) hf.restrict (μ := volume.restrict Q)
  have he : (1 / ENNReal.toReal 1 - 1 / ENNReal.toReal (3/2)) = (1/3:ℝ) := by norm_num
  rw [he,Measure.restrict_apply_univ] at h
  have hpow : (volume Q)^(1/3:ℝ) ≤ 1 := by
    simpa using ENNReal.rpow_le_rpow hQ (by norm_num : (0:ℝ) ≤ 1/3)
  calc
    _ = eLpNorm f 1 (volume.restrict Q) := by
      rw [eLpNorm_one_eq_lintegral_enorm hf.restrict]
      simp only [← ofReal_norm,Real.norm_eq_abs,abs_of_nonneg (hf0 _)]
    _ ≤ eLpNorm f (3/2) (volume.restrict Q)*(volume Q)^(1/3:ℝ) := h
    _ ≤ eLpNorm f (3/2) (volume.restrict Q) := by simpa using mul_le_mul_right hpow _
    _ ≤ _ := eLpNorm_mono_measure _ Measure.restrict_le_self
end DiskMaximalTools

namespace PlanePotential
open LocalCancellation

/-- The complete local L^(3/2) value estimate for a genuine finite vector
cancellation decomposition, with the common 1/100 price. -/
theorem local_value_lp : ∃ C : ℝ, 0 < C ∧
    ∀ {ι : Type} [Fintype ι] (b : ι → ErrorPiece 2) {g : ℂ → ℝ},
    ContDiff ℝ 1 g → (∃ D : ℝ, ∀ y, ‖fderiv ℝ g y‖ ≤ D) →
    (∀ᵐ y, ‖y‖ ≤ 8 → gradient g y = ∑ i, (b i).density y) →
    ∃ c : ℝ, eLpNorm (fun x => g x-c) (3/2) (volume.restrict {x : ℂ | ‖x‖ ≤ 8}) ≤
      ENNReal.ofReal (C * errorPrice b (1/100)) := by
  obtain ⟨ψ,C,hC,hψ,hψc,hψ1,hψs,hprice⟩ := exists_green_price
  obtain ⟨B,hB⟩ := hψc.exists_bound_of_continuous hψ.continuous
  have hB0 : 0 ≤ B := (norm_nonneg (ψ 0)).trans (hB 0)
  have hψB (z : ℂ) : |ψ z| ≤ B := by simpa only [Real.norm_eq_abs] using hB z
  refine ⟨C,hC,?_⟩
  intro ι _ b g hg hD hdecomp
  obtain ⟨D,hD⟩ := hD
  refine ⟨∫ z, ψ z*g z,?_⟩
  apply (green_decomposition_norm_local hψ.continuous hψc hg hD hψ1 hψs hψB
    (by norm_num : (1:ℝ) ≤ 8) (by norm_num : (0:ℝ) < 1+8) hB0 (by norm_num : (0:ℝ) < 8)
    (fun i => (b i).density) (fun i => (b i).integrable) hdecomp).trans
  apply (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hprice (b i))).trans_eq
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (b i).size_pos.le _)) (b i).mass_nonneg)]
  congr 1
  rw [errorPrice,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring
end PlanePotential

namespace DiskMoments
open DiskMaximalTools

lemma signedAverage_sub_const {g : ℂ → ℝ} (hg : Continuous g) (c : ℝ) (x : ℂ) {t : ℝ} (ht : 0 < t) :
    signedAverage (fun y => g y-c) x t = signedAverage g x t-c := by
  have hi : IntegrableOn g (Metric.ball x t) :=
    (hg.continuousOn.integrableOn_compact (isCompact_closedBall x t)).mono_set Metric.ball_subset_closedBall
  have hc : IntegrableOn (fun _ : ℂ => c) (Metric.ball x t) := integrableOn_const measure_ball_lt_top.ne
  unfold signedAverage
  rw [integral_sub hi hc,integral_const]
  have hv : (volume (Metric.ball x t)).toReal = Real.pi*t^2 := by
    rw [volume_disk_real x ht.le,ENNReal.toReal_ofReal (by positivity)]
  simp only [Measure.real,Measure.restrict_apply_univ,hv,smul_eq_mul]
  field_simp

/-- A true disk average of a continuous function is controlled by the local
absolute-density maximal function. No maximizing-radius selection is used. -/
lemma local_average_le {g : ℂ → ℝ} (hg : Continuous g) (c : ℝ)
    {x : ℂ} (hx : ‖x‖ ≤ 2) {t : ℝ} (ht : 0 < t) (ht4 : t ≤ 4) :
    ENNReal.ofReal |signedAverage g x t-c| ≤
      rationalMaximal (volume.withDensity (fun y => ENNReal.ofReal
        (({y : ℂ | ‖y‖ ≤ 8}.indicator (fun y => |g y-c|)) y))) x := by
  let f : ℂ → ℝ := {y : ℂ | ‖y‖ ≤ 8}.indicator (fun y => |g y-c|)
  have hf : Measurable f := ((hg.measurable.sub measurable_const).abs).indicator
    (measurableSet_le measurable_norm measurable_const)
  have hfi : Integrable f := by
    apply IntegrableOn.integrable_indicator _ (measurableSet_le measurable_norm measurable_const)
    apply ContinuousOn.integrableOn_compact
      (show IsCompact {y : ℂ | ‖y‖ ≤ 8} by simpa only [Metric.closedBall,dist_zero_right] using isCompact_closedBall (0:ℂ) 8)
    exact (hg.sub continuous_const).abs.continuousOn
  have hsub (y : ℂ) (hy : y ∈ Metric.ball x t) : ‖y‖ ≤ 8 := by
    have hy' : ‖y-x‖ < t := by simpa only [Metric.mem_ball,dist_eq_norm] using hy
    have hh := norm_add_le (y-x) x
    rw [sub_add_cancel] at hh
    linarith
  have he : (∫ y in Metric.ball x t, f y) = ∫ y in Metric.ball x t, |g y-c| := by
    apply setIntegral_congr_fun measurableSet_ball
    intro y hy
    simp [f,hsub y hy]
  have hav : |signedAverage g x t-c| ≤ (∫ y in Metric.ball x t, f y)/(Real.pi*t^2) := by
    rw [← signedAverage_sub_const hg c x ht,signedAverage,abs_div,abs_of_pos (by positivity : 0 < Real.pi*t^2),he]
    apply div_le_div_of_nonneg_right _ (by positivity)
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun y => g y-c) (μ := volume.restrict (Metric.ball x t))
  have hν : (volume.withDensity (fun y => ENNReal.ofReal (f y))) (Metric.ball x t) =
      ENNReal.ofReal (∫ y in Metric.ball x t, f y) := by
    rw [withDensity_apply _ measurableSet_ball]
    exact (ofReal_integral_eq_lintegral_ofReal hfi.integrableOn
      (ae_of_all _ (fun y => by dsimp [f]; exact Set.indicator_nonneg (fun _ _ => abs_nonneg _ ) y))).symm
  apply (ENNReal.ofReal_le_ofReal hav).trans
  rw [ENNReal.ofReal_div_of_pos (by positivity : 0 < Real.pi*t^2),← hν,← volume_disk_real x ht.le]
  exact disk_average_le_rationalMaximal_exact _ x ht
end DiskMoments

namespace PlanePotential
open LocalCancellation DiskMaximalTools DiskMoments

/-- Full local value-oscillation price, for every pair of positive radii at
most four. The measurable majorant is an actual centered Euclidean disk
maximal function, not an assumed analytic input. -/
theorem local_value_majorant : ∃ C : ℝ, 0 < C ∧
    ∀ {ι : Type} [Fintype ι] (b : ι → ErrorPiece 2) {g : ℂ → ℝ},
    ContDiff ℝ 1 g → (∃ D : ℝ, ∀ y, ‖fderiv ℝ g y‖ ≤ D) →
    (∀ᵐ y, ‖y‖ ≤ 8 → gradient g y = ∑ i, (b i).density y) →
    ∀ Q : Set ℂ, volume Q ≤ ENNReal.ofReal 1 →
    ∃ F : ℂ → ℝ≥0∞, Measurable F ∧
      (∫⁻ x in Q, F x) ≤ ENNReal.ofReal (C*errorPrice b (1/100)) ∧
      ∀ x, ‖x‖ ≤ 2 → ∀ t t', 0 < t → t ≤ 4 → 0 < t' → t' ≤ 4 →
        ENNReal.ofReal |signedAverage g x t-signedAverage g x t'| ≤ F x := by
  obtain ⟨C,hC,hlocal⟩ := local_value_lp
  let K : ℝ := (150*2^(1/2:ℝ))^(2/3:ℝ)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨2*K*C,by positivity,?_⟩
  intro ι _ b g hg hD hdecomp Q hQ
  obtain ⟨c,hc⟩ := hlocal b hg hD hdecomp
  let f : ℂ → ℝ := {y : ℂ | ‖y‖ ≤ 8}.indicator (fun y => |g y-c|)
  have hf : Measurable f := ((hg.continuous.measurable.sub measurable_const).abs).indicator
    (measurableSet_le measurable_norm measurable_const)
  have hf0 (y : ℂ) : 0 ≤ f y := Set.indicator_nonneg (fun _ _ => abs_nonneg _) y
  have hfi : Integrable f := by
    apply IntegrableOn.integrable_indicator _ (measurableSet_le measurable_norm measurable_const)
    apply ContinuousOn.integrableOn_compact
      (show IsCompact {y : ℂ | ‖y‖ ≤ 8} by simpa only [Metric.closedBall,dist_zero_right] using isCompact_closedBall (0:ℂ) 8)
    exact (hg.continuous.sub continuous_const).abs.continuousOn
  let ν := volume.withDensity (fun y => ENNReal.ofReal (f y))
  have hν : ν univ = ENNReal.ofReal (∫ y, f y) := by
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
    exact (ofReal_integral_eq_lintegral_ofReal hfi (ae_of_all _ hf0)).symm
  have : IsFiniteMeasure ν := ⟨by rw [hν]; exact ENNReal.ofReal_lt_top⟩
  let M : ℂ → ℝ := fun x => (rationalMaximal ν x).toReal
  have hM : Measurable M := (measurable_rationalMaximal ν).ennreal_toReal
  have hMf : ∀ x, rationalMaximal ν x ≠ ⊤ := by
    obtain ⟨B,hB⟩ := (isCompact_closedBall (0:ℂ) 8).exists_bound_of_continuousOn
      (hg.continuous.sub (continuous_const (y := c))).continuousOn
    have hbnd (y : ℂ) : f y ≤ max B 0 := by
      by_cases hy : ‖y‖ ≤ 8
      · have hby := hB y (by simpa only [Metric.mem_closedBall,dist_zero_right] using hy)
        simpa [f, hy, Real.norm_eq_abs] using hby.trans (le_max_left B 0)
      · simp [f, hy]
    intro x
    exact ne_of_lt ((rationalMaximal_le_of_density_le (fun y => ENNReal.ofReal_le_ofReal (hbnd y)) x).trans_lt ENNReal.ofReal_lt_top)
  have hfnorm : eLpNorm f (3/2) volume = eLpNorm (fun x => g x-c) (3/2) (volume.restrict {x : ℂ | ‖x‖ ≤ 8}) := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict (measurableSet_le measurable_norm measurable_const)]
    simpa only [Real.norm_eq_abs] using eLpNorm_norm (fun x => g x-c)
      (hg.continuous.sub continuous_const).aestronglyMeasurable
      (p := (3/2:ℝ≥0∞)) (μ := volume.restrict {x : ℂ | ‖x‖ ≤ 8})
  have hn : eLpNorm M (3/2) volume ≤ ENNReal.ofReal K*ENNReal.ofReal (C*errorPrice b (1/100)) := by
    apply (strong_three_halves_norm hf hf0).trans
    apply mul_le_mul_right _ _
    simpa only [hfnorm] using hc
  refine ⟨fun x => ENNReal.ofReal 2*ENNReal.ofReal (M x),measurable_const.mul hM.ennreal_ofReal,?_,?_⟩
  · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply (mul_le_mul_right (lintegral_le_three_halves_norm hM.aestronglyMeasurable
      (fun _ => ENNReal.toReal_nonneg) (by simpa using hQ)) _).trans
    apply (mul_le_mul_right hn _).trans_eq
    rw [← ENNReal.ofReal_mul hK.le,← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    ring
  · intro x hx t t' ht ht4 ht' ht4'
    have ha : |signedAverage g x t-c| ≤ M x :=
      (ENNReal.ofReal_le_iff_le_toReal (hMf x)).mp (local_average_le hg.continuous c hx ht ht4)
    have hb : |signedAverage g x t'-c| ≤ M x :=
      (ENNReal.ofReal_le_iff_le_toReal (hMf x)).mp (local_average_le hg.continuous c hx ht' ht4')
    change ENNReal.ofReal _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal (M x)
    rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    apply ENNReal.ofReal_le_ofReal
    have hh := abs_sub_le (signedAverage g x t) c (signedAverage g x t')
    rw [abs_sub_comm c] at hh
    linarith
end PlanePotential

namespace AffineDensities
lemma fderiv_affine_bound {g : ℂ → ℝ} (hg : Differentiable ℝ g) (p : ℂ) (r : ℝ)
    {D : ℝ} (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) :
    ∃ B : ℝ, ∀ X, ‖fderiv ℝ (fun Y => g (p+r • Y)) X‖ ≤ B := by
  refine ⟨D*|r|,?_⟩
  intro X
  have hA : HasFDerivAt (fun Y : ℂ => p+r • Y)
      (r • ContinuousLinearMap.id ℝ ℂ) X := by
    simpa using ((hasFDerivAt_id X).const_smul r).const_add p
  have hd := (hg (p+r • X)).hasFDerivAt.comp X hA
  simp only [Function.comp_def] at hd
  rw [hd.fderiv]
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  simp only [norm_smul,Real.norm_eq_abs,ContinuousLinearMap.norm_id, mul_one]
  exact mul_le_mul_of_nonneg_right (hD _) (abs_nonneg _)
end AffineDensities

namespace CommonPrices
open DyadicHats ConeCoordinates LocalCancellation AffineDensities DirectionNeighbors Finset DiskMoments PricePieces

/-- The actual common-price value estimate, including every terminal error and
all roots. This is the third local analytic input to signed run assembly. -/
theorem value_cell_price : ∃ C : ℝ, 0 < C ∧
    ∀ {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hN : R/r+1 ≤ (N:ℝ))
    {g : ℂ → ℝ}, ContDiff ℝ 1 g → Integrable (gradient g) →
    (∀ y, gradient g y ≠ 0 → ‖y‖ ≤ R) →
    (∃ D : ℝ, ∀ y, ‖fderiv ℝ g y‖ ≤ D) → ∀ (k : ℕ) (p : ℤ × ℤ)
    {n : ℂ}, n ∈ fixedPalette.labels → ∀ Q : Set ℂ, volume Q ≤ ENNReal.ofReal 1 →
    ∃ F : ℂ → ℝ≥0∞, Measurable F ∧
      (∫⁻ X in Q, F X) ≤ ENNReal.ofReal (C*(scale r k)⁻¹*
        (rootMass (gradient g) r k (cellRoots N p)+cellPrice N r (gradient g) k (cellRoots N p))) ∧
      ∀ X, ‖X‖ ≤ 2 → ∀ t t', 0 < t → t ≤ 4 → 0 < t' → t' ≤ 4 →
        ENNReal.ofReal |signedAverage (fun Y => g (point (scale r k) p+scale r k • Y)) X t-
          signedAverage (fun Y => g (point (scale r k) p+scale r k • Y)) X t'| ≤ F X := by
  obtain ⟨C,hC,hmajor⟩ := PlanePotential.local_value_majorant
  refine ⟨4*C,by positivity,?_⟩
  intro N r R hr hR hN g hg hh hsupp hD k p n hn Q hQ
  let b := sizeErrors hr hh k (point (scale r k) p) (cellRoots N p) n
  have hg' : ContDiff ℝ 1 (fun Y => g (point (scale r k) p+scale r k • Y)) := hg.comp (by fun_prop)
  obtain ⟨D,hD⟩ := hD
  have hD' := fderiv_affine_bound (hg.differentiable one_ne_zero) (point (scale r k) p) (scale r k) hD
  have hd : ∀ᵐ X, ‖X‖ ≤ 8 →
      gradient (fun Y => g (point (scale r k) p+scale r k • Y)) X = ∑ i, (b i).density X := by
    filter_upwards with X hX
    exact (sizeErrors_gradient hr hR hN (hg.differentiable one_ne_zero) hh hsupp k p
      (fixedPalette.unit n hn) X (by linarith)).symm
  obtain ⟨F,hFm,hFi,hFb⟩ := hmajor b hg' hD' hd Q hQ
  refine ⟨F,hFm,?_,hFb⟩
  apply hFi.trans
  apply ENNReal.ofReal_le_ofReal
  have hb := sizeErrors_price hr hR hN hh hsupp k (point (scale r k) p) (cellRoots N p) hn
  have hDp : 0 ≤ cellPrice N r (gradient g) k (cellRoots N p) :=
    sum_nonneg (fun q _ => rootPrice_nonneg hr hR hN hh hsupp k q)
  change errorPrice b (1/100) ≤ _ at hb
  have hrk := scale_pos hr k
  nlinarith [mul_le_mul_of_nonneg_left hb hC.le,inv_nonneg.mpr hrk.le,
    mul_nonneg (inv_nonneg.mpr hrk.le) hDp]
end CommonPrices

namespace PhysicalCells
open MeasureTheory Set

def unitCell : Set ℂ := {X | X.re ∈ Ico (0:ℝ) 1 ∧ X.im ∈ Ico (0:ℝ) 1}
def toUnit (p : ℂ) (r : ℝ) (y : ℂ) : ℂ := r⁻¹ • (y-p)
def cell (p : ℂ) (r : ℝ) : Set ℂ := toUnit p r ⁻¹' unitCell

lemma unitCell_measurable : MeasurableSet unitCell :=
  (Complex.measurable_re measurableSet_Ico).inter (Complex.measurable_im measurableSet_Ico)
lemma toUnit_continuous (p : ℂ) (r : ℝ) : Continuous (toUnit p r) := by unfold toUnit; fun_prop
lemma cell_measurable (p : ℂ) (r : ℝ) : MeasurableSet (cell p r) :=
  (toUnit_continuous p r).measurable unitCell_measurable
lemma volume_unitCell : volume unitCell = 1 := by
  have he := Complex.volume_preserving_equiv_real_prod.measure_preimage
    (s := Ico (0:ℝ) 1 ×ˢ Ico (0:ℝ) 1) (measurableSet_Ico.prod measurableSet_Ico).nullMeasurableSet
  change volume unitCell = _ at he
  rw [he]
  change (volume.prod volume) (Ico (0:ℝ) 1 ×ˢ Ico (0:ℝ) 1) = 1
  rw [Measure.prod_prod]
  norm_num
lemma norm_unitCell {X : ℂ} (hX : X ∈ unitCell) : ‖X‖ ≤ 2 := by
  have h := Complex.norm_le_abs_re_add_abs_im X
  rw [abs_of_nonneg hX.1.1,abs_of_nonneg hX.2.1] at h
  linarith [hX.1.2,hX.2.2]
lemma toUnit_affine (p : ℂ) {r : ℝ} (hr : r ≠ 0) (X : ℂ) : toUnit p r (p+r • X) = X := by
  simp [toUnit,hr]
lemma affine_toUnit (p : ℂ) {r : ℝ} (hr : r ≠ 0) (y : ℂ) : p+r • toUnit p r y = y := by
  simp [toUnit,hr]

lemma lintegral_smul (F : ℂ → ℝ≥0∞) {r : ℝ} (hr : r ≠ 0) :
    (∫⁻ X : ℂ, F (r • X)) = ENNReal.ofReal ((r^2)⁻¹)*(∫⁻ y, F y) := by
  have he := (lintegral_map_equiv (μ := volume) F
    (Homeomorph.smul (isUnit_iff_ne_zero.mpr hr).unit).toMeasurableEquiv).symm
  change (∫⁻ X : ℂ, F (r • X)) = ∫⁻ y, F y ∂Measure.map (fun X : ℂ => r • X) volume at he
  rw [he,Measure.map_addHaar_smul volume hr,lintegral_smul_measure]
  simp only [Complex.finrank_real_complex,abs_of_nonneg (inv_nonneg.mpr (sq_nonneg r)),smul_eq_mul]

lemma lintegral_toUnit (F : ℂ → ℝ≥0∞) (p : ℂ) {r : ℝ} (hr : r ≠ 0) :
    (∫⁻ y : ℂ, F (toUnit p r y)) = ENNReal.ofReal (r^2)*(∫⁻ X, F X) := by
  calc
    (∫⁻ y : ℂ, F (r⁻¹ • (y-p))) = ∫⁻ y : ℂ, F (r⁻¹ • y) :=
      lintegral_sub_right_eq_self (μ := (volume : Measure ℂ)) (fun y : ℂ => F (r⁻¹ • y)) p
    _ = _ := by rw [lintegral_smul _ (inv_ne_zero hr),inv_pow,inv_inv]

/-- Exact physical-space change of variables, with the two-dimensional volume
factor and no integrability or measurability assumptions on the majorant. -/
lemma lintegral_cell (F : ℂ → ℝ≥0∞) (p : ℂ) {r : ℝ} (hr : r ≠ 0) :
    (∫⁻ y in cell p r, F y) = ENNReal.ofReal (r^2)*∫⁻ X in unitCell, F (p+r • X) := by
  rw [← lintegral_indicator (cell_measurable p r),← lintegral_indicator unitCell_measurable]
  have he (y : ℂ) : (cell p r).indicator F y =
      unitCell.indicator (fun X => F (p+r • X)) (toUnit p r y) := by
    by_cases hy : y ∈ cell p r
    · rw [Set.indicator_of_mem hy,Set.indicator_of_mem (show toUnit p r y ∈ unitCell from hy),affine_toUnit p hr]
    · rw [Set.indicator_of_notMem hy,Set.indicator_of_notMem (show toUnit p r y ∉ unitCell from hy)]
  simp_rw [he]
  exact lintegral_toUnit _ p hr

lemma cell_majorant {F : ℂ → ℝ≥0∞} (p : ℂ) {r : ℝ} (hr : r ≠ 0) :
    (∫⁻ y in cell p r, F (toUnit p r y)) = ENNReal.ofReal (r^2)*∫⁻ X in unitCell, F X := by
  rw [lintegral_cell _ p hr]
  simp only [toUnit_affine p hr]
end PhysicalCells

namespace DiskMoments
lemma signedAverage_affine (g : ℂ → ℝ) (p X : ℂ) {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    signedAverage (fun Y => g (p+r • Y)) X t = signedAverage g (p+r • X) (r*t) := by
  rw [signedAverage_fixedDomain _ _ ht,signedAverage_fixedDomain _ _ (mul_pos hr ht)]
  congr 1
  apply setIntegral_congr_fun measurableSet_ball
  intro Z _
  change g (p+r • (X+t • Z)) = g (p+r • X+(r*t) • Z)
  congr 1
  rw [smul_add,smul_smul]
  abel

lemma gradient_signedAverage {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) {D : ℝ}
    (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) (x : ℂ) {t : ℝ} (ht : 0 < t) :
    gradient (fun y => signedAverage g y t) x =
      (Real.pi*t^2)⁻¹ • ∫ y in Metric.ball x t, gradient g y := by
  have hi : IntegrableOn (fun z : ℂ => fderiv ℝ g (x+t • z)) (Metric.ball 0 1) :=
    (((hg.continuous_fderiv one_ne_zero).comp (by fun_prop)).continuousOn.integrableOn_compact
      (isCompact_closedBall (0:ℂ) 1)).mono_set Metric.ball_subset_closedBall
  rw [gradient,(hasFDerivAt_signedAverage hg hD x ht).fderiv,map_smul]
  have he := (InnerProductSpace.toDual ℝ ℂ).symm.toContinuousLinearMap.integral_comp_comm hi
  change (∫ z in Metric.ball (0:ℂ) 1, (InnerProductSpace.toDual ℝ ℂ).symm (fderiv ℝ g (x+t • z))) =
    (InnerProductSpace.toDual ℝ ℂ).symm (∫ z in Metric.ball (0:ℂ) 1, fderiv ℝ g (x+t • z)) at he
  rw [← he]
  change (1/Real.pi) • (∫ z in Metric.ball (0:ℂ) 1, gradient g (x+t • z)) = _
  rw [integral_scale_ball (fun z => gradient g (x+z)) ht,integral_translate_ball,smul_smul]
  congr 1
  ring

lemma gradient_average_affine {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) {D : ℝ}
    (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) (p X : ℂ) {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    gradient (fun Y => signedAverage (fun Z => g (p+r • Z)) Y t) X =
      r • gradient (fun y => signedAverage g y (r*t)) (p+r • X) := by
  have he : (fun Y => signedAverage (fun Z => g (p+r • Z)) Y t) =
      (fun Y => signedAverage g (p+r • Y) (r*t)) := by
    funext Y
    exact signedAverage_affine g p Y hr ht
  rw [he]
  exact AffineDensities.gradient_affine (fun y =>
    (hasFDerivAt_signedAverage hg hD y (mul_pos hr ht)).differentiableAt) p r X

def PhysicalNeighborhoodRadius (g : ℂ → ℝ) (r : ℝ) (x : ℂ) (t : ℝ) : Prop :=
  t ∈ Icc r (2*r) ∧ ∀ s, 0 < s → |s-t| ≤ r/4 → signedAverage g x s ≤ signedAverage g x t

def PhysicalEndpointRadius (g : ℂ → ℝ) (r : ℝ) (x : ℂ) (t : ℝ) : Prop :=
  t ∈ Icc r (2*r) ∧ (t = r ∨ t = 2*r ∨ ∀ s ∈ Icc r (2*r), signedAverage g x s ≤ signedAverage g x t)

lemma neighborhoodRadius_affine {g : ℂ → ℝ} (p X : ℂ) {r t : ℝ} (hr : 0 < r)
    (ht : PhysicalNeighborhoodRadius g r (p+r • X) (r*t)) :
    NeighborhoodRadius (fun Y => g (p+r • Y)) X t := by
  have ht1 : 1 ≤ t := (le_of_mul_le_mul_left (by simpa only [mul_one] using ht.1.1) hr)
  have ht2 : t ≤ 2 := (le_of_mul_le_mul_left (by simpa only [mul_comm 2 r] using ht.1.2) hr)
  refine ⟨⟨ht1,ht2⟩,?_⟩
  intro s hs habs
  rw [signedAverage_affine _ _ _ hr hs,signedAverage_affine _ _ _ hr (by linarith)]
  apply ht.2 (r*s) (mul_pos hr hs)
  rw [← mul_sub,abs_mul,abs_of_pos hr]
  nlinarith

lemma endpointRadius_affine {g : ℂ → ℝ} (p X : ℂ) {r t : ℝ} (hr : 0 < r)
    (ht : PhysicalEndpointRadius g r (p+r • X) (r*t)) :
    EndpointRadius (fun Y => g (p+r • Y)) X t := by
  have ht1 : 1 ≤ t := (le_of_mul_le_mul_left (by simpa only [mul_one] using ht.1.1) hr)
  have ht2 : t ≤ 2 := (le_of_mul_le_mul_left (by simpa only [mul_comm 2 r] using ht.1.2) hr)
  refine ⟨⟨ht1,ht2⟩,?_⟩
  rcases ht.2 with he | he | he
  · left
    nlinarith
  · right; left
    nlinarith
  · right; right
    intro s hs
    rw [signedAverage_affine _ _ _ hr (by linarith [hs.1]),signedAverage_affine _ _ _ hr (by linarith)]
    exact he (r*s) ⟨by nlinarith [hs.1],by nlinarith [hs.2]⟩
end DiskMoments

end SignedDisk

end

end OAI
