import Mathlib
import OAI.Combinatorics.StripMass.DensityExhaustion

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators
open Set MeasureTheory Filter
lemma isOpen_coordinateBox {ι : Type*} [Fintype ι] {I : Set ℝ} (hI : IsOpen I) :
    IsOpen (coordinateBox ι I) := by
  have he : coordinateBox ι I = ⋂ i : ι, (fun x : ι → ℝ => x i) ⁻¹' I := by
    ext x
    simp [coordinateBox]
  rw [he]
  exact isOpen_iInter_of_finite fun i : ι => hI.preimage (continuous_apply i)

lemma isOpen_cutoffEvent (N : ℕ) (R : ℝ) : IsOpen (cutoffEvent N R) :=
  isOpen_coordinateBox isOpen_Iio

lemma laguerreDomain_cutoff_nonempty (N : ℕ) {R : ℝ} (hR : 0 < R) :
    (laguerreDomain N ∩ cutoffEvent N R).Nonempty := by
  obtain ⟨v, hvm, hv⟩ := orderedDomain_nonempty N
  refine ⟨fun i => R * v i, ⟨?_, ?_⟩, ?_⟩
  · intro i j hij
    exact mul_lt_mul_of_pos_left (hvm hij) hR
  · intro i
    exact mul_pos hR (hv i).1
  · intro i
    simpa using mul_lt_mul_of_pos_left (hv i).2 hR

 

theorem laguerreLaw_cutoff_pos (N : ℕ) {a R : ℝ} (ha : 0 < a) (hR : 0 < R) :
    0 < (laguerreLaw N a).real (cutoffEvent N R) := by
  rw [laguerreLaw_measureReal N ha (measurableSet_cutoffEvent N R)]
  apply div_pos ?_ (laguerreNormalizer_pos N ha)
  let S : Set (Fin N → ℝ) := laguerreDomain N ∩ cutoffEvent N R
  have hS : IsOpen S := (isOpen_laguerreDomain N).inter (isOpen_cutoffEvent N R)
  have hi : IntegrableOn (laguerreDensity N a) S :=
    (integrableOn_laguerreDensity N ha).mono_set inter_subset_left
  have hpos : 0 ≤ᵐ[volume.restrict S] laguerreDensity N a := by
    filter_upwards [ae_restrict_mem hS.measurableSet] with r hr
    exact (laguerreDensity_pos a hr.1).le
  apply (integral_pos_iff_support_of_nonneg_ae hpos hi).2
  calc 0 < volume S := hS.measure_pos volume (laguerreDomain_cutoff_nonempty N hR)
       _ = (volume.restrict S) S := (Measure.restrict_apply_self _ _).symm
       _ ≤ (volume.restrict S) (Function.support (laguerreDensity N a)) :=
         measure_mono (fun r hr => (laguerreDensity_pos a hr.1).ne')

 

theorem laguerreLaw_conditioned_antitone {N : ℕ} {a R : ℝ} (ha : 0 < a) (hR : 0 < R)
    (f : (Fin N → ℝ) → ℝ)
    (hfc : ContinuousOn f (coordinateBox (Fin N) (Ioi 0)))
    (hfm : AntitoneOn f (coordinateBox (Fin N) (Ioi 0)))
    (hf : Integrable f (laguerreLaw N a)) :
    (∫ r, f r ∂laguerreLaw N a) ≤
      (∫ r in cutoffEvent N R, f r ∂laguerreLaw N a) /
        (laguerreLaw N a).real (cutoffEvent N R) := by
  exact (le_div_iff₀ (laguerreLaw_cutoff_pos N ha hR)).2
    (laguerreLaw_cutoff_covariance ha R f hfc hfm hf)

 

def positiveLaw (N : ℕ) : Measure (Fin N → ℝ) :=
  (ENNReal.ofReal (normalizer N))⁻¹ •
    (volume.restrict (orderedDomain N)).withDensity (fun y => ENNReal.ofReal (density N y))

theorem positiveLaw_isProbabilityMeasure (N : ℕ) : IsProbabilityMeasure (positiveLaw N) := by
  refine ⟨?_⟩
  rw [positiveLaw, Measure.smul_apply, smul_eq_mul, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal (integrableOn_density N)]
  · exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr (normalizer_pos N)).ne' ENNReal.ofReal_ne_top
  · filter_upwards [ae_restrict_mem (isOpen_orderedDomain N).measurableSet] with y hy
    exact (density_pos hy).le

theorem ae_positiveLaw_orderedDomain (N : ℕ) : ∀ᵐ y ∂positiveLaw N, y ∈ orderedDomain N := by
  apply Measure.ae_smul_measure
  apply (ae_withDensity_iff (measurable_density N).ennreal_ofReal).2
  filter_upwards [ae_restrict_mem (isOpen_orderedDomain N).measurableSet] with y hy
  exact fun _ => hy

theorem integral_positiveLaw (N : ℕ) (f : (Fin N → ℝ) → ℝ) :
    (∫ y, f y ∂positiveLaw N) = expectation N f := by
  rw [positiveLaw, integral_smul_measure,
    integral_withDensity_eq_integral_toReal_smul (measurable_density N).ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofReal (normalizer_pos N).le,
    smul_eq_mul, expectation, div_eq_mul_inv]
  rw [mul_comm]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (isOpen_orderedDomain N).measurableSet] with y hy
  rw [ENNReal.toReal_ofReal (density_pos hy).le, mul_comm]

theorem integrable_positiveLaw_iff {N : ℕ} {f : (Fin N → ℝ) → ℝ} :
    Integrable f (positiveLaw N) ↔
      IntegrableOn (fun y => f y * density N y) (orderedDomain N) := by
  rw [positiveLaw, integrable_smul_measure (by simp) (by simpa using normalizer_pos N),
    integrable_withDensity_iff_integrable_smul' (measurable_density N).ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integrable_congr
  filter_upwards [ae_restrict_mem (isOpen_orderedDomain N).measurableSet] with y hy
  simp [smul_eq_mul, ENNReal.toReal_ofReal (density_pos hy).le, mul_comm]

theorem positiveLaw_covariance {N : ℕ} (f g : (Fin N → ℝ) → ℝ)
    (hfc : ContinuousOn f (coordinateBox (Fin N) (Ioo 0 1)))
    (hgc : ContinuousOn g (coordinateBox (Fin N) (Ioo 0 1)))
    (hfm : MonotoneOn f (coordinateBox (Fin N) (Ioo 0 1)))
    (hgm : MonotoneOn g (coordinateBox (Fin N) (Ioo 0 1)))
    (hf : Integrable f (positiveLaw N)) (hg : Integrable g (positiveLaw N))
    (hfg : Integrable (fun r => f r * g r) (positiveLaw N)) :
    (∫ r, f r ∂positiveLaw N) * (∫ r, g r ∂positiveLaw N) ≤
      ∫ r, f r * g r ∂positiveLaw N := by
  simpa only [integral_positiveLaw] using
    expectation_covariance f g hfc hgc hfm hgm (integrable_positiveLaw_iff.1 hf)
      (integrable_positiveLaw_iff.1 hg) (integrable_positiveLaw_iff.1 hfg)

theorem positiveLaw_covariance_antitone {N : ℕ} (f g : (Fin N → ℝ) → ℝ)
    (hfc : ContinuousOn f (coordinateBox (Fin N) (Ioo 0 1)))
    (hgc : ContinuousOn g (coordinateBox (Fin N) (Ioo 0 1)))
    (hfm : AntitoneOn f (coordinateBox (Fin N) (Ioo 0 1)))
    (hgm : AntitoneOn g (coordinateBox (Fin N) (Ioo 0 1)))
    (hf : Integrable f (positiveLaw N)) (hg : Integrable g (positiveLaw N))
    (hfg : Integrable (fun r => f r * g r) (positiveLaw N)) :
    (∫ r, f r ∂positiveLaw N) * (∫ r, g r ∂positiveLaw N) ≤
      ∫ r, f r * g r ∂positiveLaw N := by
  have h := positiveLaw_covariance (fun r => -f r) (fun r => -g r) hfc.neg hgc.neg
    (fun _ hx _ hy hxy => neg_le_neg (hfm hx hy hxy))
    (fun _ hx _ hy hxy => neg_le_neg (hgm hx hy hxy)) hf.neg hg.neg (by simpa using hfg)
  simpa only [integral_neg, neg_mul_neg] using h

theorem positiveLaw_cutoff_covariance {N : ℕ} (R : ℝ) (f : (Fin N → ℝ) → ℝ)
    (hfc : ContinuousOn f (coordinateBox (Fin N) (Ioo 0 1)))
    (hfm : AntitoneOn f (coordinateBox (Fin N) (Ioo 0 1)))
    (hf : Integrable f (positiveLaw N)) :
    (∫ r, f r ∂positiveLaw N) * (positiveLaw N).real (cutoffEvent N R) ≤
      ∫ r in cutoffEvent N R, f r ∂positiveLaw N := by
  let := positiveLaw_isProbabilityMeasure N
  apply le_of_tendsto_of_tendsto
    (tendsto_const_nhds.mul (cutoffProduct_integral_tendsto (positiveLaw N) R))
    (cutoffProduct_weighted_tendsto (positiveLaw N) R f hf)
  apply Eventually.of_forall
  intro n
  exact positiveLaw_covariance_antitone f (cutoffProduct N n R) hfc
    (continuous_cutoffProduct N n R).continuousOn hfm
    ((antitone_cutoffProduct N n R).antitoneOn _) hf (cutoffProduct_integrable _ n R)
    (hf.mul_bdd (continuous_cutoffProduct N n R).aestronglyMeasurable
      (Eventually.of_forall (cutoffProduct_norm_le N n R)))

theorem positiveLaw_integrable_inverseQuarterSum (N : ℕ) :
    Integrable (fun y : Fin N → ℝ => (∑ i, (y i)⁻¹) ^ (1 / 4 : ℝ)) (positiveLaw N) :=
  integrable_positiveLaw_iff.2 (integrableOn_inverseQuarterSum_density N)

theorem positiveLaw_integrable_inverseQuarterCoordinate {N : ℕ} (i : Fin N) :
    Integrable (fun y : Fin N → ℝ => (y i) ^ (-(1 / 4 : ℝ))) (positiveLaw N) :=
  integrable_positiveLaw_iff.2 (integrableOn_inverseQuarterCoordinate_density N i)



theorem positiveLaw_measureReal (N : ℕ)
    {s : Set (Fin N → ℝ)} (hs : MeasurableSet s) :
    (positiveLaw N).real s = (∫ r in orderedDomain N ∩ s, density N r) / normalizer N := by
  let := positiveLaw_isProbabilityMeasure N
  rw [← integral_indicator_one hs, integral_positiveLaw N]
  unfold expectation
  simp_rw [← Set.indicator_mul_left, Pi.one_apply, one_mul]
  rw [setIntegral_indicator hs]

lemma orderedDomain_cutoff_nonempty (N : ℕ) {R : ℝ} (hR : 0 < R) :
    (orderedDomain N ∩ cutoffEvent N R).Nonempty := by
  obtain ⟨v, hvm, hv⟩ := orderedDomain_nonempty N
  have ht : 0 < min R 1 := lt_min hR (by norm_num)
  refine ⟨fun i => min R 1 * v i, ⟨?_, ?_⟩, ?_⟩
  · intro i j hij
    exact mul_lt_mul_of_pos_left (hvm hij) ht
  · intro i
    have hi : min R 1 * v i < min R 1 := by simpa using mul_lt_mul_of_pos_left (hv i).2 ht
    exact ⟨mul_pos ht (hv i).1, hi.trans_le (min_le_right _ _)⟩
  · intro i
    have hi : min R 1 * v i < min R 1 := by simpa using mul_lt_mul_of_pos_left (hv i).2 ht
    exact hi.trans_le (min_le_left _ _)

theorem positiveLaw_cutoff_pos (N : ℕ) {R : ℝ} (hR : 0 < R) :
    0 < (positiveLaw N).real (cutoffEvent N R) := by
  rw [positiveLaw_measureReal N (measurableSet_cutoffEvent N R)]
  apply div_pos ?_ (normalizer_pos N)
  let S : Set (Fin N → ℝ) := orderedDomain N ∩ cutoffEvent N R
  have hS : IsOpen S := (isOpen_orderedDomain N).inter (isOpen_cutoffEvent N R)
  have hi : IntegrableOn (density N) S := (integrableOn_density N).mono_set inter_subset_left
  have hpos : 0 ≤ᵐ[volume.restrict S] density N := by
    filter_upwards [ae_restrict_mem hS.measurableSet] with r hr
    exact (density_pos hr.1).le
  apply (integral_pos_iff_support_of_nonneg_ae hpos hi).2
  calc 0 < volume S := hS.measure_pos volume (orderedDomain_cutoff_nonempty N hR)
       _ = (volume.restrict S) S := (Measure.restrict_apply_self _ _).symm
       _ ≤ (volume.restrict S) (Function.support (density N)) :=
         measure_mono (fun _ hr => (density_pos hr.1).ne')

 

theorem positiveLaw_conditioned_antitone {N : ℕ} {R : ℝ} (hR : 0 < R)
    (f : (Fin N → ℝ) → ℝ)
    (hfc : ContinuousOn f (coordinateBox (Fin N) (Ioo 0 1)))
    (hfm : AntitoneOn f (coordinateBox (Fin N) (Ioo 0 1)))
    (hf : Integrable f (positiveLaw N)) :
    (∫ r, f r ∂positiveLaw N) ≤
      (∫ r in cutoffEvent N R, f r ∂positiveLaw N) /
        (positiveLaw N).real (cutoffEvent N R) := by
  exact (le_div_iff₀ (positiveLaw_cutoff_pos N hR)).2
    (positiveLaw_cutoff_covariance R f hfc hfm hf)

lemma continuousOn_inverse_coordinate {ι : Type*} [Fintype ι] (i : ι) (p : ℝ) :
    ContinuousOn (fun r : ι → ℝ => (r i) ^ (-p)) (coordinateBox ι (Ioi 0)) :=
  (continuous_apply i).continuousOn.rpow_const (fun _ hr => Or.inl (hr i).ne')

lemma antitoneOn_inverse_coordinate {ι : Type*} [Fintype ι] (i : ι) {p : ℝ}
    (hp : 0 ≤ p) :
    AntitoneOn (fun r : ι → ℝ => (r i) ^ (-p)) (coordinateBox ι (Ioi 0)) := by
  intro x hx y hy hxy
  exact Real.rpow_le_rpow_of_nonpos (hx i) (hxy i) (neg_nonpos.mpr hp)

lemma continuousOn_inverseQuarterSum {ι : Type*} [Fintype ι] :
    ContinuousOn (fun r : ι → ℝ => (∑ i, (r i)⁻¹) ^ (1 / 4 : ℝ))
      (coordinateBox ι (Ioi 0)) := by
  have hsum : ContinuousOn (fun r : ι → ℝ => ∑ i, (r i)⁻¹) (coordinateBox ι (Ioi 0)) := by
    exact continuousOn_finsetSum _ fun i _ =>
      (continuous_apply i).continuousOn.inv₀ (fun _ hr => (hr i).ne')
  exact hsum.rpow_const (fun _ _ => Or.inr (by norm_num))

lemma antitoneOn_inverseQuarterSum {ι : Type*} [Fintype ι] :
    AntitoneOn (fun r : ι → ℝ => (∑ i, (r i)⁻¹) ^ (1 / 4 : ℝ))
      (coordinateBox ι (Ioi 0)) := by
  intro x hx y hy hxy
  apply Real.rpow_le_rpow (Finset.sum_nonneg (fun i _ => inv_nonneg.mpr (hy i).le)) ?_ (by norm_num)
  exact Finset.sum_le_sum fun i _ => inv_anti₀ (hx i) (hxy i)

theorem positiveLaw_cutoff_inverseQuarterSum {N : ℕ} {R : ℝ} (hR : 0 < R) :
    (∫ y : Fin N → ℝ, (∑ i, (y i)⁻¹) ^ (1 / 4 : ℝ) ∂positiveLaw N) ≤
      (∫ y in cutoffEvent N R, (∑ i, (y i)⁻¹) ^ (1 / 4 : ℝ) ∂positiveLaw N) /
        (positiveLaw N).real (cutoffEvent N R) := by
  exact positiveLaw_conditioned_antitone hR _
    (continuousOn_inverseQuarterSum.mono (fun _ hx i => (hx i).1))
    (antitoneOn_inverseQuarterSum.mono (fun _ hx i => (hx i).1))
    (positiveLaw_integrable_inverseQuarterSum N)

theorem laguerreLaw_cutoff_inverseQuarterSum {N : ℕ} {a R : ℝ}
    (ha : 1 / 4 < a) (hR : 0 < R) :
    (∫ r : Fin N → ℝ, (∑ i, (r i)⁻¹) ^ (1 / 4 : ℝ) ∂laguerreLaw N a) ≤
      (∫ r in cutoffEvent N R, (∑ i, (r i)⁻¹) ^ (1 / 4 : ℝ) ∂laguerreLaw N a) /
        (laguerreLaw N a).real (cutoffEvent N R) := by
  exact laguerreLaw_conditioned_antitone (by linarith) hR _
    continuousOn_inverseQuarterSum antitoneOn_inverseQuarterSum
    (integrable_laguerreLaw_inverseQuarterSum ha)

theorem laguerreLaw_cutoff_inverse_coordinate {N : ℕ} {a R p : ℝ} (ha : 0 < a)
    (hR : 0 < R) (i : Fin N) (hp : 0 ≤ p) (hpD : p < laguerreDimension a (i.val + 1)) :
    (∫ r, (r i) ^ (-p) ∂laguerreLaw N a) ≤
      (∫ r in cutoffEvent N R, (r i) ^ (-p) ∂laguerreLaw N a) /
        (laguerreLaw N a).real (cutoffEvent N R) := by
  exact laguerreLaw_conditioned_antitone ha hR _
    (continuousOn_inverse_coordinate i p) (antitoneOn_inverse_coordinate i hp)
    (integrable_laguerreLaw_inverse_coordinate_full ha i hpD)

lemma mem_cutoffEvent_iff_last {n : ℕ} {r : Fin (n + 1) → ℝ} (hr : Monotone r) (R : ℝ) :
    r ∈ cutoffEvent (n + 1) R ↔ r (Fin.last n) < R := by
  constructor
  · exact fun h => h (Fin.last n)
  · intro h i
    exact (hr (Fin.le_last i)).trans_lt h

end

noncomputable section
open scoped BigOperators
open Set MeasureTheory

 

theorem omega_antitoneOn : AntitoneOn omega (Ioi 0) := by
  intro x hx y hy hxy
  change 0 < x at hx
  change 0 < y at hy
  apply mul_le_mul_of_nonneg_left ?_ (by norm_num)
  apply Real.sqrt_le_sqrt
  apply sub_le_sub_right
  apply Real.sqrt_le_sqrt
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * y) (by positivity : 0 < 2 * x)).2
  nlinarith

 
def mobiusCoordinate (z : ℝ) : ℝ := 2 * z / (1 + z)

lemma mobiusCoordinate_mem {z : ℝ} (hz : z ∈ Ioo 0 1) :
    mobiusCoordinate z ∈ Ioo 0 1 := by
  have hd : 0 < 1 + z := by linarith [hz.1]
  exact ⟨div_pos (by linarith [hz.1]) hd, (div_lt_one hd).2 (by linarith [hz.2])⟩

lemma mobiusCoordinate_strictMonoOn : StrictMonoOn mobiusCoordinate (Ioi 0) := by
  intro x hx y hy hxy
  change 0 < x at hx
  change 0 < y at hy
  apply (div_lt_div_iff₀ (by linarith : 0 < 1 + x) (by linarith : 0 < 1 + y)).2
  nlinarith

lemma pairKernel_mobius {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    pairKernel (mobiusCoordinate x) (mobiusCoordinate y) =
      2 * pairKernel x y / ((1 + x) * (1 + y) * (1 + 2 * x * y / (x + y))) := by
  have hxy : x + y ≠ 0 := ne_of_gt (add_pos hx hy)
  have hx1 : 1 + x ≠ 0 := by positivity
  have hy1 : 1 + y ≠ 0 := by positivity
  have ht : x + y + 2 * x * y ≠ 0 := by positivity
  unfold pairKernel mobiusCoordinate
  field_simp
  ring

lemma harmonicPair_monotone {x x' y y' : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxx' : x ≤ x') (hyy' : y ≤ y') :
    2 * x * y / (x + y) ≤ 2 * x' * y' / (x' + y') := by
  have hx' := hx.trans_le hxx'
  have hy' := hy.trans_le hyy'
  calc
    2 * x * y / (x + y) ≤ 2 * x' * y / (x' + y) := by
      apply (div_le_div_iff₀ (add_pos hx hy) (add_pos hx' hy)).2
      nlinarith [mul_nonneg (sub_nonneg.mpr hxx') (sq_nonneg y)]
    _ ≤ 2 * x' * y' / (x' + y') := by
      apply (div_le_div_iff₀ (add_pos hx' hy) (add_pos hx' hy')).2
      nlinarith [mul_nonneg (sub_nonneg.mpr hyy') (sq_nonneg x')]

 
def mobiusPairFactor (x y : ℝ) : ℝ := (1 + 2 * x * y / (x + y))⁻¹

lemma mobiusPairFactor_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    0 < mobiusPairFactor x y := by unfold mobiusPairFactor; positivity

lemma mobiusPairFactor_antitone {x x' y y' : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxx' : x ≤ x') (hyy' : y ≤ y') :
    mobiusPairFactor x' y' ≤ mobiusPairFactor x y := by
  exact inv_anti₀ (by positivity : 0 < 1 + 2 * x * y / (x + y))
    (by linarith [harmonicPair_monotone hx hy hxx' hyy'])

lemma exponential_over_power_antitone {m β : ℝ} (hm : 0 ≤ m) (hb : β ≤ m / 2) :
    AntitoneOn (fun x : ℝ => Real.exp (β * x - m * Real.log (1 + x))) (Ioo 0 1) := by
  have hd (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt (fun x : ℝ => β * x - m * Real.log (1 + x)) (β - m / (1 + x)) x := by
    have hd0 : (1 : ℝ) + id x ≠ 0 := by change 1 + x ≠ 0; linarith [hx.1]
    apply (((hasDerivAt_id x).const_mul β).sub
      ((((hasDerivAt_id x).const_add 1).log hd0).const_mul m)).congr_deriv
    simp only [id_eq, mul_one, div_eq_mul_inv, one_mul]
  have hder (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : β - m / (1 + x) ≤ 0 := by
    have : m / 2 ≤ m / (1 + x) := div_le_div_of_nonneg_left hm (by linarith [hx.1]) (by linarith [hx.2])
    linarith
  have hlog : AntitoneOn (fun x : ℝ => β * x - m * Real.log (1 + x)) (Ioo 0 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioo (0 : ℝ) 1)
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hd x (by simpa only [interior_Ioo] using hx)).hasDerivWithinAt)
      (fun x hx => hder x (by simpa only [interior_Ioo] using hx))
  intro x hx y hy hxy
  exact Real.exp_le_exp.mpr (hlog hx hy hxy)

lemma exponential_over_natPower_eq (k : ℕ) (β : ℝ) {x : ℝ} (hx : 0 < x) :
    Real.exp (β * x - (k : ℝ) * Real.log (1 + x)) = Real.exp (β * x) / (1 + x) ^ k := by
  rw [Real.exp_sub, mul_comm (k : ℝ), ← Real.rpow_def_of_pos (by linarith : 0 < 1 + x),
    Real.rpow_natCast]

 
def lowerLikelihoodWeight (N : ℕ) (β z : ℝ) : ℝ :=
  omega (mobiusCoordinate z) * (Real.exp (β * z) / (1 + z) ^ (N + 1))

lemma lowerLikelihoodWeight_pos (N : ℕ) (β : ℝ) {z : ℝ} (hz : z ∈ Ioo 0 1) :
    0 < lowerLikelihoodWeight N β z := by
  have hz0 := hz.1
  exact mul_pos (omega_pos (mobiusCoordinate_mem hz)) (by positivity)

lemma lowerLikelihoodWeight_antitone (N : ℕ) {β : ℝ} (hb : β ≤ (N + 1 : ℝ) / 2) :
    AntitoneOn (lowerLikelihoodWeight N β) (Ioo 0 1) := by
  intro x hx y hy hxy
  have hω : omega (mobiusCoordinate y) ≤ omega (mobiusCoordinate x) :=
    omega_antitoneOn (mobiusCoordinate_mem hx).1 (mobiusCoordinate_mem hy).1
      (mobiusCoordinate_strictMonoOn.monotoneOn hx.1 hy.1 hxy)
  have he := exponential_over_power_antitone (by positivity : 0 ≤ (N + 1 : ℝ)) hb hx hy hxy
  simp only [← Nat.cast_add_one, exponential_over_natPower_eq (N + 1) β hx.1,
    exponential_over_natPower_eq (N + 1) β hy.1] at he
  have hy0 := hy.1
  exact mul_le_mul hω he (by positivity) (omega_nonneg _)

 

def lowerLikelihood (N : ℕ) (β : ℝ) (z : Fin N → ℝ) : ℝ :=
  (∏ i, lowerLikelihoodWeight N β (z i)) *
    ∏ i, ∏ j ∈ Finset.univ.filter (i < ·), mobiusPairFactor (z i) (z j)

lemma lowerLikelihood_pos (N : ℕ) (β : ℝ) {z : Fin N → ℝ}
    (hz : z ∈ coordinateBox (Fin N) (Ioo 0 1)) : 0 < lowerLikelihood N β z := by
  apply mul_pos
  · exact Finset.prod_pos fun i _ => lowerLikelihoodWeight_pos N β (hz i)
  · exact Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => mobiusPairFactor_pos (hz i).1 (hz j).1

theorem lowerLikelihood_antitone (N : ℕ) {β : ℝ} (hb : β ≤ (N + 1 : ℝ) / 2) :
    AntitoneOn (lowerLikelihood N β) (coordinateBox (Fin N) (Ioo 0 1)) := by
  intro x hx y hy hxy
  have hw : (∏ i, lowerLikelihoodWeight N β (y i)) ≤ ∏ i, lowerLikelihoodWeight N β (x i) :=
    Finset.prod_le_prod₀ (fun i _ => (lowerLikelihoodWeight_pos N β (hy i)).le)
      (fun i _ => lowerLikelihoodWeight_antitone N hb (hx i) (hy i) (hxy i))
  have hp : (∏ i, ∏ j ∈ Finset.univ.filter (i < ·), mobiusPairFactor (y i) (y j)) ≤
      ∏ i, ∏ j ∈ Finset.univ.filter (i < ·), mobiusPairFactor (x i) (x j) := by
    apply Finset.prod_le_prod₀
    · exact fun i _ => Finset.prod_nonneg fun j _ => (mobiusPairFactor_pos (hy i).1 (hy j).1).le
    · intro i _
      exact Finset.prod_le_prod₀ (fun j _ => (mobiusPairFactor_pos (hy i).1 (hy j).1).le)
        (fun j _ => mobiusPairFactor_antitone (hx i).1 (hx j).1 (hxy i) (hxy j))
  exact mul_le_mul hw hp
    (Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => (mobiusPairFactor_pos (hy i).1 (hy j).1).le)
    (Finset.prod_nonneg fun i _ => (lowerLikelihoodWeight_pos N β (hx i)).le)

 
def omegaLogHalf (x : ℝ) : ℝ := Real.log (omega x) + (1 / 2 : ℝ) * Real.log x

end
end CriticalStrip

end OAI
