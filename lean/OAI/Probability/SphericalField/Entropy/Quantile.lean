import Mathlib
import OAI.Probability.SphericalField.Entropy.Kernel
import OAI.Probability.SphericalField.Entropy.CappedDensity

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
theorem cappedA_sphere_equation (μ : Measure Time) [IsProbabilityMeasure μ] {B r : ℝ}
    (hB : B < 1) (hμ : ∀ᵐ s : Time ∂μ, (s : ℝ) ≤ B) (hr : 0 ≤ r) (hrB : r ≤ B) :
    cappedA μ B r * realTail μ r = r +
      ∫ s : Time, (min r (s : ℝ) - r * (s : ℝ)) * cappedA μ B s ∂μ := by
  have hA : Continuous (fun s : Time => cappedA μ B s) :=
    (cappedA_continuous μ hB).comp continuous_subtype_val
  have ht := realTail_mul_A μ hB hμ hr hrB
  rw [realTail_inv_zero_formula μ hB (hr.trans hrB) hμ] at ht
  have hk (s : Time) :
      (min r (s : ℝ) - r * (s : ℝ)) * cappedA μ B s =
      r * ((1 - (s : ℝ)) * cappedA μ B s) - max (r - s) 0 * cappedA μ B s := by
    rcases le_total r (s : ℝ) with hs | hs
    · rw [min_eq_left hs, max_eq_right (sub_nonpos.mpr hs)]
      ring
    · rw [min_eq_right hs, max_eq_left (sub_nonneg.mpr hs)]
      ring
  simp_rw [hk]
  rw [integral_sub (continuous_time_integrable μ (by fun_prop))
    (continuous_time_integrable μ (by fun_prop)), integral_const_mul]
  nlinarith [ht]

lemma cappedA_eq_integral (μ : Measure Time) [IsProbabilityMeasure μ] {B r : ℝ}
    (hμ : ∀ᵐ s : Time ∂μ, (s : ℝ) ≤ B) (hr : 0 ≤ r) (hrB : r ≤ B) :
    cappedA μ B r = ∫ t in 0..r, (realTail μ t)⁻¹ ^ 2 := by
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le hr] at hx
  exact cappedDensity_eq μ hμ (hx.2.trans hrB)

theorem sphere_self_consistency (μ : Measure Time) [IsProbabilityMeasure μ]
    {a : Time → ℝ} {A : ℝ} (hA : 0 ≤ A) (ha : AEStronglyMeasurable a μ)
    (haNonneg : ∀ᵐ r ∂μ, 0 ≤ a r) (haBound : ∀ᵐ r ∂μ, a r ≤ A)
    (haEq : ∀ᵐ r ∂μ, a r * sphereTail μ r = (r : ℝ) + ∫ s, sphereKernel r s * a s ∂μ) :
    (∀ᵐ r : Time ∂μ, a r = ∫ t in 0..(r : ℝ), (realTail μ t)⁻¹ ^ 2) ∧
      ∀ᵐ r : Time ∂μ, (r : ℝ) ≤ A / (1 + A) := by
  have hμ := sphere_equation_support_bound μ hA haNonneg haBound haEq
  have hB : A / (1 + A) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  let B := A / (1 + A)
  have hb : Continuous (fun s : Time => cappedA μ B s) :=
    (cappedA_continuous μ hB).comp continuous_subtype_val
  obtain ⟨C, hC⟩ := (isCompact_range hb.abs).bddAbove
  have hident := sphere_equation_unique μ hB hμ ha hb.aestronglyMeasurable
    ⟨A, by
      filter_upwards [haNonneg, haBound] with s hs hsA
      simpa only [abs_of_nonneg hs] using hsA⟩
    ⟨C, Eventually.of_forall fun s => hC (mem_range_self s)⟩ haEq
    (by
      filter_upwards [hμ] with r hr
      exact cappedA_sphere_equation μ hB hμ r.property.1 hr)
  refine ⟨?_, hμ⟩
  filter_upwards [hident, hμ] with r hr hrB
  rw [hr, cappedA_eq_integral μ hμ r.property.1 hrB]

def boundedCDF (μ : Measure Time) (r : Time) : ℝ := μ.real (Iic r)

lemma boundedCDF_eq (μ : Measure Time) [IsProbabilityMeasure μ] (r : Time) :
    boundedCDF μ r = cdf (μ.map fun s : Time => (s : ℝ)) r := by
  rw [cdf_eq_real, map_measureReal_apply measurable_subtype_coe measurableSet_Iic]
  rfl

lemma boundedCDF_monotone (μ : Measure Time) [IsProbabilityMeasure μ] :
    Monotone (boundedCDF μ) := by
  intro r s hrs
  exact measureReal_mono (Iic_subset_Iic.mpr hrs)

lemma boundedCDF_top (μ : Measure Time) [IsProbabilityMeasure μ] :
    boundedCDF μ 1 = 1 := by
  have h : Iic (1 : Time) = univ := by
    ext r
    simp only [mem_Iic, mem_univ, iff_true]
    exact r.property.2
  simp [boundedCDF, h]

lemma boundedCDF_nonneg (μ : Measure Time) (r : Time) : 0 ≤ boundedCDF μ r :=
  measureReal_nonneg

lemma boundedCDF_le_one (μ : Measure Time) [IsProbabilityMeasure μ] (r : Time) :
    boundedCDF μ r ≤ 1 := by
  rw [boundedCDF_eq]
  exact cdf_le_one _ _

lemma boundedCDF_right_continuous (μ : Measure Time) [IsProbabilityMeasure μ] (r : Time) :
    ContinuousWithinAt (boundedCDF μ) (Ici r) r := by
  have hc := (cdf (μ.map fun s : Time => (s : ℝ))).right_continuous (r : ℝ)
  have hmap : MapsTo (Subtype.val : Time → ℝ) (Ici r) (Ici (r : ℝ)) := fun _ hs => hs
  have hcomp := hc.comp continuous_subtype_val.continuousWithinAt hmap
  simpa only [Function.comp_def, ← boundedCDF_eq] using hcomp

def boundedQuantile (μ : Measure Time) (u : Time) : Time :=
  sInf {r : Time | (u : ℝ) ≤ boundedCDF μ r}

lemma boundedQuantile_le_iff (μ : Measure Time) [IsProbabilityMeasure μ] (u r : Time) :
    boundedQuantile μ u ≤ r ↔ (u : ℝ) ≤ boundedCDF μ r := by
  let A : Set Time := {r | (u : ℝ) ≤ boundedCDF μ r}
  have hA : A.Nonempty := ⟨1, by simpa [A, boundedCDF_top] using u.property.2⟩
  have hcont : ContinuousWithinAt (boundedCDF μ) A (sInf A) :=
    (boundedCDF_right_continuous μ _).mono (fun x hx => sInf_le hx)
  have hmin : (u : ℝ) ≤ boundedCDF μ (sInf A) := by
    rw [MonotoneOn.map_csInf_of_continuousWithinAt hcont ((boundedCDF_monotone μ).monotoneOn A) hA]
    apply le_csInf (hA.image _)
    rintro _ ⟨s, hs, rfl⟩
    exact hs
  constructor
  · intro h
    exact hmin.trans (boundedCDF_monotone μ h)
  · exact fun h => sInf_le h

lemma boundedQuantile_monotone (μ : Measure Time) [IsProbabilityMeasure μ] :
    Monotone (boundedQuantile μ) := by
  intro u v huv
  rw [boundedQuantile_le_iff]
  exact (show (u : ℝ) ≤ v from huv).trans ((boundedQuantile_le_iff μ v _).mp le_rfl)

lemma boundedQuantile_measurable (μ : Measure Time) [IsProbabilityMeasure μ] :
    Measurable (boundedQuantile μ) := (boundedQuantile_monotone μ).measurable

theorem boundedQuantile_law (μ : Measure Time) [IsProbabilityMeasure μ] :
    (volume : Measure Time).map (boundedQuantile μ) = μ := by
  apply Measure.ext_of_Iic
  intro r
  rw [Measure.map_apply (boundedQuantile_measurable μ) measurableSet_Iic]
  have hpre : boundedQuantile μ ⁻¹' Iic r =
      Iic (⟨boundedCDF μ r, boundedCDF_nonneg μ r, boundedCDF_le_one μ r⟩ : Time) := by
    ext u
    exact boundedQuantile_le_iff μ u r
  rw [hpre, unitInterval.volume_Iic]
  exact ENNReal.ofReal_toReal (measure_ne_top μ _)

lemma map_snd_restrict_prod (μ : Measure (Time × Time)) (s t : Set Time)
    (ht : MeasurableSet t) :
    ((μ.restrict (s ×ˢ univ)).map Prod.snd) t = μ (s ×ˢ t) := by
  rw [Measure.map_apply measurable_snd ht,
    Measure.restrict_apply (ht.preimage measurable_snd)]
  congr 1
  ext x
  simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, and_true]
  exact and_comm

lemma map_fst_restrict_prod (μ : Measure (Time × Time)) (s t : Set Time)
    (hs : MeasurableSet s) :
    ((μ.restrict (univ ×ˢ t)).map Prod.fst) s = μ (s ×ˢ t) := by
  rw [Measure.map_apply measurable_fst hs,
    Measure.restrict_apply (hs.preimage measurable_fst)]
  congr 1
  ext x
  simp

lemma measure_prod_ext_Iic (μ ν : Measure (Time × Time)) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν]
    (h : ∀ r t, μ (Iic r ×ˢ Iic t) = ν (Iic r ×ˢ Iic t)) : μ = ν := by
  have hrow (r : Time) : (μ.restrict (Iic r ×ˢ univ)).map Prod.snd =
      (ν.restrict (Iic r ×ˢ univ)).map Prod.snd := by
    apply Measure.ext_of_Iic
    intro t
    rw [map_snd_restrict_prod μ _ _ measurableSet_Iic,
      map_snd_restrict_prod ν _ _ measurableSet_Iic]
    exact h r t
  apply Measure.ext_prod
  intro s t hs ht
  have hcol : (μ.restrict (univ ×ˢ t)).map Prod.fst =
      (ν.restrict (univ ×ˢ t)).map Prod.fst := by
    apply Measure.ext_of_Iic
    intro r
    rw [map_fst_restrict_prod μ _ _ measurableSet_Iic,
      map_fst_restrict_prod ν _ _ measurableSet_Iic]
    have hr := congrArg (fun ζ : Measure Time => ζ t) (hrow r)
    simpa only [map_snd_restrict_prod μ _ _ ht, map_snd_restrict_prod ν _ _ ht] using hr
  have hc := congrArg (fun ζ : Measure Time => ζ s) hcol
  simpa only [map_fst_restrict_prod μ _ _ hs, map_fst_restrict_prod ν _ _ hs] using hc

theorem no_crossing_lower_orthant (μ : Measure (Time × Time))
    (hNo : ∀ r t : Time, μ (Iic r ×ˢ Ioi t) = 0 ∨ μ (Ioi r ×ˢ Iic t) = 0)
    (r t : Time) :
    μ (Iic r ×ˢ Iic t) = min (μ (Iic r ×ˢ univ)) (μ (univ ×ˢ Iic t)) := by
  have h₁ : Iic r ×ˢ univ ∩ univ ×ˢ Iic t = Iic r ×ˢ Iic t := by
    ext x
    simp only [mem_inter_iff, mem_prod, mem_Iic, mem_univ, and_true, true_and]
  have h₂ : (Iic r ×ˢ univ) \ (univ ×ˢ Iic t) = Iic r ×ˢ Ioi t := by ext x; simp
  have h₃ : (univ ×ˢ Iic t) \ (Iic r ×ˢ univ) = Ioi r ×ˢ Iic t := by ext x; simp [and_comm]
  have ha := measure_inter_add_sdiff (μ := μ) (t := univ ×ˢ Iic t) (Iic r ×ˢ univ)
    (MeasurableSet.univ.prod measurableSet_Iic)
  have hb := measure_inter_add_sdiff (μ := μ) (t := Iic r ×ˢ univ) (univ ×ˢ Iic t)
    (measurableSet_Iic.prod MeasurableSet.univ)
  rw [h₁, h₂] at ha
  rw [inter_comm, h₁, h₃] at hb
  rcases hNo r t with h | h
  · rw [h, add_zero] at ha
    rw [← ha, min_eq_left (measure_mono (by intro x hx; exact ⟨mem_univ _, hx.2⟩))]
  · rw [h, add_zero] at hb
    rw [← hb, min_eq_right (measure_mono (by intro x hx; exact ⟨hx.1, mem_univ _⟩))]

theorem no_crossing_quantile_coupling (μ : Measure (Time × Time)) [IsProbabilityMeasure μ]
    (hNo : ∀ r t : Time, μ (Iic r ×ˢ Ioi t) = 0 ∨ μ (Ioi r ×ˢ Iic t) = 0) :
    (volume : Measure Time).map
      (fun u => (boundedQuantile (μ.map Prod.fst) u, boundedQuantile (μ.map Prod.snd) u)) = μ := by
  apply measure_prod_ext_Iic
  intro r t
  rw [Measure.map_apply ((boundedQuantile_measurable _).prodMk (boundedQuantile_measurable _))
    (measurableSet_Iic.prod measurableSet_Iic), no_crossing_lower_orthant μ hNo]
  let a : Time := ⟨boundedCDF (μ.map Prod.fst) r,
    boundedCDF_nonneg _ _, boundedCDF_le_one _ _⟩
  let b : Time := ⟨boundedCDF (μ.map Prod.snd) t,
    boundedCDF_nonneg _ _, boundedCDF_le_one _ _⟩
  have hp : (fun u => (boundedQuantile (μ.map Prod.fst) u,
      boundedQuantile (μ.map Prod.snd) u)) ⁻¹' (Iic r ×ˢ Iic t) = Iic (min a b) := by
    ext u
    simp only [mem_preimage, mem_prod, mem_Iic, le_min_iff, boundedQuantile_le_iff]
    rfl
  rw [hp, unitInterval.volume_Iic]
  change ENNReal.ofReal (min (boundedCDF (μ.map Prod.fst) r)
    (boundedCDF (μ.map Prod.snd) t)) = _
  rw [ENNReal.ofReal_min, boundedCDF, boundedCDF, measureReal_def, measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top _ _), ENNReal.ofReal_toReal (measure_ne_top _ _),
    Measure.map_apply measurable_fst measurableSet_Iic,
    Measure.map_apply measurable_snd measurableSet_Iic]
  congr 2 <;> ext x <;> simp

theorem no_crossing_quantile_bin_integral (μ : Measure (Time × Time)) [IsProbabilityMeasure μ]
    (hNo : ∀ r t : Time, μ (Iic r ×ˢ Ioi t) = 0 ∨ μ (Ioi r ×ˢ Iic t) = 0)
    (a b : Time) :
    (∫ x in (univ ×ˢ Ioc a b), (x.1 : ℝ) ∂μ) =
      ∫ u in (Ioc (⟨boundedCDF (μ.map Prod.snd) a,
        boundedCDF_nonneg _ _, by
          exact boundedCDF_le_one _ _⟩ : Time)
        (⟨boundedCDF (μ.map Prod.snd) b,
        boundedCDF_nonneg _ _, by
          exact boundedCDF_le_one _ _⟩ : Time)),
        (boundedQuantile (μ.map Prod.fst) u : ℝ) := by
  let g : Time → Time × Time := fun u =>
    (boundedQuantile (μ.map Prod.fst) u, boundedQuantile (μ.map Prod.snd) u)
  have hg : Measurable g := (boundedQuantile_measurable _).prodMk (boundedQuantile_measurable _)
  have hmap : (volume : Measure Time).map g = μ := no_crossing_quantile_coupling μ hNo
  have hi := setIntegral_map (μ := (volume : Measure Time))
    (f := fun x : Time × Time => (x.1 : ℝ))
    (MeasurableSet.univ.prod (measurableSet_Ioc (a := a) (b := b)))
    (by fun_prop) hg.aemeasurable
  rw [hmap] at hi
  rw [hi]
  have hs : g ⁻¹' (univ ×ˢ Ioc a b) =
      Ioc (⟨boundedCDF (μ.map Prod.snd) a,
        boundedCDF_nonneg _ _, boundedCDF_le_one _ _⟩ : Time)
      (⟨boundedCDF (μ.map Prod.snd) b,
        boundedCDF_nonneg _ _, boundedCDF_le_one _ _⟩ : Time) := by
    ext u
    simp only [mem_preimage, g, mem_prod, mem_univ, true_and, mem_Ioc,
      lt_iff_not_ge, boundedQuantile_le_iff]
    rfl
  rw [hs]

end SphericalPerceptron
end
end

end OAI
