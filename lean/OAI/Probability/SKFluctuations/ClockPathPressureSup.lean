import Mathlib
import OAI.Probability.SKFluctuations.ClockSampledRate

namespace OAI

/-! Clock Path Pressure Sup. -/

noncomputable section


namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
attribute [local instance] Classical.propDecidable
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]

 omit [Nonempty ι] in
 theorem clockL1Distance_le (D C : ι → ℝ) (q r : ℝ → ι → ℝ≥0)
    (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (hr : ∀ i, MonotoneOn (fun u => r u i) (Icc (0:ℝ) 1))
    (hC : ∀ u ∈ Icc (0:ℝ) 1, ∀ i, |(q u i:ℝ)-(r u i:ℝ)|≤C i) :
    clockL1Distance D q r≤(1/2:ℝ)*∑ i, C i*(D i)^2 := by
  unfold clockL1Distance
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro i _
  have hi : (∫ u in (0:ℝ)..1, |(q u i:ℝ)-(r u i:ℝ)|)≤C i := by
    calc
      _ ≤ ∫ u in (0:ℝ)..1, C i :=
        intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num)
          (clockDirection_intervalIntegrable r q hr hq i).abs intervalIntegrable_const
          (fun u hu => hC u ⟨hu.1.le,hu.2.le⟩ i)
      _ = _ := by simp
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hi (sq_nonneg (D i))

 theorem pathDisorderPressure_sup_comparison {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (C D M : ι → ℝ)
    (hself : ∀ σ i, (φ σ (Pi.single i 1))^2=C i)
    (hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i)
    (q r : ℝ → ι → ℝ≥0)
    (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (hr : ∀ i, MonotoneOn (fun u => r u i) (Icc (0:ℝ) 1))
    (hM : ∀ u ∈ Icc (0:ℝ) 1, ∀ i, |(q u i:ℝ)-(r u i:ℝ)|≤M i) (x : ι → ℝ) :
    |pathDisorderPressure w φ C q x-pathDisorderPressure w φ C r x| ≤
      (1/2:ℝ)*∑ i, M i*(D i)^2 :=
  (pathDisorderPressure_l1_comparison hw φ C D hself (fun i σ => hφ σ i) q r hq hr x).trans
    (clockL1Distance_le D M q r hq hr hM)

 omit [Fintype ι] [Nonempty ι] in
 theorem affineClockPath_zero (q r : ℝ → ι → ℝ≥0) : affineClockPath q r 0=q := by
  funext u i
  simp [affineClockPath]
 omit [Fintype ι] [Nonempty ι] in
 theorem affineClockPath_one (q r : ℝ → ι → ℝ≥0) : affineClockPath q r 1=r := by
  funext u i
  simp [affineClockPath]

 omit [Fintype ι] [Nonempty ι] in
 theorem affineClockPath_difference (q r : ℝ → ι → ℝ≥0) {s t : ℝ}
    (hs : s ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1) (u : ℝ) (i : ι) :
    |(affineClockPath q r s u i:ℝ)-(affineClockPath q r t u i:ℝ)|=
      |s-t| *|(r u i:ℝ)-(q u i:ℝ)| := by
  rw [affineClockPath_coe q r hs,affineClockPath_coe q r ht,←abs_mul]
  congr 1
  ring

 theorem pathDisorderPressure_affine_continuousOn {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (C D : ι → ℝ)
    (hself : ∀ σ i, (φ σ (Pi.single i 1))^2=C i)
    (hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i)
    (q r : ℝ → ι → ℝ≥0)
    (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (hr : ∀ i, MonotoneOn (fun u => r u i) (Icc (0:ℝ) 1)) (x : ι → ℝ) :
    ContinuousOn (fun t => pathDisorderPressure w φ C (affineClockPath q r t) x) (Icc (0:ℝ) 1) := by
  let A : ℝ≥0 := ⟨(1/2:ℝ)*∑ i, ((r 1 i:ℝ)+(q 1 i:ℝ))*(D i)^2, by positivity⟩
  apply (show LipschitzOnWith A (fun t => pathDisorderPressure w φ C (affineClockPath q r t) x)
      (Icc (0:ℝ) 1) from ?_).continuousOn
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs t ht
  rw [Real.dist_eq,Real.dist_eq]
  have he := pathDisorderPressure_sup_comparison hw φ C D
    (fun i => |s-t| *((r 1 i:ℝ)+(q 1 i:ℝ))) hself hφ
    (affineClockPath q r s) (affineClockPath q r t)
    (affineClockPath_monotone q r hq hr s) (affineClockPath_monotone q r hq hr t)
    (fun u hu i => by
      rw [affineClockPath_difference q r hs ht]
      exact mul_le_mul_of_nonneg_left (clockDirection_bound q r hq hr hu i) (abs_nonneg _)) x
  convert he using 1
  change ((1/2:ℝ)*∑ i, ((r 1 i:ℝ)+(q 1 i:ℝ))*(D i)^2) * |s-t| = _
  simp only [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
attribute [local instance] Classical.propDecidable
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]

 theorem intervalIntegral_mul_abs_le {f g : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 1) (hg : IntervalIntegrable g volume 0 1)
    {A B : ℝ} (hA : 0≤A) (_hB : 0≤B)
    (hfB : ∀ u ∈ Ioc (0:ℝ) 1, |f u|≤A) (hgB : ∀ u ∈ Ioc (0:ℝ) 1, |g u|≤B) :
    |∫ u in (0:ℝ)..1, f u*g u|≤A*B := by
  have hi := intervalIntegrable_mul_bounded hf hg hgB
  calc
    _ ≤ ∫ u in (0:ℝ)..1, |f u*g u| := by
      simpa only [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm
        (f := fun u => f u*g u) (by norm_num : (0:ℝ)≤1)
    _ ≤ ∫ _u in (0:ℝ)..1, A*B := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num) hi.abs intervalIntegrable_const
      intro u hu
      rw [abs_mul]
      exact mul_le_mul (hfB u ⟨hu.1,hu.2.le⟩) (hgB u ⟨hu.1,hu.2.le⟩) (abs_nonneg _) hA
    _ = _ := by simp

 theorem pathPressureRate_sup_comparison {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (D C M : ι → ℝ) (hD : ∀ i, 0≤D i)
    (hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i)
    (p p' q r : ℝ → ι → ℝ≥0)
    (hp : ∀ i, MonotoneOn (fun u => p u i) (Icc (0:ℝ) 1))
    (hp' : ∀ i, MonotoneOn (fun u => p' u i) (Icc (0:ℝ) 1))
    (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (hr : ∀ i, MonotoneOn (fun u => r u i) (Icc (0:ℝ) 1))
    (hC : ∀ u ∈ Icc (0:ℝ) 1, ∀ i, |(r u i:ℝ)-(q u i:ℝ)|≤C i)
    (hM : ∀ u ∈ Icc (0:ℝ) 1, ∀ i, |(p u i:ℝ)-(p' u i:ℝ)|≤M i) :
    |pathPressureRate w φ p (fun u i => (r u i:ℝ)-(q u i:ℝ))-
      pathPressureRate w φ p' (fun u i => (r u i:ℝ)-(q u i:ℝ))| ≤
      (3/2:ℝ)*ClockTree.errorJetVariation 2 0 0*(∑ i, M i*(D i)^2)*(∑ i, C i*(D i)^2) := by
  have hC0 (i : ι) : 0≤C i := (abs_nonneg _).trans (hC 0 (by constructor <;> norm_num) i)
  have hM0 (i : ι) : 0≤M i := (abs_nonneg _).trans (hM 0 (by constructor <;> norm_num) i)
  have hA : 0≤∑ i, M i*(D i)^2 := Finset.sum_nonneg fun i _ => mul_nonneg (hM0 i) (sq_nonneg _)
  have hi (z : ℝ → ι → ℝ≥0) (hz : ∀ i, MonotoneOn (fun u => z u i) (Icc (0:ℝ) 1)) (i : ι) :
      IntervalIntegrable (fun u => ((r u i:ℝ)-(q u i:ℝ))*pathPairMoment w φ z (coordinatePairTest φ i) u) volume 0 1 := by
    simpa only [mul_comm] using intervalIntegrable_mul_bounded
      (pathPairMoment_intervalIntegrable_all hw φ z hz _) (clockDirection_intervalIntegrable q r hq hr i)
      (fun u hu => hC u ⟨hu.1.le,hu.2⟩ i)
  have hI (i : ι) : |(∫ u in (0:ℝ)..1, ((r u i:ℝ)-(q u i:ℝ))*pathPairMoment w φ p (coordinatePairTest φ i) u)-
      (∫ u in (0:ℝ)..1, ((r u i:ℝ)-(q u i:ℝ))*pathPairMoment w φ p' (coordinatePairTest φ i) u)|≤
      C i*(ClockTree.errorJetVariation 2 0 0*(D i)^2*(3*∑ j, M j*(D j)^2)) := by
    rw [←intervalIntegral.integral_sub (hi p hp i) (hi p' hp' i)]
    have he : (fun u => ((r u i:ℝ)-(q u i:ℝ))*pathPairMoment w φ p (coordinatePairTest φ i) u-
        ((r u i:ℝ)-(q u i:ℝ))*pathPairMoment w φ p' (coordinatePairTest φ i) u)=
        fun u => ((r u i:ℝ)-(q u i:ℝ))*(pathPairMoment w φ p (coordinatePairTest φ i) u-
          pathPairMoment w φ p' (coordinatePairTest φ i) u) := by funext u; ring
    rw [he]
    apply intervalIntegral_mul_abs_le (clockDirection_intervalIntegrable q r hq hr i)
      ((pathPairMoment_intervalIntegrable_all hw φ p hp _).sub
        (pathPairMoment_intervalIntegrable_all hw φ p' hp' _)) (hC0 i)
      (by apply mul_nonneg (mul_nonneg (ClockTree.errorJetVariation_nonneg _ _ _) (sq_nonneg _)); positivity)
      (fun u hu => hC u ⟨hu.1.le,hu.2⟩ i)
    intro u hu
    exact pathPairMoment_sup_comparison hw φ D M hD hφ p p' hp hp' hM hu
      (coordinatePairTest φ i) (sq_nonneg _) (coordinatePairTest_bound φ D hφ i)
  unfold pathPressureRate
  rw [←mul_sub,abs_mul,←Finset.sum_sub_distrib]
  norm_num only [abs_neg,abs_div,abs_one,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
  apply (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num : (0:ℝ)≤1/2)).trans
  calc
    _ ≤ (1/2:ℝ)*∑ i, C i*(ClockTree.errorJetVariation 2 0 0*(D i)^2*(3*∑ j, M j*(D j)^2)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum fun i _ => hI i
    _ = _ := by
      conv_lhs => rw [Finset.mul_sum]
      conv_rhs => rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
attribute [local instance] Classical.propDecidable
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]

 theorem pathDisorderPressure_taylor {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (C D B : ι → ℝ)
    (hself : ∀ σ i, (φ σ (Pi.single i 1))^2=C i)
    (hD : ∀ i, 0≤D i) (hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i)
    (q r : ℝ → ι → ℝ≥0)
    (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (hr : ∀ i, MonotoneOn (fun u => r u i) (Icc (0:ℝ) 1))
    (hB : ∀ u ∈ Icc (0:ℝ) 1, ∀ i, |(r u i:ℝ)-(q u i:ℝ)|≤B i) :
    |pathDisorderPressure w φ C r 0-pathDisorderPressure w φ C q 0-
      pathPressureRate w φ q (fun u i => (r u i:ℝ)-(q u i:ℝ))| ≤
      (3/2:ℝ)*ClockTree.errorJetVariation 2 0 0*(∑ i, B i*(D i)^2)^2 := by
  obtain ⟨t,ht,he⟩ := exists_hasDerivAt_eq_slope
    (fun t => pathDisorderPressure w φ C (affineClockPath q r t) 0)
    (fun t => pathPressureRate w φ (affineClockPath q r t) (fun u i => (r u i:ℝ)-(q u i:ℝ)))
    (by norm_num : (0:ℝ)<1)
    (pathDisorderPressure_affine_continuousOn hw φ C D hself hφ q r hq hr 0)
    (fun t ht => pathDisorderPressure_hasDerivAt hw φ C hself q r hq hr ht)
  simp only [affineClockPath_zero,affineClockPath_one,sub_zero,div_one] at he
  rw [←he]
  have hb : ∀ u ∈ Icc (0:ℝ) 1, ∀ i,
      |(affineClockPath q r t u i:ℝ)-(q u i:ℝ)|≤B i := by
    intro u hu i
    have hd := affineClockPath_difference q r ⟨ht.1.le,ht.2.le⟩
      (show (0:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num) u i
    simp only [affineClockPath_zero,sub_zero,abs_of_pos ht.1] at hd
    rw [hd]
    exact (mul_le_of_le_one_left (abs_nonneg _) ht.2.le).trans (hB u hu i)
  have hbnd := pathPressureRate_sup_comparison hw φ D B B hD hφ
    (affineClockPath q r t) q q r (affineClockPath_monotone q r hq hr t) hq hq hr hB hb
  convert hbnd using 1; ring

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
attribute [local instance] Classical.propDecidable
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]

 omit [Nonempty S] [Nonempty ι] in
 theorem pathPressureRate_const_mul (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (p : ℝ → ι → ℝ≥0) (K : ℝ → ι → ℝ) (a : ℝ) :
    pathPressureRate w φ p (fun u i => a*K u i)=a*pathPressureRate w φ p K := by
  unfold pathPressureRate
  simp only [mul_assoc,intervalIntegral.integral_const_mul,←Finset.mul_sum]
  ring

 theorem pathPressureRate_direction_integrable {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (D : ι → ℝ) (hD : ∀ i, 0≤D i)
    (hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i)
    (p : ℝ → ι → ℝ≥0) (hp : ∀ i, MonotoneOn (fun u => p u i) (Icc (0:ℝ) 1))
    (K : ℝ → ι → ℝ) (hK : ∀ i, IntervalIntegrable (fun u => K u i) volume 0 1) (i : ι) :
    IntervalIntegrable (fun u => K u i*pathPairMoment w φ p (coordinatePairTest φ i) u) volume 0 1 :=
  intervalIntegrable_mul_bounded (hK i) (pathPairMoment_intervalIntegrable_all hw φ p hp _)
    (fun _ hu => pathPairMoment_bound hw φ D hD hφ p hp _ (sq_nonneg _) (coordinatePairTest_bound φ D hφ i) hu)

 theorem pathPressureRate_sub {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (D : ι → ℝ) (hD : ∀ i, 0≤D i)
    (hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i)
    (p : ℝ → ι → ℝ≥0) (hp : ∀ i, MonotoneOn (fun u => p u i) (Icc (0:ℝ) 1))
    (K L : ℝ → ι → ℝ)
    (hK : ∀ i, IntervalIntegrable (fun u => K u i) volume 0 1)
    (hL : ∀ i, IntervalIntegrable (fun u => L u i) volume 0 1) :
    pathPressureRate w φ p (fun u i => K u i-L u i)=
      pathPressureRate w φ p K-pathPressureRate w φ p L := by
  unfold pathPressureRate
  simp only [sub_mul]
  simp_rw [intervalIntegral.integral_sub (pathPressureRate_direction_integrable hw φ D hD hφ p hp K hK _)
    (pathPressureRate_direction_integrable hw φ D hD hφ p hp L hL _)]
  rw [Finset.sum_sub_distrib,mul_sub]

 theorem pathPressureRate_bound {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (D B : ι → ℝ) (hD : ∀ i, 0≤D i)
    (hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i)
    (p : ℝ → ι → ℝ≥0) (hp : ∀ i, MonotoneOn (fun u => p u i) (Icc (0:ℝ) 1))
    (K : ℝ → ι → ℝ) (hK : ∀ i, IntervalIntegrable (fun u => K u i) volume 0 1)
    (hB : ∀ u ∈ Ioc (0:ℝ) 1, ∀ i, |K u i|≤B i) :
    |pathPressureRate w φ p K|≤(1/2:ℝ)*∑ i, B i*(D i)^2 := by
  have hB0 (i : ι) : 0≤B i := (abs_nonneg _).trans (hB 1 (by constructor <;> norm_num) i)
  unfold pathPressureRate
  rw [abs_mul]
  norm_num only [abs_neg,abs_div,abs_one,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
  apply (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num : (0:ℝ)≤1/2)).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro i _
  exact intervalIntegral_mul_abs_le (hK i) (pathPairMoment_intervalIntegrable_all hw φ p hp _)
    (hB0 i) (sq_nonneg _) (fun u hu => hB u hu i)
    (fun _ hu => pathPairMoment_bound hw φ D hD hφ p hp _ (sq_nonneg _) (coordinatePairTest_bound φ D hφ i) hu)

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
attribute [local instance] Classical.propDecidable
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]

 theorem pathPressureRate_tendsto {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (D B : ι → ℝ) (hD : ∀ i, 0≤D i)
    (hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i)
    (p : ℝ → ι → ℝ≥0) (hp : ∀ i, MonotoneOn (fun u => p u i) (Icc (0:ℝ) 1))
    {A : Type*} {l : Filter A} [l.IsCountablyGenerated]
    (K : A → ℝ → ι → ℝ) (L : ℝ → ι → ℝ)
    (hK : ∀ᶠ a in l, ∀ i, IntervalIntegrable (fun u => K a u i) volume 0 1)
    (hB : ∀ᶠ a in l, ∀ u ∈ Ioc (0:ℝ) 1, ∀ i, |K a u i|≤B i)
    (hL : ∀ i, ∀ᵐ u ∂volume, u ∈ Ioc (0:ℝ) 1 → Tendsto (fun a => K a u i) l (𝓝 (L u i))) :
    Tendsto (fun a => pathPressureRate w φ p (K a)) l (𝓝 (pathPressureRate w φ p L)) := by
  unfold pathPressureRate
  apply Tendsto.const_mul
  apply tendsto_finsetSum
  intro i _
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => B i*(D i)^2)
  · filter_upwards [hK] with a ha
    simpa only [uIoc_of_le (by norm_num : (0:ℝ)≤1)] using
      (pathPressureRate_direction_integrable hw φ D hD hφ p hp (K a) ha i).1.aestronglyMeasurable
  · filter_upwards [hB] with a ha
    filter_upwards [] with u hu
    rw [uIoc_of_le (by norm_num : (0:ℝ)≤1)] at hu
    rw [Real.norm_eq_abs,abs_mul]
    exact mul_le_mul (ha u hu i)
      (pathPairMoment_bound hw φ D hD hφ p hp _ (sq_nonneg _) (coordinatePairTest_bound φ D hφ i) hu)
      (abs_nonneg _) ((abs_nonneg _).trans (ha u hu i))
  · exact intervalIntegrable_const
  · filter_upwards [hL i] with u hu hu'
    rw [uIoc_of_le (by norm_num : (0:ℝ)≤1)] at hu'
    exact (hu hu').mul_const _

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
attribute [local instance] Classical.propDecidable
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]

 theorem pathDisorderPressure_slope_error {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (C D B : ι → ℝ)
    (hself : ∀ σ i, (φ σ (Pi.single i 1))^2=C i)
    (hD : ∀ i, 0≤D i) (hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i)
    (q r : ℝ → ι → ℝ≥0)
    (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (hr : ∀ i, MonotoneOn (fun u => r u i) (Icc (0:ℝ) 1))
    {t : ℝ} (ht : t≠0)
    (hB : ∀ u ∈ Icc (0:ℝ) 1, ∀ i, |(r u i:ℝ)-(q u i:ℝ)|≤|t| *B i) :
    |(pathDisorderPressure w φ C r 0-pathDisorderPressure w φ C q 0)/t-
      pathPressureRate w φ q (fun u i => ((r u i:ℝ)-(q u i:ℝ))/t)| ≤
      (3/2:ℝ)*ClockTree.errorJetVariation 2 0 0*(∑ i, B i*(D i)^2)^2*|t| := by
  have hd : pathPressureRate w φ q (fun u i => ((r u i:ℝ)-(q u i:ℝ))/t)=
      pathPressureRate w φ q (fun u i => (r u i:ℝ)-(q u i:ℝ))/t := by
    simp only [div_eq_mul_inv,mul_comm _ t⁻¹]
    exact pathPressureRate_const_mul w φ q _ _
  rw [hd,←sub_div,abs_div]
  apply (div_le_iff₀ (abs_pos.mpr ht)).mpr
  have hbnd := pathDisorderPressure_taylor hw φ C D (fun i => |t| *B i) hself hD hφ q r hq hr hB
  have hs : (∑ i, |t| *B i*(D i)^2)=|t| *(∑ i, B i*(D i)^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  apply hbnd.trans
  rw [hs]
  exact le_of_eq (by ring)

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
attribute [local instance] Classical.propDecidable
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]

 theorem pathDisorderPressure_hasDerivWithinAt_curve {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (C D B : ι → ℝ)
    (hself : ∀ σ i, (φ σ (Pi.single i 1))^2=C i)
    (hD : ∀ i, 0≤D i) (hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i)
    (q : ℝ → ℝ → ι → ℝ≥0) (K : ℝ → ι → ℝ) (s : Set ℝ)
    (hq0 : ∀ i, MonotoneOn (fun u => q 0 u i) (Icc (0:ℝ) 1))
    (hq : ∀ᶠ t in 𝓝[s \ {0}] 0, ∀ i, MonotoneOn (fun u => q t u i) (Icc (0:ℝ) 1))
    (hB : ∀ᶠ t in 𝓝[s \ {0}] 0, ∀ u ∈ Icc (0:ℝ) 1, ∀ i,
      |(q t u i:ℝ)-(q 0 u i:ℝ)|≤|t| *B i)
    (hK : ∀ i, ∀ᵐ u ∂volume, u ∈ Ioc (0:ℝ) 1 →
      Tendsto (fun t => ((q t u i:ℝ)-(q 0 u i:ℝ))/t) (𝓝[s \ {0}] 0) (𝓝 (K u i))) :
    HasDerivWithinAt (fun t => pathDisorderPressure w φ C (q t) 0)
      (pathPressureRate w φ (q 0) K) s 0 := by
  let L : ℝ → ℝ → ι → ℝ := fun t u i => ((q t u i:ℝ)-(q 0 u i:ℝ))/t
  have hne : ∀ᶠ t in 𝓝[s \ {0}] 0, t≠0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ht.2
  have hlim := pathPressureRate_tendsto hw φ D B hD hφ (q 0) hq0 L K
    (by
      filter_upwards [hq] with t ht i
      exact (clockDirection_intervalIntegrable (q 0) (q t) hq0 ht i).div_const t)
    (by
      filter_upwards [hB,hne] with t ht ht0 u hu i
      dsimp [L]
      rw [abs_div,div_le_iff₀ (abs_pos.mpr ht0)]
      simpa only [mul_comm] using ht u ⟨hu.1.le,hu.2⟩ i)
    hK
  have herr : Tendsto (fun t =>
      (pathDisorderPressure w φ C (q t) 0-pathDisorderPressure w φ C (q 0) 0)/t-
        pathPressureRate w φ (q 0) (L t)) (𝓝[s \ {0}] 0) (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun t =>
      (3/2:ℝ)*ClockTree.errorJetVariation 2 0 0*(∑ i, B i*(D i)^2)^2*|t|) ?_ ?_
    · filter_upwards [hq,hB,hne] with t ht hb ht0
      rw [Real.norm_eq_abs]
      exact pathDisorderPressure_slope_error hw φ C D B hself hD hφ (q 0) (q t) hq0 ht ht0 hb
    · simpa only [abs_zero,mul_zero] using
        ((continuous_abs.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds).const_mul
          ((3/2:ℝ)*ClockTree.errorJetVariation 2 0 0*(∑ i, B i*(D i)^2)^2)
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hs : slope (fun t => pathDisorderPressure w φ C (q t) 0) 0 =
      fun t => (pathDisorderPressure w φ C (q t) 0-pathDisorderPressure w φ C (q 0) 0)/(t-0) :=
    funext fun t => slope_def_field _ _ _
  rw [hs]
  simpa only [sub_zero,sub_add_cancel,zero_add] using herr.add hlim

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
attribute [local instance] Classical.propDecidable
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]

 theorem pathPressureRate_integral_direction {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (D : ι → ℝ) (hD : ∀ i, 0≤D i)
    (hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i)
    (p : ℝ → ι → ℝ≥0) (hp : ∀ i, MonotoneOn (fun u => p u i) (Icc (0:ℝ) 1))
    (K : ℝ → ι → ℝ) (hK : ∀ i, IntervalIntegrable (fun u => K u i) volume 0 1) :
    pathPressureRate w φ p K=-(1/2:ℝ)*∫ u in (0:ℝ)..1,
      pathPairMoment w φ p (featureKernel φ (K u)) u := by
  unfold pathPressureRate
  rw [←intervalIntegral.integral_finsetSum (fun i _ =>
    pathPressureRate_direction_integrable hw φ D hD hφ p hp K hK i)]
  congr 1
  apply intervalIntegral.integral_congr_ae
  filter_upwards [] with u hu
  rw [uIoc_of_le (by norm_num : (0:ℝ)≤1)] at hu
  exact (pathPairMoment_featureKernel hw φ p hp _ hu).symm

 theorem pathPairMoment_mul_intervalIntegrable {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (D : ι → ℝ) (hD : ∀ i, 0≤D i)
    (hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i)
    (p : ℝ → ι → ℝ≥0) (hp : ∀ i, MonotoneOn (fun u => p u i) (Icc (0:ℝ) 1))
    (P : S → S → ℝ) {B : ℝ} (hB : 0≤B) (hP : ∀ σ τ, |P σ τ|≤B)
    (K : ℝ → ℝ) (hK : IntervalIntegrable K volume 0 1) :
    IntervalIntegrable (fun u => K u*pathPairMoment w φ p P u) volume 0 1 :=
  intervalIntegrable_mul_bounded hK (pathPairMoment_intervalIntegrable_all hw φ p hp _)
    (fun _ hu => pathPairMoment_bound hw φ D hD hφ p hp P hB hP hu)

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 def orderedPathClock (n : ℕ) (b h : ℝ → ℝ≥0) (u : ℝ) : OrderedFeatureIndex n → ℝ≥0 :=
  Sum.elim (fun _ => h u) (fun _ => b u)

 theorem orderedPathClock_monotone (n : ℕ) {b h : ℝ → ℝ≥0}
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1)) :
    ∀ i, MonotoneOn (fun u => orderedPathClock n b h u i) (Icc (0:ℝ) 1) := by
  intro i
  cases i with
  | inl i => exact hh
  | inr i => exact hb

 def orderedSKPathPressure (n : ℕ) (b h : ℝ → ℝ≥0)
    (x : OrderedFeatureIndex n → ℝ) : ℝ :=
  pathDisorderPressure (uniformWeight n) (orderedFeature n) (fun i => (orderedAmplitude n i)^2)
    (orderedPathClock n b h) x/(n:ℝ)

 theorem orderedPathClock_l1 (n : ℕ) (hn : 0<n) (b h b' h' : ℝ → ℝ≥0) :
    clockL1Distance (orderedAmplitude n) (orderedPathClock n b h) (orderedPathClock n b' h') =
      (n:ℝ)*((1/4:ℝ)*(∫ u in (0:ℝ)..1, |(b u:ℝ)-(b' u:ℝ)|)+
        (1/2:ℝ)*(∫ u in (0:ℝ)..1, |(h u:ℝ)-(h' u:ℝ)|)) := by
  unfold clockL1Distance
  have he : (∑ i : OrderedFeatureIndex n, (orderedAmplitude n i)^2*
      (∫ u in (0:ℝ)..1, |(orderedPathClock n b h u i:ℝ)-(orderedPathClock n b' h' u i:ℝ)|)) =
      (n:ℝ)*((∫ u in (0:ℝ)..1, |(h u:ℝ)-(h' u:ℝ)|)+
        (∫ u in (0:ℝ)..1, |(b u:ℝ)-(b' u:ℝ)|)/2) := by
    calc
      _ = ∑ i : OrderedFeatureIndex n, Sum.elim
          (fun _ => ∫ u in (0:ℝ)..1, |(h u:ℝ)-(h' u:ℝ)|)
          (fun _ => ∫ u in (0:ℝ)..1, |(b u:ℝ)-(b' u:ℝ)|) i*(orderedAmplitude n i)^2 := by
        apply Finset.sum_congr rfl
        intro i _
        cases i <;> exact mul_comm _ _
      _ = _ := orderedAmplitude_sum n hn _ _
  rw [he]
  ring

 theorem orderedSKPathPressure_l1_comparison (n : ℕ) (hn : 0<n)
    (b h b' h' : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (hb' : MonotoneOn b' (Icc (0:ℝ) 1)) (hh' : MonotoneOn h' (Icc (0:ℝ) 1))
    (x : OrderedFeatureIndex n → ℝ) :
    |orderedSKPathPressure n b h x-orderedSKPathPressure n b' h' x| ≤
      (1/4:ℝ)*(∫ u in (0:ℝ)..1, |(b u:ℝ)-(b' u:ℝ)|)+
      (1/2:ℝ)*(∫ u in (0:ℝ)..1, |(h u:ℝ)-(h' u:ℝ)|) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hnp : 0<(n:ℝ) := Nat.cast_pos.mpr hn
  have hd := pathDisorderPressure_l1_comparison (uniformWeight_pos n) (orderedFeature n)
    (fun i => (orderedAmplitude n i)^2) (orderedAmplitude n) (orderedFeature_square n)
    (fun i σ => (orderedFeature_abs n σ i).le) (orderedPathClock n b h) (orderedPathClock n b' h')
    (orderedPathClock_monotone n hb hh) (orderedPathClock_monotone n hb' hh') x
  rw [orderedPathClock_l1 n hn] at hd
  unfold orderedSKPathPressure
  rw [← sub_div,abs_div,abs_of_pos hnp]
  exact (div_le_iff₀ hnp).mpr (by simpa only [mul_comm] using hd)

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators
attribute [local instance] Classical.propDecidable
local instance (n : ℕ) : DecidableEq (OrderedFeatureIndex n) := fun _ _ => Classical.propDecidable _

 def orderedPathPair (n : ℕ) (b h : ℝ → ℝ≥0) (P : Spin n → Spin n → ℝ) (u : ℝ) : ℝ :=
  pathPairMoment (uniformWeight n) (orderedFeature n) (orderedPathClock n b h) P u
 def orderedPathS (n : ℕ) (b h : ℝ → ℝ≥0) : ℝ → ℝ :=
  orderedPathPair n b h (orderedOverlap n)
 def orderedPathB (n : ℕ) (b h : ℝ → ℝ≥0) : ℝ → ℝ :=
  orderedPathPair n b h (fun σ τ => (orderedOverlap n σ τ)^2)

 theorem orderedPathPair_linear (n : ℕ) (hn : 0<n) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (P Q : Spin n → Spin n → ℝ) (c d : ℝ) {u : ℝ} (hu : u ∈ Ioc (0:ℝ) 1) :
    orderedPathPair n b h (fun σ τ => c*P σ τ+d*Q σ τ) u=
      c*orderedPathPair n b h P u+d*orderedPathPair n b h Q u := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  unfold orderedPathPair
  rw [pathPairMoment_add (uniformWeight_pos n) _ _ (orderedPathClock_monotone n hb hh) _ _ hu,
    pathPairMoment_const_mul (uniformWeight_pos n) _ _ (orderedPathClock_monotone n hb hh) _ _ hu,
    pathPairMoment_const_mul (uniformWeight_pos n) _ _ (orderedPathClock_monotone n hb hh) _ _ hu]

 theorem orderedPathPair_direction_integrable (n : ℕ) (hn : 0<n) (b h q r : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (hq : MonotoneOn q (Icc (0:ℝ) 1)) (hr : MonotoneOn r (Icc (0:ℝ) 1))
    (P : Spin n → Spin n → ℝ) :
    IntervalIntegrable (fun u => ((r u:ℝ)-(q u:ℝ))*orderedPathPair n b h P u) volume 0 1 := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hi := clockDirection_intervalIntegrable (fun (u : ℝ) (_ : Unit) => q u) (fun (u : ℝ) (_ : Unit) => r u)
    (fun _ => hq) (fun _ => hr) ()
  simpa only [mul_comm,orderedPathPair] using intervalIntegrable_mul_bounded
    (pathPairMoment_intervalIntegrable_all (uniformWeight_pos n) (orderedFeature n)
      (orderedPathClock n b h) (orderedPathClock_monotone n hb hh) P) hi
    (fun u hu => clockDirection_bound (fun (u : ℝ) (_ : Unit) => q u) (fun (u : ℝ) (_ : Unit) => r u)
      (fun _ => hq) (fun _ => hr) ⟨hu.1.le,hu.2⟩ ())

 theorem pathPressureRate_ordered (n : ℕ) (hn : 0<n) (b h b₀ h₀ b₁ h₁ : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (hb₀ : MonotoneOn b₀ (Icc (0:ℝ) 1)) (hh₀ : MonotoneOn h₀ (Icc (0:ℝ) 1))
    (hb₁ : MonotoneOn b₁ (Icc (0:ℝ) 1)) (hh₁ : MonotoneOn h₁ (Icc (0:ℝ) 1)) :
    pathPressureRate (uniformWeight n) (orderedFeature n) (orderedPathClock n b h)
      (fun u i => (orderedPathClock n b₁ h₁ u i:ℝ)-(orderedPathClock n b₀ h₀ u i:ℝ))/(n:ℝ)=
      -(1/4:ℝ)*(∫ u in (0:ℝ)..1, ((b₁ u:ℝ)-(b₀ u:ℝ))*orderedPathB n b h u)-
        (1/2:ℝ)*(∫ u in (0:ℝ)..1, ((h₁ u:ℝ)-(h₀ u:ℝ))*orderedPathS n b h u) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hk (u : ℝ) : featureKernel (orderedFeature n)
      (fun i => (orderedPathClock n b₁ h₁ u i:ℝ)-(orderedPathClock n b₀ h₀ u i:ℝ))=
      fun σ τ => ((n:ℝ)/2*((b₁ u:ℝ)-(b₀ u:ℝ)))*(orderedOverlap n σ τ)^2+
        ((n:ℝ)*((h₁ u:ℝ)-(h₀ u:ℝ)))*orderedOverlap n σ τ := by
    funext σ τ
    have he : (fun i => (orderedPathClock n b₁ h₁ u i:ℝ)-(orderedPathClock n b₀ h₀ u i:ℝ))=
        Sum.elim (fun _ => (h₁ u:ℝ)-(h₀ u:ℝ)) (fun _ => (b₁ u:ℝ)-(b₀ u:ℝ)) := by
      funext i; cases i <;> rfl
    rw [he]
    simp only [featureKernel]
    have hs (σ : Spin n) (i : OrderedFeatureIndex n) :
        orderedFeature n σ (Pi.single i 1)=orderedFeatureCoefficient n σ i := by
      simp [orderedFeature_apply,Pi.single_apply]
    simp only [hs]
    rw [orderedCovariance n hn]
    ring
  rw [pathPressureRate_integral (uniformWeight_pos n) _ _ _ _ (orderedPathClock_monotone n hb hh)
    (orderedPathClock_monotone n hb₀ hh₀) (orderedPathClock_monotone n hb₁ hh₁)]
  have he : (∫ u in (0:ℝ)..1, pathPairMoment (uniformWeight n) (orderedFeature n)
      (orderedPathClock n b h) (featureKernel (orderedFeature n)
        (fun i => (orderedPathClock n b₁ h₁ u i:ℝ)-(orderedPathClock n b₀ h₀ u i:ℝ))) u)=
      ∫ u in (0:ℝ)..1, (n:ℝ)/2*(((b₁ u:ℝ)-(b₀ u:ℝ))*orderedPathB n b h u)+
        (n:ℝ)*(((h₁ u:ℝ)-(h₀ u:ℝ))*orderedPathS n b h u) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [] with u hu
    rw [uIoc_of_le (by norm_num : (0:ℝ)≤1)] at hu
    rw [hk]
    change orderedPathPair n b h _ u=_
    rw [orderedPathPair_linear n hn b h hb hh _ _ _ _ hu]
    dsimp [orderedPathB,orderedPathS]
    ring
  rw [he]
  change (-(1/2:ℝ)*(∫ u in (0:ℝ)..1, (n:ℝ)/2*(((b₁ u:ℝ)-(b₀ u:ℝ))*
    orderedPathPair n b h (fun σ τ => (orderedOverlap n σ τ)^2) u)+(n:ℝ)*
    (((h₁ u:ℝ)-(h₀ u:ℝ))*orderedPathPair n b h (orderedOverlap n) u)))/(n:ℝ)=_
  rw [intervalIntegral.integral_add
    ((orderedPathPair_direction_integrable n hn b h b₀ b₁ hb hh hb₀ hb₁ _).const_mul ((n:ℝ)/2))
    ((orderedPathPair_direction_integrable n hn b h h₀ h₁ hb hh hh₀ hh₁ _).const_mul (n:ℝ)),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  have hn0 : (n:ℝ)≠0 := ne_of_gt (Nat.cast_pos.mpr hn)
  dsimp only [orderedPathB,orderedPathS]
  field_simp
  ring

 def affineNNPath (b c : ℝ → ℝ≥0) (s : ℝ) (u : ℝ) : ℝ≥0 :=
  Real.toNNReal (1-s)*b u+Real.toNNReal s*c u

 theorem affineNNPath_monotone (b c : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hc : MonotoneOn c (Icc (0:ℝ) 1)) (s : ℝ) :
    MonotoneOn (affineNNPath b c s) (Icc (0:ℝ) 1) := by
  intro u hu v hv huv
  exact add_le_add (mul_le_mul_of_nonneg_left (hb hu hv huv) zero_le)
    (mul_le_mul_of_nonneg_left (hc hu hv huv) zero_le)

 theorem orderedSKPathPressure_hasDerivAt (n : ℕ) (hn : 0<n) (b h b' h' : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (hb' : MonotoneOn b' (Icc (0:ℝ) 1)) (hh' : MonotoneOn h' (Icc (0:ℝ) 1))
    {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (fun s => orderedSKPathPressure n (affineNNPath b b' s) (affineNNPath h h' s) 0)
      (-(1/4:ℝ)*(∫ u in (0:ℝ)..1, ((b' u:ℝ)-(b u:ℝ))*
          orderedPathB n (affineNNPath b b' t) (affineNNPath h h' t) u)-
       (1/2:ℝ)*(∫ u in (0:ℝ)..1, ((h' u:ℝ)-(h u:ℝ))*
          orderedPathS n (affineNNPath b b' t) (affineNNPath h h' t) u)) t := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have he (s : ℝ) : affineClockPath (orderedPathClock n b h) (orderedPathClock n b' h') s=
      orderedPathClock n (affineNNPath b b' s) (affineNNPath h h' s) := by
    funext u i; cases i <;> rfl
  have hd := (pathDisorderPressure_hasDerivAt (uniformWeight_pos n) (orderedFeature n)
    (fun i => (orderedAmplitude n i)^2) (fun σ i => by
      simpa [orderedFeature_apply,Pi.single_apply] using orderedFeature_square n σ i)
    (orderedPathClock n b h) (orderedPathClock n b' h')
    (orderedPathClock_monotone n hb hh) (orderedPathClock_monotone n hb' hh') ht).div_const (n:ℝ)
  simp_rw [he] at hd
  rw [pathPressureRate_ordered n hn _ _ b h b' h'
    (affineNNPath_monotone b b' hb hb' t) (affineNNPath_monotone h h' hh hh' t) hb hh hb' hh'] at hd
  exact hd

end SKFluctuations

end

end OAI
