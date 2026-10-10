import Mathlib
import OAI.Probability.SKFluctuations.ClockPathPressureSup
import OAI.Probability.SKFluctuations.InverseConstraintQuantile

namespace OAI

/-! Ordered S K Rate Direction. -/

noncomputable section


namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators
attribute [local instance] Classical.propDecidable
local instance (n : ℕ) : DecidableEq (OrderedFeatureIndex n) := fun _ _ => Classical.propDecidable _

 theorem orderedPathPair_mul_integrable (n : ℕ) (hn : 0<n) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (P : Spin n → Spin n → ℝ) (K : ℝ → ℝ) (hK : IntervalIntegrable K volume 0 1) :
    IntervalIntegrable (fun u => K u*orderedPathPair n b h P u) volume 0 1 := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hφ (σ : Spin n) (i : OrderedFeatureIndex n) :
      |orderedFeature n σ (Pi.single i 1)|≤orderedAmplitude n i := by
    simpa [orderedFeature_apply,Pi.single_apply] using (orderedFeature_abs n σ i).le
  let A : ℝ := ∑ σ, ∑ τ, |P σ τ|
  have hA : 0≤A := Finset.sum_nonneg fun σ _ => Finset.sum_nonneg fun τ _ => abs_nonneg _
  have hP : ∀ σ τ, |P σ τ|≤A := by
    intro σ τ
    exact (Finset.single_le_sum (fun ρ _ => abs_nonneg (P σ ρ)) (Finset.mem_univ τ)).trans
      (Finset.single_le_sum (fun ρ _ => Finset.sum_nonneg fun η _ => abs_nonneg (P ρ η)) (Finset.mem_univ σ))
  exact pathPairMoment_mul_intervalIntegrable (uniformWeight_pos n) _ (orderedAmplitude n)
    (orderedAmplitude_nonneg n) hφ _ (orderedPathClock_monotone n hb hh) P hA hP K hK

 theorem pathPressureRate_ordered_direction (n : ℕ) (hn : 0<n) (b h : ℝ → ℝ≥0) (B H : ℝ → ℝ)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (hB : IntervalIntegrable B volume 0 1) (hH : IntervalIntegrable H volume 0 1) :
    pathPressureRate (uniformWeight n) (orderedFeature n) (orderedPathClock n b h)
      (fun u => Sum.elim (fun _ => H u) (fun _ => B u))/(n:ℝ)=
      -(1/4:ℝ)*(∫ u in (0:ℝ)..1, B u*orderedPathB n b h u)-
        (1/2:ℝ)*(∫ u in (0:ℝ)..1, H u*orderedPathS n b h u) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hk (u : ℝ) : featureKernel (orderedFeature n)
      (Sum.elim (fun _ => H u) (fun _ => B u))=
      fun σ τ => ((n:ℝ)/2*B u)*(orderedOverlap n σ τ)^2+
        ((n:ℝ)*H u)*orderedOverlap n σ τ := by
    funext σ τ
    simp only [featureKernel]
    have hs (σ : Spin n) (i : OrderedFeatureIndex n) :
        orderedFeature n σ (Pi.single i 1)=orderedFeatureCoefficient n σ i := by
      simp [orderedFeature_apply,Pi.single_apply]
    simp only [hs]
    rw [orderedCovariance n hn]
    ring
  have hφ (σ : Spin n) (i : OrderedFeatureIndex n) :
      |orderedFeature n σ (Pi.single i 1)|≤orderedAmplitude n i := by
    simpa [orderedFeature_apply,Pi.single_apply] using (orderedFeature_abs n σ i).le
  rw [pathPressureRate_integral_direction (uniformWeight_pos n) _ (orderedAmplitude n)
    (orderedAmplitude_nonneg n) hφ _ (orderedPathClock_monotone n hb hh) _
    (fun i => by cases i <;> assumption)]
  have he : (∫ u in (0:ℝ)..1, pathPairMoment (uniformWeight n) (orderedFeature n)
      (orderedPathClock n b h) (featureKernel (orderedFeature n)
        (Sum.elim (fun _ => H u) (fun _ => B u))) u)=
      ∫ u in (0:ℝ)..1, (n:ℝ)/2*(B u*orderedPathB n b h u)+
        (n:ℝ)*(H u*orderedPathS n b h u) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [] with u hu
    rw [uIoc_of_le (by norm_num : (0:ℝ)≤1)] at hu
    rw [hk]
    change orderedPathPair n b h _ u=_
    rw [orderedPathPair_linear n hn b h hb hh _ _ _ _ hu]
    dsimp [orderedPathB,orderedPathS]
    ring
  rw [he]
  change (-(1/2:ℝ)*(∫ u in (0:ℝ)..1, (n:ℝ)/2*(B u*
    orderedPathPair n b h (fun σ τ => (orderedOverlap n σ τ)^2) u)+(n:ℝ)*
    (H u*orderedPathPair n b h (orderedOverlap n) u)))/(n:ℝ)=_
  rw [intervalIntegral.integral_add
    ((orderedPathPair_mul_integrable n hn b h hb hh _ B hB).const_mul ((n:ℝ)/2))
    ((orderedPathPair_mul_integrable n hn b h hb hh _ H hH).const_mul (n:ℝ)),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  have hn0 : (n:ℝ)≠0 := ne_of_gt (Nat.cast_pos.mpr hn)
  dsimp only [orderedPathB,orderedPathS]
  field_simp
  ring

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators
attribute [local instance] Classical.propDecidable
local instance (n : ℕ) : DecidableEq (OrderedFeatureIndex n) := fun _ _ => Classical.propDecidable _

 theorem orderedSKPathPressure_hasDerivWithinAt_curve (n : ℕ) (hn : 0<n)
    (b h : ℝ → ℝ → ℝ≥0) (B H : ℝ → ℝ) (Cb Ch : ℝ) (s : Set ℝ)
    (hb0 : MonotoneOn (b 0) (Icc (0:ℝ) 1)) (hh0 : MonotoneOn (h 0) (Icc (0:ℝ) 1))
    (hb : ∀ᶠ t in 𝓝[s \ {0}] 0, MonotoneOn (b t) (Icc (0:ℝ) 1))
    (hh : ∀ᶠ t in 𝓝[s \ {0}] 0, MonotoneOn (h t) (Icc (0:ℝ) 1))
    (hCb : ∀ᶠ t in 𝓝[s \ {0}] 0, ∀ u ∈ Icc (0:ℝ) 1, |(b t u:ℝ)-(b 0 u:ℝ)|≤|t| *Cb)
    (hCh : ∀ᶠ t in 𝓝[s \ {0}] 0, ∀ u ∈ Icc (0:ℝ) 1, |(h t u:ℝ)-(h 0 u:ℝ)|≤|t| *Ch)
    (hB : IntervalIntegrable B volume 0 1) (hH : IntervalIntegrable H volume 0 1)
    (hBl : ∀ᵐ u ∂volume, u ∈ Ioc (0:ℝ) 1 →
      Tendsto (fun t => ((b t u:ℝ)-(b 0 u:ℝ))/t) (𝓝[s \ {0}] 0) (𝓝 (B u)))
    (hHl : ∀ᵐ u ∂volume, u ∈ Ioc (0:ℝ) 1 →
      Tendsto (fun t => ((h t u:ℝ)-(h 0 u:ℝ))/t) (𝓝[s \ {0}] 0) (𝓝 (H u))) :
    HasDerivWithinAt (fun t => orderedSKPathPressure n (b t) (h t) 0)
      (-(1/4:ℝ)*(∫ u in (0:ℝ)..1, B u*orderedPathB n (b 0) (h 0) u)-
        (1/2:ℝ)*(∫ u in (0:ℝ)..1, H u*orderedPathS n (b 0) (h 0) u)) s 0 := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hd := (pathDisorderPressure_hasDerivWithinAt_curve (uniformWeight_pos n)
    (orderedFeature n) (fun i => (orderedAmplitude n i)^2) (orderedAmplitude n)
    (Sum.elim (fun _ => Ch) (fun _ => Cb))
    (fun σ i => by simpa [orderedFeature_apply,Pi.single_apply] using orderedFeature_square n σ i)
    (orderedAmplitude_nonneg n)
    (fun σ i => by simpa [orderedFeature_apply,Pi.single_apply] using (orderedFeature_abs n σ i).le)
    (fun t => orderedPathClock n (b t) (h t))
    (fun u => Sum.elim (fun _ => H u) (fun _ => B u)) s
    (orderedPathClock_monotone n hb0 hh0)
    (by filter_upwards [hb,hh] with t hbt hht; exact orderedPathClock_monotone n hbt hht)
    (by
      filter_upwards [hCb,hCh] with t hbt hht u hu i
      cases i with
      | inl i => exact hht u hu
      | inr i => exact hbt u hu)
    (by intro i; cases i <;> assumption)).div_const (n:ℝ)
  rw [pathPressureRate_ordered_direction n hn _ _ B H hb0 hh0 hB hH] at hd
  exact hd

end SKFluctuations

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set
open scoped Topology NNReal

 theorem curve_interval_integral_hasDerivWithinAt {a b A : ℝ} {s : Set ℝ}
    {q : ℝ → ℝ → ℝ} {K : ℝ → ℝ}
    (hq0 : IntervalIntegrable (q 0) volume a b)
    (hq : ∀ᶠ t in 𝓝[s \ {0}] 0, IntervalIntegrable (q t) volume a b)
    (hA : ∀ᶠ t in 𝓝[s \ {0}] 0, ∀ᵐ u, u ∈ uIoc a b → |q t u-q 0 u| ≤ |t| *A)
    (hK : ∀ᵐ u, u ∈ uIoc a b → HasDerivWithinAt (fun t => q t u) (K u) s 0) :
    HasDerivWithinAt (fun t => ∫ u in a..b, q t u) (∫ u in a..b, K u) s 0 := by
  have hne : ∀ᶠ t in 𝓝[s \ {0}] 0, t≠0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ht.2
  have hlim : Tendsto (fun t => ∫ u in a..b, (q t u-q 0 u)/t)
      (𝓝[s \ {0}] 0) (𝓝 (∫ u in a..b, K u)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => A)
    · filter_upwards [hq] with t ht
      exact ((ht.sub hq0).div_const t).def'.aestronglyMeasurable
    · filter_upwards [hA,hne] with t ht ht0
      filter_upwards [ht] with u hu hui
      rw [Real.norm_eq_abs,abs_div,div_le_iff₀ (abs_pos.mpr ht0)]
      simpa only [mul_comm] using hu hui
    · exact intervalIntegrable_const
    · filter_upwards [hK] with u hu hui
      have hh := (hasDerivWithinAt_iff_tendsto_slope.mp (hu hui))
      have hs : slope (fun t => q t u) 0=fun t => (q t u-q 0 u)/t := by
        funext t; rw [slope_def_field,sub_zero]
      rwa [hs] at hh
  rw [hasDerivWithinAt_iff_tendsto_slope]
  apply hlim.congr'
  filter_upwards [hq] with t ht
  rw [slope_def_field,sub_zero,intervalIntegral.integral_div,
    intervalIntegral.integral_sub ht hq0]

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 def realOrderedSKPathPressure (n : ℕ) (b h : ℝ → ℝ)
    (x : OrderedFeatureIndex n → ℝ) : ℝ :=
  orderedSKPathPressure n (fun u => Real.toNNReal (b u)) (fun u => Real.toNNReal (h u)) x

 theorem toNNReal_monotoneOn {b : ℝ → ℝ} (hb : MonotoneOn b (Icc (0:ℝ) 1)) :
    MonotoneOn (fun u => Real.toNNReal (b u)) (Icc (0:ℝ) 1) := by
  intro u hu v hv huv
  exact Real.toNNReal_mono (hb hu hv huv)

 theorem sampled_orderedSKPressure_eq (n : ℕ) (b h : ℝ → ℝ)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (hb0 : 0≤b 0) (hh0 : 0≤h 0) (as : List PositiveMass) (ha : MassOrdered 0 as)
    (x : OrderedFeatureIndex n → ℝ) :
    orderedSKPressure n as (fun j => b (partitionPoint 0 as j))
        (fun j => h (partitionPoint 0 as j)) x =
      sampledDisorderPressure (uniformWeight n) (orderedFeature n)
        (fun i => (orderedAmplitude n i)^2)
        (orderedPathClock n (fun u => Real.toNNReal (b u)) (fun u => Real.toNNReal (h u))) as x/(n:ℝ) := by
  rw [sampledDisorderPressure_eq _ _ _ _
    (orderedPathClock_monotone n (toNNReal_monotoneOn hb) (toNNReal_monotoneOn hh)) as ha]
  unfold orderedSKPressure
  congr 2
  funext j i
  have hj := partitionPoint_mem as ha j
  have hb' : 0≤b (partitionPoint 0 as j) := hb0.trans (hb (by norm_num) hj hj.1)
  have hh' : 0≤h (partitionPoint 0 as j) := hh0.trans (hh (by norm_num) hj hj.1)
  cases i <;> simp [orderedClock,orderedPathClock,hb',hh']

 theorem orderedSKPressure_samples_tendsto (n : ℕ) (hn : 0<n) (b h : ℝ → ℝ)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (hb0 : 0≤b 0) (hh0 : 0≤h 0) (x : OrderedFeatureIndex n → ℝ) :
    Tendsto (fun k => orderedSKPressure n (uniformMasses k)
      (fun j => b (partitionPoint 0 (uniformMasses k) j))
      (fun j => h (partitionPoint 0 (uniformMasses k) j)) x) atTop
      (𝓝 (realOrderedSKPathPressure n b h x)) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have ht := sampledDisorderPressure_tendsto (uniformWeight_pos n) (orderedFeature n)
    (fun i => (orderedAmplitude n i)^2) (orderedAmplitude n) (orderedFeature_square n)
    (fun i σ => (orderedFeature_abs n σ i).le)
    (orderedPathClock n (fun u => Real.toNNReal (b u)) (fun u => Real.toNNReal (h u)))
    (orderedPathClock_monotone n (toNNReal_monotoneOn hb) (toNNReal_monotoneOn hh)) x
  have he (k : ℕ) := sampled_orderedSKPressure_eq n b h hb hh hb0 hh0
    (uniformMasses k) (uniformMasses_ordered k) x
  simp_rw [he]
  exact ht.div_const (n:ℝ)

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

 theorem realOrderedSKPathPressure_hasDerivWithinAt_curve (n : ℕ) (hn : 0<n)
    (b h : ℝ → ℝ → ℝ) (B H : ℝ → ℝ) (Cb Ch : ℝ) (s : Set ℝ)
    (hb0 : MonotoneOn (b 0) (Icc (0:ℝ) 1)) (hh0 : MonotoneOn (h 0) (Icc (0:ℝ) 1))
    (hb0n : ∀ u ∈ Icc (0:ℝ) 1, 0 ≤ b 0 u) (hh0n : ∀ u ∈ Icc (0:ℝ) 1, 0 ≤ h 0 u)
    (hb : ∀ᶠ t in 𝓝[s \ {0}] 0, MonotoneOn (b t) (Icc (0:ℝ) 1))
    (hh : ∀ᶠ t in 𝓝[s \ {0}] 0, MonotoneOn (h t) (Icc (0:ℝ) 1))
    (hbn : ∀ᶠ t in 𝓝[s \ {0}] 0, ∀ u ∈ Icc (0:ℝ) 1, 0 ≤ b t u)
    (hhn : ∀ᶠ t in 𝓝[s \ {0}] 0, ∀ u ∈ Icc (0:ℝ) 1, 0 ≤ h t u)
    (hCb : ∀ᶠ t in 𝓝[s \ {0}] 0, ∀ u ∈ Icc (0:ℝ) 1, |b t u-b 0 u| ≤ |t| *Cb)
    (hCh : ∀ᶠ t in 𝓝[s \ {0}] 0, ∀ u ∈ Icc (0:ℝ) 1, |h t u-h 0 u| ≤ |t| *Ch)
    (hB : IntervalIntegrable B volume 0 1) (hH : IntervalIntegrable H volume 0 1)
    (hBl : ∀ᵐ u, u ∈ Ioc (0:ℝ) 1 → HasDerivWithinAt (fun t => b t u) (B u) s 0)
    (hHl : ∀ᵐ u, u ∈ Ioc (0:ℝ) 1 → HasDerivWithinAt (fun t => h t u) (H u) s 0) :
    HasDerivWithinAt (fun t => realOrderedSKPathPressure n (b t) (h t) 0)
      (-(1/4:ℝ)*(∫ u in (0:ℝ)..1, B u*orderedPathB n (fun u => (b 0 u).toNNReal) (fun u => (h 0 u).toNNReal) u)-
        (1/2:ℝ)*(∫ u in (0:ℝ)..1, H u*orderedPathS n (fun u => (b 0 u).toNNReal) (fun u => (h 0 u).toNNReal) u)) s 0 := by
  apply orderedSKPathPressure_hasDerivWithinAt_curve n hn _ _ B H Cb Ch s
  · intro u hu v hv huv; exact Real.toNNReal_mono (hb0 hu hv huv)
  · intro u hu v hv huv; exact Real.toNNReal_mono (hh0 hu hv huv)
  · filter_upwards [hb] with t ht u hu v hv huv; exact Real.toNNReal_mono (ht hu hv huv)
  · filter_upwards [hh] with t ht u hu v hv huv; exact Real.toNNReal_mono (ht hu hv huv)
  · filter_upwards [hCb,hbn] with t ht htn u hu
    simpa only [Real.coe_toNNReal _ (htn u hu),Real.coe_toNNReal _ (hb0n u hu)] using ht u hu
  · filter_upwards [hCh,hhn] with t ht htn u hu
    simpa only [Real.coe_toNNReal _ (htn u hu),Real.coe_toNNReal _ (hh0n u hu)] using ht u hu
  · exact hB
  · exact hH
  · filter_upwards [hBl] with u hu hui
    have he : (fun t => (((b t u).toNNReal:ℝ)-((b 0 u).toNNReal:ℝ))/t)=ᶠ[𝓝[s \ {0}] 0]
        fun t => (b t u-b 0 u)/t := by
      filter_upwards [hbn] with t ht
      rw [Real.coe_toNNReal _ (ht u ⟨hui.1.le,hui.2⟩),Real.coe_toNNReal _ (hb0n u ⟨hui.1.le,hui.2⟩)]
    apply Tendsto.congr' he.symm
    simpa only [slope_fun_def_field,sub_zero] using hasDerivWithinAt_iff_tendsto_slope.mp (hu hui)
  · filter_upwards [hHl] with u hu hui
    have he : (fun t => (((h t u).toNNReal:ℝ)-((h 0 u).toNNReal:ℝ))/t)=ᶠ[𝓝[s \ {0}] 0]
        fun t => (h t u-h 0 u)/t := by
      filter_upwards [hhn] with t ht
      rw [Real.coe_toNNReal _ (ht u ⟨hui.1.le,hui.2⟩),Real.coe_toNNReal _ (hh0n u ⟨hui.1.le,hui.2⟩)]
    apply Tendsto.congr' he.symm
    simpa only [slope_fun_def_field,sub_zero] using hasDerivWithinAt_iff_tendsto_slope.mp (hu hui)

end SKFluctuations

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 theorem partitionSum_error {q : ℝ → ℝ} (hq : MonotoneOn q (Icc (0:ℝ) 1))
    (as : List PositiveMass) (ha : MassOrdered 0 as) {h : ℝ} (hm : PartitionMesh h 0 as) :
    |massStepSum as 0 (fun j => q (partitionPoint 0 as j))-(∫ u in (0:ℝ)..1, q u)| ≤
      h*(q 1-q 0) := by
  have hi : IntervalIntegrable q volume 0 1 :=
    (show MonotoneOn q (uIcc (0:ℝ) 1) by simpa using hq).intervalIntegrable
  have hs := partitionSample_intervalIntegrable q 0 as 0 1
  have he : (fun j => q (partitionPoint 0 as j))=partitionValues q 0 as := by
    funext j; exact (partitionValues_point q 0 as j).symm
  rw [he,← massStepFunction_integral as 0 _ ha]
  change |(∫ u in (0:ℝ)..1, partitionSample q 0 as u)-(∫ u in (0:ℝ)..1, q u)| ≤ _
  rw [← intervalIntegral.integral_sub hs hi]
  refine (intervalIntegral.abs_integral_le_integral_abs (by norm_num)).trans ?_
  simp_rw [abs_sub_comm (partitionSample q 0 as _)]
  exact partitionSample_l1_error hq as ha hm

 theorem partitionSum_tendsto {q : ℝ → ℝ} (hq : MonotoneOn q (Icc (0:ℝ) 1)) :
    Tendsto (fun k => massStepSum (uniformMasses k) 0
      (fun j => q (partitionPoint 0 (uniformMasses k) j))) atTop (𝓝 (∫ u in (0:ℝ)..1, q u)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [Real.norm_eq_abs]
  apply squeeze_zero (fun _ => abs_nonneg _) (fun k =>
    partitionSum_error hq (uniformMasses k) (uniformMasses_ordered k) (uniformMasses_mesh k))
  simpa using uniformMasses_mesh_tendsto.mul_const (q 1-q 0)

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 def pathCompensatedPressure (n : ℕ) (b h e r : ℝ → ℝ)
    (x : OrderedFeatureIndex n → ℝ) : ℝ :=
  realOrderedSKPathPressure n (fun u => b u-e u) (fun u => h u+e u*r u) x+
    (1/4:ℝ)*(∫ u in (0:ℝ)..1, e u*(r u)^2)

 theorem comp_partitionPoint_monotone {f : ℝ → ℝ} (hf : MonotoneOn f (Icc (0:ℝ) 1))
    (as : List PositiveMass) (ha : MassOrdered 0 as) :
    Monotone (fun j => f (partitionPoint 0 as j)) := by
  intro i j hij
  exact hf (partitionPoint_mem as ha i) (partitionPoint_mem as ha j) (partitionPoint_mono as ha hij)

 theorem finiteCompensatedPressure_tendsto_path (n : ℕ) (hn : 0<n) (b h e r : ℝ → ℝ)
    (hb : MonotoneOn (fun u => b u-e u) (Icc (0:ℝ) 1))
    (hh : MonotoneOn (fun u => h u+e u*r u) (Icc (0:ℝ) 1))
    (hb0 : 0≤b 0-e 0) (hh0 : 0≤h 0+e 0*r 0)
    (hp : MonotoneOn (fun u => e u*(r u)^2) (Icc (0:ℝ) 1)) (x : OrderedFeatureIndex n → ℝ) :
    Tendsto (fun k => finiteCompensatedPressure n (uniformMasses k)
      (fun j => b (partitionPoint 0 (uniformMasses k) j))
      (fun j => h (partitionPoint 0 (uniformMasses k) j))
      (fun j => e (partitionPoint 0 (uniformMasses k) j))
      (fun j => r (partitionPoint 0 (uniformMasses k) j)) x) atTop
      (𝓝 (pathCompensatedPressure n b h e r x)) := by
  exact (orderedSKPressure_samples_tendsto n hn (fun u => b u-e u) (fun u => h u+e u*r u)
    hb hh hb0 hh0 x).add ((partitionSum_tendsto hp).const_mul (1/4:ℝ))

 theorem pathCompensatedPressure_mono (n : ℕ) (hn : 0<n) (b h e e' r : ℝ → ℝ)
    (he : ∀ u ∈ Icc (0:ℝ) 1, e u≤e' u)
    (hb : MonotoneOn (fun u => b u-e u) (Icc (0:ℝ) 1))
    (hh : MonotoneOn (fun u => h u+e u*r u) (Icc (0:ℝ) 1))
    (hb' : MonotoneOn (fun u => b u-e' u) (Icc (0:ℝ) 1))
    (hh' : MonotoneOn (fun u => h u+e' u*r u) (Icc (0:ℝ) 1))
    (hb0 : 0≤b 0-e 0) (hh0 : 0≤h 0+e 0*r 0)
    (hb0' : 0≤b 0-e' 0) (hh0' : 0≤h 0+e' 0*r 0)
    (hp : MonotoneOn (fun u => e u*(r u)^2) (Icc (0:ℝ) 1))
    (hp' : MonotoneOn (fun u => e' u*(r u)^2) (Icc (0:ℝ) 1))
    (x : OrderedFeatureIndex n → ℝ) :
    pathCompensatedPressure n b h e r x≤pathCompensatedPressure n b h e' r x := by
  apply le_of_tendsto_of_tendsto (finiteCompensatedPressure_tendsto_path n hn b h e r hb hh hb0 hh0 hp x)
    (finiteCompensatedPressure_tendsto_path n hn b h e' r hb' hh' hb0' hh0' hp' x)
  apply Eventually.of_forall
  intro k
  have ha := uniformMasses_ordered k
  apply finiteCompensatedPressure_mono n hn (uniformMasses k) ha.pairwise ha.members_le_one
    (fun j => b (partitionPoint 0 (uniformMasses k) j))
    (fun j => h (partitionPoint 0 (uniformMasses k) j))
    (fun j => e (partitionPoint 0 (uniformMasses k) j))
    (fun j => e' (partitionPoint 0 (uniformMasses k) j))
    (fun j => r (partitionPoint 0 (uniformMasses k) j))
  · exact fun j _ => he _ (partitionPoint_mem _ ha j)
  · exact comp_partitionPoint_monotone hb _ ha
  · exact comp_partitionPoint_monotone hh _ ha
  · exact comp_partitionPoint_monotone hb' _ ha
  · exact comp_partitionPoint_monotone hh' _ ha
  · simpa [partitionPoint] using hb0
  · simpa [partitionPoint] using hh0
  · simpa [partitionPoint] using hb0'
  · simpa [partitionPoint] using hh0'

 theorem pathCompensatedPressure_lower (n : ℕ) (hn : 0<n) (b h e r : ℝ → ℝ)
    (he : ∀ u ∈ Icc (0:ℝ) 1, 0≤e u)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (hb0 : 0≤b 0) (hh0 : 0≤h 0)
    (hb' : MonotoneOn (fun u => b u-e u) (Icc (0:ℝ) 1))
    (hh' : MonotoneOn (fun u => h u+e u*r u) (Icc (0:ℝ) 1))
    (hb0' : 0≤b 0-e 0) (hh0' : 0≤h 0+e 0*r 0)
    (hp : MonotoneOn (fun u => e u*(r u)^2) (Icc (0:ℝ) 1)) (x : OrderedFeatureIndex n → ℝ) :
    realOrderedSKPathPressure n b h x≤pathCompensatedPressure n b h e r x := by
  have hmono := pathCompensatedPressure_mono n hn b h (fun _ => 0) e r he
    (by simpa using hb) (by simpa using hh) hb' hh'
    (by simpa using hb0) (by simpa using hh0) hb0' hh0'
    (by intro u hu v hv huv; simp) hp x
  simpa only [pathCompensatedPressure,sub_zero,zero_mul,add_zero,intervalIntegral.integral_zero,
    mul_zero] using hmono

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

 theorem compensated_curve_derivative (n : ℕ) (hn : 0<n)
    (b h : ℝ → ℝ) (e q c : ℝ → ℝ → ℝ) (E Q K : ℝ → ℝ)
    (Cb Ch Cc : ℝ) (s : Set ℝ)
    (hb0 : MonotoneOn (fun u => b u-e 0 u) (Icc (0:ℝ) 1))
    (hh0 : MonotoneOn (fun u => h u+q 0 u) (Icc (0:ℝ) 1))
    (hb0n : ∀ u ∈ Icc (0:ℝ) 1, 0 ≤ b u-e 0 u)
    (hh0n : ∀ u ∈ Icc (0:ℝ) 1, 0 ≤ h u+q 0 u)
    (hb : ∀ᶠ t in 𝓝[s \ {0}] 0, MonotoneOn (fun u => b u-e t u) (Icc (0:ℝ) 1))
    (hh : ∀ᶠ t in 𝓝[s \ {0}] 0, MonotoneOn (fun u => h u+q t u) (Icc (0:ℝ) 1))
    (hbn : ∀ᶠ t in 𝓝[s \ {0}] 0, ∀ u ∈ Icc (0:ℝ) 1, 0 ≤ b u-e t u)
    (hhn : ∀ᶠ t in 𝓝[s \ {0}] 0, ∀ u ∈ Icc (0:ℝ) 1, 0 ≤ h u+q t u)
    (hCb : ∀ᶠ t in 𝓝[s \ {0}] 0, ∀ u ∈ Icc (0:ℝ) 1, |e t u-e 0 u| ≤ |t| *Cb)
    (hCh : ∀ᶠ t in 𝓝[s \ {0}] 0, ∀ u ∈ Icc (0:ℝ) 1, |q t u-q 0 u| ≤ |t| *Ch)
    (hCc : ∀ᶠ t in 𝓝[s \ {0}] 0, ∀ u ∈ Icc (0:ℝ) 1, |c t u-c 0 u| ≤ |t| *Cc)
    (hE : IntervalIntegrable E volume 0 1) (hQ : IntervalIntegrable Q volume 0 1)
    (hK : IntervalIntegrable K volume 0 1)
    (hc0 : IntervalIntegrable (c 0) volume 0 1)
    (hc : ∀ᶠ t in 𝓝[s \ {0}] 0, IntervalIntegrable (c t) volume 0 1)
    (hEl : ∀ᵐ u, u ∈ Ioc (0:ℝ) 1 → HasDerivWithinAt (fun t => e t u) (E u) s 0)
    (hQl : ∀ᵐ u, u ∈ Ioc (0:ℝ) 1 → HasDerivWithinAt (fun t => q t u) (Q u) s 0)
    (hKl : ∀ᵐ u, u ∈ Ioc (0:ℝ) 1 → HasDerivWithinAt (fun t => c t u) (K u) s 0) :
    HasDerivWithinAt (fun t => realOrderedSKPathPressure n (fun u => b u-e t u)
        (fun u => h u+q t u) 0+(1/4:ℝ)*(∫ u in (0:ℝ)..1, c t u))
      ((1/4:ℝ)*(∫ u in (0:ℝ)..1,
        E u*orderedPathB n (fun u => (b u-e 0 u).toNNReal) (fun u => (h u+q 0 u).toNNReal) u-
        2*(Q u*orderedPathS n (fun u => (b u-e 0 u).toNNReal) (fun u => (h u+q 0 u).toNNReal) u)+K u)) s 0 := by
  have hp := realOrderedSKPathPressure_hasDerivWithinAt_curve n hn
    (fun t u => b u-e t u) (fun t u => h u+q t u) (fun u => -E u) Q Cb Ch s
    hb0 hh0 hb0n hh0n hb hh hbn hhn
    (by
      filter_upwards [hCb] with t ht u hu
      have he : b u-e t u-(b u-e 0 u)=-(e t u-e 0 u) := by ring
      rw [he,abs_neg]; exact ht u hu)
    (by
      filter_upwards [hCh] with t ht u hu
      have he : h u+q t u-(h u+q 0 u)=q t u-q 0 u := by ring
      rw [he]; exact ht u hu)
    hE.neg hQ
    (by
      filter_upwards [hEl] with u hu hi
      exact (hu hi).const_sub (b u))
    (by
      filter_upwards [hQl] with u hu hi
      exact (hu hi).const_add (h u))
  have hc' := curve_interval_integral_hasDerivWithinAt hc0 hc
    (by
      filter_upwards [hCc] with t ht
      exact Eventually.of_forall fun u hu => ht u ⟨(by simpa using hu.1.le),(by simpa using hu.2)⟩)
    (by simpa only [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hKl)
  have hb' : MonotoneOn (fun u => (b u-e 0 u).toNNReal) (Icc (0:ℝ) 1) :=
    fun u hu v hv huv => Real.toNNReal_mono (hb0 hu hv huv)
  have hh' : MonotoneOn (fun u => (h u+q 0 u).toNNReal) (Icc (0:ℝ) 1) :=
    fun u hu v hv huv => Real.toNNReal_mono (hh0 hu hv huv)
  have hiE := orderedPathPair_mul_integrable n hn _ _ hb' hh'
    (fun σ τ => (orderedOverlap n σ τ)^2) E hE
  have hiQ := orderedPathPair_mul_integrable n hn _ _ hb' hh' (orderedOverlap n) Q hQ
  convert hp.add (hc'.const_mul (1/4:ℝ)) using 1; try rfl
  symm
  change -(1/4:ℝ)*(∫ u in (0:ℝ)..1, -E u*orderedPathB n _ _ u)-
    (1/2:ℝ)*(∫ u in (0:ℝ)..1, Q u*orderedPathS n _ _ u)+(1/4:ℝ)*(∫ u in (0:ℝ)..1, K u)=_
  simp_rw [neg_mul,intervalIntegral.integral_neg]
  simp only [orderedPathB,orderedPathS]
  rw [intervalIntegral.integral_add (hiE.sub (hiQ.const_mul 2)) hK,
    intervalIntegral.integral_sub hiE (hiQ.const_mul 2),intervalIntegral.integral_const_mul]
  ring

 theorem comparison_gradient_algebra (e de r S B v : ℝ) (hr : r≠0) (he : e≠0) :
    de*v*B-2*((de*r+e)*v*S)+(de*r^2+2*e*r)*v=
      e*((2-(-r*de/e))*r-2*(1-(-r*de/e))*S-(-r*de/e)*B/r)*v := by
  field_simp
  ring

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

 theorem radius_curve_derivative (n : ℕ) (hn : 0<n) (b h : ℝ → ℝ)
    {u₀ a z A : ℝ} (hA : 0 ≤ A) {s : Set ℝ}
    (F₀ F₁ F₂ D₀ D₁ D₂ V : ℝ → ℝ) (R : ℝ → ℝ → ℝ)
    (_hF₀ : Continuous F₀) (_hF₁ : Continuous F₁) (hF₂ : Continuous F₂)
    (hD₀ : ContinuousOn D₀ (Icc a z)) (hD₁ : ContinuousOn D₁ (Icc a z))
    (hD₂ : ContinuousOn D₂ (Icc a z))
    (hd₀ : ∀ x ∈ Icc a z, HasDerivAt F₀ (D₀ x) x)
    (hd₁ : ∀ x ∈ Icc a z, HasDerivAt F₁ (D₁ x) x)
    (hd₂ : ∀ x ∈ Icc a z, HasDerivAt F₂ (D₂ x) x)
    {K₀ K₁ K₂ : ℝ≥0}
    (hl₀ : LipschitzOnWith K₀ F₀ (Icc a z)) (hl₁ : LipschitzOnWith K₁ F₁ (Icc a z))
    (hl₂ : LipschitzOnWith K₂ F₂ (Icc a z))
    (hR : ∀ t, Continuous (R t)) (hRm : ∀ t u, R t u ∈ Icc a z)
    (hRb : ∀ᶠ t in 𝓝[s \ {0}] 0, ∀ u ∈ Icc u₀ 1, |R t u-R 0 u| ≤ A*|t|)
    (hRd : ∀ᵐ u, u ∈ Icc u₀ 1 → HasDerivWithinAt (fun t => R t u) (V u) s 0)
    (hV : Measurable V) (hVb : ∀ᵐ u, u ∈ Icc u₀ 1 → |V u| ≤ A)
    (hb0 : MonotoneOn (fun u => b u-omittedCurve u₀ F₀ R 0 u) (Icc (0:ℝ) 1))
    (hh0 : MonotoneOn (fun u => h u+omittedCurve u₀ F₁ R 0 u) (Icc (0:ℝ) 1))
    (hbn0 : ∀ u ∈ Icc (0:ℝ) 1, 0 ≤ b u-omittedCurve u₀ F₀ R 0 u)
    (hhn0 : ∀ u ∈ Icc (0:ℝ) 1, 0 ≤ h u+omittedCurve u₀ F₁ R 0 u)
    (hb : ∀ᶠ t in 𝓝[s \ {0}] 0, MonotoneOn (fun u => b u-omittedCurve u₀ F₀ R t u) (Icc (0:ℝ) 1))
    (hh : ∀ᶠ t in 𝓝[s \ {0}] 0, MonotoneOn (fun u => h u+omittedCurve u₀ F₁ R t u) (Icc (0:ℝ) 1))
    (hbn : ∀ᶠ t in 𝓝[s \ {0}] 0, ∀ u ∈ Icc (0:ℝ) 1, 0 ≤ b u-omittedCurve u₀ F₀ R t u)
    (hhn : ∀ᶠ t in 𝓝[s \ {0}] 0, ∀ u ∈ Icc (0:ℝ) 1, 0 ≤ h u+omittedCurve u₀ F₁ R t u) :
    HasDerivWithinAt (fun t => realOrderedSKPathPressure n
        (fun u => b u-omittedCurve u₀ F₀ R t u) (fun u => h u+omittedCurve u₀ F₁ R t u) 0+
        (1/4:ℝ)*(∫ u in (0:ℝ)..1, omittedCurve u₀ F₂ R t u))
      ((1/4:ℝ)*(∫ u in (0:ℝ)..1,
        (if u₀ ≤ u then D₀ (R 0 u)*V u else 0)*
          orderedPathB n (fun u => (b u-omittedCurve u₀ F₀ R 0 u).toNNReal)
            (fun u => (h u+omittedCurve u₀ F₁ R 0 u).toNNReal) u-
        2*((if u₀ ≤ u then D₁ (R 0 u)*V u else 0)*
          orderedPathS n (fun u => (b u-omittedCurve u₀ F₀ R 0 u).toNNReal)
            (fun u => (h u+omittedCurve u₀ F₁ R 0 u).toNNReal) u)+
        (if u₀ ≤ u then D₂ (R 0 u)*V u else 0))) s 0 := by
  apply compensated_curve_derivative n hn b h (omittedCurve u₀ F₀ R) (omittedCurve u₀ F₁ R)
    (omittedCurve u₀ F₂ R) _ _ _ ((K₀:ℝ)*A) ((K₁:ℝ)*A) ((K₂:ℝ)*A) s
    hb0 hh0 hbn0 hhn0 hb hh hbn hhn
  · exact hRb.mono fun t ht => omittedCurve_displacement hA hl₀ hRm ht
  · exact hRb.mono fun t ht => omittedCurve_displacement hA hl₁ hRm ht
  · exact hRb.mono fun t ht => omittedCurve_displacement hA hl₂ hRm ht
  · exact omittedCurve_rate_integrable hD₀ (hR 0) (hRm 0) hV hA hVb
  · exact omittedCurve_rate_integrable hD₁ (hR 0) (hRm 0) hV hA hVb
  · exact omittedCurve_rate_integrable hD₂ (hR 0) (hRm 0) hV hA hVb
  · exact omittedCurve_integrable hF₂ hR hRm 0
  · exact Eventually.of_forall fun t => omittedCurve_integrable hF₂ hR hRm t
  · exact omittedCurve_hasDerivWithinAt hd₀ hRm hRd
  · exact omittedCurve_hasDerivWithinAt hd₁ hRm hRd
  · exact omittedCurve_hasDerivWithinAt hd₂ hRm hRd

end SKFluctuations

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set
open scoped Topology NNReal

section
variable {r₀ u₀ c T B : ℝ} {k M ψ : ℝ → ℝ}
variable (hr : r₀ ≤ 1) (hu : u₀ ∈ Icc (0:ℝ) 1) (hc : 0<c)
variable (hk : ContinuousOn k (Icc r₀ 1)) (hkc : ∀ r ∈ Icc r₀ 1, c ≤ k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1) (hMc : Continuous M)
variable (α : inverseIntegralConstraints r₀ u₀ k M)
variable (hfeas : ∀ t ∈ Icc (0:ℝ) T,
  sourceInverseConstraints r₀ u₀ k M (fun r => α.val.val r+t*ψ r))

 theorem source_velocity_measurable (hψ : ContinuousOn ψ (Icc r₀ 1)) :
    Measurable (fun u => -ψ (sourceForwardCurve hr hu hc hk hkc hm hM hMc α hfeas 0 u)/
      deriv α.val.val (sourceForwardCurve hr hu hc hk hkc hm hM hMc α hfeas 0 u)) := by
  exact inverse_velocity_measurable hψ
    (sourceForwardCurve_continuous hr hu hc hk hkc hm hM hMc α hfeas 0)
    (sourceForwardCurve_mem hr hu hc hk hkc hm hM hMc α hfeas 0)

 theorem source_velocity_bound (hT : 0 ≤ T) (hB : 0 ≤ B)
    (hψb : ∀ r ∈ Icc r₀ 1, |ψ r| ≤ B) :
    ∀ᵐ u, u ∈ Icc u₀ 1 →
      |-ψ (sourceForwardCurve hr hu hc hk hkc hm hM hMc α hfeas 0 u)/
        deriv α.val.val (sourceForwardCurve hr hu hc hk hkc hm hM hMc α hfeas 0 u)| ≤ B/c := by
  let R := sourceForwardCurve hr hu hc hk hkc hm hM hMc α hfeas 0
  have hα := inverseIntegralConstraints_lipschitz hm hM α.property
  have hd : ∀ᵐ r, r ∈ Icc r₀ 1 → c ≤ deriv α.val.val r := by
    have hl := (lipschitz_ae_deriv_lower_iff hr hα hk).mpr
      (fun x hx y hy hxy => (α.property.2.2 x hx y hy hxy).1)
    exact hl.mono fun r hr' hri => (hkc r hri).trans (hr' hri)
  have hp := ae_inverse_pullback hα
    (fun u (_ : u ∈ Icc u₀ 1) => sourceForwardCurve_mem hr hu hc hk hkc hm hM hMc α hfeas 0 u)
    (fun u hu' => sourceForwardCurve_initial hr hu hc hk hkc hm hM hMc α hfeas hT hu') hd
  filter_upwards [hp] with u hu' hui
  have hd' := hu' hui
  rw [abs_div,abs_neg,abs_of_pos (hc.trans_le hd')]
  exact (div_le_div_of_nonneg_right
    (hψb _ (sourceForwardCurve_mem hr hu hc hk hkc hm hM hMc α hfeas 0 u)) (hc.le.trans hd')).trans
    (div_le_div_of_nonneg_left hB hc hd')

 theorem sourceForwardCurve_initial_eq (hT : 0 ≤ T) (u : ℝ) :
    sourceForwardCurve hr hu hc hk hkc hm hM hMc α hfeas 0 u=
      (constrainedQuantile hr hc hk hkc hm hM α (projIcc u₀ 1 hu.2 u)).val := by
  apply (inverseConstraint_strictMonoOn hc hk hkc α.property).injOn
    (sourceForwardCurve_mem hr hu hc hk hkc hm hM hMc α hfeas 0 u)
    (constrainedQuantile hr hc hk hkc hm hM α (projIcc u₀ 1 hu.2 u)).property
  rw [constrainedQuantile_spec]
  have he := sourceForwardCurve_initial hr hu hc hk hkc hm hM hMc α hfeas hT
    (projIcc u₀ 1 hu.2 u).property
  simpa only [sourceForwardCurve,projIcc_val] using he

end
end SKFluctuations.Hierarchy

end

end OAI
