import Mathlib
import OAI.Analysis.CoulombRadii.Packets.BandOscillation
import OAI.Analysis.CoulombRadii.RandomFields.PosteriorCount
import OAI.Analysis.CoulombRadii.Packets.PacketBandGeometry
import OAI.Analysis.CoulombRadii.RandomFields.PosteriorSpatialCap
import OAI.Analysis.CoulombRadii.Packets.NormalizedBandModulus

namespace OAI

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical SchwartzMap
noncomputable section
namespace NeutralAtom

theorem physical_posterior_band_event (g : 𝓢(Position,ℝ))
    (hg : ∀ z,1 < ‖z‖ → g z=0) :
    ∃ B D : ℝ,0 ≤ B ∧ 0 ≤ D ∧
    ∀ {n J : ℕ} (ν : Measure (Configuration n)) [IsProbabilityMeasure ν],
    ∀ {c r₀ s r L : ℝ},0 < c → 0 < r₀ → 0 < s → 0 < r → 1 ≤ L → r₀ ≤ r → r ≤ s →
    c*(1+packetExponent)*s^packetExponent ≤ 1/4 → c*s^packetExponent ≤ 1/100 →
    ∀ (rads : Fin J → ℝ),(∀ k,0 ≤ rads k) → ∀ {j : ℕ} (k : Fin J),j ≤ k.val →
    Real.sqrt 3*(rads k)^(101/100:ℝ) ≤ r/12 →
    ∃ G : Set (ObservationSample n J),
    (MeasurableSet G ∧ MeasurableSet[observationSigma rads j] G) ∧
    (observationLaw J ν) Gᶜ=0 ∧ ∀ sample∈G,
      let μ := conditionalPacketDensity (observationLaw J ν) Prod.fst (tailObservation rads j)
        g c r₀ s (tailObservation rads j sample)
      let m := rawCount {x : Position | r/4 ≤ ‖x‖ ∧ ‖x‖ ≤ 12*L*r} (observedOrdered rads k sample)
      let τ := c*(r/3)*(r/3)^packetExponent
      (∀ y : Position,r/2 ≤ ‖y‖ → ‖y‖ ≤ 8*L*r → μ y ≤ (B/τ^3)*m) ∧
      (∀ y z : Position,r/2 ≤ ‖y‖ → ‖y‖ ≤ 8*L*r → r/2 ≤ ‖z‖ → ‖z‖ ≤ 8*L*r →
        |μ y-μ z| ≤ (D/τ^4)*‖y-z‖*m) := by
  obtain ⟨B,D,hB,hD,hbound,hlip⟩ := schwartz_square_bounded_lipschitz g
  refine ⟨B,D,hB,hD,?_⟩
  intro n J ν hν c r₀ s r L hc hr₀ hs hr hL hrr₀ hrs hscale hwidth rads hrads j k hk hnoise
  let S := {x : Position | r/3 ≤ ‖x‖ ∧ ‖x‖ ≤ 10*L*r}
  let T := {x : Position | r/2 ≤ ‖x‖ ∧ ‖x‖ ≤ 8*L*r}
  let O := {x : Position | r/4 ≤ ‖x‖ ∧ ‖x‖ ≤ 12*L*r}
  have hS : MeasurableSet S := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  have hO : MeasurableSet O := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  have hgs : HasCompactSupport (g : Position → ℝ) := HasCompactSupport.intro
    (isCompact_closedBall (0:Position) 1) (fun z hz => hg z
      (by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hz))
  have hpost := posterior_count_le_observed ν rads hrads k hk hS hO
    (fun x hx y hxy => packet_band_observation_support hr hL hnoise hx hxy)
  let obs := tailObservation (n:=n) rads j
  let P := observationLaw J ν
  let C := fun datum : Fin J → UnorderedArray n =>
    ∫ x,rawCount S x ∂ProbabilityTheory.condDistrib Prod.fst obs P datum
  let M := fun datum : Fin J → UnorderedArray n =>
    unorderedSum (O.indicator (fun _ => (1:ℝ))) (datum k)
  have hC : Measurable C := ((measurable_rawCount hS).stronglyMeasurable.integral_kernel
    (κ:=ProbabilityTheory.condDistrib Prod.fst obs P)).measurable
  have hM : Measurable M := (measurable_unorderedSum
    (measurable_const.indicator hO)).comp (measurable_pi_apply k)
  let G := obs ⁻¹' {datum | C datum ≤ M datum}
  have hM_eq (sample : ObservationSample n J) : M (obs sample)=
      rawCount O (observedOrdered rads k sample) := by
    exact unorderedSum_tailObservation rads k hk _ sample
  have hG : MeasurableSet G := (measurableSet_le hC hM).preimage (measurable_tailObservation rads j)
  have hGt : MeasurableSet[observationSigma rads j] G :=
    ⟨{datum | C datum ≤ M datum},measurableSet_le hC hM,rfl⟩
  have hGae : ∀ᵐ sample ∂P,sample∈G := by
    filter_upwards [hpost] with sample hh
    change C (obs sample) ≤ M (obs sample)
    rw [hM_eq]
    exact hh
  refine ⟨G,⟨hG,hGt⟩,by exact ae_iff.mp hGae,?_⟩
  intro sample hsamp
  have hh : C (obs sample) ≤ rawCount O (observedOrdered rads k sample) := by
    have hh : C (obs sample) ≤ M (obs sample) := hsamp
    rwa [hM_eq] at hh
  let ν' := ProbabilityTheory.condDistrib Prod.fst (tailObservation rads j) (observationLaw J ν)
    (tailObservation rads j sample)
  have hτ : 0 < c*(r/3)*(r/3)^packetExponent := by positivity
  have H := mixture_packet_band_bounds ν' g.continuous hgs hB hD hbound hlip hc hr₀ hs hτ hS
    (T:=T) (fun y hy x hx => packet_band_center_support hg hc hr₀ hs hr hL hrr₀ hscale hwidth hy.1 hy.2 hx)
    (fun x hx => packet_band_width_lower hc hr₀ hs hr hrs hx.1)
  dsimp only
  constructor
  · intro y hy0 hy1
    exact (H.1 y ⟨hy0,hy1⟩).trans (mul_le_mul_of_nonneg_left hh (by positivity))
  · intro y z hy0 hy1 hz0 hz1
    exact (H.2 y ⟨hy0,hy1⟩ z ⟨hz0,hz1⟩).trans (mul_le_mul_of_nonneg_left hh (by positivity))
end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace NeutralAtom

lemma posterior_mesh_modulus {Ω Data : Type*} [MeasurableSpace Ω] [MeasurableSpace Data]
    {n : ℕ} (P : Measure Ω) [IsFiniteMeasure P]
    (raw : Ω → Configuration n) (obs : Ω → Data) (g : Position → ℝ)
    {c r₀ s : ℝ} (hc : 0 < c) (hr₀ : 0 < r₀) (hs : 0 < s)
    (datum : Data) (Z : ℝ) {r L τ B D K C : ℝ}
    (hr : 0 < r) (hL : 1 ≤ L) (hτ : 0 < τ) (hτr : τ ≤ r)
    (hrsmall : r ≤ 1/16) (hB : 0 ≤ B) (hD : 0 ≤ D) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hden : ∀ y,r/2 ≤ ‖y‖ → ‖y‖ ≤ 8*L*r →
      conditionalPacketDensity P raw obs g c r₀ s datum y ≤ (B/τ^3)*(K/r^3))
    (hlip : ∀ y z,r/2 ≤ ‖y‖ → ‖y‖ ≤ 8*L*r → r/2 ≤ ‖z‖ → ‖z‖ ≤ 8*L*r →
      |conditionalPacketDensity P raw obs g c r₀ s datum z-
        conditionalPacketDensity P raw obs g c r₀ s datum y| ≤ (D/τ^4)*‖z-y‖*(K/r^3))
    (hcap : ∀ y,3*r/4 ≤ ‖y‖ → ‖y‖ ≤ 6*L*r →
      ‖y‖^4*(Z*coulombKernel y-potentialOf (conditionalPacketDensity P raw obs g c r₀ s datum) y) ≤ physicalSpatialCap)
    (hosc : ∀ y z,r ≤ ‖y‖ → ‖y‖ ≤ 4*L*r → ‖z-y‖ ≤ r/16 →
      let F := fun x => Z*coulombKernel x-potentialOf (conditionalPacketDensity P raw obs g c r₀ s datum) x
      ‖F z-F y‖ ≤ C*(‖z-y‖/r)*((r/τ)^3/r^4+max (-F y) 0))
    {y z : Position} (hy0 : r ≤ ‖y‖) (hy1 : ‖y‖ ≤ 4*L*r)
    (hz0 : r ≤ ‖z‖) (hz1 : ‖z‖ ≤ 4*L*r) (hdist : ‖z-y‖ ≤ r^2) :
    let ρ := conditionalPacketDensity P raw obs g c r₀ s datum
    let U := fun x => ‖x‖^4*(Z*coulombKernel x-potentialOf ρ x)
    |‖z‖^6*ρ z-‖y‖^6*ρ y| ≤
      ((4*L)^6*(D*K)+6*(4*L)^5*(B*K))*(r*(r/τ)^4) ∧
    |U z-U y| ≤ (((4*L)^4*C+4*(4*L)^3*max physicalSpatialCap 1)*r)*
      ((r/τ)^3+max (-U y) 0) := by
  let ρ := conditionalPacketDensity P raw obs g c r₀ s datum
  let F := fun x => Z*coulombKernel x-potentialOf ρ x
  have hLr : 0 ≤ L*r := mul_nonneg (by linarith) hr.le
  have hylo : r/2 ≤ ‖y‖ := by linarith
  have hyhi : ‖y‖ ≤ 8*L*r := by nlinarith
  have hzlo : r/2 ≤ ‖z‖ := by linarith
  have hzhi : ‖z‖ ≤ 8*L*r := by nlinarith
  dsimp only
  constructor
  · exact mesh_normalized_density_bound hr hL hτ hτr hB hD hK hy0 hy1 hz0 hz1 hdist
      (conditionalPacketDensity_nonneg P raw obs g hc hr₀ hs datum y)
      (hden y hylo hyhi) (hlip y z hylo hyhi hzlo hzhi)
  · have hd : ‖z-y‖ ≤ r/16 := hdist.trans (by nlinarith)
    have HH := normalized_field_difference (F:=F) (lam:=(r/τ)^3) hr hL hC physicalSpatialCap_pos.le
      (one_le_pow₀ ((le_div_iff₀ hτ).mpr (by simpa using hτr))) hy0 hy1 hz0 hz1
      (hcap y (by linarith) (by nlinarith)) (by simpa only [Real.norm_eq_abs] using hosc y z hy0 hy1 hd)
    apply HH.trans
    have hratio : ‖z-y‖/r ≤ r := (div_le_iff₀ hr).mpr (by nlinarith)
    gcongr
end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace NeutralAtom

lemma measurable_tailObservation_for_sigma {n J : ℕ} (r : Fin J → ℝ) (j : ℕ) :
    Measurable[observationSigma r j] (tailObservation (n:=n) r j) :=
  measurable_iff_comap_le.mpr le_rfl

lemma measurable_observed_count_tail {n J : ℕ} (r : Fin J → ℝ) {j : ℕ} (k : Fin J)
    (hk : j ≤ k.val) {S : Set Position} (hS : MeasurableSet S) :
    Measurable[observationSigma r j]
      (fun z : ObservationSample n J => rawCount S (observedOrdered r k z)) := by
  have HM : Measurable (fun datum : Fin J → UnorderedArray n =>
      unorderedSum (S.indicator (fun _ => (1:ℝ))) (datum k)) :=
    (measurable_unorderedSum (measurable_const.indicator hS)).comp (measurable_pi_apply k)
  have H := HM.comp (measurable_tailObservation_for_sigma r j)
  convert H using 1
  funext z
  exact (unorderedSum_tailObservation r k hk _ z).symm

lemma measurable_normalized_posterior_density_tail {n J : ℕ}
    (P : Measure (ObservationSample n J)) [IsFiniteMeasure P]
    (r : Fin J → ℝ) (j : ℕ) {g : Position → ℝ} (hg : Continuous g)
    {c r₀ s : ℝ} (hc : 0 < c) (hr₀ : 0 < r₀) (hs : 0 < s) (y : Position) :
    Measurable[observationSigma r j] (fun z => ‖y‖^6*
      conditionalPacketDensity P Prod.fst (tailObservation r j) g c r₀ s (tailObservation r j z) y) :=
  measurable_const.mul ((measurable_conditionalPacketDensity_data P Prod.fst
    (tailObservation r j) hg hc hr₀ hs y).comp (measurable_tailObservation_for_sigma r j))

lemma measurable_normalized_posterior_field_tail {n J : ℕ}
    (P : Measure (ObservationSample n J)) [IsFiniteMeasure P]
    (r : Fin J → ℝ) (j : ℕ) {g : Position → ℝ} (hg : Continuous g)
    (hgs : HasCompactSupport g) (hm : (∫ z,g z^2)=1)
    {c r₀ s : ℝ} (hc : 0 < c) (hr₀ : 0 < r₀) (hs : 0 < s) (Z : ℝ) (y : Position) :
    Measurable[observationSigma r j] (fun z => ‖y‖^4*(Z*coulombKernel y-potentialOf
      (conditionalPacketDensity P Prod.fst (tailObservation r j) g c r₀ s (tailObservation r j z)) y)) :=
  measurable_const.mul (measurable_const.sub
    ((measurable_conditionalPacketPotential_data P Prod.fst (tailObservation r j) hg hgs hm hc hr₀ hs y).comp
      (measurable_tailObservation_for_sigma r j)))
end NeutralAtom
end

end

end OAI
