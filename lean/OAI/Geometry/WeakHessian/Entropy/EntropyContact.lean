import Mathlib
import OAI.Geometry.WeakHessian.Transport.QuadraticCostIncrement
import OAI.Geometry.WeakHessian.Transport.VariationQuotient

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile1
noncomputable section
namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

lemma IsTestPlan.restrict_reference_of_tracks {π : Measure (Curve X)}
    (hπ : IsTestPlan m π) {S : Set X} (hS : MeasurableSet S)
    (hs : ∀ᵐ γ ∂π, ∀ t : Time, γ t ∈ S) : IsTestPlan (m.restrict S) π := by
  refine ⟨hπ.1,?_,hπ.2.2⟩
  obtain ⟨C,hC⟩ := hπ.2.1
  refine ⟨C,fun t => ?_⟩
  have ha : ∀ᵐ x ∂(π.map (fun γ => γ t)), x ∈ S :=
    (ae_map_iff (continuous_eval_const t).measurable.aemeasurable hS).mpr
      (hs.mono fun γ hγ => hγ t)
  rw [← Measure.restrict_eq_self_of_ae_mem ha]
  convert Measure.restrict_mono le_rfl (hC t) using 1
  exact (Measure.restrict_smul _ _ _).symm

lemma IsTestPlan.ball_localization {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    (hb : BoundedTracks π) :
    ∃ o : X, ∃ R : ℝ, 0 < R ∧ IsTestPlan (m.restrict (Metric.ball o R)) π := by
  obtain ⟨o,R,hR,hb⟩ := hb
  refine ⟨o,R+1,by linarith,hπ.restrict_reference_of_tracks measurableSet_ball ?_⟩
  filter_upwards [hb] with γ hγ t
  exact (hγ t).trans_lt (by linarith)

lemma IsTestPlan.integrable_eval {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    {f : X → ℝ} (hf : Integrable f m) (t : Time) :
    Integrable (fun γ => f (γ t)) π := by
  obtain ⟨C,hC⟩ := hπ.2.1
  exact ((hf.smul_measure ENNReal.coe_ne_top).mono_measure (hC t)).comp_aemeasurable
    (continuous_eval_const t).measurable.aemeasurable

lemma IsTestPlan.integrable_eval_local {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    (hb : BoundedTracks π) {f : X → ℝ}
    (hf : ∀ o : X, ∀ R : ℝ, 0 < R → Integrable f (m.restrict (Metric.ball o R)))
    (t : Time) : Integrable (fun γ => f (γ t)) π := by
  obtain ⟨o,R,hR,hplan⟩ := hπ.ball_localization hb
  exact hplan.integrable_eval (hf o R hR) t

lemma IsTestPlan.continuous_integral_eval_local (hfin : FiniteOnBoundedSets m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    {f : X → ℝ}
    (hf : ∀ o : X, ∀ R : ℝ, 0 < R → Integrable f (m.restrict (Metric.ball o R))) :
    Continuous (fun t : Time => ∫ γ, f (γ t) ∂π) := by
  obtain ⟨o,R,hR,hplan⟩ := hπ.ball_localization hb
  let : IsFiniteMeasure (m.restrict (Metric.ball o R)) := ⟨by
    simpa only [Measure.restrict_apply_univ] using hfin _ Metric.isBounded_ball⟩
  exact hplan.continuous_integral_eval (hf o R hR)

lemma LocallyL2.integrable_eval (hfin : FiniteOnBoundedSets m)
    {f : X → ℝ} (hf : LocallyL2 m f) {π : Measure (Curve X)}
    (hπ : IsTestPlan m π) (hb : BoundedTracks π) (t : Time) :
    Integrable (fun γ => f (γ t)) π := by
  apply hπ.integrable_eval_local hb _ t
  intro o R hR
  let : IsFiniteMeasure (m.restrict (Metric.ball o R)) := ⟨by
    simpa only [Measure.restrict_apply_univ] using hfin _ Metric.isBounded_ball⟩
  exact (hf o R hR).integrable (by norm_num)

lemma LocallyL2.integrable_sq_eval {f : X → ℝ} (hf : LocallyL2 m f)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π) (t : Time) :
    Integrable (fun γ => (f (γ t))^2) π :=
  hπ.integrable_eval_local hb (fun o R hR => (hf o R hR).integrable_sq) t

lemma LocallyL2.continuous_integral_sq_eval (hfin : FiniteOnBoundedSets m)
    {f : X → ℝ} (hf : LocallyL2 m f) {π : Measure (Curve X)}
    (hπ : IsTestPlan m π) (hb : BoundedTracks π) :
    Continuous (fun t : Time => ∫ γ, (f (γ t))^2 ∂π) :=
  hπ.continuous_integral_eval_local hfin hb (fun o R hR => (hf o R hR).integrable_sq)

lemma LocallyL2.integrable_sq_prod_eval {D : X → ℝ} (hD : LocallyL2 m D)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π) :
    Integrable (fun z : Curve X × ℝ => (D (evalReal z.1 z.2))^2)
      (π.prod (volume.restrict (Icc (0:ℝ) 1))) := by
  let : IsProbabilityMeasure π := hπ.1
  have hm := (hπ.aemeasurable_evalReal hD.aemeasurable).pow_const 2
  refine ⟨hm.aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun z => sq_nonneg _)]
  rw [lintegral_prod _ hm.ennreal_ofReal]
  exact hπ.lintegral_square_eval_lt_top hb hD

lemma IsTestPlan.continuous_local_gradient_energy (hfin : FiniteOnBoundedSets m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    {f : X → ℝ} (hf : LocalSobolev m f) :
    Continuous (fun s : ℝ => ∫ γ, (weakGradient m f (evalReal γ s))^2 ∂π) :=
  ((weakGradient_isMinimal hf.2).1.1.continuous_integral_sq_eval hfin hπ hb).comp continuous_clampTime

lemma IsTestPlan.tendsto_average_local_gradient_energy (hfin : FiniteOnBoundedSets m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    {f : X → ℝ} (hf : LocalSobolev m f) :
    Tendsto (fun t : ℝ => (∫ s in 0..t, ∫ γ, (weakGradient m f (evalReal γ s))^2 ∂π)/t)
      (𝓝[>] 0) (𝓝 (∫ γ, (weakGradient m f (γ timeZero))^2 ∂π)) := by
  have hc := hπ.continuous_local_gradient_energy hfin hb hf
  have H := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 0)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt).tendsto_slope_zero_right
  have he : clampTime 0 = timeZero := Subtype.ext (by simp [clampTime,timeZero])
  simpa only [zero_add,intervalIntegral.integral_same,sub_zero,smul_eq_mul,
    evalReal,he,div_eq_mul_inv,mul_comm] using H

end WeakHessian

namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}
lemma IsLocalWeakUpperGradient.geodesic_young_local
    {f D : X → ℝ} (hD : IsLocalWeakUpperGradient m f D) (hf : AEMeasurable f m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ) (t : Time) (ht : 0 < t.val) :
    (∫ γ, f (γ timeZero)-f (γ t) ∂π) ≤
      ∫ z : Curve X × ℝ, ((D (evalReal z.1 z.2))^2+
        dist (z.1 timeZero) (z.1 timeOne)^2)/2
        ∂(π.prod (volume.restrict (Icc (0:ℝ) t.val))) := by
  let : IsProbabilityMeasure π := hπ.1
  let ν := volume.restrict (Icc (0:ℝ) t.val)
  have hν : ν ≤ volume.restrict (Icc (0:ℝ) 1) :=
    Measure.restrict_mono_set _ (Icc_subset_Icc le_rfl t.property.2)
  have hprod : π.prod ν ≤ π.prod (volume.restrict (Icc (0:ℝ) 1)) := Measure.prod_mono le_rfl hν
  have hDm := (hπ.aemeasurable_evalReal hD.1.aemeasurable).mono_measure hprod
  have hDI : Integrable (fun z : Curve X × ℝ => (D (evalReal z.1 z.2))^2) (π.prod ν) :=
    (hD.1.integrable_sq_prod_eval hπ hb).mono_measure hprod
  have hLI := hb.integrable_length_sq.comp_fst ν
  have hI := (hDI.add hLI).div_const (2:ℝ)
  dsimp only [Pi.add_apply] at hI
  have hn : 0 ≤ᵐ[π.prod ν] (fun z : Curve X × ℝ =>
      ((D (evalReal z.1 z.2))^2+dist (z.1 timeZero) (z.1 timeOne)^2)/2) :=
    ae_of_all _ fun z => by positivity
  have H : ENNReal.ofReal (∫ γ, f (γ timeZero)-f (γ t) ∂π) ≤
      ∫⁻ z : Curve X × ℝ, ENNReal.ofReal (((D (evalReal z.1 z.2))^2+
        dist (z.1 timeZero) (z.1 timeOne)^2)/2) ∂(π.prod ν) := by
    calc
      _ ≤ ENNReal.ofReal |∫ γ, f (γ timeZero)-f (γ t) ∂π| := ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ ≤ ∫⁻ γ, ENNReal.ofReal |f (γ timeZero)-f (γ t)| ∂π := by
        simpa only [Real.enorm_eq_ofReal_abs] using
          enorm_integral_le_lintegral_enorm (μ := π) (fun γ => f (γ timeZero)-f (γ t))
      _ ≤ ∫⁻ γ, ∫⁻ s, ENNReal.ofReal (((D (evalReal γ s))^2+
          dist (γ timeZero) (γ timeOne)^2)/2) ∂ν ∂π := by
        apply lintegral_mono_ae
        filter_upwards [hD.ae_subinterval_le hf hπ hb timeZero t ht,hgeo,
          hπ.ae_ae_eval_of_ae hD.2.1] with γ hg hγ hpos
        rw [abs_sub_comm] at hg
        apply hg.trans
        apply lintegral_mono_ae
        filter_upwards [ae_mono hν hγ.ae_metricSpeed_le,ae_mono hν hpos] with s hs hDs
        calc
          _ ≤ ENNReal.ofReal (D (evalReal γ s))*ENNReal.ofReal (dist (γ timeZero) (γ timeOne)) :=
            mul_le_mul_of_nonneg_left hs bot_le
          _ = ENNReal.ofReal (D (evalReal γ s)*dist (γ timeZero) (γ timeOne)) := (ENNReal.ofReal_mul hDs).symm
          _ ≤ _ := ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (D (evalReal γ s)-dist (γ timeZero) (γ timeOne))])
      _ = _ := (lintegral_prod _ hI.aestronglyMeasurable.aemeasurable.ennreal_ofReal).symm
  rw [← ofReal_integral_eq_lintegral_ofReal hI hn] at H
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg_of_ae hn)).mp H

end WeakHessian

noncomputable section
namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma IsLocalWeakUpperGradient.geodesic_young_time_local
    {f D : X → ℝ} (hD : IsLocalWeakUpperGradient m f D) (hf : AEMeasurable f m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ) (t : Time) (ht : 0 < t.val) :
    (∫ γ, f (γ timeZero)-f (γ t) ∂π) ≤
      ((∫ s in 0..t.val, ∫ γ, (D (evalReal γ s))^2 ∂π)+
        t.val*(∫ γ, dist (γ timeZero) (γ timeOne)^2 ∂π))/2 := by
  let : IsProbabilityMeasure π := hπ.1
  let ν := volume.restrict (Icc (0:ℝ) t.val)
  have hν : ν ≤ volume.restrict (Icc (0:ℝ) 1) :=
    Measure.restrict_mono_set _ (Icc_subset_Icc le_rfl t.property.2)
  have hprod : π.prod ν ≤ π.prod (volume.restrict (Icc (0:ℝ) 1)) := Measure.prod_mono le_rfl hν
  have hDm := (hπ.aemeasurable_evalReal hD.1.aemeasurable).mono_measure hprod
  have hDI : Integrable (fun z : Curve X × ℝ => (D (evalReal z.1 z.2))^2) (π.prod ν) :=
    (hD.1.integrable_sq_prod_eval hπ hb).mono_measure hprod
  have hLI := hb.integrable_length_sq.comp_fst ν
  have H := hD.geodesic_young_local hf hπ hb hgeo t ht
  calc
    _ ≤ _ := H
    _ = _ := by
      rw [integral_div,integral_add hDI hLI,integral_prod_symm _ hDI,integral_prod _ hLI]
      simp only [ν,integral_const,Measure.real,Measure.restrict_apply_univ,
        Real.volume_Icc,sub_zero,smul_eq_mul,ENNReal.toReal_ofReal ht.le]
      rw [integral_const_mul,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le ht.le]

end WeakHessian

namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma IsTestPlan.integrable_local_gamma_eval (hfin : FiniteOnBoundedSets m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    {f g : X → ℝ} (hf : LocalSobolev m f) (hg : LocalSobolev m g) (t : Time) :
    Integrable (fun γ => gamma m f g (γ t)) π := by
  exact (((weakGradient_isMinimal (hf.add hfin hg).2).1.1.integrable_sq_eval hπ hb t).sub
    ((weakGradient_isMinimal (hf.sub hfin hg).2).1.1.integrable_sq_eval hπ hb t)).div_const 4

lemma IsTestPlan.local_perturbation_energy (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    (hb : BoundedTracks π) {f g : X → ℝ} (hf : LocalSobolev m f) (hg : LocalSobolev m g)
    (t : Time) (a : ℝ) :
    (∫ γ, (weakGradient m (fun x => f x+a*g x) (γ t))^2 ∂π) =
      (∫ γ, (weakGradient m f (γ t))^2 ∂π)+2*a*(∫ γ,gamma m f g (γ t) ∂π)+
      a^2*(∫ γ, (weakGradient m g (γ t))^2 ∂π) := by
  rw [integral_congr_ae (hπ.ae_eval_of_ae (weakGradient_linear_combination_sq hfin hpar hf hg a) t)]
  have hi1 := (weakGradient_isMinimal hf.2).1.1.integrable_sq_eval hπ hb t
  have hi2 := (hπ.integrable_local_gamma_eval hfin hb hf hg t).const_mul (2*a)
  have hi3 := ((weakGradient_isMinimal hg.2).1.1.integrable_sq_eval hπ hb t).const_mul (a^2)
  have hi12 := hi1.add hi2
  change Integrable (fun γ => (weakGradient m f (γ t))^2+2*a*gamma m f g (γ t)) π at hi12
  rw [integral_add hi12 hi3,integral_add hi1 hi2,integral_const_mul,integral_const_mul]

lemma IsTestPlan.contact_first_variation_local (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    (hb : BoundedTracks π) (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {φ ψ f : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ) (hf : LocalSobolev m f)
    (hdual : ∀ x y, φ x+ψ y ≤ dist x y^2/2)
    (hcontact : ∀ᵐ γ ∂π, φ (γ timeZero)+ψ (γ timeOne) = dist (γ timeZero) (γ timeOne)^2/2) :
    Tendsto (fun t : ℝ => (∫ γ, f (γ timeZero)-f (evalReal γ t) ∂π)/t)
      (𝓝[>] 0) (𝓝 (∫ γ, gamma m φ f (γ timeZero) ∂π)) := by
  let : IsProbabilityMeasure π := hπ.1
  let A := ∫ γ, dist (γ timeZero) (γ timeOne)^2 ∂π
  let P := ∫ γ, (weakGradient m φ (γ timeZero))^2 ∂π
  let Q := (∫ γ, (weakGradient m f (γ timeZero))^2 ∂π)/2
  have hP : P ≤ A := hπ.contact_gradient_energy_le hfin hb hφ hdual hcontact
  apply WeakHessianTransport.tendsto_of_quadratic_variations (Q := Q)
  intro a
  let u : X → ℝ := fun x => φ x+a*f x
  have hφS := localSobolev_of_lipschitz hfin hφ
  have hu : LocalSobolev m u := hφS.add hfin (hf.const_mul a)
  let I : ℝ → ℝ := fun t => ∫ s in 0..t, ∫ γ, (weakGradient m u (evalReal γ s))^2 ∂π
  refine ⟨fun t => (I t/t-P+t*A)/2,?_,?_⟩
  · have H := ((hπ.tendsto_average_local_gradient_energy hfin hb hu).sub_const P).add
      ((tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0)).mul_const A)
    have HH := H.div_const (2:ℝ)
    have he : ((∫ γ, (weakGradient m u (γ timeZero))^2 ∂π)-P+0*A)/2 =
        a*(∫ γ, gamma m φ f (γ timeZero) ∂π)+a^2*Q := by
      dsimp only [u]
      rw [hπ.local_perturbation_energy hfin hpar hb hφS hf timeZero a]
      dsimp [P,Q]
      ring
    rw [he] at HH
    exact HH
  · have hevent : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t ∧ t < 1 := by
      have hgt : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
      have hlt : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
        (eventually_lt_nhds (by norm_num : (0:ℝ) < 1)).filter_mono nhdsWithin_le_nhds
      exact hgt.and hlt
    filter_upwards [hevent] with t ht
    let τ : Time := ⟨t,ht.1.le,ht.2.le⟩
    have hc : clampTime t = τ := Subtype.ext (clampTime_of_mem τ.property)
    have hU := (weakGradient_isMinimal hu.2).1
    have hY := hU.geodesic_young_time_local hu.1.aemeasurable hπ hb hgeo τ ht.1
    have hiφ (s : Time) := hb.integrable_lipschitz_eval hφ s
    have hif (s : Time) := hf.1.integrable_eval hfin hπ hb s
    have hcomb : (∫ γ, u (γ timeZero)-u (γ τ) ∂π) =
        (∫ γ, φ (γ timeZero)-φ (γ τ) ∂π)+a*(∫ γ, f (γ timeZero)-f (γ τ) ∂π) := by
      have H : (fun γ : Curve X => u (γ timeZero)-u (γ τ)) =
          fun γ => (φ (γ timeZero)-φ (γ τ))+a*(f (γ timeZero)-f (γ τ)) := by
        funext γ; dsimp [u]; ring
      have hi1 := (hiφ timeZero).sub (hiφ τ)
      have hi2 := ((hif timeZero).sub (hif τ)).const_mul a
      change Integrable (fun γ => φ (γ timeZero)-φ (γ τ)) π at hi1
      change Integrable (fun γ => a*(f (γ timeZero)-f (γ τ))) π at hi2
      rw [H,integral_add hi1 hi2,integral_const_mul]
    rw [hcomb] at hY
    have hC : t*(1-t/2)*A ≤ (∫ γ, φ (γ timeZero)-φ (γ τ) ∂π) := by
      rw [← integral_const_mul]
      apply integral_mono_ae (hb.integrable_length_sq.const_mul _) ((hiφ timeZero).sub (hiφ τ))
      filter_upwards [hgeo,hcontact] with γ hγ hg
      exact contact_geodesic_decrease hdual hγ hg τ
    have H := WeakHessianTransport.variation_quotient_le ht.1 hP hC hY
    simpa only [I,τ,evalReal,hc] using H
end WeakHessian
noncomputable section
namespace WeakHessianTransport
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X]

def lowerLipExtension (S : Set X) (f : S → ℝ) (D : ℝ≥0) (x : X) : ℝ :=
  ⨆ z : S, f z - D * dist x z

lemma lowerLipExtension_bdd {S : Set X} [Nonempty S] {f : S → ℝ} {D : ℝ≥0}
    (hf : LipschitzWith D f) (x : X) :
    BddAbove (range (fun z : S => f z - D * dist x z)) := by
  obtain ⟨o⟩ := ‹Nonempty S›
  refine ⟨f o+D*dist x o,?_⟩
  rintro r ⟨z,rfl⟩
  have H := hf.le_add_mul z o
  have J := mul_le_mul_of_nonneg_left (dist_triangle_left (z:X) (o:X) x) D.coe_nonneg
  change f z ≤ f o+D*dist (z:X) (o:X) at H
  nlinarith

lemma lowerLipExtension_eq {S : Set X} [Nonempty S] {f : S → ℝ} {D : ℝ≥0}
    (hf : LipschitzWith D f) (x : S) : lowerLipExtension S f D x = f x := by
  apply le_antisymm
  · apply ciSup_le
    intro z
    have H := hf.le_add_mul z x
    change f z ≤ f x+D*dist (z:X) (x:X) at H
    rw [dist_comm] at H
    linarith
  · have H := le_ciSup (lowerLipExtension_bdd hf (x:X)) x
    simpa only [dist_self,mul_zero,sub_zero,lowerLipExtension] using H

lemma lowerLipExtension_lipschitz {S : Set X} [Nonempty S] {f : S → ℝ} {D : ℝ≥0}
    (hf : LipschitzWith D f) : LipschitzWith D (lowerLipExtension S f D) := by
  apply LipschitzWith.of_le_add_mul D
  intro x y
  apply ciSup_le
  intro z
  have H := le_ciSup (lowerLipExtension_bdd hf y) z
  change f z-D*dist y z ≤ lowerLipExtension S f D y at H
  have J := mul_le_mul_of_nonneg_left (dist_triangle y x (z:X)) D.coe_nonneg
  rw [dist_comm y x] at J
  linarith

lemma quadratic_cost_two_point_lower {D : ℝ≥0} {z w x y : X}
    (hD : dist z w ≤ D) :
    dist z w^2/2-D*(dist x z+dist y w) ≤ dist x y^2/2 := by
  have hr : 0 ≤ dist x z+dist y w := by positivity
  have ha : dist z w ≤ dist x z+dist y w+dist x y := by
    have H := dist_triangle z x w
    have J := dist_triangle x y w
    rw [dist_comm z x] at H
    linarith
  by_cases h : dist x y ≤ dist z w
  · have H : dist z w^2-dist x y^2 ≤ (dist x z+dist y w)*(2*D) := by
      calc
        _ = (dist z w-dist x y)*(dist z w+dist x y) := by ring
        _ ≤ (dist x z+dist y w)*(dist z w+dist x y) := by gcongr; linarith
        _ ≤ (dist x z+dist y w)*(2*D) := by gcongr; linarith
    nlinarith
  · have H := (sq_le_sq₀ dist_nonneg dist_nonneg).mpr (le_of_not_ge h)
    nlinarith [mul_nonneg D.coe_nonneg hr]

lemma lowerLipExtension_dual {S : Set X} [Nonempty S] {f g : S → ℝ} {D : ℝ≥0}
    (hf : LipschitzWith D f) (hg : LipschitzWith D g)
    (hD : ∀ z w : S, dist (z:X) (w:X) ≤ D)
    (hdual : ∀ z w : S, f z+g w ≤ dist (z:X) (w:X)^2/2) (x y : X) :
    lowerLipExtension S f D x+lowerLipExtension S g D y ≤ dist x y^2/2 := by
  rw [← le_sub_iff_add_le]
  apply (ciSup_le_iff (lowerLipExtension_bdd hf x)).mpr
  intro z
  rw [le_sub_iff_add_le,add_comm,← le_sub_iff_add_le]
  apply (ciSup_le_iff (lowerLipExtension_bdd hg y)).mpr
  intro w
  have H := quadratic_cost_two_point_lower (hD z w) (x := x) (y := y)
  have J := hdual z w
  linarith

variable [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
open WeakHessian

lemma quadraticTransportCost_map_subtype {S : Set X} (hS : MeasurableSet S)
    (q : Measure (S×S)) :
    QuadraticTransportCost (q.map (Prod.map Subtype.val Subtype.val)) =
      QuadraticTransportCost q := by
  unfold QuadraticTransportCost
  rw [lintegral_map (measurable_fst.edist measurable_snd |>.pow_const 2)
    ((MeasurableEmbedding.subtype_coe hS).prodMap
      (MeasurableEmbedding.subtype_coe hS)).measurable]
  rfl

lemma compact_quadraticCost_eq [CompactSpace X] (q : Measure (X×X))
    [IsFiniteMeasure q] :
    QuadraticTransportCost q = ENNReal.ofReal (2*(∫ p,quadraticCost 1 p ∂q)) := by
  have hi : Integrable (fun p : X×X => dist p.1 p.2^2) q :=
    ((continuous_fst.dist continuous_snd).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have heq : (∫ p : X×X, dist p.1 p.2^2 ∂q) = 2*(∫ p,quadraticCost 1 p ∂q) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ (fun p => by simp only [quadraticCost_apply]; ring)
  rw [← heq,ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun p => sq_nonneg _))]
  apply lintegral_congr
  intro p
  rw [edist_dist,ENNReal.ofReal_pow dist_nonneg]

lemma compact_kantorovich_potentials_of_optimal [CompactSpace X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {q : Measure (X×X)} (hq : IsOptimalCoupling q μ ν)
    {R : ℝ≥0} (hR : ∀ x y : X, dist x y ≤ R) (o : X) :
    ∃ φ ψ : C(X,ℝ), LipschitzWith R φ ∧ LipschitzWith R ψ ∧
      (∀ x y, φ x+ψ y ≤ dist x y^2/2) ∧
      ∀ᵐ p ∂q, φ p.1+ψ p.2 = dist p.1 p.2^2/2 := by
  have hqp : IsProbabilityMeasure q := by
    constructor
    have H := congrArg (fun μ => μ Set.univ) hq.1.1
    simpa only [Measure.map_apply measurable_fst MeasurableSet.univ,preimage_univ,measure_univ] using H
  let := hqp
  obtain ⟨q',hqp',hq0',hq1',hqmin',φ,ψ,hφ,hψ,hdual,hcontact⟩ :=
    compact_kantorovich_potentials μ ν hR o
  let := hqp'
  have H := hq.2 q' ⟨hq0',hq1'⟩
  rw [compact_quadraticCost_eq,compact_quadraticCost_eq] at H
  have hcost : (∫ p,quadraticCost 1 p ∂q) ≤ ∫ p,quadraticCost 1 p ∂q' := by
    have hn : 0 ≤ 2*(∫ p,quadraticCost 1 p ∂q') := by
      apply mul_nonneg (by norm_num)
      apply integral_nonneg
      intro p
      simp only [quadraticCost_apply]
      positivity
    have he := (ENNReal.ofReal_le_ofReal_iff hn).mp H
    linarith
  have hm (r : Measure (X×X)) [IsProbabilityMeasure r]
      (hr0 : r.map Prod.fst = μ) (hr1 : r.map Prod.snd = ν) :
      (∫ p,φ p.1+ψ p.2 ∂r) = (∫ x,φ x ∂μ)+(∫ y,ψ y ∂ν) := by
    rw [integral_add,← integral_map measurable_fst.aemeasurable φ.continuous.aestronglyMeasurable,
      ← integral_map measurable_snd.aemeasurable ψ.continuous.aestronglyMeasurable,hr0,hr1]
    · exact (φ.continuous.comp continuous_fst).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    · exact (ψ.continuous.comp continuous_snd).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hi : Integrable (fun p : X×X => φ p.1+ψ p.2) q :=
    ((φ.continuous.comp continuous_fst).add (ψ.continuous.comp continuous_snd)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  refine ⟨φ,ψ,hφ,hψ,hdual,?_⟩
  have heq : (∫ p,φ p.1+ψ p.2 ∂q) = (∫ p,quadraticCost 1 p ∂q) := by
    apply le_antisymm
    · apply integral_mono hi (quadraticCost 1).integrable
      intro p
      simpa only [quadraticCost_apply,mul_one] using hdual p.1 p.2
    · calc
        _ ≤ ∫ p,quadraticCost 1 p ∂q' := hcost
        _ = ∫ p,φ p.1+ψ p.2 ∂q' := by
          apply integral_congr_ae
          filter_upwards [hcontact] with p hp
          simpa only [quadraticCost_apply,mul_one] using hp.symm
        _ = _ := by rw [hm q' hq0' hq1',hm q hq.1.1 hq.1.2]
  have H := (integral_eq_iff_of_ae_le hi (quadraticCost 1).integrable
    (ae_of_all _ (fun p => by simpa only [quadraticCost_apply,mul_one] using hdual p.1 p.2))).mp heq
  filter_upwards [H] with p hp
  simpa only [quadraticCost_apply,mul_one] using hp

lemma bounded_support_kantorovich_potentials
    {S : Set X} (hS : IsCompact S) (hne : S.Nonempty)
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ x ∂μ, x ∈ S) (hν : ∀ᵐ y ∂ν, y ∈ S)
    {q : Measure (X×X)} (hq : IsOptimalCoupling q μ ν)
    {R : ℝ≥0} (hR : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ R) :
    ∃ φ ψ : X → ℝ, LipschitzWith R φ ∧ LipschitzWith R ψ ∧
      (∀ x y,φ x+ψ y ≤ dist x y^2/2) ∧
      ∀ᵐ p ∂q,φ p.1+ψ p.2 = dist p.1 p.2^2/2 := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let : Nonempty S := hne.to_subtype
  have he := MeasurableEmbedding.subtype_coe hS.measurableSet
  have hep := he.prodMap he
  let μs : Measure S := μ.comap Subtype.val
  let νs : Measure S := ν.comap Subtype.val
  have hμr : ∀ᵐ x ∂μ,x ∈ range (Subtype.val : S → X) := by simpa using hμ
  have hνr : ∀ᵐ x ∂ν,x ∈ range (Subtype.val : S → X) := by simpa using hν
  let : IsProbabilityMeasure μs := he.isProbabilityMeasure_comap hμr
  let : IsProbabilityMeasure νs := he.isProbabilityMeasure_comap hνr
  have hμs : μs.map Subtype.val = μ := by
    rw [he.map_comap,Measure.restrict_eq_self_of_ae_mem hμr]
  have hνs : νs.map Subtype.val = ν := by
    rw [he.map_comap,Measure.restrict_eq_self_of_ae_mem hνr]
  have hqr : ∀ᵐ p ∂q,p ∈ range (Prod.map (Subtype.val : S → X) (Subtype.val : S → X)) := by
    have H : ∀ᵐ p ∂q,p.1 ∈ S := by
      apply (ae_map_iff measurable_fst.aemeasurable hS.measurableSet).mp
      rwa [hq.1.1]
    have J : ∀ᵐ p ∂q,p.2 ∈ S := by
      apply (ae_map_iff measurable_snd.aemeasurable hS.measurableSet).mp
      rwa [hq.1.2]
    filter_upwards [H,J] with p hp0 hp1
    exact ⟨(⟨p.1,hp0⟩,⟨p.2,hp1⟩),rfl⟩
  let qs : Measure (S×S) := q.comap (Prod.map Subtype.val Subtype.val)
  have hqs : qs.map (Prod.map Subtype.val Subtype.val) = q := by
    rw [hep.map_comap,Measure.restrict_eq_self_of_ae_mem hqr]
  have hqs0 : qs.map Prod.fst = μs := by
    apply he.map_injective
    rw [Measure.map_map he.measurable measurable_fst,hμs,← hq.1.1,← hqs,
      Measure.map_map measurable_fst hep.measurable]
    rfl
  have hqs1 : qs.map Prod.snd = νs := by
    apply he.map_injective
    rw [Measure.map_map he.measurable measurable_snd,hνs,← hq.1.2,← hqs,
      Measure.map_map measurable_snd hep.measurable]
    rfl
  have hqsopt : IsOptimalCoupling qs μs νs := by
    refine ⟨⟨hqs0,hqs1⟩,?_⟩
    intro r hr
    have hr' : IsCoupling (r.map (Prod.map Subtype.val Subtype.val)) μ ν := by
      constructor
      · rw [Measure.map_map measurable_fst hep.measurable,← hμs,← hr.1,
          Measure.map_map he.measurable measurable_fst]
        rfl
      · rw [Measure.map_map measurable_snd hep.measurable,← hνs,← hr.2,
          Measure.map_map he.measurable measurable_snd]
        rfl
    have H := hq.2 _ hr'
    rw [← hqs,quadraticTransportCost_map_subtype hS.measurableSet,
      quadraticTransportCost_map_subtype hS.measurableSet] at H
    exact H
  obtain ⟨f,g,hf,hg,hdual,hcontact⟩ := compact_kantorovich_potentials_of_optimal μs νs hqsopt
    (fun x y => hR x x.property y y.property) (Classical.arbitrary S)
  let φ := lowerLipExtension S f R
  let ψ := lowerLipExtension S g R
  refine ⟨φ,ψ,lowerLipExtension_lipschitz hf,lowerLipExtension_lipschitz hg,
    lowerLipExtension_dual hf hg (fun x y => hR x x.property y y.property) hdual,?_⟩
  rw [← hqs]
  apply (ae_map_iff hep.measurable.aemeasurable ?_).mpr
  · filter_upwards [hcontact] with p hp
    simpa only [Prod.map_fst,Prod.map_snd,φ,ψ,lowerLipExtension_eq hf,
      lowerLipExtension_eq hg,Subtype.dist_eq] using hp
  · exact (isClosed_eq
      (((lowerLipExtension_lipschitz hf).continuous.comp continuous_fst).add
        ((lowerLipExtension_lipschitz hg).continuous.comp continuous_snd))
      (((continuous_fst.dist continuous_snd).pow 2).div_const 2)).measurableSet

end WeakHessianTransport

end
end
end
end InlinedFile1

end OAI
