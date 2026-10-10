import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.MetricDefinitions

namespace OAI

noncomputable section
open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

namespace WeakMTWTransport
open Matrix
open scoped MatrixOrder

lemma convex_linear_bound {f : ℝ → ℝ} {l C : ℝ} (hl : 0 < l)
    (hf : ConvexOn ℝ (Icc 0 l) f) (hzero : f 0 = 0) (hend : f l ≤ C * l)
    {t : ℝ} (ht : t ∈ Icc 0 l) : f t ≤ C * t := by
  have htl : 0 ≤ t / l := div_nonneg ht.1 hl.le
  have htl1 : t / l ≤ 1 := (div_le_one hl).mpr ht.2
  have hh := hf.2 (show (0 : ℝ) ∈ Icc 0 l from ⟨le_rfl, hl.le⟩)
    (show l ∈ Icc 0 l from ⟨hl.le, le_rfl⟩)
    (show 0 ≤ 1 - t / l from sub_nonneg.mpr htl1) htl (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, hzero] at hh
  have hcancel : t / l * l = t := div_mul_cancel₀ t hl.ne'
  rw [hcancel] at hh
  have hmul := mul_le_mul_of_nonneg_left hend htl
  apply hh.trans
  calc
    t / l * f l ≤ t / l * (C * l) := hmul
    _ = C * (t / l * l) := by ring
    _ = C * t := by rw [hcancel]
section TransportCertificates
variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

omit [MetricSpace M] [BorelSpace M] in
lemma density_nonnegative {vol : Measure M} {lam cap : ℝ} {rho : M → ℝ}
    (hlam : 0 < lam) (hrho : AdmissibleDensity vol lam cap rho) :
    ∀ᵐ x ∂vol, 0 ≤ rho x := by
  filter_upwards [hrho.2.2.2] with x hx
  exact hlam.le.trans hx.1

omit [MetricSpace M] [BorelSpace M] in
lemma densityMeasure_probability {vol : Measure M} {lam cap : ℝ} {rho : M → ℝ}
    (hlam : 0 < lam) (hrho : AdmissibleDensity vol lam cap rho) :
    IsProbabilityMeasure (densityMeasure vol rho) := by
  constructor
  rw [densityMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hrho.2.1 (density_nonnegative hlam hrho),
    hrho.2.2.1, ENNReal.ofReal_one]

omit [MetricSpace M] [BorelSpace M] in

lemma integral_densityMeasure {vol : Measure M} {lam cap : ℝ} {rho : M → ℝ}
    (hlam : 0 < lam) (hrho : AdmissibleDensity vol lam cap rho) (f : M → ℝ) :
    (∫ x, f x ∂densityMeasure vol rho) = ∫ x, f x * rho x ∂vol := by
  rw [densityMeasure, integral_withDensity_eq_integral_toReal_smul₀
    hrho.1.ennreal_ofReal (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [density_nonnegative hlam hrho] with x hx
  simp only [ENNReal.toReal_ofReal hx, smul_eq_mul, mul_comm]

variable [CompactSpace M]

lemma integrable_continuous_compact {mu : Measure M} [IsFiniteMeasure mu]
    {f : M → ℝ} (hf : Continuous f) : Integrable f mu := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact Integrable.of_bound hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun x => hC x (mem_univ x)))

lemma integrable_cost_map {mu : Measure M} [IsFiniteMeasure mu]
    {S : M → M} (hS : Measurable S) : Integrable (fun x => cost x (S x)) mu := by
  have hcost : Continuous (fun z : M × M => cost z.1 z.2) := by
    exact ((continuous_fst.dist continuous_snd).pow 2).div_const 2
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hcost.continuousOn
  exact Integrable.of_bound
    ((hcost.stronglyMeasurable.comp_measurable (measurable_id.prodMk hS)).aestronglyMeasurable) C
    (Filter.Eventually.of_forall (fun x => hC (x, S x) (mem_univ _)))

lemma integrable_comp_transport {mu nu : Measure M} [IsFiniteMeasure nu]
    {f : M → ℝ} {S : M → M} (hf : Continuous f) (hS : Measurable S)
    (hpush : Measure.map S mu = nu) : Integrable (fun x => f (S x)) mu := by
  have hh := integrable_continuous_compact (mu := nu) hf
  rw [← hpush, integrable_map_measure hf.aestronglyMeasurable hS.aemeasurable] at hh
  exact hh

lemma integral_contactGap_transport {mu nu : Measure M} [IsFiniteMeasure mu]
    [IsFiniteMeasure nu] {u v : M → ℝ} {S : M → M}
    (hu : Continuous u) (hv : Continuous v) (hS : Measurable S)
    (hpush : Measure.map S mu = nu) :
    (∫ x, contactGap u v x (S x) ∂mu) =
      (∫ x, u x ∂mu) + (∫ x, cost x (S x) ∂mu) + (∫ y, v y ∂nu) := by
  have hiu := integrable_continuous_compact (mu := mu) hu
  have hic := integrable_cost_map (mu := mu) hS
  have hiv := integrable_comp_transport hv hS hpush
  have hadd : (∫ x, contactGap u v x (S x) ∂mu) =
      (∫ x, u x + cost x (S x) ∂mu) + ∫ x, v (S x) ∂mu := by
    simpa only [contactGap, Pi.add_apply] using integral_add (hiu.add hic) hiv
  rw [hadd, integral_add hiu hic]
  congr 1
  rw [← hpush, integral_map_of_stronglyMeasurable hS hv.stronglyMeasurable]

lemma isOptimalMap_of_dual_contact {vol : Measure M} {lam cap : ℝ}
    {rho0 rho1 u v : M → ℝ} {T : M → M}
    (hlam : 0 < lam) (hrho0 : AdmissibleDensity vol lam cap rho0)
    (hrho1 : AdmissibleDensity vol lam cap rho1)
    (hu : Continuous u) (hv : Continuous v)
    (hgap : ∀ x y, 0 ≤ contactGap u v x y)
    (hT : Measurable T) (hpush : Measure.map T (densityMeasure vol rho0) = densityMeasure vol rho1)
    (hcontact : ∀ x, contactGap u v x (T x) = 0) :
    IsOptimalMap vol rho0 rho1 T := by
  let := densityMeasure_probability hlam hrho0
  let := densityMeasure_probability hlam hrho1
  refine ⟨hT, hpush, ?_⟩
  intro S hS hpushS
  rw [← integral_densityMeasure hlam hrho0, ← integral_densityMeasure hlam hrho0]
  have hzero : (∫ x, contactGap u v x (T x) ∂densityMeasure vol rho0) = 0 := by
    simp only [hcontact, integral_zero]
  have hnonneg : 0 ≤ ∫ x, contactGap u v x (S x) ∂densityMeasure vol rho0 :=
    integral_nonneg (fun x => hgap x (S x))
  rw [integral_contactGap_transport hu hv hT hpush] at hzero
  rw [integral_contactGap_transport hu hv hS hpushS] at hnonneg
  linarith

lemma optimalMap_ae_eq_of_singleton_contacts {vol : Measure M} {lam cap : ℝ}
    {rho0 rho1 u v : M → ℝ} {T S : M → M}
    (hlam : 0 < lam) (hrho0 : AdmissibleDensity vol lam cap rho0)
    (hrho1 : AdmissibleDensity vol lam cap rho1)
    (hu : Continuous u) (hv : Continuous v)
    (hgap : ∀ x y, 0 ≤ contactGap u v x y)
    (hT : Measurable T) (hpush : Measure.map T (densityMeasure vol rho0) = densityMeasure vol rho1)
    (hcontact : ∀ x, contactGap u v x (T x) = 0)
    (hsingle : ∀ x y, contactGap u v x y = 0 → y = T x)
    (hS : IsOptimalMap vol rho0 rho1 S) :
    S =ᵐ[densityMeasure vol rho0] T := by
  let := densityMeasure_probability hlam hrho0
  let := densityMeasure_probability hlam hrho1
  have hzero : (∫ x, contactGap u v x (T x) ∂densityMeasure vol rho0) = 0 := by
    simp only [hcontact, integral_zero]
  have hle := hS.2.2 T hT hpush
  rw [← integral_densityMeasure hlam hrho0, ← integral_densityMeasure hlam hrho0] at hle
  rw [integral_contactGap_transport hu hv hT hpush] at hzero
  have hnonneg : ∀ᵐ x ∂densityMeasure vol rho0, 0 ≤ contactGap u v x (S x) :=
    Filter.Eventually.of_forall (fun x => hgap x (S x))
  have hgapint : Integrable (fun x => contactGap u v x (S x)) (densityMeasure vol rho0) :=
    ((integrable_continuous_compact hu).add (integrable_cost_map hS.1)).add
      (integrable_comp_transport hv hS.1 hS.2.1)
  have hgapzero : (∫ x, contactGap u v x (S x) ∂densityMeasure vol rho0) = 0 := by
    have hnn := integral_nonneg_of_ae hnonneg
    rw [integral_contactGap_transport hu hv hS.1 hS.2.1] at hnn ⊢
    linarith
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnonneg hgapint).mp hgapzero
  filter_upwards [hae] with x hx
  exact hsingle x (S x) hx

end TransportCertificates

open scoped BoundedContinuousFunction

end WeakMTWTransport
end

end OAI
