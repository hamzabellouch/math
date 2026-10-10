import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.Midpoint
import OAI.Analysis.BiholderTransport.CostGeometry.SectionDiameter
import OAI.Analysis.BiholderTransport.Coordinates.ManifoldLipschitz
import OAI.Analysis.BiholderTransport.Duality.RiemannianTransport

namespace OAI

section

section

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff NNReal BoundedContinuousFunction

namespace WeakMTWTransport
section PowerEndpoint
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.section_diameter_of_exp_bound (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (hdual : IsCostDualPair u v)
    {L : ℝ≥0} (hL : ∀ x : M, ∀ p q : TangentSpace 𝓘(ℝ,Model n) x,
      ‖p‖≤Metric.diam (univ : Set M) → ‖q‖≤Metric.diam (univ : Set M) →
      dist (riemannianExp x p) (riemannianExp x q)≤L*‖p-q‖)
    {x : M} {r : ℝ} (hr : 0≤r) {y y' : M}
    (hy : y∈gapSection u v x r) (hy' : y'∈gapSection u v x r) :
    dist y y'≤L*Real.sqrt (8*(sectionOscillation u v x r+r)) := by
  rw [←liftedGapSection_image (n := n) u v x r] at hy hy'
  obtain ⟨p,hp,rfl⟩ := hy
  obtain ⟨q,hq,rfl⟩ := hy'
  have hb : ∀ w∈minimizingVectors (n := n) x, ‖w‖≤Metric.diam (univ : Set M) := by
    intro w hw
    rw [←show dist x (riemannianExp x w)=‖w‖ from hw]
    exact Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ _) (mem_univ _)
  apply (hL x p q (hb p hp.1) (hb q hq.1)).trans
  apply mul_le_mul_of_nonneg_left _ L.coe_nonneg
  apply Real.le_sqrt_of_sq_le
  simpa only [add_comm] using hmtw.liftedGapSection_diameter_sq hu hv hdual hr hp hq

variable [MeasurableSpace M]

lemma WeakMTW.contact_bounds_of_class_power (hmtw : WeakMTW (n := n) (M := M))
    {vol : Measure M} {lam cap : ℝ} {x0 : M}
    (hpower : HasPowerUpperBound (classOscillation vol lam cap x0)) :
    ∃ alpha C : ℝ, 0<alpha ∧ alpha≤1 ∧ 0≤C ∧
      ∀ uv∈densityDualClass vol lam cap x0,
        ∀ x x' y y' : M,
          contactGap uv.1 uv.2 x y=0 → contactGap uv.1 uv.2 x' y'=0 →
          dist y y'≤C*dist x x'^alpha := by
  obtain ⟨beta,C0,r0,hbeta,hC0,hr0,hpow⟩ := hpower
  obtain ⟨L,hL⟩ := exists_uniform_exp_lipschitz (n := n) (M := M) (Metric.diam (univ : Set M))
  let alpha := min beta 1/2
  let r1 := min r0 1
  let K : ℝ := L*Real.sqrt (8*(C0+1))
  let D : ℝ≥0 := ⟨Metric.diam (univ : Set M),Metric.diam_nonneg⟩
  have hD : ∀ x y : M, dist x y≤D := fun x y =>
    Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ x) (mem_univ y)
  have hr1 : 0<r1 := lt_min hr0 (by norm_num)
  have hK : 0≤K := by dsimp [K]; positivity
  have ha := power_reduction_exponent hbeta
  let C := K*(2*D+1)^alpha+D/(r1/(2*D+1))^alpha
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨alpha,C,ha.1,ha.2,hC,?_⟩
  intro uv huv
  have hdual := densityDualClass_isDual huv
  have hu : LipschitzWith D uv.1 := hdual.1.symm ▸ cTransform_lipschitz uv.2.continuous hD
  apply contact_bound_of_section_bound hu hD hK ha.1 hr1
  intro x r hr hrr y hy y' hy'
  have hF := (sectionOscillation_le_classOscillation huv x hr.le).trans
    (hpow r hr (hrr.trans_le (min_le_left _ _)))
  have hs := scalar_sqrt_power_bound hr (hrr.le.trans (min_le_right _ _)) hC0.le hF
  calc
    _≤(L:ℝ)*Real.sqrt (8*(sectionOscillation uv.1 uv.2 x r+r)) :=
      hmtw.section_diameter_of_exp_bound uv.1.continuous uv.2.continuous hdual hL hr.le hy hy'
    _≤(L:ℝ)*(Real.sqrt (8*(C0+1))*r^alpha) := mul_le_mul_of_nonneg_left hs L.coe_nonneg
    _=K*r^alpha := by dsimp [K]; ring

variable [BorelSpace M]

lemma WeakMTW.transport_endpoint_of_class_power (hmtw : WeakMTW (n := n) (M := M))
    {lam cap : ℝ} (hlam : 0<lam) (x0 : M)
    (hpower : HasPowerUpperBound (classOscillation (metricVolume n) lam cap x0)) :
    ∃ alpha C : ℝ, 0 < alpha ∧ alpha ≤ 1 ∧ 0 ≤ C ∧
      ∀ rho0 rho1 : M → ℝ,
        AdmissibleDensity (metricVolume n) lam cap rho0 →
        AdmissibleDensity (metricVolume n) lam cap rho1 →
        ∃ T : M ≃ₜ M,
          IsOptimalMap (metricVolume n) rho0 rho1 T ∧
          (∀ S : M → M, IsOptimalMap (metricVolume n) rho0 rho1 S →
            S =ᵐ[densityMeasure (metricVolume n) rho0] T) ∧
          BiHolderEstimate alpha C T := by
  obtain ⟨alpha,C,ha,ha1,hC,H⟩ := hmtw.contact_bounds_of_class_power hpower
  refine ⟨alpha,C,ha,ha1,hC,?_⟩
  intro rho0 rho1 hrho0 hrho1
  have := densityMeasure_probability hlam hrho0
  have := densityMeasure_probability hlam hrho1
  obtain ⟨uv,huv,hmin⟩ := exists_minimizing_normalizedDualPair
    (densityMeasure (metricVolume n) rho0) (densityMeasure (metricVolume n) rho1) x0
  have hm : ∀ a b : M →ᵇ ℝ, (∀ x y, 0≤contactGap a b x y) →
      dualObjective (densityMeasure (metricVolume n) rho0) (densityMeasure (metricVolume n) rho1) uv≤
      dualObjective (densityMeasure (metricVolume n) rho0) (densityMeasure (metricVolume n) rho1) (a,b) := by
    intro a b hab
    exact (hmin (normalizeDualPair_mem x0 b)).trans
      (dualObjective_normalize_le _ _ x0 a b hab)
  have hclass : uv∈densityDualClass (metricVolume n) lam cap x0 :=
    ⟨huv,rho0,rho1,hrho0,hrho1,hm⟩
  have hdual := densityDualClass_isDual hclass
  have hf := H uv hclass
  have hr : ∀ x x' y y' : M, contactGap uv.1 uv.2 x y=0 →
      contactGap uv.1 uv.2 x' y'=0 → dist x x'≤C*dist y y'^alpha := by
    intro x x' y y' hy hy'
    exact H _ (densityDualClass_reverse hlam hclass) y y' x x'
      (by rwa [reverseNormalizedPair_gap]) (by rwa [reverseNormalizedPair_gap])
  obtain ⟨T,hT,hTf,hTr⟩ := homeomorph_of_contact_bounds
    uv.1.continuous uv.2.continuous hdual ha hC hf hr
  have hs : ∀ x y, contactGap uv.1 uv.2 x y=0 → y=T x := by
    intro x y hy
    apply dist_eq_zero.mp
    apply le_antisymm _ dist_nonneg
    simpa only [dist_self,Real.zero_rpow ha.ne',mul_zero] using hf x x y (T x) hy (hT x)
  obtain ⟨S,_,hS,_,_,_,_,_,hpush,_⟩ := dual_minimizer_rough_transport hlam hrho0 hrho1 hdual hm
  have hST : S=T := funext (fun x => hs x (S x) (hS x))
  rw [hST] at hpush
  have hgap := dualPair_gap_nonneg uv.2.continuous hdual
  refine ⟨T,isOptimalMap_of_dual_contact hlam hrho0 hrho1
    uv.1.continuous uv.2.continuous hgap T.continuous.measurable hpush hT,?_,hTf,hTr⟩
  intro S hS
  exact optimalMap_ae_eq_of_singleton_contacts hlam hrho0 hrho1
    uv.1.continuous uv.2.continuous hgap T.continuous.measurable hpush hT hs hS

end PowerEndpoint
end WeakMTWTransport

end

end

end

end OAI
