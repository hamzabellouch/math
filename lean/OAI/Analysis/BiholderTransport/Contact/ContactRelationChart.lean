import Mathlib
import OAI.Analysis.BiholderTransport.Contact.GlobalSupport
import OAI.Analysis.BiholderTransport.Duality.RiemannianTransport
import OAI.Analysis.BiholderTransport.Volume.EuclideanVolumeFactorNe

namespace OAI

section
section
noncomputable section
open Set Filter MeasureTheory Manifold Bundle
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction

namespace WeakMTWTransport
section ContactRelationChart
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  [MeasurableSpace M] [BorelSpace M]

def chartContactRelation (a b : M) (u v : M → ℝ) (T : Set M)
    (z q : Model n) : Prop :=
  q∈(extChartAt 𝓘(ℝ,Model n) b).target ∧
  (extChartAt 𝓘(ℝ,Model n) b).symm q∈T ∧
  contactGap u v ((extChartAt 𝓘(ℝ,Model n) a).symm z)
    ((extChartAt 𝓘(ℝ,Model n) b).symm q)=0

lemma chartContactRelation_volume_upper {lam cap : ℝ} {rho0 rho1 : M → ℝ}
    (hlam : 0 < lam)
    (hrho0 : AdmissibleDensity (metricVolume n) lam cap rho0)
    (hrho1 : AdmissibleDensity (metricVolume n) lam cap rho1)
    {u v : M →ᵇ ℝ} (hdual : IsCostDualPair u v)
    (hmin : ∀ a b : M →ᵇ ℝ, (∀ x y, 0 ≤ contactGap a b x y) →
      dualObjective (densityMeasure (metricVolume n) rho0)
        (densityMeasure (metricVolume n) rho1) (u,v) ≤
      dualObjective (densityMeasure (metricVolume n) rho0)
        (densityMeasure (metricVolume n) rho1) (a,b))
    {a b : M} {A : Set (Model n)} {T : Set M} (hA : MeasurableSet A)
    (ha : A⊆(extChartAt 𝓘(ℝ,Model n) a).target) {Da Cb : ℝ≥0}
    (hDa : LipschitzOnWith Da (extChartAt 𝓘(ℝ,Model n) a).symm A)
    (hCb : LipschitzOnWith Cb (extChartAt 𝓘(ℝ,Model n) b) T) :
    ENNReal.ofReal lam*metricVolume n {q | ∃ z∈A, chartContactRelation a b u v T z q} ≤
      ENNReal.ofReal cap*((Cb:ℝ≥0∞)*(Da:ℝ≥0∞))^n*metricVolume n A := by
  let χ := extChartAt 𝓘(ℝ,Model n) a
  let ψ := extChartAt 𝓘(ℝ,Model n) b
  let X := χ.symm '' A
  let Y := contactImage u v X
  have hXm : MeasurableSet X := hA.image_of_continuousOn_injOn
    ((continuousOn_extChartAt_symm a).mono ha) (χ.symm.injOn.mono ha)
  have hmass := (dual_minimizer_contactImage_mass hlam hrho0 hrho1 hdual hmin hXm).2.2.2
  have hsub : {q | ∃ z∈A, chartContactRelation a b u v T z q}⊆ψ '' (Y∩T) := by
    rintro q ⟨z,hz,hq,hqT,hgap⟩
    refine ⟨ψ.symm q,⟨?_,hqT⟩,ψ.right_inv hq⟩
    exact ⟨χ.symm z,⟨z,hz,rfl⟩,hgap⟩
  have h1 := lipschitzOn_metricVolume_image_le (hCb.mono inter_subset_right :
    LipschitzOnWith Cb ψ (Y∩T)) n
  have h2 := lipschitzOn_metricVolume_image_le hDa n
  calc
    _ ≤ ENNReal.ofReal lam*metricVolume n (ψ '' (Y∩T)) :=
      mul_le_mul_right (measure_mono hsub) _
    _ ≤ ENNReal.ofReal lam*((Cb:ℝ≥0∞)^n*metricVolume n (Y∩T)) :=
      mul_le_mul_right h1 _
    _ ≤ ENNReal.ofReal lam*((Cb:ℝ≥0∞)^n*metricVolume n Y) :=
      mul_le_mul_right (mul_le_mul_right (measure_mono inter_subset_left) _) _
    _ = (Cb:ℝ≥0∞)^n*(ENNReal.ofReal lam*metricVolume n Y) := by ac_rfl
    _ ≤ (Cb:ℝ≥0∞)^n*(ENNReal.ofReal cap*metricVolume n X) :=
      mul_le_mul_right hmass _
    _ ≤ (Cb:ℝ≥0∞)^n*(ENNReal.ofReal cap*((Da:ℝ≥0∞)^n*metricVolume n A)) :=
      mul_le_mul_right (mul_le_mul_right h2 _) _
    _ = _ := by rw [mul_pow]; ac_rfl

end ContactRelationChart
end WeakMTWTransport

end

end

section

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section AllLocalContact
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.local_contact_global (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hdual : IsCostDualPair u v) {x y : M}
    (hmin : IsLocalMin (fun z => u z+cost z y) x) : contactGap u v x y=0 := by
  obtain ⟨p,hp,rfl⟩ := exists_minimizing_vector (n := n) x y
  have ht : (0:ℝ)<1/2 := by norm_num
  have ht1 : (1:ℝ)/2<1 := by norm_num
  have hID := contracted_minimizer_mem_injectivityDomain hp ht ht1
  have hcon := splitNormalAction_contact hp ht ht1
  simp only [splitNormalAction,normalCost,riemannianExp_zero] at hcon
  have hsub : p∈normalSubdifferential u x := by
    apply local_min_divided_cost_subgradient (t := 1/2) (by norm_num) hID
    filter_upwards [hmin] with z hz
    have H := squared_dist_divided_action_le z
      (riemannianExp x ((1/2:ℝ) • p)) (riemannianExp x p) ht ht1
    have H' : cost z (riemannianExp x p)≤
        cost z (riemannianExp x ((1/2:ℝ) • p))/(1/2)+
          cost (riemannianExp x ((1/2:ℝ) • p)) (riemannianExp x p)/(1-1/2) := by
      convert H using 1 <;> simp only [cost,div_div]
    linarith only [hz,H',hcon]
  rw [hdual.1] at hsub
  have H := (hmtw.global_support hv hsub).2
  rw [←hdual.1] at H
  have hupp : v (riemannianExp x p)≤-cost (riemannianExp x p) x-u x := by
    rw [hdual.2,cTransform_le_iff hu]
    intro a
    have h := H a
    rw [cost_symm a,cost_symm x] at h
    linarith only [h]
  have hgap := dualPair_gap_nonneg hv hdual x (riemannianExp x p)
  dsimp only [contactGap] at hgap ⊢
  rw [cost_symm (riemannianExp x p)] at hupp
  linarith only [hgap,hupp]

lemma WeakMTW.chart_local_contact_global (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hdual : IsCostDualPair u v) {a : M} {z : Model n} {y : M}
    (hz : z∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hmin : IsLocalMin (fun w => u ((extChartAt 𝓘(ℝ,Model n) a).symm w)+
      cost ((extChartAt 𝓘(ℝ,Model n) a).symm w) y) z) :
    contactGap u v ((extChartAt 𝓘(ℝ,Model n) a).symm z) y=0 := by
  let χ := extChartAt 𝓘(ℝ,Model n) a
  have hx : χ.symm z∈χ.source := χ.map_target hz
  have hc : ContinuousAt χ (χ.symm z) :=
    (continuousOn_extChartAt a (χ.symm z) hx).continuousAt
      ((isOpen_extChartAt_source a).mem_nhds hx)
  have hm : ∀ᶠ x in 𝓝 (χ.symm z), u (χ.symm z)+cost (χ.symm z) y≤u x+cost x y := by
    have H : ∀ᶠ x in 𝓝 (χ.symm z),
        u (χ.symm z)+cost (χ.symm z) y≤u (χ.symm (χ x))+cost (χ.symm (χ x)) y := by
      have HH := hc.eventually (χ.right_inv hz ▸ hmin)
      simpa only [show extChartAt 𝓘(ℝ,Model n) a=χ from rfl,χ.right_inv hz] using HH
    filter_upwards [H,(isOpen_extChartAt_source a).mem_nhds hx] with x hx1 hx2
    simpa only [χ.left_inv hx2] using hx1
  exact hmtw.local_contact_global hu hv hdual hm

end AllLocalContact
end WeakMTWTransport

end

end

end

end OAI
