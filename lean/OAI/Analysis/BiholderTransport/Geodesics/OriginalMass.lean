import Mathlib
import OAI.Analysis.BiholderTransport.Volume.RadialNull
import OAI.Analysis.BiholderTransport.Volume.MeasureContacts
import OAI.Analysis.BiholderTransport.Duality.AEDual
import OAI.Analysis.BiholderTransport.Volume.AESelection
import OAI.Analysis.BiholderTransport.Contact.ContactImage

namespace OAI

section
section
noncomputable section
open Set Filter MeasureTheory Metric Manifold Bundle
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction

namespace WeakMTWTransport
section OriginalMass
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma minimizing_dualPair_selection_pushforward {lam cap : ℝ} (hlam : 0<lam)
    {rho0 rho1 : M → ℝ}
    (h0 : AdmissibleDensity (metricVolume n) lam cap rho0)
    (h1 : AdmissibleDensity (metricVolume n) lam cap rho1)
    {u v : M →ᵇ ℝ} (huv : IsCostDualPair u v)
    (hmin : ∀ a b : M →ᵇ ℝ, (∀ x y,0≤contactGap a b x y) →
      dualObjective (densityMeasure (metricVolume n) rho0)
        (densityMeasure (metricVolume n) rho1) (u,v) ≤
      dualObjective (densityMeasure (metricVolume n) rho0)
        (densityMeasure (metricVolume n) rho1) (a,b)) :
    Measure.map (contactSelection v.continuous) (densityMeasure (metricVolume n) rho0)=
      densityMeasure (metricVolume n) rho1 := by
  let : IsProbabilityMeasure (densityMeasure (metricVolume n) rho0) := densityMeasure_probability hlam h0
  let : IsProbabilityMeasure (densityMeasure (metricVolume n) rho1) := densityMeasure_probability hlam h1
  have heq : u=boundedCTransform v := by
    ext x
    exact congrFun huv.1 x
  have habs : densityMeasure (metricVolume n) rho0 ≪ metricVolume n :=
    withDensity_absolutelyContinuous (metricVolume (M := M) n) _
  apply dual_minimum_pushforward_ae _ _ v (contactSelection v.continuous)
    ((contactSelection_aemeasurable (n := n) v.continuous).mono_ac habs)
  · filter_upwards [habs.ae_le (cTransform_ae_unique_contact (n := n) v.continuous)] with x hx
    exact ⟨contactSelection_mem v.continuous x,
      fun y hy => hx.unique hy (contactSelection_mem v.continuous x)⟩
  · simpa only [heq] using hmin

lemma minimizing_dualPair_contact_mass {lam cap : ℝ} (hlam : 0<lam)
    {rho0 rho1 : M → ℝ}
    (h0 : AdmissibleDensity (metricVolume n) lam cap rho0)
    (h1 : AdmissibleDensity (metricVolume n) lam cap rho1)
    {u v : M →ᵇ ℝ} (huv : IsCostDualPair u v)
    (hmin : ∀ a b : M →ᵇ ℝ, (∀ x y,0≤contactGap a b x y) →
      dualObjective (densityMeasure (metricVolume n) rho0)
        (densityMeasure (metricVolume n) rho1) (u,v) ≤
      dualObjective (densityMeasure (metricVolume n) rho0)
        (densityMeasure (metricVolume n) rho1) (a,b))
    {A : Set M} (hA : MeasurableSet A) :
    densityMeasure (metricVolume n) rho1 (contactImage u v A)=
      densityMeasure (metricVolume n) rho0 A := by
  have hrev : ∀ a b : M →ᵇ ℝ, (∀ x y,0≤contactGap a b x y) →
      dualObjective (densityMeasure (metricVolume n) rho1)
        (densityMeasure (metricVolume n) rho0) (v,u) ≤
      dualObjective (densityMeasure (metricVolume n) rho1)
        (densityMeasure (metricVolume n) rho0) (a,b) := by
    intro a b hab
    have H := hmin b a (fun x y => by rw [contactGap_swap]; exact hab y x)
    simpa only [dualObjective,add_comm] using H
  have hp := minimizing_dualPair_selection_pushforward hlam h1 h0
    ⟨huv.2,huv.1⟩ hrev
  have habs : densityMeasure (metricVolume n) rho1 ≪ metricVolume n :=
    withDensity_absolutelyContinuous (metricVolume (M := M) n) _
  have hc : ∀ y,contactGap u v (contactSelection u.continuous y) y=0 := by
    intro y
    rw [contactGap_swap,huv.2]
    exact contactSelection_mem u.continuous y
  have hs : ∀ᵐ y ∂densityMeasure (metricVolume n) rho1,
      ∀ x,contactGap u v x y=0 → x=contactSelection u.continuous y := by
    filter_upwards [habs.ae_le (cTransform_ae_unique_contact (n := n) u.continuous)] with y hy
    intro x hx
    rw [contactGap_swap,huv.2] at hx
    exact hy.unique hx (contactSelection_mem u.continuous y)
  exact (contactImage_measure hc hs
    ((contactSelection_aemeasurable (n := n) u.continuous).mono_ac habs) hp hA).2

lemma minimizing_dualPair_contact_volume {lam cap : ℝ} (hlam : 0<lam) (hcap : lam≤cap)
    {rho0 rho1 : M → ℝ}
    (h0 : AdmissibleDensity (metricVolume n) lam cap rho0)
    (h1 : AdmissibleDensity (metricVolume n) lam cap rho1)
    {u v : M →ᵇ ℝ} (huv : IsCostDualPair u v)
    (hmin : ∀ a b : M →ᵇ ℝ, (∀ x y,0≤contactGap a b x y) →
      dualObjective (densityMeasure (metricVolume n) rho0)
        (densityMeasure (metricVolume n) rho1) (u,v) ≤
      dualObjective (densityMeasure (metricVolume n) rho0)
        (densityMeasure (metricVolume n) rho1) (a,b))
    {A : Set M} (hA : MeasurableSet A) :
    ENNReal.ofReal (lam/cap)*metricVolume n A ≤ metricVolume n (contactImage u v A) ∧
      metricVolume n (contactImage u v A) ≤ ENNReal.ofReal (cap/lam)*metricVolume n A := by
  have hm := minimizing_dualPair_contact_mass hlam h0 h1 huv hmin hA
  have ha := (densityMeasure_bounds h0).1 A
  have hb := (densityMeasure_bounds h0).2 A
  have hc := (densityMeasure_bounds h1).1 (contactImage u v A)
  have hd := (densityMeasure_bounds h1).2 (contactImage u v A)
  simp only [Measure.smul_apply,smul_eq_mul] at ha hb hc hd
  rw [hm] at hc hd
  have hcap' := hlam.trans_le hcap
  have hdiv (a b c : ℝ≥0∞) : a/b*c=a*c/b := by
    simp only [div_eq_mul_inv,mul_right_comm]
  constructor
  · rw [ENNReal.ofReal_div_of_pos hcap',hdiv,
      ENNReal.div_le_iff' (ENNReal.ofReal_pos.mpr hcap').ne' ENNReal.ofReal_ne_top]
    exact ha.trans hd
  · rw [ENNReal.ofReal_div_of_pos hlam,hdiv,
      ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.mpr hlam).ne')
        (Or.inl ENNReal.ofReal_ne_top),mul_comm]
    exact hc.trans hb

end OriginalMass
end WeakMTWTransport

end

end

end

end OAI
