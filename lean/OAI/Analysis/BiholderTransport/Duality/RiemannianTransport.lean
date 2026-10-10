import Mathlib
import OAI.Analysis.BiholderTransport.Volume.RadialNull
import OAI.Analysis.BiholderTransport.Regularity.CompactAE
import OAI.Analysis.BiholderTransport.Coordinates.ActiveDifferentiability
import OAI.Analysis.BiholderTransport.Volume.MeasureContacts

namespace OAI

section
section
noncomputable section
open Set Filter MeasureTheory Manifold Bundle
open scoped ENNReal NNReal ContDiff Topology BoundedContinuousFunction

namespace WeakMTWTransport
section RiemannianTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  [MeasurableSpace M] [BorelSpace M]

lemma dual_minimizer_rough_transport {lam cap : ℝ} {rho0 rho1 : M → ℝ}
    (hlam : 0 < lam)
    (hrho0 : AdmissibleDensity (metricVolume n) lam cap rho0)
    (hrho1 : AdmissibleDensity (metricVolume n) lam cap rho1)
    {u v : M →ᵇ ℝ} (hdual : IsCostDualPair u v)
    (hmin : ∀ a b : M →ᵇ ℝ, (∀ x y, 0 ≤ contactGap a b x y) →
      dualObjective (densityMeasure (metricVolume n) rho0)
        (densityMeasure (metricVolume n) rho1) (u,v) ≤
      dualObjective (densityMeasure (metricVolume n) rho0)
        (densityMeasure (metricVolume n) rho1) (a,b)) :
    ∃ T S : M → M,
      (∀ x, contactGap u v x (T x) = 0) ∧
      (∀ y, contactGap u v (S y) y = 0) ∧
      (∀ᵐ x ∂(metricVolume n), ∀ y, contactGap u v x y = 0 → y = T x) ∧
      (∀ᵐ y ∂(metricVolume n), ∀ x, contactGap u v x y = 0 → x = S y) ∧
      AEMeasurable T (densityMeasure (metricVolume n) rho0) ∧
      AEMeasurable S (densityMeasure (metricVolume n) rho1) ∧
      Measure.map T (densityMeasure (metricVolume n) rho0) = densityMeasure (metricVolume n) rho1 ∧
      Measure.map S (densityMeasure (metricVolume n) rho1) = densityMeasure (metricVolume n) rho0 := by
  have : IsProbabilityMeasure (densityMeasure (metricVolume n) rho0) :=
    densityMeasure_probability hlam hrho0
  have : IsProbabilityMeasure (densityMeasure (metricVolume n) rho1) :=
    densityMeasure_probability hlam hrho1
  have hcontactT : ∀ x : M, ∃ y : M, contactGap u v x y = 0 := by
    intro x
    obtain ⟨y,hy,_⟩ := exists_cTransform_contact v.continuous x
    refine ⟨y,?_⟩
    simp only [contactGap,hdual.1,hy]
    ring
  have hcontactS : ∀ y : M, ∃ x : M, contactGap u v x y = 0 := by
    intro y
    obtain ⟨x,hx,_⟩ := exists_cTransform_contact u.continuous y
    refine ⟨x,?_⟩
    rw [contactGap_symm]
    simp only [contactGap,hdual.2,hx]
    ring
  choose T hT using hcontactT
  choose S hS using hcontactS
  have hsingleT : ∀ᵐ x ∂(metricVolume n),
      ∀ y, contactGap u v x y = 0 → y = T x := by
    filter_upwards [cTransform_ae_singleton_contacts (n := n) v.continuous] with x hx
    intro y hy
    exact hx y (T x) (by simpa only [← hdual.1] using hy)
      (by simpa only [← hdual.1] using hT x)
  have hsingleS : ∀ᵐ y ∂(metricVolume n),
      ∀ x, contactGap u v x y = 0 → x = S y := by
    filter_upwards [cTransform_ae_singleton_contacts (n := n) u.continuous] with y hy
    intro x hx
    apply hy x (S y)
    · simpa only [← hdual.2,← contactGap_symm u v x y] using hx
    · simpa only [← hdual.2,← contactGap_symm u v (S y) y] using hS y
  have hmaybeT := dual_minimum_ae_pushforward
    (densityMeasure (metricVolume n) rho0) (densityMeasure (metricVolume n) rho1) v T
    (by simpa only [← hdual.1] using hT)
    (by
      have he := (withDensity_absolutelyContinuous (metricVolume n)
        (fun x => ENNReal.ofReal (rho0 x))).ae_le hsingleT
      filter_upwards [he] with x hx
      intro y hy
      exact hx y (by simpa only [← hdual.1] using hy))
    (by
      have he : boundedCTransform v = u := by
        ext x; exact congrFun hdual.1.symm x
      simpa only [he] using hmin)
  have hmaybeS := dual_minimum_ae_pushforward
    (densityMeasure (metricVolume n) rho1) (densityMeasure (metricVolume n) rho0) u S
    (by intro y; simpa only [← hdual.2,← contactGap_symm u v (S y) y] using hS y)
    (by
      filter_upwards [(withDensity_absolutelyContinuous (metricVolume n) _).ae_le hsingleS] with y hy
      intro x hx
      apply hy x
      simpa only [← hdual.2,← contactGap_symm u v x y] using hx)
    (by
      have he : boundedCTransform u = v := by
        ext x; exact congrFun hdual.2.symm x
      simpa only [he] using dual_minimum_swap hmin)
  exact ⟨T,S,hT,hS,hsingleT,hsingleS,hmaybeT.1,hmaybeS.1,hmaybeT.2,hmaybeS.2⟩

lemma dual_minimizer_contactImage_mass {lam cap : ℝ} {rho0 rho1 : M → ℝ}
    (hlam : 0 < lam)
    (hrho0 : AdmissibleDensity (metricVolume n) lam cap rho0)
    (hrho1 : AdmissibleDensity (metricVolume n) lam cap rho1)
    {u v : M →ᵇ ℝ} (hdual : IsCostDualPair u v)
    (hmin : ∀ a b : M →ᵇ ℝ, (∀ x y, 0 ≤ contactGap a b x y) →
      dualObjective (densityMeasure (metricVolume n) rho0)
        (densityMeasure (metricVolume n) rho1) (u,v) ≤
      dualObjective (densityMeasure (metricVolume n) rho0)
        (densityMeasure (metricVolume n) rho1) (a,b))
    {A : Set M} (hA : MeasurableSet A) :
    NullMeasurableSet (contactImage u v A) (metricVolume n) ∧
      densityMeasure (metricVolume n) rho1 (contactImage u v A) =
        densityMeasure (metricVolume n) rho0 A ∧
      ENNReal.ofReal lam * metricVolume n A ≤
        ENNReal.ofReal cap * metricVolume n (contactImage u v A) ∧
      ENNReal.ofReal lam * metricVolume n (contactImage u v A) ≤
        ENNReal.ofReal cap * metricVolume n A := by
  obtain ⟨T,S,_,hS,_,hsingleS,_,hSmeas,_,hpushS⟩ :=
    dual_minimizer_rough_transport hlam hrho0 hrho1 hdual hmin
  have hs : ∀ᵐ y ∂(densityMeasure (metricVolume n) rho1),
      ∀ x, contactGap u v x y = 0 → x = S y :=
    (withDensity_absolutelyContinuous (metricVolume n) _).ae_le hsingleS
  have hm := contactImage_measure hS hs hSmeas hpushS hA
  refine ⟨?_,hm.2,(contactImage_volume_comparison hrho0 hrho1 hm.2).1,
    (contactImage_volume_comparison hrho0 hrho1 hm.2).2⟩
  exact hm.1.mono_ac (volume_absolutelyContinuous_densityMeasure hlam hrho1)

end RiemannianTransport
end WeakMTWTransport

end

end

end

end OAI
