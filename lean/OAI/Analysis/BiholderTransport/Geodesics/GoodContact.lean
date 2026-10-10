import Mathlib
import OAI.Analysis.BiholderTransport.Geodesics.OriginalMass
import OAI.Analysis.BiholderTransport.Volume.MeasurableFullSubset

namespace OAI

section
section
noncomputable section
open Set Filter MeasureTheory Metric Manifold Bundle
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction

namespace WeakMTWTransport
section GoodContact
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma minimizing_dualPair_good_contact_set {lam cap : ℝ} (hlam : 0<lam) (hcap : lam≤cap)
    {rho0 rho1 : M → ℝ}
    (h0 : AdmissibleDensity (metricVolume n) lam cap rho0)
    (h1 : AdmissibleDensity (metricVolume n) lam cap rho1)
    {u v : M →ᵇ ℝ} (huv : IsCostDualPair u v)
    (hmin : ∀ a b : M →ᵇ ℝ, (∀ x y,0≤contactGap a b x y) →
      dualObjective (densityMeasure (metricVolume n) rho0)
        (densityMeasure (metricVolume n) rho1) (u,v) ≤
      dualObjective (densityMeasure (metricVolume n) rho0)
        (densityMeasure (metricVolume n) rho1) (a,b)) :
    ∃ G : Set M, MeasurableSet G ∧ (∀ᵐ x ∂metricVolume n, x∈G) ∧
      InjOn (contactSelection v.continuous) G ∧
      (∀ x∈G, MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (cTransform v) x) ∧
      (∀ A : Set M, MeasurableSet A → A⊆G →
        ENNReal.ofReal (lam/cap)*metricVolume n A ≤
          metricVolume n (contactSelection v.continuous '' A) ∧
        metricVolume n (contactSelection v.continuous '' A) ≤
          ENNReal.ofReal (cap/lam)*metricVolume n A) := by
  let μ := densityMeasure (metricVolume n) rho0
  let ν := densityMeasure (metricVolume n) rho1
  let T := contactSelection v.continuous
  have hT (x : M) : contactGap u v x (T x)=0 := by
    rw [huv.1]
    exact contactSelection_mem v.continuous x
  have hμ : μ ≪ metricVolume n := withDensity_absolutelyContinuous _ _
  have hν : ν ≪ metricVolume n := withDensity_absolutelyContinuous _ _
  have hTm : AEMeasurable T μ := (contactSelection_aemeasurable (n := n) v.continuous).mono_ac hμ
  have hpush : Measure.map T μ=ν := minimizing_dualPair_selection_pushforward hlam h0 h1 huv hmin
  have hrev : ∀ᵐ x ∂metricVolume n, ∀ a, contactGap u v a (T x)=0 → a=x := by
    have H := hν.ae_le (cTransform_ae_unique_contact (n := n) u.continuous)
    rw [←hpush] at H
    have H' := ae_of_ae_map hTm H
    apply (volume_absolutelyContinuous_densityMeasure hlam h0).ae_le
    filter_upwards [H'] with x hx
    intro a ha
    have hax : contactGap (cTransform u) u (T x) a=0 := by
      simpa only [←huv.2,contactGap_swap _ _ (T x) a] using ha
    have hxx : contactGap (cTransform u) u (T x) x=0 := by
      simpa only [←huv.2,contactGap_swap _ _ (T x) x] using hT x
    exact hx.unique hax hxx
  obtain ⟨G,hGm,hGae,hG⟩ := exists_measurable_full_subset
    ((cTransform_ae_mdifferentiableAt (n := n) v.continuous).and hrev)
  refine ⟨G,hGm,hGae,?_,fun x hx => (hG x hx).1,?_⟩
  · intro x hx z hz he
    apply (hG z hz).2 x
    change T x=T z at he
    rw [←he]
    exact hT x
  · intro A hA hAG
    have he : contactImage u v A=T '' A := by
      ext y
      constructor
      · rintro ⟨x,hx,hxy⟩
        refine ⟨x,hx,?_⟩
        apply contact_unique_of_mdifferentiable v.continuous (hG x (hAG hx)).1
        · exact contactSelection_mem v.continuous x
        · rwa [←huv.1]
      · rintro ⟨x,hx,rfl⟩
        exact ⟨x,hx,hT x⟩
    simpa only [he] using minimizing_dualPair_contact_volume hlam hcap h0 h1 huv hmin hA

end GoodContact
end WeakMTWTransport

end

end

end

end OAI
