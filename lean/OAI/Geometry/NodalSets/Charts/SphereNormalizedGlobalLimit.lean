import OAI.Geometry.NodalSets.Charts.SphereGlobalSmoothCompactness
import OAI.Geometry.NodalSets.Charts.SphereLimitEquation
import OAI.Geometry.NodalSets.Charts.SphereWeightedPairingLimit

namespace OAI

namespace Yau.Target
open Manifold Yau.Analysis Yau.Geometry Set Metric Filter
open scoped Topology ContDiff
noncomputable section
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

theorem sphere_normalized_global_limit (A : T → IntrinsicTensor) (rho : T → Base → ℝ)
    (hA : ∀ t, IntrinsicTensorSmooth (A t))
    (hs : ∀ t p v w, A t p v w = A t p w v) (hp : ∀ t p v, v ≠ 0 → 0 < A t p v v)
    (hr : ∀ t, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (rho t)) (hrp : ∀ t p, 0 < rho t p)
    (hrjoint : Continuous (fun z : T × Base ↦ rho z.1 z.2)) (lam : ℝ)
    (hCjoint : ∀ p i j ds, Continuous (fun z : T × Yau.Jets.Coord ↦
      partialJet (fun x ↦ intrinsicDivergencePrincipal (A z.1) p x i j) ds z.2))
    (hVjoint : ∀ p ds, Continuous (fun z : T × Yau.Jets.Coord ↦
      partialJet (intrinsicDivergencePotential (rho z.1) lam p) ds z.2))
    (t : ℕ → T) (t0 : T) (ht : Tendsto t atTop (𝓝 t0)) (w : ℕ → Base → ℝ) (hw : ∀ j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (w j))
    (he : ∀ j q z, -intrinsicWeightedChartOperator (A (t j)) (rho (t j)) (w j) q z =
      lam*w j ((extChartAt (𝓡 4) q).symm z))
    (hn : ∀ j, sphereWeightedPairing (rho (t j)) (w j) (w j)=1)
    (u : Base → ℝ) (hu : Continuous u)
    (ho : ∀ j, sphereWeightedPairing (rho (t j)) (w j) u=0) :
    ∃ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v ∧ v ≠ 0 ∧
      (∀ p z, -intrinsicWeightedChartOperator (A t0) (rho t0) v p z =
        lam*v ((extChartAt (𝓡 4) p).symm z)) ∧
      sphereWeightedPairing (rho t0) v v=1 ∧ sphereWeightedPairing (rho t0) v u=0 ∧
      ∃ nu : ℕ → ℕ, StrictMono nu ∧ TendstoUniformly (fun j ↦ w (nu j)) v atTop ∧
        (∀ p ds (Q : Set Yau.Jets.Coord), IsCompact Q →
          TendstoUniformlyOn (fun j ↦ partialJet (w (nu j) ∘ sphereChartCoordMap p) ds)
            (partialJet (v ∘ sphereChartCoordMap p) ds) atTop Q) ∧
        (∀ p n (Q : Set Yau.Jets.Coord), IsCompact Q →
          TendstoUniformlyOn (fun j ↦ iteratedFDeriv ℝ n (w (nu j) ∘ sphereChartCoordMap p))
            (iteratedFDeriv ℝ n (v ∘ sphereChartCoordMap p)) atTop Q) := by
  obtain ⟨v,hv,nu,hnu,hval,hpartial,hderiv⟩ := sphere_global_smooth_subsequence A rho hA hs hp hr hrp
    hrjoint lam hCjoint hVjoint t w hw he hn
  have ht' := ht.comp hnu.tendsto_atTop
  have hev := sphere_limit_equation A rho hA hs hp hrp lam hCjoint hVjoint (t ∘ nu) t0 ht'
    (fun j ↦ w (nu j)) v (fun j ↦ hw _) hv (fun j ↦ he _)
    (fun p ds x ↦ (hpartial p ds {x} isCompact_singleton).tendsto_at (mem_singleton x))
  have hnorm : sphereWeightedPairing (rho t0) v v=1 := by
    apply tendsto_nhds_unique (sphereWeightedPairing_family_limit rho hrjoint (t ∘ nu) t0 ht'
      (fun j ↦ w (nu j)) (fun j ↦ w (nu j)) v v
      (fun j ↦ (hw _).continuous) (fun j ↦ (hw _).continuous) hv.continuous hv.continuous hval hval)
    simpa only [Function.comp_apply,hn] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1:ℝ)) atTop (𝓝 1))
  have hortho : sphereWeightedPairing (rho t0) v u=0 := by
    apply tendsto_nhds_unique (sphereWeightedPairing_family_limit rho hrjoint (t ∘ nu) t0 ht'
      (fun j ↦ w (nu j)) (fun _ ↦ u) v u (fun j ↦ (hw _).continuous)
      (fun _ ↦ hu) hv.continuous hu hval (by
        rw [Metric.tendstoUniformly_iff]
        exact fun eps heps ↦ Eventually.of_forall (fun _ _ ↦ by simpa using heps)))
    simpa only [Function.comp_apply,ho] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0:ℝ)) atTop (𝓝 0))
  have hvne : v ≠ 0 := by
    intro hzero
    simp [hzero,sphereWeightedPairing] at hnorm
  exact ⟨v,hv,hvne,hev,hnorm,hortho,nu,hnu,hval,hpartial,hderiv⟩

end
end Yau.Target

end OAI
