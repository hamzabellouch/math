import OAI.Geometry.NodalSets.Charts.SphereChartLimitGluing
import OAI.Geometry.NodalSets.Elliptic.UniformSubsequenceLimit

namespace OAI

namespace Yau.Target
open Manifold Yau.Analysis Yau.Geometry Set Metric Filter
open scoped Topology ContDiff
noncomputable section
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

theorem sphere_global_smooth_subsequence (A : T → IntrinsicTensor) (rho : T → Base → ℝ)
    (hA : ∀ t, IntrinsicTensorSmooth (A t))
    (hs : ∀ t p v w, A t p v w = A t p w v) (hp : ∀ t p v, v ≠ 0 → 0 < A t p v v)
    (hr : ∀ t, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (rho t)) (hrp : ∀ t p, 0 < rho t p)
    (hrjoint : Continuous (fun z : T × Base ↦ rho z.1 z.2)) (lam : ℝ)
    (hCjoint : ∀ p i j ds, Continuous (fun z : T × Yau.Jets.Coord ↦
      partialJet (fun x ↦ intrinsicDivergencePrincipal (A z.1) p x i j) ds z.2))
    (hVjoint : ∀ p ds, Continuous (fun z : T × Yau.Jets.Coord ↦
      partialJet (intrinsicDivergencePotential (rho z.1) lam p) ds z.2))
    (t : ℕ → T) (w : ℕ → Base → ℝ) (hw : ∀ j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (w j))
    (he : ∀ j q z, -intrinsicWeightedChartOperator (A (t j)) (rho (t j)) (w j) q z =
      lam*w j ((extChartAt (𝓡 4) q).symm z))
    (hn : ∀ j, sphereWeightedPairing (rho (t j)) (w j) (w j)=1)  :
    ∃ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v ∧ ∃ nu : ℕ → ℕ, StrictMono nu ∧
      TendstoUniformly (fun j ↦ w (nu j)) v atTop ∧
      (∀ p ds (Q : Set Yau.Jets.Coord), IsCompact Q →
        TendstoUniformlyOn (fun j ↦ partialJet (w (nu j) ∘ sphereChartCoordMap p) ds)
          (partialJet (v ∘ sphereChartCoordMap p) ds) atTop Q) ∧
      (∀ p n (Q : Set Yau.Jets.Coord), IsCompact Q →
        TendstoUniformlyOn (fun j ↦ iteratedFDeriv ℝ n (w (nu j) ∘ sphereChartCoordMap p))
          (iteratedFDeriv ℝ n (v ∘ sphereChartCoordMap p)) atTop Q) := by
  obtain ⟨P,hP⟩ := finite_sphere_coordinate_cover
  obtain ⟨nu,hnu,hcharts⟩ := sphere_finite_atlas_subsequence A rho hA hs hp hr hrp
    hrjoint lam hCjoint hVjoint t w hw he hn P
  have hvalues (p : Base) (hp : p ∈ P) : ∃ f : Yau.Jets.Coord → ℝ,
      ContDiff ℝ ∞ f ∧ ∀ Q : Set Yau.Jets.Coord, IsCompact Q →
        TendstoUniformlyOn (fun j ↦ w (nu j) ∘ sphereChartCoordMap p) f atTop Q := by
    obtain ⟨f,hf,hpartial,_⟩ := hcharts p hp
    exact ⟨f,hf,hpartial []⟩
  obtain ⟨v,hv,hval,_⟩ := sphere_chart_limit_gluing P hP (fun j ↦ w (nu j)) hvalues
  have hsub (p : Base) (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop) :
      ∃ mu : ℕ → ℕ,
        (∀ ds (Q : Set Yau.Jets.Coord), IsCompact Q →
          TendstoUniformlyOn (fun j ↦ partialJet (w (nu (ns (mu j))) ∘ sphereChartCoordMap p) ds)
            (partialJet (v ∘ sphereChartCoordMap p) ds) atTop Q) ∧
        (∀ n (Q : Set Yau.Jets.Coord), IsCompact Q →
          TendstoUniformlyOn (fun j ↦ iteratedFDeriv ℝ n (w (nu (ns (mu j))) ∘ sphereChartCoordMap p))
            (iteratedFDeriv ℝ n (v ∘ sphereChartCoordMap p)) atTop Q) := by
    obtain ⟨f,hf,mu,hmu,hpartial,hderiv⟩ := sphere_normalized_chart_subsequence A rho hA hs hp hr hrp
      hrjoint lam p (hCjoint p) (hVjoint p) (fun j ↦ t (nu (ns j)))
      (fun j ↦ w (nu (ns j))) (fun j ↦ hw _) (fun j ↦ he _) (fun j ↦ hn _)
    have heq : f = v ∘ sphereChartCoordMap p := by
      funext x
      exact tendsto_nhds_unique ((hpartial [] {x} isCompact_singleton).tendsto_at (mem_singleton x))
        ((hval.tendsto_at (sphereChartCoordMap p x)).comp (hns.comp hmu.tendsto_atTop))
    rw [heq] at hpartial hderiv
    exact ⟨mu,hpartial,hderiv⟩
  refine ⟨v,hv,nu,hnu,hval,?_,?_⟩
  · intro p ds Q hQ
    apply uniformOn_of_subsequence_limits
    intro ns hns
    obtain ⟨mu,hm,_⟩ := hsub p ns hns
    exact ⟨mu,hm ds Q hQ⟩
  · intro p n Q hQ
    apply uniformOn_of_subsequence_limits
    intro ns hns
    obtain ⟨mu,_,hm⟩ := hsub p ns hns
    exact ⟨mu,hm n Q hQ⟩

end
end Yau.Target

end OAI
