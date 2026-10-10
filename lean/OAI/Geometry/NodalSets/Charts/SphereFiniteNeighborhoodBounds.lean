import OAI.Geometry.NodalSets.Spectral.SphereEigenGlobalNormalization
import OAI.Geometry.NodalSets.Spectral.SphereEigenNeighborhoodPointwise

namespace OAI

namespace Yau.Target
open MeasureTheory Manifold Set Metric Yau.Geometry Yau.Analysis
open scoped ContDiff
noncomputable section
local instance sphereFiniteBoundsMeasurable : MeasurableSpace Base := borel Base
local instance sphereFiniteBoundsBorel : BorelSpace Base := ⟨rfl⟩

theorem finite_positive_common_lower_bound {I : Type*} [Fintype I]
    (e : I → ℝ) (he : ∀ i, 0 < e i) : ∃ eps > 0, ∀ i, eps ≤ e i := by
  classical
  have h : ∀ P : Finset I, ∃ eps > 0, ∀ i ∈ P, eps ≤ e i := by
    intro P
    induction P using Finset.induction_on with
    | empty => exact ⟨1,by norm_num,by simp⟩
    | @insert i P hi ih =>
      obtain ⟨eps,heps,hsmall⟩ := ih
      refine ⟨min (e i) eps,lt_min (he i) heps,?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hsmall j hj)
  obtain ⟨eps,heps,hs⟩ := h Finset.univ
  exact ⟨eps,heps,fun i ↦ hs i (Finset.mem_univ i)⟩

theorem sphere_finite_neighborhood_bounds (d₀ : SphereEnergyData) (P : Finset Base)
    (hrho₀ : ∀ p : Base, ContDiff ℝ ∞ (fun x ↦ d₀.density (sphereChartCoordMap p x)))
    (mu₀ : ℝ) (n : ℕ) (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (hRO : closedBall (0 : Yau.Jets.Coord) R ⊆ interior (Yau.realCenteredCube 4 (1/64))) :
    ∃ eps > 0, ∃ B : {p // p ∈ P} → ℝ, (∀ p, 0 ≤ B p) ∧
      ∀ (d : SphereEnergyData) (mu : ℝ),
        (∀ p : Base, ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x))) → mu ≠ 0 →
        (∀ p ∈ P, ∀ x ∈ closedBall (0 : Yau.Jets.Coord) R,
          ∀ es : List (Fin 4), es.length ≤ n+5 →
            (∀ a b, |partialJet (fun z ↦ sphereChartPrincipalDensity d p z a b) es x-
              partialJet (fun z ↦ sphereChartPrincipalDensity d₀ p z a b) es x| ≤ eps) ∧
            |partialJet (sphereEigenForcingCoefficient d p mu) es x-
              partialJet (sphereEigenForcingCoefficient d₀ p mu₀) es x| ≤ eps) →
        (∀ p ∈ P, ∀ x ∈ closedBall (0 : Yau.Jets.Coord) R,
          |roundCoordDensity x*d.density (sphereChartCoordMap p x)-
            roundCoordDensity x*d₀.density (sphereChartCoordMap p x)| ≤ eps) →
        ∀ f : SphereWeightedL2 d, sphereL2Resolvent d f=mu • f → ‖f‖=1 →
        ∀ u : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u →
          u =ᵐ[sphereWeightedMeasure d.density] (f : Base → ℝ) →
          ∀ (p : {p // p ∈ P}) (ds : List (Fin 4)), ds.length ≤ n →
            ∀ x ∈ closedBall (0 : Yau.Jets.Coord) r,
              |partialJet (u ∘ sphereChartCoordMap p.val) ds x| ≤ B p := by
  classical
  choose e he K hK hb using (fun p : {p // p ∈ P} ↦
    sphere_eigen_neighborhood_pointwise d₀ p.val (hrho₀ p.val) mu₀ n 0 r R hr hR hRO)
  obtain ⟨eps,heps,hsmall⟩ := finite_positive_common_lower_bound e he
  refine ⟨eps,heps,(fun p ↦ Real.sqrt (K p)),(fun p ↦ Real.sqrt_nonneg _),?_⟩
  intro d mu hrho hmu hclose hrclose f heigen hn u hu ha p ds hd x hx
  have hachart : (u ∘ sphereChartCoordMap p.val) =ᵐ[
      volume.restrict (Yau.realCenteredCube 4 (1/32))]
        (fun x ↦ f (sphereChartCoordMap p.val x)) :=
    ae_restrict_of_ae ((sphereWeightedMeasure_ae_chart_iff d p.val _).mp ha)
  have hb' := hb p d mu (hrho p.val) hmu (by
    intro x hx es hes
    exact ⟨fun a b ↦ ((hclose p.val p.property x hx es hes).1 a b).trans (hsmall p),
      (hclose p.val p.property x hx es hes).2.trans (hsmall p)⟩)
    (fun x hx ↦ (hrclose p.val p.property x hx).trans (hsmall p)) f heigen
    (u ∘ sphereChartCoordMap p.val) ((hu.comp (sphereChartCoordMap_smooth p.val)).contDiff)
    hachart ds hd x hx
  rw [hn,one_pow,mul_one] at hb'
  simpa only [Real.sqrt_sq_eq_abs] using Real.sqrt_le_sqrt hb'

end
end Yau.Target

end OAI
