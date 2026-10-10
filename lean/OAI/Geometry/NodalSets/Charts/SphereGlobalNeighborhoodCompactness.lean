import OAI.Geometry.NodalSets.Charts.SphereFiniteJetCompactness
import OAI.Geometry.NodalSets.Charts.SphereFiniteNeighborhoodBounds
import OAI.Geometry.NodalSets.Charts.SphereUniformDensityPairingLimit
import OAI.Geometry.NodalSets.Elliptic.RealBallCubeContainmentLemmas

namespace OAI

namespace Yau.Target
open MeasureTheory Manifold Set Metric Filter Yau.Geometry Yau.Analysis
open scoped ContDiff Topology
noncomputable section
local instance sphereGlobalCompactMeasurable : MeasurableSpace Base := borel Base
local instance sphereGlobalCompactBorel : BorelSpace Base := ⟨rfl⟩

theorem sphere_eigen_global_neighborhood_compactness (d₀ : SphereEnergyData)
    (hrho₀ : ∀ p : Base, ContDiff ℝ ∞ (fun x ↦ d₀.density (sphereChartCoordMap p x)))
    (mu₀ : ℝ) (n : ℕ) :
    ∃ P : Finset Base,
      (∀ x : Base, ∃ p ∈ P, ∃ z ∈ ball (0 : Yau.Jets.Coord) (1/512),
        sphereChartCoordMap p z=x) ∧
      ∃ eps > 0, ∀ (d : ℕ → SphereEnergyData) (mu : ℕ → ℝ),
        (∀ j p, ContDiff ℝ ∞ (fun x ↦ (d j).density (sphereChartCoordMap p x))) →
        (∀ j, mu j ≠ 0) →
        (∀ j p, p ∈ P → ∀ x ∈ closedBall (0 : Yau.Jets.Coord) (1/128),
          ∀ es : List (Fin 4), es.length ≤ n+6 →
            (∀ a b, |partialJet (fun z ↦ sphereChartPrincipalDensity (d j) p z a b) es x-
              partialJet (fun z ↦ sphereChartPrincipalDensity d₀ p z a b) es x| ≤ eps) ∧
            |partialJet (sphereEigenForcingCoefficient (d j) p (mu j)) es x-
              partialJet (sphereEigenForcingCoefficient d₀ p mu₀) es x| ≤ eps) →
        (∀ j p, p ∈ P → ∀ x ∈ closedBall (0 : Yau.Jets.Coord) (1/128),
          |roundCoordDensity x*(d j).density (sphereChartCoordMap p x)-
            roundCoordDensity x*d₀.density (sphereChartCoordMap p x)| ≤ eps) →
        ∀ f : ∀ j, SphereWeightedL2 (d j),
          (∀ j, sphereL2Resolvent (d j) (f j)=mu j • f j) → (∀ j, ‖f j‖=1) →
        ∃ u : ℕ → Base → ℝ,
          (∀ j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (u j)) ∧
          (∀ j, u j =ᵐ[sphereWeightedMeasure (d j).density] (f j : Base → ℝ)) ∧
          (∀ j, sphereWeightedPairing (d j).density (u j) (u j)=1) ∧
          (∀ j, u j ≠ 0) ∧
          ∃ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) n v ∧
            ∃ nu : ℕ → ℕ, StrictMono nu ∧ TendstoUniformly (fun j ↦ u (nu j)) v atTop ∧
              (∀ p ∈ P, ∀ ds : List (Fin 4), ds.length ≤ n →
                TendstoUniformlyOn (fun j ↦ partialJet (u (nu j) ∘ sphereChartCoordMap p) ds)
                  (partialJet (v ∘ sphereChartCoordMap p) ds) atTop (ball 0 (1/256))) ∧
              (TendstoUniformly (fun j ↦ (d j).density) d₀.density atTop →
                sphereWeightedPairing d₀.density v v=1 ∧ v ≠ 0) := by
  classical
  obtain ⟨P,hP⟩ := finite_sphere_coordinate_cover_radius (1/512) (by norm_num)
  obtain ⟨eps,heps,B,hB,hbound⟩ := sphere_finite_neighborhood_bounds d₀ P hrho₀ mu₀
    (n+1) (1/256) (1/128) (by norm_num) (by norm_num)
    (Yau.real_closedBall_subset_cube_interior (by norm_num))
  refine ⟨P,hP,eps,heps,?_⟩
  intro d mu hrho hmu hclose hrclose f heigen hn
  choose u hu ha huN hu0 hue using (fun j ↦
    sphere_eigen_global_normalized (d j) (hrho j) (mu j) (hmu j) (f j) (heigen j) (hn j))
  have hb : ∀ (p : {p // p ∈ P}) j (ds : List (Fin 4)), ds.length ≤ n+1 →
      ∀ x ∈ closedBall (0 : Yau.Jets.Coord) (1/256),
        |partialJet (u j ∘ sphereChartCoordMap p.val) ds x| ≤ B p := by
    intro p j ds hd x hx
    exact hbound (d j) (mu j) (hrho j) (hmu j)
      (fun p hp x hx es hes ↦ hclose j p hp x hx es (by omega)) (hrclose j)
      (f j) (heigen j) (hn j) (u j) (hu j) (ha j) p ds hd x hx
  obtain ⟨v,hv,nu,hnu,ht,hjet⟩ := sphere_finite_jet_compactness P (1/512) (1/256)
    (by norm_num) n hP u hu B hB hb
  refine ⟨u,hu,ha,huN,hu0,v,hv,nu,hnu,ht,hjet,?_⟩
  intro htr
  exact sphere_uniform_limit_normalized (fun j ↦ (d (nu j)).density) d₀.density
    (fun j ↦ (d (nu j)).continuous) d₀.continuous
    (tendstoUniformly_iff_seq_tendstoUniformly.mp htr nu hnu.tendsto_atTop) (fun j ↦ u (nu j)) v
    (fun j ↦ (hu (nu j)).continuous) hv.continuous ht (fun j ↦ huN (nu j))

end
end Yau.Target

end OAI
