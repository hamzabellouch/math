import OAI.Geometry.NodalSets.Charts.SphereChartDivergenceData
import OAI.Geometry.NodalSets.Coefficients.SphereWeightedCoefficientJets

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Analysis Metric
open scoped ContDiff
noncomputable section

theorem sphere_coefficient_divergence_jet_bound (J : ℕ) :
    ∃ C > 0, ∀ (P : Finset Base) (d b : SphereEnergyData),
      ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density → ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b.density →
      ∀ p ∈ P, ∀ x ∈ closedBall (0 : Yau.Jets.Coord) 1,
      ∀ ds : List (Fin 4), ds.length ≤ J →
        (∀ i j, |partialJet (fun y ↦ sphereChartPrincipalDensity b p y i j) ds x-
          partialJet (fun y ↦ sphereChartPrincipalDensity d p y i j) ds x| ≤
            C*sphereCoefficientDistance P J d.tensor d.density b.tensor b.density) ∧
        |partialJet (fun y ↦ roundCoordDensity y*b.density (sphereChartCoordMap p y)) ds x-
          partialJet (fun y ↦ roundCoordDensity y*d.density (sphereChartCoordMap p y)) ds x| ≤
            C*sphereCoefficientDistance P J d.tensor d.density b.tensor b.density := by
  choose K hK hKb using (fun i j : Fin 4 ↦ sphere_weighted_coefficient_scalar_jet_bound J (coefficientPrincipalEntry i j))
  obtain ⟨R,hR,hRb⟩ := sphere_weighted_coefficient_scalar_jet_bound J
    (ContinuousLinearMap.snd ℝ ((BaseModel →L[ℝ] ℝ) →L[ℝ] BaseModel) ℝ)
  let C := R+∑ i, ∑ j, K i j
  have hsum : 0 ≤ ∑ i, ∑ j, K i j := Finset.sum_nonneg (fun i _ ↦ Finset.sum_nonneg (fun j _ ↦ (hK i j).le))
  have hRC : R ≤ C := by dsimp [C]; linarith
  have hKC (i j : Fin 4) : K i j ≤ C := by
    have h1 := Finset.single_le_sum (fun j _ ↦ (hK i j).le) (Finset.mem_univ j)
    have h2 := Finset.single_le_sum (fun i _ ↦ Finset.sum_nonneg (s := Finset.univ)
      (fun j _ ↦ (hK i j).le)) (Finset.mem_univ i)
    dsimp [C]
    linarith
  refine ⟨C,hR.trans_le hRC,?_⟩
  intro P d b hd hb p hp x hx ds hds
  have hD := sphereCoefficientDistance_nonneg P J d.tensor b.tensor d.density b.density
    (fun q _ ↦ intrinsic_coefficient_chart_smooth d.tensor d.smooth d.symm d.pos d.density hd q)
    (fun q _ ↦ intrinsic_coefficient_chart_smooth b.tensor b.smooth b.symm b.pos b.density hb q)
  constructor
  · intro i j
    have h := hKb i j P d b hd hb p hp x hx ds hds
    simp only [coefficientPrincipalEntry_apply] at h
    exact h.trans (mul_le_mul_of_nonneg_right (hKC i j) hD)
  · have h := hRb P d b hd hb p hp x hx ds hds
    exact h.trans (mul_le_mul_of_nonneg_right hRC hD)

end
end Yau.Target

end OAI
