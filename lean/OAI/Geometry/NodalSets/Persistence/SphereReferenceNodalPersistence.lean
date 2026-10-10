import OAI.Geometry.NodalSets.Charts.GlobalSphereEquation
import OAI.Geometry.NodalSets.Coefficients.SphereCoefficientAtlasInclusionLemmas
import OAI.Geometry.NodalSets.Hausdorff.SphereFiniteNormNodalTransfer
import OAI.Geometry.NodalSets.Persistence.LiteralNodalUniformPersistence
import OAI.Geometry.NodalSets.Persistence.SphereSimpleOrientedPersistence

namespace OAI

namespace Yau.Target
open Manifold MeasureTheory Set Yau.Geometry
open scoped ContDiff ENNReal NNReal
noncomputable section

theorem sphere_reference_literal_nodal_persistence
    (P₀ : Finset Base)
    (hcover : ∀ x : Base, ∃ p ∈ P₀, ∃ y ∈ sphereAtlasCore, (extChartAt (𝓡 4) p).symm y=x)
    (d₀ : SphereEnergyData) (hd₀ : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d₀.density)
    {H : Set Yau.Jets.Coord} (hH : IsCompact H) :
    ∃ delta > 0, ∃ C : ℝ≥0, 0 < C ∧
      ∀ (d : SphereEnergyData), ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density →
        sphereCoefficientDistance P₀ 0 d₀.tensor d₀.density d.tensor d.density < delta →
        ∀ (u : Base → ℝ), ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u → u ≠ 0 →
        ∀ lam > 0,
          (∀ p y, -intrinsicWeightedChartOperator d.tensor d.density u p y =
            lam*u ((extChartAt (𝓡 4) p).symm y)) →
          (∀ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v →
            (∀ p y, -intrinsicWeightedChartOperator d.tensor d.density v p y =
              lam*v ((extChartAt (𝓡 4) p).symm y)) → ∃ c : ℝ, v=c • u) →
          ∀ (g : Yau.Jets.Coord → Yau.Jets.Coord →L[ℝ] Yau.Jets.Coord →L[ℝ] ℝ)
            (S : Yau.Jets.Coord → ℝ) (Q U : Set Yau.Jets.Coord) (n : ℕ) (M : ℝ),
            U ⊆ H → LiteralNodalCertificate g S Q U n (fun x ↦ u (seedSphereFromCoord x)) M →
            ∃ N : ℕ, sphereIndexedEigenvalue d N=lam ∧
              ∃ P : Finset Base, P₀ ⊆ P ∧
                ∃ eta > 0, ∀ (b : SphereEnergyData) (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b.density),
                  sphereCoefficientDistance P 8 d.tensor d.density b.tensor b.density < eta →
                  sphereIndexedEigenvalue b N ∈ Icc (lam/2) (2*lam) ∧
                  ∃ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v ∧ v ≠ 0 ∧
                    (∀ p y, -intrinsicWeightedChartOperator b.tensor b.density v p y =
                      sphereIndexedEigenvalue b N*v ((extChartAt (𝓡 4) p).symm y)) ∧
                    ContMDiff modelWithCorners 𝓘(ℝ,ℝ) ∞ (circleLift v) ∧ circleLift v ≠ 0 ∧
                    (∀ x : Manifold5, -chartLaplacian
                      (intrinsicWeightedMetric b.tensor b.smooth b.symm b.pos b.density hb b.positive)
                      (extChartAt modelWithCorners x) (circleLift v) (extChartAt modelWithCorners x x) =
                        sphereIndexedEigenvalue b N*circleLift v x) ∧
                    ENNReal.ofReal (M/(C:ℝ)^4) ≤ nodalMeasure
                      (intrinsicWeightedMetric b.tensor b.smooth b.symm b.pos b.density hb b.positive) (circleLift v) := by
  classical
  obtain ⟨delta,hdelta,C,hC,Htransfer⟩ := sphere_finite_norm_uniform_nodal_transfer P₀ hcover d₀ hd₀ hH
  refine ⟨delta/2,by positivity,C,hC,?_⟩
  intro d hd hdist₀ u hu hu0 lam hlam he hsimple g S Q U n M hUH hcert
  obtain ⟨eps,heps,Hcert⟩ := hcert.uniform_persistence
  obtain ⟨N,hN,P₁,hP₁,Hspec⟩ := sphere_finite_norm_simple_oriented_persistence d hd u hu hu0 lam hlam he hsimple
  obtain ⟨eta,heta,Heta⟩ := Hspec eps heps
  refine ⟨N,hN,P₀ ∪ P₁,Finset.subset_union_left,min eta (delta/2),lt_min heta (by positivity),?_⟩
  intro b hb hdist
  have hd₁ := (sphereCoefficientDistance_mono_atlas P₁ (P₀ ∪ P₁) Finset.subset_union_right d b hd hb 8).trans_lt
    (hdist.trans_le (min_le_left _ _))
  obtain ⟨hval,v,hv,hv0,hve,hclose⟩ := Heta b hb hd₁
  have hdb : sphereCoefficientDistance P₀ 0 d.tensor d.density b.tensor b.density < delta/2 :=
    (sphereCoefficientDistance_mono_order P₀ d b hd hb 0 8 (by omega)).trans_lt
      ((sphereCoefficientDistance_mono_atlas P₀ (P₀ ∪ P₁) Finset.subset_union_left d b hd hb 8).trans_lt
        (hdist.trans_le (min_le_right _ _)))
  have htriangle := sphereCoefficientDistance_triangle P₀ 0 d₀.tensor d.tensor b.tensor
    d₀.density d.density b.density
    (fun p _ ↦ intrinsic_coefficient_chart_smooth d₀.tensor d₀.smooth d₀.symm d₀.pos d₀.density hd₀ p)
    (fun p _ ↦ intrinsic_coefficient_chart_smooth d.tensor d.smooth d.symm d.pos d.density hd p)
    (fun p _ ↦ intrinsic_coefficient_chart_smooth b.tensor b.smooth b.symm b.pos b.density hb p)
  have hnear : sphereCoefficientDistance P₀ 0 d₀.tensor d₀.density b.tensor b.density < delta := by linarith
  have hcoord := Hcert (fun x ↦ v (seedSphereFromCoord x))
    (hv.continuous.comp seedSphereFromCoord_continuous) (fun x ↦ hclose (seedSphereFromCoord x))
  have hmeasure := ofReal_le_of_fourth_power_mul_le hC (hcoord.trans (Htransfer b hb hnear v U hUH))
  have hlift := intrinsicWeightedMetric_eigenfunction b.tensor b.smooth b.symm b.pos b.density hb b.positive
    v hv hv0 (sphereIndexedEigenvalue b N)
    (intrinsic_global_equation_at_center b.tensor b.density v _ hve)
  exact ⟨hval,v,hv,hv0,hve,hlift.1,hlift.2.1,hlift.2.2,hmeasure⟩

end
end Yau.Target

end OAI
