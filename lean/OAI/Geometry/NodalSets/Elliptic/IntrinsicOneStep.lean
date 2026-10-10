import OAI.Geometry.NodalSets.Charts.SphereSimplicityInNeighborhood
import OAI.Geometry.NodalSets.Elliptic.IntrinsicPackedQuantitativeCertificateGain
import OAI.Geometry.NodalSets.Elliptic.QuantitativeCertificateNormalization
import OAI.Geometry.NodalSets.Persistence.SphereReferenceNodalPersistence

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Set Metric
open scoped ContDiff RealInnerProductSpace ENNReal NNReal
noncomputable section

theorem intrinsic_one_step :
    ∃ r a δ : ℝ, 0 < r ∧ 0 < a ∧ 0 < δ ∧
      seedCoordCube a ⊆ seedCoordPatch r ∧ closure (seedCoordPatch r) ⊆ seedCoordBranch ∧
      ∀ (d : SphereEnergyData) (_ : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density),
        (∀ y ∈ closedBall (0 : BaseModel) r,
          dist ((intrinsicChartCoefficient d.tensor d.density seedPoint y,
            fderiv ℝ (intrinsicChartCoefficient d.tensor d.density seedPoint) y) : CoefficientFirstJet BaseModel)
            (roundCoefficientJet y) < δ) →
        ∀ K : Set Base, IsCompact K → K ⊆ seedSpherePatch r →
        (∀ x ∉ K, ∀ v w : AmbientBase,
          ⟪(x:AmbientBase),v⟫=0 → ⟪(x:AmbientBase),w⟫=0 →
          d.tensor x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w)=⟪v,w⟫) →
        (∀ x ∉ K, d.density x=1) →
        ∀ T > 0, ∀ (P : Finset Base) (J : ℕ) (eps : ℝ), 0 < eps → ∀ n₀ : ℕ,
          ∃ n : ℕ, n₀ ≤ n ∧ 0 < n ∧
            ∃ (d' : SphereEnergyData) (_ : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d'.density),
              sphereCoefficientDistance P J d.tensor d.density d'.tensor d'.density < eps ∧
              (∀ y ∈ closedBall (0 : BaseModel) r,
                dist ((intrinsicChartCoefficient d'.tensor d'.density seedPoint y,
                  fderiv ℝ (intrinsicChartCoefficient d'.tensor d'.density seedPoint) y) : CoefficientFirstJet BaseModel)
                  (roundCoefficientJet y) < δ) ∧
              ∃ K' : Set Base, IsCompact K' ∧ K ⊆ K' ∧ K' ⊆ seedSpherePatch r ∧
                (∀ x ∉ K', ∀ v w : AmbientBase,
                  ⟪(x:AmbientBase),v⟫=0 → ⟪(x:AmbientBase),w⟫=0 →
                  d'.tensor x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w)=⟪v,w⟫) ∧
                (∀ x ∉ K', d'.density x=1) ∧
                ∃ (P' : Finset Base) (eta : ℝ), 0 < eta ∧
                  ∀ (b : SphereEnergyData) (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b.density),
                    sphereCoefficientDistance P' 8 d'.tensor d'.density b.tensor b.density < eta →
                    ∃ (mu : ℝ) (v : Base → ℝ), mu ∈ Icc (seedEigenvalue n/2) (2*seedEigenvalue n) ∧
                      0 < mu ∧ ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v ∧ v ≠ 0 ∧
                      (∀ p y, -intrinsicWeightedChartOperator b.tensor b.density v p y =
                        mu*v ((extChartAt (𝓡 4) p).symm y)) ∧
                      ContMDiff modelWithCorners 𝓘(ℝ,ℝ) ∞ (circleLift v) ∧ circleLift v ≠ 0 ∧
                      (∀ x : Manifold5, -chartLaplacian
                        (intrinsicWeightedMetric b.tensor b.smooth b.symm b.pos b.density hb b.positive)
                        (extChartAt modelWithCorners x) (circleLift v) (extChartAt modelWithCorners x x) =
                          mu*circleLift v x) ∧
                      ENNReal.ofReal T < nodalMeasure
                        (intrinsicWeightedMetric b.tensor b.smooth b.symm b.pos b.density hb b.positive)
                        (circleLift v) / ENNReal.ofReal (Real.sqrt mu) := by
  classical
  obtain ⟨r,a,δ,hr,ha,hδ,hcube,hbranch,Hgain⟩ := intrinsic_packed_quantitative_certificate_gain
  refine ⟨r,a,δ,hr,ha,hδ,hcube,hbranch,?_⟩
  intro d hd hclose K hK hKP hA hrho T hT P J eps heps n₀
  obtain ⟨P₀,hP₀⟩ := finite_sphere_coefficient_atlas
  have hcover : ∀ x : Base, ∃ p ∈ P₀, ∃ y ∈ sphereAtlasCore, (extChartAt (𝓡 4) p).symm y=x := by
    intro x
    obtain ⟨p,hp,y,hy,hx⟩ := hP₀ x
    exact ⟨p,hp,y,interior_subset hy,hx⟩
  obtain ⟨delta,hdelta,C,hC,Hpersist⟩ := sphere_reference_literal_nodal_persistence P₀ hcover d hd
    (seedCoordPatch_compactClosure r)
  let e : ℝ := min eps delta/3
  have he : 0 < e := by dsimp [e]; positivity
  have heps' : 2*e < eps := by have := min_le_left eps delta; dsimp [e]; linarith
  have hdelta' : 2*e < delta := by have := min_le_right eps delta; dsimp [e]; linarith
  let Pbig := P ∪ P₀
  have hC4 : 0 < (C:ℝ)^4 := by positivity
  obtain ⟨n,hnlarge,hn0,d₁,hd₁,hdist₁,hclose₁,K₁,hK₁,hKK₁,hK₁P,hA₁,hrho₁,
    u,hu,hu0,heq,S,U,M,hM,hgain,hUP,hcert⟩ :=
    Hgain d hd hclose K hK hKP hA hrho ((C:ℝ)^4) hC4 T hT Pbig J e he n₀
  have hlam : 0 < seedEigenvalue n := seedEigenvalue_pos hn0
  obtain ⟨d₂,hd₂,hdist₂,hclose₂,K₂,hK₂,hK₁K₂,hK₂P,hA₂,hrho₂,heq₂,hsimple⟩ :=
    sphere_simplicity_in_comparison_neighborhood d₁ hd₁ hr hclose₁ K₁ hK₁ hK₁P hA₁ hrho₁
      u hu hu0 (seedEigenvalue n) hlam heq Pbig J e he
  have htriangle := sphereCoefficientDistance_triangle Pbig J d.tensor d₁.tensor d₂.tensor
    d.density d₁.density d₂.density
    (fun p _ ↦ intrinsic_coefficient_chart_smooth d.tensor d.smooth d.symm d.pos d.density hd p)
    (fun p _ ↦ intrinsic_coefficient_chart_smooth d₁.tensor d₁.smooth d₁.symm d₁.pos d₁.density hd₁ p)
    (fun p _ ↦ intrinsic_coefficient_chart_smooth d₂.tensor d₂.smooth d₂.symm d₂.pos d₂.density hd₂ p)
  have hdist : sphereCoefficientDistance Pbig J d.tensor d.density d₂.tensor d₂.density < 2*e := by linarith
  have hdistP := (sphereCoefficientDistance_mono_atlas P Pbig Finset.subset_union_left d d₂ hd hd₂ J).trans_lt hdist
  have hdist₀ : sphereCoefficientDistance P₀ 0 d.tensor d.density d₂.tensor d₂.density < delta :=
    (sphereCoefficientDistance_mono_order P₀ d d₂ hd hd₂ 0 J (Nat.zero_le _)).trans_lt
      (((sphereCoefficientDistance_mono_atlas P₀ Pbig Finset.subset_union_right d d₂ hd hd₂ J).trans_lt hdist).trans hdelta')
  obtain ⟨N,hN,P',hP',eta,heta,Heta⟩ := Hpersist d₂ hd₂ hdist₀ u hu hu0 (seedEigenvalue n) hlam
    heq₂ hsimple (intrinsicSeedCoordMetric d.tensor d.density) S (seedCoordCube a) U n M
    (hUP.trans subset_closure) hcert
  refine ⟨n,hnlarge,hn0,d₂,hd₂,hdistP.trans heps',hclose₂,K₂,hK₂,hKK₁.trans hK₁K₂,hK₂P,
    hA₂,hrho₂,P',eta,heta,?_⟩
  intro b hb hdistb
  obtain ⟨hwindow,v,hv,hv0,hve,hlift,hln,hle,hm⟩ := Heta b hb hdistb
  have hmu : 0 < sphereIndexedEigenvalue b N := (half_pos hlam).trans_le hwindow.1
  exact ⟨sphereIndexedEigenvalue b N,v,hwindow,hmu,hv,hv0,hve,hlift,hln,hle,
    quantitative_certificate_window_ratio hn0 hC4 hT hgain hmu hwindow.2 hm⟩

end
end Yau.Target

end OAI
