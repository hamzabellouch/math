import OAI.Geometry.NodalSets.Charts.SphereSimplicity
import OAI.Geometry.NodalSets.Elliptic.SmallRoundComparisonNeighborhood

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Set Metric
open scoped ContDiff RealInnerProductSpace
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] intrinsicRoundPerturbationLocalInst3 intrinsicRoundPerturbationLocalInst4 intrinsicRoundPerturbationLocalInst5 intrinsicRoundPerturbationLocalInst6 intrinsicRoundPerturbationLocalInst7 intrinsicRoundPerturbationLocalInst8 intrinsicRoundPerturbationLocalInst9 intrinsicRoundPerturbationLocalInst10 intrinsicRoundPerturbationLocalInst11 intrinsicRoundPerturbationLocalInst12 intrinsicRoundPerturbationLocalInst13 intrinsicRoundPerturbationLocalInst14 intrinsicRoundPerturbationLocalInst15 intrinsicRoundPerturbationLocalInst16 intrinsicRoundPerturbationLocalInst17 intrinsicRoundPerturbationLocalInst18

theorem sphere_simplicity_in_comparison_neighborhood
    (d : SphereEnergyData) (hd : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density)
    {r delta : ℝ} (hr : 0 < r)
    (hclose : ∀ y ∈ closedBall (0 : BaseModel) r,
      dist ((intrinsicChartCoefficient d.tensor d.density seedPoint y,
        fderiv ℝ (intrinsicChartCoefficient d.tensor d.density seedPoint) y) : CoefficientFirstJet BaseModel)
        (roundCoefficientJet y) < delta)
    (K : Set Base) (hK : IsCompact K) (hKP : K ⊆ seedSpherePatch r)
    (hA : ∀ x ∉ K, ∀ v w : AmbientBase, ⟪(x:AmbientBase),v⟫=0 → ⟪(x:AmbientBase),w⟫=0 →
      d.tensor x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w)=⟪v,w⟫)
    (hrho : ∀ x ∉ K, d.density x=1)
    (u : Base → ℝ) (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (hu0 : u ≠ 0)
    (lam : ℝ) (hlam : 0 < lam)
    (he : ∀ p y, -intrinsicWeightedChartOperator d.tensor d.density u p y =
      lam*u ((extChartAt (𝓡 4) p).symm y))
    (P : Finset Base) (J : ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∃ (b : SphereEnergyData) (_ : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b.density),
      sphereCoefficientDistance P J d.tensor d.density b.tensor b.density < eps ∧
      (∀ y ∈ closedBall (0 : BaseModel) r,
        dist ((intrinsicChartCoefficient b.tensor b.density seedPoint y,
          fderiv ℝ (intrinsicChartCoefficient b.tensor b.density seedPoint) y) : CoefficientFirstJet BaseModel)
          (roundCoefficientJet y) < delta) ∧
      ∃ K' : Set Base, IsCompact K' ∧ K ⊆ K' ∧ K' ⊆ seedSpherePatch r ∧
        (∀ x ∉ K', ∀ v w : AmbientBase, ⟪(x:AmbientBase),v⟫=0 → ⟪(x:AmbientBase),w⟫=0 →
          b.tensor x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w)=⟪v,w⟫) ∧
        (∀ x ∉ K', b.density x=1) ∧
        (∀ p y, -intrinsicWeightedChartOperator b.tensor b.density u p y =
          lam*u ((extChartAt (𝓡 4) p).symm y)) ∧
        (∀ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v →
          (∀ p y, -intrinsicWeightedChartOperator b.tensor b.density v p y =
            lam*v ((extChartAt (𝓡 4) p).symm y)) → ∃ c : ℝ, v=c • u) := by
  obtain ⟨Q,a,b,hQ,hQP,ha,hb,haQ,hbQ,himage,himageP,hext,H⟩ :=
    exists_sphere_simplicity_perturbation d.tensor d.smooth d.symm d.pos d.density hd d.positive
      u hu hu0 lam hlam he r hr
  obtain ⟨eta,heta,Heta⟩ := small_round_perturbation_in_comparison_neighborhood d hd a b ha hb hr.le hclose
  obtain ⟨ds,hds,Hds⟩ := H P J eps heps
  let t : ℝ := min eta ds/2
  have ht : 0 < t := by dsimp [t]; positivity
  have hteta : |t| < eta := by rw [abs_of_pos ht]; have := min_le_left eta ds; dsimp [t]; linarith
  have htds : |t| < ds := by rw [abs_of_pos ht]; have := min_le_right eta ds; dsimp [t]; linarith
  obtain ⟨h1,h2,h3,h4,h5,h6,he',hsimple⟩ := Hds t htds ht.ne'
  let d' : SphereEnergyData := ⟨_,h1,h2,h3,_,h4.continuous,h5⟩
  refine ⟨d',h4,h6,Heta t hteta,K ∪ seedSphereFromCoord '' Q,
    hK.union himage,subset_union_left,union_subset hKP himageP,?_,?_,he',hsimple⟩
  · intro x hx v w hv hw
    change (d.tensor x+roundTensorPerturbation (fun y ↦ t*a y) x) _ _ = _
    rw [(hext t x (fun h ↦ hx (Or.inr h))).1]
    exact hA x (fun h ↦ hx (Or.inl h)) v w hv hw
  · intro x hx
    change d.density x+t*b x=1
    rw [(hext t x (fun h ↦ hx (Or.inr h))).2]
    exact hrho x (fun h ↦ hx (Or.inl h))

end
end Yau.Target

end OAI
