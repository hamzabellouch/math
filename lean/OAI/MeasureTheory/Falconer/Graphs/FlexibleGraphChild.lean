import OAI.MeasureTheory.Falconer.Angular.FlexibleAngularRoot
import OAI.MeasureTheory.Falconer.Estimates.TwoPolicyEnergy

namespace OAI

/-! # Applying the recursive estimate to the actual outer graph children -/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap ContDiff
open PlanarFalconer (sourcePolicyBlock sourceSmoothingLevels)

namespace PolicyJetData
variable {m : ℕ}

noncomputable def rootBoundAt (P : PolicyJetData m) (c : ℕ) (σ κ η : ℝ) : ℝ :=
  4^(sourceSmoothingLevels σ κ+1)*
    (((2:ℝ)^P.N)^(2*P.policy c-
      PlanarFalconer.potential P.policy c P.t (10*sourcePolicyBlock P.N κ)+
      500*((m+3:ℕ):ℝ)*κ+10^6*(dimensionalBranchReserve (m+3) P.lam σ+σ)/κ+η)+
      ((2:ℝ)^P.N)^(-10:ℝ))

end PolicyJetData

theorem exists_flexible_graph_child
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m : ℕ) {lam σ κ η T : ℝ} (hlam : 0 ≤ lam) (hσ : 0 < σ)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hgap : σ < κ/1000)
    (hη : 0 < η) (hη1 : η ≤ 1)
    (hloss : 4000*(dimensionalBranchReserve (m+3) lam σ+σ) ≤ 1)
    (hT : (20/κ+1/σ)*(3*((m+3:ℕ):ℝ)+2)+10 < T)
    (φ : 𝓢(ℝ,ℂ)) (Ψ : ℝ → ℝ) (hφ : ∀ r, φ r = (Ψ r : ℂ))
    (hΨ : Measurable Ψ) (hsmooth : ContDiff ℝ ∞ Ψ)
    (hpos : ∀ r, 0 ≤ Ψ r) (hzero : ∀ r ≤ 0, Ψ r = 0)
    (hone : ∀ r ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ r)
    {V : ℝ} (hV : 0 ≤ V) (hΨV : ∀ r, Ψ r ≤ V)
    (hsupp : ∀ r, Ψ r ≠ 0 → r ∈ Ioo (1/4:ℝ) 4) (minJet : ℕ) :
    ∃ (K L : ℕ) (Z : ℝ) (N₀ : ℕ), minJet ≤ K ∧ 1 ≤ Z ∧ 0 < N₀ ∧
      ∀ k l : ℕ, k ≤ K → L ≤ l →
      ∀ P : PolicyJetData m, P.lam = lam → P.σ = σ →
      P.J = sourceSmoothingLevels σ κ → P.q = sourcePolicyBlock P.N κ →
      N₀ ≤ P.N → P.i = 0 → P.policy = profileExcess (d := m+3) P.profile P.N →
      (∀ b, ∀ w : Sphere (m+3), ∃ c ∈ P.masks b,
        dist w c ≤ descriptorMaskRadius P.N P.σ b/2) →
      (P.t₀:ℝ) ≤ P.t+P.σ*P.N →
      ∀ c : ℕ, P.a ≤ c → c+100*P.q < P.t →
      P.graphChild k l c Ψ ≤ (Z/P.Z)^4*P.rootBoundAt c σ κ η := by
  obtain ⟨K,L,Z,N₀,hK,hZ,hN₀,hroot⟩ := exists_flexible_angular_root
    hgnomonic hquadratic m hlam hσ hκ hκ1 hgap hη hη1 hloss hT
    φ Ψ hφ hΨ hsmooth hpos hzero hone hV hΨV hsupp minJet
  refine ⟨K,L,Z,N₀,hK,hZ,hN₀,?_⟩
  intro k l hk hl P hLam hσP hJ hq hN hi hprofile hcover hbase c hac hwide
  apply P.graphChild_le k l c hac Ψ (by unfold PolicyJetData.rootBoundAt; positivity)
  intro row hrow
  have hb := hroot k l hk hl (P.child c hac row hrow)
    hLam hσP hJ hq hN hi hprofile hcover hwide hbase
  exact hb

end Falconer

end OAI
