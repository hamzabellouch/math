import OAI.MeasureTheory.Falconer.Recursion.PolicyWeightedRecursion
import OAI.MeasureTheory.Falconer.Estimates.PolicyRootDecay

namespace OAI

/-! # The weighted estimate on actual positive and angular root states -/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap ContDiff
open PlanarFalconer (sourcePolicyBlock sourceSmoothingLevels)

noncomputable def PolicyJetData.rootBound {m : ℕ} (P : PolicyJetData m) (σ κ η : ℝ) : ℝ :=
  4^(sourceSmoothingLevels σ κ+1)*
    (((2:ℝ)^P.N)^(2*P.policy P.a-
      PlanarFalconer.potential P.policy P.a P.t (10*sourcePolicyBlock P.N κ)+
      500*((m+3:ℕ):ℝ)*κ+10^6*(dimensionalBranchReserve (m+3) P.lam σ+σ)/κ+η)+
      ((2:ℝ)^P.N)^(-10:ℝ))

theorem exists_policy_root_bounds
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
    (hsupp : ∀ r, Ψ r ≠ 0 → r ∈ Ioo (1/4:ℝ) 4) (minJet : ℕ := 0) :
    ∃ (K L : ℕ) (Z : ℝ) (N₀ : ℕ), minJet ≤ K ∧ 1 ≤ Z ∧ 0 < N₀ ∧
      ∀ P : PolicyJetData m, P.lam = lam → P.σ = σ →
      P.J = sourceSmoothingLevels σ κ → P.q = sourcePolicyBlock P.N κ → P.Z = Z →
      N₀ ≤ P.N → P.i = 0 → P.policy = profileExcess (d := m+3) P.profile P.N →
      (∀ b, ∀ w : Sphere (m+3), ∃ c ∈ P.masks b,
        dist w c ≤ descriptorMaskRadius P.N P.σ b/2) →
      P.a+100*P.q < P.t → ∀ w₀ : Sphere (m+3),
      (P.a₀ = P.a → P.t₀ = P.t →
        125*(((m+3:ℕ):ℝ)+1)*(P.Q.descendant P.X).side ≤
          ‖(P.Q.descendant P.X).center-(P.Q.descendant P.Y).center‖ →
        ‖(P.Q.descendant P.X).center-(P.Q.descendant P.Y).center‖ ≤
          2000*(((m+3:ℕ):ℝ)+1)*(P.Q.descendant P.X).side →
        P.positiveCount w₀ ≤ P.rootBound σ κ η) ∧
      ((P.t₀:ℝ) ≤ P.t+P.σ*P.N → P.envelope K L Ψ ≤ P.rootBound σ κ η) := by
  obtain ⟨K,L,Z,N₀,hminJet,hZ,hN₀,hbound⟩ := exists_policy_weighted_recursion
    hgnomonic hquadratic m hlam hσ hκ hκ1 hgap hη hη1 hloss hT
    φ Ψ hφ hΨ hsmooth hpos hzero hone hV hΨV hsupp minJet
  refine ⟨K,L,Z,N₀,hminJet,hZ,hN₀,?_⟩
  intro P hLam hσP hJ hq hZP hN hi hprofile hcover hwide w₀
  have hwide' : P.a+100*sourcePolicyBlock P.N κ < P.t := by simpa only [hq] using hwide
  constructor
  · intro hleft hright hlo hhi
    have hs := P.positiveBranchState_valid (by omega : P.a ≤ P.t)
    have hb := hbound P.context hLam hσP hJ hq hZP hN hprofile hcover w₀
      P.positiveBranchState (by simpa only [PolicyJetData.context,hσP] using hs) hi hwide'
      (P.positiveCount w₀) (.positive P hleft hright hlo hhi)
    simpa only [PolicyJetData.rootBound,PolicyJetData.context,
      PolicyJetData.positiveBranchState,PlanarFalconer.BranchState.start,
      PlanarFalconer.BranchState.finish,hLam] using hb
  · intro hbase
    have hs := P.branchState_valid (by omega : P.a ≤ P.t) hbase
    have hb := hbound P.context hLam hσP hJ hq hZP hN hprofile hcover w₀
      P.branchState (by simpa only [PolicyJetData.context,hσP] using hs) hi hwide'
      (P.envelope K L Ψ) (.angular P)
    simpa only [PolicyJetData.rootBound,PolicyJetData.context,
      PolicyJetData.branchState,PlanarFalconer.BranchState.start,
      PlanarFalconer.BranchState.finish,hLam] using hb

end Falconer

end OAI
