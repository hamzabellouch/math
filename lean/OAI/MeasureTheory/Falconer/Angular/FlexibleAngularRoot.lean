import OAI.MeasureTheory.Falconer.Estimates.PolicyRootApplication
import OAI.MeasureTheory.Falconer.Fourier.JetNormalization

namespace OAI

/-! # Applying the recursive root estimate at the outer graph budgets -/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap ContDiff
open PlanarFalconer (sourcePolicyBlock sourceSmoothingLevels)

namespace PolicyJetData
variable {m : ℕ}

def withNormalization (P : PolicyJetData m) (Z : ℝ) (hZ : 0 < Z) : PolicyJetData m :=
  { P with Z := Z, Z_pos := hZ }

end PolicyJetData

theorem exists_flexible_angular_root
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
      P.a+100*P.q < P.t → (P.t₀:ℝ) ≤ P.t+P.σ*P.N →
      P.envelope k l Ψ ≤ (Z/P.Z)^4*P.rootBound σ κ η := by
  obtain ⟨K,L,Z,N₀,hK,hZ,hN₀,hroot⟩ := exists_policy_root_bounds
    hgnomonic hquadratic m hlam hσ hκ hκ1 hgap hη hη1 hloss hT
    φ Ψ hφ hΨ hsmooth hpos hzero hone hV hΨV hsupp minJet
  refine ⟨K,L,Z,N₀,hK,hZ,hN₀,?_⟩
  intro k l hk hl P hLam hσP hJ hq hN hi hprofile hcover hwide hbase
  let P' := P.withNormalization Z (zero_lt_one.trans_le hZ)
  have hroot' : P'.envelope K L Ψ ≤ P.rootBound σ κ η :=
    (hroot P' hLam hσP hJ hq rfl hN hi hprofile hcover hwide
      (gnomonicChart (0 : Space (m+2)))).2 hbase
  let := P.regular.probability
  let := P'.regular.probability
  let := PlanarFalconer.sourceAngularShellMeasure_finite (P.t:ℝ) Ψ hV hΨV
    (fun u hu => by by_contra hn; exact (not_lt_of_ge hu.le) (hsupp u hn).2)
  have hmass : 0 < profileModelMass P.profile P.N P.a := by unfold profileModelMass; positivity
  have hnorm : P.envelope k l Ψ ≤ (Z/P.Z)^4*P'.envelope k l Ψ :=
    jetStateEnvelope_renormalize P.Q P.ρ (fun u => P.profile (u/P.N))
      P.N P.σ P.J P.i P.masks P.separated P.separated P.Z_pos P'.Z_pos
      _ _ hmass hmass P.a P.t Ψ
  have hbudget : P'.envelope k l Ψ ≤ P'.envelope K L Ψ :=
    jetStateEnvelope_budget_mono hk hl (by norm_num) le_rfl
      P.Q P.ρ (fun u => P.profile (u/P.N)) P.N P.σ P.J P.i P.masks
      P.separated P.separated P'.Z_pos _ _ hmass hmass P.a P.t Ψ
  exact hnorm.trans (mul_le_mul_of_nonneg_left (hbudget.trans hroot') (by positivity))

end Falconer

end OAI
