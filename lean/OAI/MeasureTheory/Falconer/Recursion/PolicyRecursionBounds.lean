import OAI.MeasureTheory.Falconer.Estimates.PolicyCommonBudgets
import OAI.MeasureTheory.Falconer.Estimates.PolicyFarRecurrence
import OAI.MeasureTheory.Falconer.Estimates.PolicySuffixRecurrence

namespace OAI

/-! # A common budget for all actual policy recurrences -/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap ContDiff
open PlanarFalconer (policyDepth)

def PolicyPositiveBound (m K L J : ℕ) (lam σ ε T Z : ℝ) (N₀ : ℕ) (Ψ : ℝ → ℝ) : Prop :=
  ∀ P : PolicyJetData m, P.σ = σ → P.lam = lam → P.J = J → P.Z = Z → N₀ ≤ P.N →
      P.i+1 ≤ P.J → P.a₀ = P.a → P.t₀ = P.t → P.a+100*P.q < P.t →
      P.σ*(P.N:ℝ) ≤ P.q →
      2*policyDepth P.policy P.N P.q P.a P.t ≤ P.a+P.t →
      (∀ b ∈ P.list, ∀ w : Sphere (m+3), ∃ c ∈ P.masks b,
        dist w c ≤ descriptorMaskRadius P.N P.σ b/2) →
      125*(((m+3:ℕ):ℝ)+1)*(P.Q.descendant P.X).side ≤
        ‖(P.Q.descendant P.X).center-(P.Q.descendant P.Y).center‖ →
      ‖(P.Q.descendant P.X).center-(P.Q.descendant P.Y).center‖ ≤
        2000*(((m+3:ℕ):ℝ)+1)*(P.Q.descendant P.X).side →
      ∀ (w₀ : Sphere (m+3)) (M : ℝ), 0 ≤ M →
      ((2:ℝ)^P.N)^(4*(((m+3:ℕ):ℝ)+1)*lam+ε) ≤ M →
      (∀ v ∈ Finset.Ioc P.a P.t, σ*P.N ≤ (P.t:ℝ)-v →
        ((2:ℝ)^P.N)^ε*(positiveCollisionCount w₀ P.Q P.ρ
          (fun u => P.profile (u/P.N)) P.policy P.N P.σ P.J (P.i+1) P.q P.a v P.X P.Y).toReal ≤ M) →
      (∀ v, ∀ hv : v ∈ Finset.Ioc P.a P.t, (P.t:ℝ)-v < σ*P.N →
        ∀ p, p = policyDepth P.policy P.N P.q P.a P.t → ∀ hap : P.a ≤ p,
        ∀ row, ∀ hrow : row ∈ (P.Q.descendant P.X).occupiedPaths P.ρ (p-P.a) ×ˢ
          (P.Q.descendant P.Y).occupiedPaths P.ρ (p-P.a),
        P.directWeight p lam σ ε *
          ((P.atFrequency v ((Finset.mem_Ioc.mp hv).2.trans P.base_right)).child p hap row hrow).envelope K L Ψ ≤ M) →
      P.positiveCount w₀ ≤ 3*M+((2:ℝ)^P.N)^(-T)

def PolicyFarBound (m K L : ℕ) (lam σ ε T : ℝ) (N₀ : ℕ) (Ψ : ℝ → ℝ) : Prop :=
  ∀ (P : PolicyJetData m), P.lam = lam → P.σ = σ →
      N₀ ≤ P.N → ∀ hsplit : P.a < P.splitDepth, 1 ≤ P.Z →
      ∀ (w₀ : Sphere (m+3)) (M : ℝ), 0 ≤ M →
      (∀ row, ∀ hrow : row ∈
        (P.Q.descendant P.X).occupiedPaths P.ρ (P.splitDepth-P.a) ×ˢ
          (P.Q.descendant P.Y).occupiedPaths P.ρ (P.splitDepth-P.a),
        P.farWeight P.splitDepth lam σ ε *
          (P.child P.splitDepth hsplit.le row hrow).envelope K L Ψ ≤ M) →
      (∀ b ∈ Finset.Icc (P.a+9) (P.splitDepth+6),
        ENNReal.ofReal (P.farWeight b lam σ ε)*
          farCollisionMaximum w₀ P.Q P.ρ (fun t => P.profile (t/P.N))
            P.policy P.N P.σ P.J (P.i+1) P.q b P.t P.X P.Y (b-P.a) ≤ ENNReal.ofReal M) →
      P.envelope K L Ψ ≤ 2*M+((2:ℝ)^P.N)^(-T)

def PolicySuffixBound (m J : ℕ) (lam σ ε : ℝ) (N₀ : ℕ) : Prop :=
  ∀ P : PolicyJetData m,
      P.lam = lam → P.σ = σ → P.J = J → N₀ ≤ P.N → P.i ≤ P.J →
      P.a+100*P.q < P.t → P.a+P.t < 2*policyDepth P.policy P.N P.q P.a P.t →
      125*(((m+3:ℕ):ℝ)+1)*(P.Q.descendant P.X).side ≤
        ‖(P.Q.descendant P.X).center-(P.Q.descendant P.Y).center‖ →
      ∀ (w₀ : Sphere (m+3)),
      P.positiveCount w₀ ≤ P.suffixWeight (policyDepth P.policy P.N P.q P.a P.t) lam σ ε *
        (positiveCollisionCount w₀ P.Q P.ρ (fun u => P.profile (u/P.N)) P.policy
          P.N P.σ P.J (P.i+1) P.q P.a (policyDepth P.policy P.N P.q P.a P.t) P.X P.Y).toReal

structure PolicyRecursionBounds (m K L J : ℕ) (lam σ ε T Z : ℝ)
    (N₀ : ℕ) (Ψ : ℝ → ℝ) : Prop where
  graph : PolicyGraphBound m K L J lam σ ε T Z N₀ Ψ
  positive : PolicyPositiveBound m K L J lam σ ε T Z N₀ Ψ
  far : PolicyFarBound m K L lam σ ε T N₀ Ψ
  suffix : PolicySuffixBound m J lam σ ε N₀

theorem exists_policy_recursion_bounds
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m : ℕ) {lam σ ε T : ℝ} (hlam : 0 ≤ lam) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hε : 0 < ε) (hT : 0 ≤ T) {J : ℕ} (hJ : 0 < J)
    (φ : 𝓢(ℝ,ℂ)) (Ψ : ℝ → ℝ) (hφ : ∀ r, φ r = (Ψ r : ℂ))
    (hΨ : Measurable Ψ) (hsmooth : ContDiff ℝ ∞ Ψ)
    (hpos : ∀ r, 0 ≤ Ψ r) (hzero : ∀ r ≤ 0, Ψ r = 0)
    (hone : ∀ r ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ r)
    {V : ℝ} (hV : 0 ≤ V) (hΨV : ∀ r, Ψ r ≤ V)
    (hsupp : ∀ r, Ψ r ≠ 0 → r ∈ Ioo (1/4:ℝ) 4) (minJet : ℕ := 0) :
    ∃ (K L : ℕ) (Z : ℝ) (N₀ : ℕ), minJet ≤ K ∧ 1 ≤ Z ∧
      PolicyRecursionBounds m K L J lam σ ε T Z N₀ Ψ := by
  obtain ⟨K,hminJet,hpositive⟩ := exists_policy_positive_common_budgets hgnomonic hquadratic
    m hlam hσ hσ1 hε hJ T φ Ψ hφ hΨ hpos hzero hone hV hΨV hsupp minJet
  obtain ⟨L₀,hfar⟩ := exists_policy_far_recurrence hgnomonic hquadratic m K
    hlam hσ hσ1 hε hT hsmooth hpos hsupp hV hΨV
  obtain ⟨L,Z,Np,hL,hZ,hgraph,hposstep⟩ := hpositive L₀
  obtain ⟨Nf,hfarstep⟩ := hfar L hL
  obtain ⟨Ns,hsuffix⟩ := exists_policy_positive_suffix_recurrence m hlam hσ hε hJ
  let N₀ := max Np (max Nf Ns)
  refine ⟨K,L,Z,N₀,hminJet,hZ,?_⟩
  refine ⟨?_,?_,?_,?_⟩
  · have hg : PolicyGraphBound m K L J lam σ ε T Z Np Ψ :=
      hgraph.weaken (by linarith) (by linarith)
    intro P hLam hσP hJP hZP hN
    exact hg P hLam hσP hJP hZP ((le_max_left _ _).trans hN)
  · intro P hσP hLam hJP hZP hN
    exact hposstep P hσP hLam hJP hZP ((le_max_left _ _).trans hN)
  · intro P hLam hσP hN
    exact hfarstep P hLam hσP ((le_max_left _ _).trans ((le_max_right _ _).trans hN))
  · intro P hLam hσP hJP hN
    exact hsuffix P hLam hσP hJP ((le_max_right _ _).trans ((le_max_right _ _).trans hN))

end Falconer

end OAI
