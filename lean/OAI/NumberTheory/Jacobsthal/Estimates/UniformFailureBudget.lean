import OAI.NumberTheory.Jacobsthal.Paths.FlaggedSourceStart

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.UniformFailureBudget

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualProcessCoupling ActualFlagInvariant ActualCouplingUpdates ActualCouplingError
open NearbyParentGeometry ActualSupportIntervals PrimeBinMembership RegeneratingInverseBands

noncomputable def upperDisplacement (S mesh : ℝ) (N : ℕ) : ℝ :=
  (S+1)*(Real.exp (4*(N:ℝ)*mesh)-1)

noncomputable def stepBudget (c₁ c₂ C₁ C₂ C₃ D w S mesh : ℝ) (N : ℕ) : ℝ :=
  2*((S/mesh+2)*(C₁*(1+S)^5*(mesh^2+Real.exp (-c₁*Real.sqrt ((1/2:ℝ)*Real.log w))))+
    epsilon w+(Real.exp (D*(1+S)^3*mesh)-1)+
    C₂*(1+S)^2*(upperDisplacement S mesh N+3*mesh+2*Real.exp (-c₂*Real.sqrt ((1/2:ℝ)*Real.log w)))+
    C₃*(1+S)^2*(upperDisplacement S mesh N+3*mesh))

theorem upperDisplacement_nonneg {S mesh : ℝ} (hS : 0 ≤ S+1) (hm : 0 ≤ mesh) (N : ℕ) :
    0 ≤ upperDisplacement S mesh N := by
  apply mul_nonneg hS
  apply sub_nonneg.mpr
  apply Real.one_le_exp_iff.mpr
  positivity

theorem stepBudget_nonneg {c₁ c₂ C₁ C₂ C₃ D w S mesh : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hC₃ : 0 ≤ C₃) (hD : 0 ≤ D) (hS : 0 ≤ S) (hm : 0 ≤ mesh) (N : ℕ) :
    0 ≤ stepBudget c₁ c₂ C₁ C₂ C₃ D w S mesh N := by
  have hS1 : 0 ≤ S+1 := by linarith
  have hu := upperDisplacement_nonneg hS1 hm N
  have he : 0 ≤ Real.exp (D*(1+S)^3*mesh)-1 := by
    apply sub_nonneg.mpr
    apply Real.one_le_exp_iff.mpr
    positivity
  have hEps := (epsilon_pos w).le
  unfold stepBudget
  positivity

theorem uniform_actual_bad_row : ∃ c₁ c₂ C₁ C₂ C₃ D w₀ : ℝ,
    0 < c₁ ∧ 0 < c₂ ∧ 0 < C₁ ∧ 0 < C₂ ∧ 0 < C₃ ∧ 0 < D ∧ 1 < w₀ ∧
    ∀ w : ℝ, w₀ ≤ w → ∀ ell S : ℝ, ∀ start : Node, ∀ v mesh : ℝ, ∀ N : ℕ,
      ∀ (hnorm : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS3 : 3 ≤ S) (hS : S ≤ (Real.log w)^3)
        (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S),
      Consistent start → 0 < mesh → 2*mesh ≤ 1 → upperDisplacement S mesh N+mesh ≤ 1 →
      ∀ n ≤ N, ∀ q : JointState w ell S start, GoodAt v mesh n q →
        jointKernel hnorm hell (show 0 ≤ S from by linarith) hS hr hs hsS v mesh q {y | mismatch mesh y} ≤
          ENNReal.ofReal (stepBudget c₁ c₂ C₁ C₂ C₃ D w S mesh N) := by
  obtain ⟨c₁,c₂,C₁,C₂,C₃,D,w₀,hc₁,hc₂,hC₁,hC₂,hC₃,hD,hw₀,hbound⟩ := actual_one_step_failure
  refine ⟨c₁,c₂,C₁,C₂,C₃,D,w₀,hc₁,hc₂,hC₁,hC₂,hC₃,hD,hw₀,?_⟩
  intro w hw ell S start v mesh N hnorm hell hS3 hS hr hs hsS hcons hm hmesh hupper n hn q hq
  have hS1 : 0 ≤ S+1 := by linarith
  rcases q with ⟨p,z⟩
  cases p with
  | none =>
    cases z with
    | inl z => exact False.elim hq
    | inr u =>
      cases u
      have hnot : ∀ᵐ y ∂jointKernel hnorm hell (by linarith) hS hr hs hsS v mesh (none,CemeteryKernel.dead),
          ¬mismatch mesh y := by
        filter_upwards [joint_dead_ae hnorm hell (by linarith) hS hr hs hsS v mesh] with y hy
        rw [hy]
        change ¬(MeshRatioLabels.cemeteryLabel S mesh ≠ MeshRatioLabels.cemeteryLabel S mesh)
        exact not_not.mpr rfl
      have hzero : jointKernel hnorm hell (by linarith) hS hr hs hsS v mesh (none,CemeteryKernel.dead)
          {y | mismatch mesh y} = 0 := by
        simpa only [not_not] using ae_iff.mp hnot
      exact hzero.le.trans zero_le
  | some h =>
    cases z with
    | inr u => exact False.elim hq
    | inl z =>
      have hgap := terminal_gap_positive (show 0 ≤ ell by linarith) hr hs h.admissible
      have hnR : (n:ℝ) ≤ (N:ℝ) := by exact_mod_cast hn
      have hgapN : |Real.log h.node.gap-Real.log (gapValue v z)| ≤ 4*(N:ℝ)*mesh :=
        hq.2.2.2.trans (mul_le_mul_of_nonneg_right (by linarith) hm.le)
      have hdl : |minRatio h.node.side h.node.ratio-minRatio (stateSide z.1) (stateRatio z.1)| ≤ mesh := by
        rw [← hq.2.1]
        exact (minRatio_stability _ _ _).trans hq.2.2.1
      have hdu : |upperSupport S ell h.node.gap-upperSupport S ell (gapValue v z)| ≤ upperDisplacement S mesh N :=
        arrival_endpoint_stability hgap (Real.exp_pos _) (by linarith) hS1 hgapN
      have hp := hbound w hw ell S start h v z mesh hnorm hell hS3 hS hr hs hsS hcons hq.1 hq.2.1 hm
        (by linarith) (by linarith)
      refine hp.trans (ENNReal.ofReal_le_ofReal ?_)
      have hD0 : 0 ≤ D*(1+S)^3 := by positivity
      have hpar := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hq.2.2.1 hD0)
      have hdelta : |minRatio h.node.side h.node.ratio-minRatio (stateSide z.1) (stateRatio z.1)|+
          |upperSupport S ell h.node.gap-upperSupport S ell (gapValue v z)|+2*mesh ≤
          upperDisplacement S mesh N+3*mesh := by linarith
      have h2 := mul_le_mul_of_nonneg_left
        (add_le_add_right hdelta (2*Real.exp (-c₂*Real.sqrt ((1/2:ℝ)*Real.log w))))
        (show 0 ≤ C₂*(1+S)^2 by positivity)
      have h3 := mul_le_mul_of_nonneg_left hdelta (show 0 ≤ C₃*(1+S)^2 by positivity)
      unfold stepBudget
      linarith

end NumberTheoryLean.UniformFailureBudget

end

end Erdos970

end OAI
