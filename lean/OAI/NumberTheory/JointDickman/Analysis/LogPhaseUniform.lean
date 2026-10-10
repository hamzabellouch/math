import OAI.NumberTheory.JointDickman.Analysis.LogPhaseTerminal
import OAI.NumberTheory.JointDickman.Analysis.LogPhaseIntervalBudget
import OAI.NumberTheory.JointDickman.Amplification.FinitePowerSaving

namespace OAI

/-! # Uniform cancellation for logarithmic exponential sums

Only finitely many derivative orders are required when the frequency is
bounded by a fixed power of the length scale.
-/
namespace JointDickman
open Filter Problem337
open scoped Topology

/-- A fixed power range of frequencies admits a positive power saving,
uniformly in an additional linear phase and in the interval endpoints. -/
theorem logarithmic_phase_uniform (B : ℝ) (hB : 1/2 ≤ B) :
    ∃ A δ : ℝ, 0 < A ∧ 0 < δ ∧
      ∀ᶠ U : ℝ in atTop, ∀ (a Z : ℝ) (L R : ℤ),
        U^(1/2:ℝ) ≤ |Z| → |Z| ≤ U^B →
        U ≤ (L:ℝ) → (R:ℝ) ≤ 2*U →
        ‖∑ n ∈ Finset.Icc L R, differencingPhase (a*n+Z*Real.log n)‖ ≤
          A*U^(1-δ) := by
  let F : ℕ → ℝ → (ℝ × ℝ × ℤ × ℤ) → ℝ := fun _ _ z =>
    ‖∑ n ∈ Finset.Icc z.2.2.1 z.2.2.2,
      differencingPhase (z.1*n+z.2.1*Real.log n)‖
  let P : ℕ → ℝ → (ℝ × ℝ × ℤ × ℤ) → Prop := fun k U z =>
    U^(-(3:ℝ)/2) ≤ |z.2.1| *U^(-((k:ℝ)+1)) ∧
    |z.2.1| *U^(-((k:ℝ)+1)) ≤ U^(-(1:ℝ)/2) ∧
    U ≤ (z.2.2.1:ℝ) ∧ (z.2.2.2:ℝ) ≤ 2*U
  have horders : ∀ k ∈ Finset.Icc 1 (Nat.ceil B+1),
      ∃ A δ : ℝ, 0 < A ∧ 0 < δ ∧ ∃ T : ℝ,
        ∀ U : ℝ, T ≤ U → ∀ z : ℝ × ℝ × ℤ × ℤ,
          P k U z → F k U z ≤ A*U^(1-δ) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkpos : (0:ℝ) < k := by exact_mod_cast (show 0<k by omega)
    have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk1
    let α : ℝ := 1/(10*(k:ℝ))
    have hα : 0 < α := by dsimp [α]; positivity
    have hαsmall : α < (1:ℝ)/5 := by
      dsimp [α]
      apply (div_lt_iff₀ (by positivity : (0:ℝ)<10*k)).mpr
      nlinarith
    obtain ⟨C,hC,hterminal⟩ := logarithmic_terminal_interval_bound k hk1
    have hb := logarithmic_interval_budget_eventually (k-1) α C hα hαsmall hC
    obtain ⟨T,hT⟩ := eventually_atTop.mp ((eventually_ge_atTop (2:ℝ)).and hb)
    refine ⟨36,α/(2:ℝ)^(k-1),by norm_num,by positivity,T,?_⟩
    intro U hU z hz
    obtain ⟨hU2,hbudget⟩ := hT U hU
    apply hbudget z.2.2.1 z.2.2.2 hz.2.2.1 hz.2.2.2
      (fun y => z.1*y+z.2.1*Real.log y)
    intro hs hlen hsteps
    exact hterminal z.1 U z.2.1 z.2.2.1 z.2.2.2 hs hU2 hlen hsteps
      hz.1 hz.2.1 hz.2.2.1 hz.2.2.2
  obtain ⟨A,δ,hA,hδ,T,_,hbound⟩ :=
    finite_uniform_rpow_saving (Finset.Icc 1 (Nat.ceil B+1)) F P 1 horders
  refine ⟨A,δ,hA,hδ,?_⟩
  filter_upwards [eventually_ge_atTop T,eventually_gt_atTop (1:ℝ)] with U hU hU1
  intro a Z L R hlo hhi hL hR
  obtain ⟨k,hk,hkB,hkl,hku⟩ := logarithmic_phase_order hU1 hB hlo hhi
  exact hbound k (Finset.mem_Icc.mpr ⟨hk,hkB⟩) U hU (a,Z,L,R) ⟨hkl,hku,hL,hR⟩

end JointDickman

end OAI
