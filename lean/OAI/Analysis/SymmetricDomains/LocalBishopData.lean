import Mathlib
import OAI.Analysis.SymmetricDomains.BishopBoundarySolutionConstants
import OAI.Analysis.SymmetricDomains.BishopDiscRadialExpansion

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
namespace Release061.Wiener
open scoped Topology
open Set Filter Metric

structure LocalBishopData (k : ℕ) (f : (Fin (k+1) → ℝ) → Fin k → ℝ) (ε : ℝ) where
  lam : realAlgebra
  eta : realAlgebra
  kappa : realAlgebra
  X : BishopParams k → BoundarySpace k
  Y : BishopParams k → BoundarySpace k
  radius : ℝ
  radius_pos : 0 < radius
  cut_nonneg : ∀ θ, 0 ≤ realEvaluation θ lam ∧ 0 ≤ realEvaluation θ eta
  cut_zero : ∀ θ, (1/2 : ℝ) ≤ dist (circleCos θ) (-1 : ℝ) →
    realEvaluation θ lam = 0 ∧ realEvaluation θ eta = 0
  cut_nested : ∀ θ, realEvaluation θ eta ≠ 0 → realEvaluation θ lam = 1
  cut_division : ∀ θ, dist (circleCos θ) (-1 : ℝ) ≤ 1/2 →
    (2-2*circleCos θ)*realEvaluation θ kappa = 1
  smoothX : ContDiffOn ℝ 1 X (ball 0 radius)
  smoothY : ContDiffOn ℝ 1 Y (ball 0 radius)
  small : ∀ p ∈ ball 0 radius, ‖X p‖ < ε ∧ ‖Y p‖ < ε ∧ ‖bishopDisc Y p‖ < ε
  equation : ∀ p ∈ ball 0 radius,
    (∀ i, X p i = constantReal (p.1 i)+normalizedHilbert (Y p i)) ∧
    (∀ θ i, realEvaluation θ (Y p i) =
      f (Fin.cons (p.2.2.1*realEvaluation θ lam+p.2.2.2)
        (fun j => realEvaluation θ (X p j))) i+realEvaluation θ eta*p.2.1 i)
  localized : ∀ p ∈ ball 0 radius, p.2.2.2 = 0 →
    ∀ θ, (1/2 : ℝ) < dist (circleCos θ) (-1 : ℝ) →
      ∀ i, realEvaluation θ (Y p i) = 0
  constant : ∀ q ∈ ball (0 : (Fin k → ℝ) × ℝ) radius, ∀ i (z : ClosedDisc),
    bishopDisc Y (q.1,0,0,q.2) i z =
      (q.1 i : ℂ)+Complex.I*(f (Fin.cons q.2 q.1) i : ℂ)
  transverse : ∀ᶠ α in 𝓝 (0 : ℝ), IsUnit
    (fderiv ℝ (fun e : Fin k → ℝ => bishopNormal kappa Y (0,e,α,0)) 0)

theorem localBishopData_exists {k : ℕ} {f : (Fin (k+1) → ℝ) → Fin k → ℝ}
    (hf : AnalyticAt ℝ f 0)
    (hf0 : ∀ᶠ X in 𝓝 (0 : Fin k → ℝ), f (Fin.cons 0 X) = 0)
    {ε : ℝ} (hε : 0 < ε) : Nonempty (LocalBishopData k f ε) := by
  obtain ⟨lam,eta,kappa,hn,hz,hs,hd,hpos⟩ := exists_transverse_cutoffs
  obtain ⟨X,Y,hX0,hY0,hX,hY,hEq,hconst⟩ := bishop_boundary_solution_with_constants hf hf0 lam eta
  have hloc := bishop_boundary_localization hf0 hz hX0 hX.continuousAt (hEq.mono fun _ h => h.2)
  have ht := bishopNormal_transverse hY (hloc.mono fun _ h => h.2) hpos
  have hconstant := bishopDisc_constant_branch (hEq.mono fun _ h => h.2) hconst
  obtain ⟨r₁,hr₁,hrc⟩ := Metric.mem_nhds_iff.mp hconstant
  have hD0 : bishopDisc Y 0 = 0 := by
    ext i z
    simp [bishopDisc,hY0]
  have hsmall : ∀ᶠ p in 𝓝 0, ‖X p‖ < ε ∧ ‖Y p‖ < ε ∧ ‖bishopDisc Y p‖ < ε := by
    have hx := hX.continuousAt.norm.eventually (eventually_lt_nhds (by simpa [hX0] using hε))
    have hy := hY.continuousAt.norm.eventually (eventually_lt_nhds (by simpa [hY0] using hε))
    have hb := (bishopDisc_smooth hY).continuousAt.norm.eventually
      (eventually_lt_nhds (by simpa [hD0] using hε))
    exact hx.and (hy.and hb)
  obtain ⟨V,hV,hXV⟩ := hX.contDiffOn (m := 1) (by simp) (by simp)
  obtain ⟨W,hW,hYW⟩ := hY.contDiffOn (m := 1) (by simp) (by simp)
  have hall : ∀ᶠ p in 𝓝 (0 : BishopParams k), p ∈ V ∧ p ∈ W ∧
      (‖X p‖ < ε ∧ ‖Y p‖ < ε ∧ ‖bishopDisc Y p‖ < ε) ∧ _ :=
    Filter.Eventually.and hV (Filter.Eventually.and hW (hsmall.and (hEq.and hloc)))
  obtain ⟨r₂,hr₂,hrall⟩ := Metric.mem_nhds_iff.mp hall
  let r := min r₁ r₂
  have hr : 0 < r := lt_min hr₁ hr₂
  have hdata (p : BishopParams k) (hp : p ∈ ball 0 r) :=
    hrall ((ball_subset_ball (min_le_right _ _)) hp)
  refine ⟨⟨lam,eta,kappa,X,Y,r,hr,hn,hz,hs,hd,?_,?_,?_,?_,?_,?_,ht⟩⟩
  · exact hXV.mono fun p hp => (hdata p hp).1
  · exact hYW.mono fun p hp => (hdata p hp).2.1
  · intro p hp
    exact (hdata p hp).2.2.1
  · intro p hp
    exact (hdata p hp).2.2.2.1
  · intro p hp
    exact (hdata p hp).2.2.2.2.1
  · intro q hq
    exact hrc ((ball_subset_ball (min_le_left _ _)) hq)

end Release061.Wiener

open Set Metric

end

end OAI
