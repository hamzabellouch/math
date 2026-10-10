import OAI.Analysis.CircleDomains.Topology.CompactScalarModel

namespace OAI

/-! A common exterior radius bounds the actual coefficient of every model.
Consequently the retained model class has near-maximal real coefficients. -/
open Set Function Filter Bornology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

 theorem finite_differentiable_of_sphere_conformal
    {f : ℂ → ℂ} {z : ℂ} (hf : IsConformalAt (extendAtInfinity f) (z : Sphere)) :
    DifferentiableAt ℂ f z := by
  obtain ⟨_, d, _, hd⟩ := hf
  have he : (fun w => chart (extendAtInfinity f (z : Sphere))
      (extendAtInfinity f (chartSymm (z : Sphere) w))) = f := by
    funext w
    simp only [extendAtInfinity_coe, chart_coe_apply, chartSymm_coe_apply, finiteCoord_coe]
  rw [he, chart_coe_self] at hd
  exact hd.differentiableAt

 namespace CompactScalarModel
 variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem coefficient_bound (M : CompactScalarModel G u)
    (harea : ExteriorCoefficientAreaTheorem) {R : ℝ} (hR : 0 < R)
    (hsource : ∀ z : ℂ, R < ‖z‖ → (z : Sphere) ∈ G) :
    ‖M.coefficient‖ ≤ 2*R^2 := by
  apply M.coefficient_limit.norm_le_of_exterior harea hR
  · intro z hz
    exact (finite_differentiable_of_sphere_conformal (M.conformal.1 _ (hsource z hz))).differentiableWithinAt
  · intro z hz w hw he
    apply OnePoint.coe_injective
    apply M.conformal.bijOn.injOn (hsource z hz) (hsource w hw)
    exact congrArg ((↑) : ℂ → Sphere) he

 def coefficientSet (G : Set Sphere) {m : ℕ} (u : Fin m → EuclideanPlane → ℝ) : Set ℝ :=
  Set.range (fun M : CompactScalarModel G u => M.coefficient.re)

 theorem coefficientSet_bddAbove (harea : ExteriorCoefficientAreaTheorem)
    {R : ℝ} (hR : 0 < R) (hsource : ∀ z : ℂ, R < ‖z‖ → (z : Sphere) ∈ G) :
    BddAbove (coefficientSet G u) := by
  refine ⟨2*R^2, ?_⟩
  rintro _ ⟨M, rfl⟩
  exact (Complex.re_le_norm M.coefficient).trans (M.coefficient_bound harea hR hsource)

 theorem exists_near_maximal (hne : Nonempty (CompactScalarModel G u))
    {d : ℝ} (hd : 0 < d) :
    ∃ M : CompactScalarModel G u,
      sSup (coefficientSet G u)-d < M.coefficient.re := by
  have hS : (coefficientSet G u).Nonempty := by
    obtain ⟨M⟩ := hne
    exact ⟨M.coefficient.re, M, rfl⟩
  obtain ⟨b, ⟨M, rfl⟩, hb⟩ := exists_lt_of_lt_csSup hS
    (show sSup (coefficientSet G u)-d < sSup (coefficientSet G u) by linarith)
  exact ⟨M, hb⟩

 theorem increment_le_of_near_maximal (M N : CompactScalarModel G u)
    (hbound : BddAbove (coefficientSet G u)) {d : ℝ}
    (hnear : sSup (coefficientSet G u)-d ≤ M.coefficient.re)
    {c : ℂ} (hc : N.coefficient = M.coefficient+c) : c.re ≤ d := by
  have hN : N.coefficient.re ≤ sSup (coefficientSet G u) :=
    le_csSup hbound ⟨N, rfl⟩
  rw [hc, Complex.add_re] at hN
  linarith

 end CompactScalarModel

end CircleDomainRigidity

end

end OAI
