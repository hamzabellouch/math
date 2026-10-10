import OAI.Analysis.CoulombTransport.StationaryMap
import OAI.Analysis.CoulombTransport.CoulombCoercivity
import OAI.Analysis.CoulombTransport.StateDual

namespace OAI

universe uE

noncomputable section

open Set
open scoped RealInnerProductSpace

namespace Problem356.StationaryMap

open CoulombCalculus

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The concrete scalar state differential is the product-state dual of its
stationary vector field. -/
theorem stateDifferential_eq_stateDual (a y : E) (s : E × E) :
    stateDifferential a y s = stateDual E E (stationary a (y, s)) := rfl

/-- The state derivative of the concrete stationary map is the coercive
regularized Coulomb Hessian. -/
theorem hasFDerivAt_stateStationary (a y : E) {s : E × E}
    (hxy : s.1 ≠ y) (hxz : s.1 ≠ s.2) (hzy : s.2 ≠ y) :
    HasFDerivAt (fun p : E × E => stationary a (y, p))
      (regularizedStateHessian (s.1 - y) (s.1 - s.2) (s.2 - y)) s := by
  have h := hasFDerivAt_regularizedStateGradient y
    (-((5 / 4 : ℝ) • a) + (20 : ℝ) • a)
    (sub_ne_zero.mpr hxy) (sub_ne_zero.mpr hxz) (sub_ne_zero.mpr hzy)
  convert h using 1
  funext p
  unfold stationary
  have hp : p.2 - p.1 = -(p.1 - p.2) := by abel
  rw [hp, pairGradient_neg, smul_add]
  congr 1
  abel

/-- Concrete strict convexity on every open convex state domain with the
uniform pair separation used in the local construction. -/
theorem statePotential_strictConvexOn_of_separated (a y : E) {V : Set (E × E)}
    (hV : Convex ℝ V) (hVopen : IsOpen V)
    (hsep : ∀ s ∈ V, (2 : ℝ) / 3 ≤ ‖s.1 - y‖ ∧
      (2 : ℝ) / 3 ≤ ‖s.1 - s.2‖ ∧ (2 : ℝ) / 3 ≤ ‖s.2 - y‖) :
    StrictConvexOn ℝ V (statePotential a y) := by
  have hne : ∀ {x z : E}, (2 : ℝ) / 3 ≤ ‖x - z‖ → x ≠ z := by
    intro x z h hxz
    norm_num [hxz] at h
  apply strictConvexOn_of_positive_stateGradient E E hV hVopen
    (G := fun s => stationary a (y, s))
    (A := fun s => regularizedStateHessian (s.1 - y) (s.1 - s.2) (s.2 - y))
  · intro s hs
    rw [← stateDifferential_eq_stateDual]
    exact hasFDerivAt_statePotential a y
      (hne (hsep s hs).1) (hne (hsep s hs).2.1) (hne (hsep s hs).2.2)
  · intro s hs
    exact hasFDerivAt_stateStationary a y
      (hne (hsep s hs).1) (hne (hsep s hs).2.1) (hne (hsep s hs).2.2)
  · intro s hs v hv
    exact regularizedStateHessian_pos (hsep s hs).1 (hsep s hs).2.1 (hsep s hs).2.2 hv

/-- A zero of the actual Coulomb stationary map is the unique minimizing state
on a separated open convex domain. -/
theorem statePotential_minimum_and_eq_iff_of_separated (a y : E) {V : Set (E × E)}
    (hV : Convex ℝ V) (hVopen : IsOpen V)
    (hsep : ∀ s ∈ V, (2 : ℝ) / 3 ≤ ‖s.1 - y‖ ∧
      (2 : ℝ) / 3 ≤ ‖s.1 - s.2‖ ∧ (2 : ℝ) / 3 ≤ ‖s.2 - y‖)
    {s : E × E} (hs : s ∈ V) (hzero : stationary a (y, s) = 0)
    {q : E × E} (hq : q ∈ V) :
    statePotential a y s ≤ statePotential a y q ∧
      (statePotential a y q = statePotential a y s ↔ q = s) := by
  have hne : ∀ {x z : E}, (2 : ℝ) / 3 ≤ ‖x - z‖ → x ≠ z := by
    intro x z h hxz
    norm_num [hxz] at h
  have hconv := statePotential_strictConvexOn_of_separated a y hV hVopen hsep
  have hstat := hasFDerivAt_statePotential_zero a y
    (hne (hsep s hs).1) (hne (hsep s hs).2.1) (hne (hsep s hs).2.2) hzero
  exact ⟨convex_isMinOn_of_hasFDerivAt_zero hconv.convexOn hs hstat hq,
    strictConvex_eq_iff_of_hasFDerivAt_zero hconv hs hstat hq⟩

/-- A smooth branch of zeros of the concrete Coulomb stationary equation
produces a smooth supporting value with its exact contact graph. All analytic
convexity hypotheses are discharged by the explicit distance separation. -/
theorem smooth_stationary_branch_support (a : E)
    {U : Set E} {V : Set (E × E)} {ψ : E → E × E} {n : WithTop ENat}
    (hV : Convex ℝ V) (hVopen : IsOpen V)
    (hsep : ∀ y ∈ U, ∀ s ∈ V, (2 : ℝ) / 3 ≤ ‖s.1 - y‖ ∧
      (2 : ℝ) / 3 ≤ ‖s.1 - s.2‖ ∧ (2 : ℝ) / 3 ≤ ‖s.2 - y‖)
    (hψ : ContDiffOn ℝ n ψ U) (hψV : MapsTo ψ U V)
    (hzero : ∀ y ∈ U, stationary a (y, ψ y) = 0) :
    ContDiffOn ℝ n (fun y => statePotential a y (ψ y)) U ∧
      ∀ y ∈ U, ∀ s ∈ V,
        statePotential a y (ψ y) ≤ statePotential a y s ∧
          (statePotential a y s = statePotential a y (ψ y) ↔ s = ψ y) := by
  have hne : ∀ {x z : E}, (2 : ℝ) / 3 ≤ ‖x - z‖ → x ≠ z := by
    intro x z h hxz
    norm_num [hxz] at h
  have hF : ContDiffOn ℝ n (jointPotential a) (U ×ˢ V) := by
    intro p hp
    exact (contDiffAt_jointPotential a
      (hne (hsep p.1 hp.1 p.2 hp.2).1)
      (hne (hsep p.1 hp.1 p.2 hp.2).2.1)
      (hne (hsep p.1 hp.1 p.2 hp.2).2.2)).contDiffWithinAt
  constructor
  · exact hF.comp (contDiffOn_id.prodMk hψ) (fun y hy => ⟨hy, hψV hy⟩)
  · intro y hy s hs
    exact statePotential_minimum_and_eq_iff_of_separated a y hV hVopen
      (hsep y hy) (hψV hy) (hzero y hy) hs

end Problem356.StationaryMap

end

end OAI
