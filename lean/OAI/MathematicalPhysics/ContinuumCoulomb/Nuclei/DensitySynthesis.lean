import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CoulombPoisson
import OAI.Analysis.CoulombRadii.Localization.TruncatedCoulomb

namespace OAI

/-!
# Nonnegative continuous-density synthesis for the unit-charge construction

The density is the uniform slab plus `ΔV/(4π)`. Compact support of `V`
inside the slab makes its attractive Coulomb field exactly the slab field
plus `V`. A pointwise Laplacian bound makes the density nonnegative.
Only C² regularity is required, as the manuscript's manufactured well is
finitely smooth.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def slabDomain (H S : ℝ) : Set Position :=
  {x | |x 0| ≤ H ∧ |x 1| ≤ H ∧ |x 2| ≤ S}

theorem slabDomain_isClosed (H S : ℝ) : IsClosed (slabDomain H S) := by
  have h0 : IsClosed {x : Position | |x 0| ≤ H} :=
    isClosed_le (by fun_prop) continuous_const
  have h1 : IsClosed {x : Position | |x 1| ≤ H} :=
    isClosed_le (by fun_prop) continuous_const
  have h2 : IsClosed {x : Position | |x 2| ≤ S} :=
    isClosed_le (by fun_prop) continuous_const
  exact h0.inter (h1.inter h2)

theorem slabDomain_isCompact {H S : ℝ} (hH : 0 ≤ H) (hS : 0 ≤ S) :
    IsCompact (slabDomain H S) := by
  apply (isCompact_closedBall (0 : Position) (3 * (H + S + 1))).of_isClosed_subset
    (slabDomain_isClosed H S)
  intro x hx
  have hcoord (a : Fin 3) : |x a| ≤ H + S := by
    fin_cases a
    · exact hx.1.trans (by linarith)
    · exact hx.2.1.trans (by linarith)
    · exact hx.2.2.trans (by linarith)
  have hsq : ‖x‖ ^ 2 ≤ 3 * (H + S) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    have h := Finset.sum_le_sum (s := Finset.univ) fun a _ =>
      (sq_le_sq₀ (abs_nonneg (x a)) (by linarith : 0 ≤ H + S)).mpr (hcoord a)
    simpa only [sq_abs, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_ofNat] using h
  rw [Metric.mem_closedBall, dist_zero_right]
  nlinarith [norm_nonneg x, sq_nonneg (H + S)]

def slabDensity (rho H S : ℝ) : Position → ℝ :=
  (slabDomain H S).indicator fun _ => rho

def slabPotential (rho H S : ℝ) (y : Position) : ℝ :=
  -(∫ x, Coulomb.coulombKernel (y - x) * slabDensity rho H S x)

def synthesizedDensity (rho H S : ℝ) (V : Position → ℝ) (x : Position) : ℝ :=
  slabDensity rho H S x + manufacturedCharge V x

theorem slabDensity_integrable {H S : ℝ} (hH : 0 ≤ H) (hS : 0 ≤ S) (rho : ℝ) :
    Integrable (slabDensity rho H S) :=
  (integrable_indicator_iff (slabDomain_isClosed H S).measurableSet).mpr
    (integrableOn_const (slabDomain_isCompact hH hS).measure_ne_top)

theorem slabDensity_integral (rho H S : ℝ) :
    (∫ x, slabDensity rho H S x) = volume.real (slabDomain H S) * rho := by
  exact integral_indicator_const rho (slabDomain_isClosed H S).measurableSet

theorem manufacturedCharge_continuous (V : Position → ℝ) (hV : ContDiff ℝ 2 V) :
    Continuous (manufacturedCharge V) :=
  (NeutralAtom.continuous_coordinateLaplacian hV).div_const _

theorem manufacturedCharge_compact (V : Position → ℝ) (hc : HasCompactSupport V) :
    HasCompactSupport (manufacturedCharge V) := by
  exact (NeutralAtom.hasCompactSupport_coordinateLaplacian hc).comp_left
    (g := fun t : ℝ => t / (4 * Real.pi)) (by simp)

theorem manufacturedCharge_zero {V : Position → ℝ} {x : Position} (hx : x ∉ tsupport V) :
    manufacturedCharge V x = 0 := by
  simp only [manufacturedCharge, NeutralAtom.coordinateLaplacian_eq_zero_of_notMem_tsupport hx,
    zero_div]

theorem synthesizedDensity_bounds {rho H S : ℝ} (hrho : 0 ≤ rho)
    (V : Position → ℝ) (hsupport : tsupport V ⊆ slabDomain H S)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho / 2) (x : Position) :
    0 ≤ synthesizedDensity rho H S V x ∧
      synthesizedDensity rho H S V x ≤ 3 * rho / 2 := by
  by_cases hx : x ∈ slabDomain H S
  · obtain ⟨hl, hu⟩ := abs_le.mp (hbound x)
    simp only [synthesizedDensity, slabDensity, Set.indicator_of_mem hx]
    constructor <;> linarith
  · have hzero := manufacturedCharge_zero (fun hv => hx (hsupport hv))
    simp only [synthesizedDensity, slabDensity, Set.indicator_of_notMem hx, hzero, add_zero]
    exact ⟨le_rfl, by linarith⟩

theorem synthesizedDensity_lower_on_slab {rho H S : ℝ} (V : Position → ℝ)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho / 2) {x : Position}
    (hx : x ∈ slabDomain H S) : rho / 2 ≤ synthesizedDensity rho H S V x := by
  have h := (abs_le.mp (hbound x)).1
  simp only [synthesizedDensity, slabDensity, Set.indicator_of_mem hx]
  linarith

theorem synthesizedDensity_integrable {H S : ℝ} (hH : 0 ≤ H) (hS : 0 ≤ S) (rho : ℝ)
    (V : Position → ℝ) (hV : ContDiff ℝ 2 V) (hc : HasCompactSupport V) :
    Integrable (synthesizedDensity rho H S V) :=
  (slabDensity_integrable hH hS rho).add
    ((manufacturedCharge_continuous V hV).integrable_of_hasCompactSupport
      (manufacturedCharge_compact V hc))

/-- The manufactured correction carries zero net charge, so the total
density mass is exactly the uniform slab mass. -/
theorem synthesizedDensity_integral {H S : ℝ} (hH : 0 ≤ H) (hS : 0 ≤ S) (rho : ℝ)
    (V : Position → ℝ) (hV : ContDiff ℝ 2 V) (hc : HasCompactSupport V) :
    (∫ x, synthesizedDensity rho H S V x) = volume.real (slabDomain H S) * rho := by
  change (∫ x, slabDensity rho H S x + manufacturedCharge V x) = _
  rw [integral_add (slabDensity_integrable hH hS rho)
      ((manufacturedCharge_continuous V hV).integrable_of_hasCompactSupport
        (manufacturedCharge_compact V hc)),
    slabDensity_integral, manufacturedCharge_integral_zero V hV hc, add_zero]

/-- Equation (4) of the unit-charge manuscript, as an identity of the actual
three-dimensional Coulomb integrals at every evaluation point. -/
theorem synthesizedDensity_potential {rho H S : ℝ} (hrho : 0 ≤ rho)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (V : Position → ℝ)
    (hV : ContDiff ℝ 2 V) (hc : HasCompactSupport V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho / 2) (y : Position) :
    -(∫ x, Coulomb.coulombKernel (y - x) * synthesizedDensity rho H S V x) =
      slabPotential rho H S y + V y := by
  have hslabMeas : Measurable (slabDensity rho H S) :=
    measurable_const.indicator (slabDomain_isClosed H S).measurableSet
  have hslabBound (x : Position) : ‖slabDensity rho H S x‖ ≤ rho := by
    by_cases hx : x ∈ slabDomain H S
    · simp only [slabDensity, Set.indicator_of_mem hx, Real.norm_eq_abs, abs_of_nonneg hrho]
      exact le_rfl
    · simp only [slabDensity, Set.indicator_of_notMem hx, norm_zero]
      exact hrho
  have hIslab := Coulomb.coulomb_signed_convolution_integrable
    (slabDensity_integrable hH hS rho) hslabMeas hslabBound y
  have hIcharge := Coulomb.coulomb_signed_convolution_integrable
    ((manufacturedCharge_continuous V hV).integrable_of_hasCompactSupport
      (manufacturedCharge_compact V hc))
    (manufacturedCharge_continuous V hV).measurable
    (fun x => by simpa only [Real.norm_eq_abs] using hbound x) y
  have heq : (fun x => Coulomb.coulombKernel (y - x) * synthesizedDensity rho H S V x) =
      (fun x => Coulomb.coulombKernel (y - x) * slabDensity rho H S x +
        Coulomb.coulombKernel (y - x) * manufacturedCharge V x) := by
    funext x
    simp only [synthesizedDensity, mul_add]
  rw [heq, integral_add hIslab hIcharge, neg_add]
  rw [manufacturedCharge_potential V hV hc y]
  rfl

end ContinuumCoulomb

end

end OAI
