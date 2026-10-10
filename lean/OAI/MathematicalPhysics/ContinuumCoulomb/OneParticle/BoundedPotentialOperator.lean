import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.H1BoundedForm

namespace OAI

/-! Actual bounded real multiplication potentials on the weak-H1 graph. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb
namespace BoundedPotential

variable {n : ℕ} (V : Configuration n → ℝ) (hV : Continuous V)
  (B : ℝ) (hB : ∀ x, |V x| ≤ B)

include hV hB in
theorem product_memLp (u : Lp ℂ 2 (volume : Measure (Configuration n))) :
    MemLp (fun x => (V x : ℂ) * u x) 2 := by
  apply (Lp.memLp u).of_le_mul (c := B)
    ((Complex.continuous_ofReal.comp hV).aestronglyMeasurable.mul (Lp.aestronglyMeasurable u))
  filter_upwards [] with x
  change ‖(V x : ℂ) * u x‖ ≤ B * ‖u x‖
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _)

def value (u : Lp ℂ 2 (volume : Measure (Configuration n))) :
    Lp ℂ 2 (volume : Measure (Configuration n)) :=
  (product_memLp V hV B hB u).toLp (fun x => (V x : ℂ)*u x)

theorem value_ae (u : Lp ℂ 2 (volume : Measure (Configuration n))) :
    value V hV B hB u =ᵐ[volume] fun x => (V x : ℂ)*u x :=
  (product_memLp V hV B hB u).coeFn_toLp

private def linear : Lp ℂ 2 (volume : Measure (Configuration n)) →ₗ[ℂ]
    Lp ℂ 2 (volume : Measure (Configuration n)) where
  toFun := value V hV B hB
  map_add' u v := by
    apply Lp.ext
    filter_upwards [value_ae V hV B hB (u+v), value_ae V hV B hB u,
      value_ae V hV B hB v, Lp.coeFn_add u v,
      Lp.coeFn_add (value V hV B hB u) (value V hV B hB v)] with x he hu hv hs ht
    simp only [he, hs, ht, hu, hv, Pi.add_apply]
    ring
  map_smul' c u := by
    change value V hV B hB (c • u) = c • value V hV B hB u
    apply Lp.ext
    filter_upwards [value_ae V hV B hB (c • u), value_ae V hV B hB u,
      Lp.coeFn_smul c u, Lp.coeFn_smul c (value V hV B hB u)] with x he hu hs ht
    simp only [he, hs, ht, hu, Pi.smul_apply, smul_eq_mul]
    ring

def operator : Lp ℂ 2 (volume : Measure (Configuration n)) →L[ℝ]
    Lp ℂ 2 (volume : Measure (Configuration n)) :=
  ((linear V hV B hB).mkContinuous B (fun u =>
    Lp.norm_le_mul_norm_of_ae_le_mul (by
      filter_upwards [value_ae V hV B hB u] with x hx
      change ‖value V hV B hB u x‖ ≤ B * ‖u x‖
      rw [hx, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _)))).restrictScalars ℝ

theorem operator_ae (u : Lp ℂ 2 (volume : Measure (Configuration n))) :
    operator V hV B hB u =ᵐ[volume] fun x => (V x : ℂ)*u x := value_ae V hV B hB u

theorem operator_pairing (u : Lp ℂ 2 (volume : Measure (Configuration n))) :
    inner ℝ u (operator V hV B hB u) = ∫ x, V x * ‖u x‖^2 := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [operator_ae V hV B hB u] with x hx
  rw [hx, ← Complex.real_smul, real_inner_smul_right, real_inner_self_eq_norm_sq]

end BoundedPotential
def boundedPotentialForm {n : ℕ} (V : Configuration n → ℝ) (u : Coulomb.H1Vector n) : ℝ :=
  Coulomb.kinetic u + ∑ s, ∫ x, V x * ‖u.value s x‖^2

theorem boundedPotentialForm_eq_graph {n : ℕ} (V : Configuration n → ℝ)
    (hV : Continuous V) (B : ℝ) (hB : ∀ x, |V x| ≤ B) (u : Coulomb.H1Vector n) :
    boundedPotentialForm V u =
      graphBoundedForm (BoundedPotential.operator V hV B hB) (h1Coordinates u) := by
  unfold boundedPotentialForm graphBoundedForm
  rw [kinetic_eq_graphKinetic]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  rw [BoundedPotential.operator_pairing]
  apply integral_congr_ae
  filter_upwards [(h1Coordinate_memLp u (Sum.inl s)).coeFn_toLp] with x hx
  change h1Coordinates u (Sum.inl s) x = u.value s x at hx
  rw [hx]

theorem boundedPotential_lower_of_compact (hpublished : PublishedSobolevSmoothDensity)
    {n : ℕ} (V : Configuration n → ℝ) (hV : Continuous V) (B : ℝ)
    (hB : ∀ x, |V x| ≤ B) (E : ℝ)
    (hcompact : ∀ v : Coulomb.H1Vector n,
      (∀ s, ContDiff ℝ 1 (v.value s) ∧ HasCompactSupport (v.value s)) →
      (∀ s a x, v.gradient s a x =
        fderiv ℝ (v.value s) x (EuclideanSpace.single a 1)) →
      E*Coulomb.mass v ≤ boundedPotentialForm V v)
    (u : Coulomb.H1Vector n) : E*Coulomb.mass u ≤ boundedPotentialForm V u := by
  rw [boundedPotentialForm_eq_graph V hV B hB]
  apply boundedForm_lower_of_compact hpublished _ E
  intro v hv hd
  rw [← boundedPotentialForm_eq_graph V hV B hB]
  exact hcompact v hv hd

end ContinuumCoulomb

end

end OAI
