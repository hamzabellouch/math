import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.BoundedPotentialOperator

namespace OAI

/-! Polarization of the actual bounded-potential quadratic form on the
full weak-H1 graph. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem h1Coordinates_add {n : ℕ} (u v : Coulomb.H1Vector n) :
    h1Coordinates (u.add v) = h1Coordinates u+h1Coordinates v := by
  funext a
  apply Lp.ext
  filter_upwards [(h1Coordinate_memLp (u.add v) a).coeFn_toLp,
    (h1Coordinate_memLp u a).coeFn_toLp, (h1Coordinate_memLp v a).coeFn_toLp,
    Lp.coeFn_add (h1Coordinates u a) (h1Coordinates v a)] with x huv hu hv ha
  change h1Coordinates (u.add v) a x = _ at huv
  change h1Coordinates u a x = _ at hu
  change h1Coordinates v a x = _ at hv
  change h1Coordinates (u.add v) a x = (h1Coordinates u a+h1Coordinates v a) x
  rw [ha]
  simp only [Pi.add_apply]
  rw [hu,hv,huv]
  cases a <;> rfl

def graphBoundedCross {n : ℕ}
    (A : Lp ℂ 2 (volume : Measure (Configuration n)) →L[ℝ]
      Lp ℂ 2 (volume : Measure (Configuration n))) (f g : H1Coordinates n) : ℝ :=
  (1/2:ℝ)*(∑ s, ∑ a, inner ℝ (f (Sum.inr (s,a))) (g (Sum.inr (s,a))))+
    ∑ s, inner ℝ (f (Sum.inl s)) (A (g (Sum.inl s)))

theorem graphBoundedForm_add {n : ℕ}
    (A : Lp ℂ 2 (volume : Measure (Configuration n)) →L[ℝ]
      Lp ℂ 2 (volume : Measure (Configuration n)))
    (hA : ∀ x y, inner ℝ x (A y) = inner ℝ y (A x)) (f g : H1Coordinates n) :
    graphBoundedForm A (f+g) = graphBoundedForm A f+graphBoundedForm A g+2*graphBoundedCross A f g := by
  have hx (s : SpinConfiguration n) :
      inner ℝ (g (Sum.inl s)) (A (f (Sum.inl s))) =
        inner ℝ (f (Sum.inl s)) (A (g (Sum.inl s))) := hA _ _
  simp only [graphBoundedForm,graphKinetic,graphBoundedCross,Pi.add_apply,
    norm_add_sq_real,map_add,inner_add_left,inner_add_right,hx,
    Finset.sum_add_distrib,← Finset.mul_sum]
  ring

theorem boundedPotential_operator_symmetric {n : ℕ} (V : Configuration n → ℝ)
    (hV : Continuous V) (B : ℝ) (hB : ∀ x, |V x| ≤ B)
    (f g : Lp ℂ 2 (volume : Measure (Configuration n))) :
    inner ℝ f (BoundedPotential.operator V hV B hB g) =
      inner ℝ g (BoundedPotential.operator V hV B hB f) := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [BoundedPotential.operator_ae V hV B hB f,
    BoundedPotential.operator_ae V hV B hB g] with x hf hg
  rw [hf,hg,← Complex.real_smul,← Complex.real_smul,
    real_inner_smul_right,real_inner_smul_right,real_inner_comm]

theorem boundedPotentialForm_add {n : ℕ} (V : Configuration n → ℝ)
    (hV : Continuous V) (B : ℝ) (hB : ∀ x, |V x| ≤ B) (u v : Coulomb.H1Vector n) :
    boundedPotentialForm V (u.add v) = boundedPotentialForm V u+boundedPotentialForm V v+
      2*graphBoundedCross (BoundedPotential.operator V hV B hB) (h1Coordinates u) (h1Coordinates v) := by
  simp only [boundedPotentialForm_eq_graph V hV B hB,h1Coordinates_add]
  exact graphBoundedForm_add _ (boundedPotential_operator_symmetric V hV B hB) _ _


theorem Lp_real_inner_eq_re {n : ℕ}
    (f g : Lp ℂ 2 (volume : Measure (Configuration n))) :
    inner ℝ f g = (inner ℂ f g).re := by
  rw [L2.inner_def,L2.inner_def]
  have hr := integral_re (L2.integrable_inner (𝕜 := ℂ) f g)
  change (∫ x, (inner ℂ (f x) (g x)).re) = (∫ x, inner ℂ (f x) (g x)).re at hr
  rw [← hr]
  apply integral_congr_ae
  filter_upwards [] with x
  exact real_inner_eq_re_inner ℂ (f x) (g x)

def graphComplexCross {n : ℕ}
    (A : Lp ℂ 2 (volume : Measure (Configuration n)) →L[ℝ]
      Lp ℂ 2 (volume : Measure (Configuration n))) (f g : H1Coordinates n) : ℂ :=
  (1/2:ℂ)*(∑ s, ∑ a, inner ℂ (f (Sum.inr (s,a))) (g (Sum.inr (s,a))))+
    ∑ s, inner ℂ (f (Sum.inl s)) (A (g (Sum.inl s)))

private theorem re_finite_sum {ι : Type*} [Fintype ι] (z : ι → ℂ) :
    (∑ i, z i).re = ∑ i, (z i).re :=
  map_sum Complex.reLm z Finset.univ

theorem graphBoundedCross_eq_re {n : ℕ}
    (A : Lp ℂ 2 (volume : Measure (Configuration n)) →L[ℝ]
      Lp ℂ 2 (volume : Measure (Configuration n))) (f g : H1Coordinates n) :
    graphBoundedCross A f g = (graphComplexCross A f g).re := by
  simp only [graphBoundedCross,graphComplexCross,Lp_real_inner_eq_re,Complex.add_re,
    Complex.mul_re,re_finite_sum]
  norm_num

end ContinuumCoulomb

end

end OAI
