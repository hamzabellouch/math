import OAI.Analysis.LipschitzHilbert.Phase.GaussianPhaseDamping

namespace OAI

/-! The actual nonnegative shift simplex and its vertex geometry. -/

noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert
variable {ι : Type*} [Fintype ι]

def sourceShiftSimplex (mu : ℝ) : Set (ι → ℝ) :=
  {a | (∀ i, 0 ≤ a i) ∧ ∑ i, a i = mu}

theorem sourceShiftSimplex_convex (mu : ℝ) : Convex ℝ (sourceShiftSimplex (ι := ι) mu) := by
  intro a ha b hb r s hr hs hrs
  constructor
  · intro i
    exact add_nonneg (mul_nonneg hr (ha.1 i)) (mul_nonneg hs (hb.1 i))
  · change ∑ i, (r*a i+s*b i) = mu
    rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,ha.2,hb.2,← add_mul,hrs,one_mul]

theorem sourceShiftSimplex_sq_sum (mu : ℝ) (a : ι → ℝ)
    (ha : a ∈ sourceShiftSimplex mu) : (∑ i, (a i)^2) ≤ mu^2 := by
  have h := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := a) (fun i _ => ha.1 i)
  simpa only [ha.2] using h

theorem sourceShiftSimplex_vertex [DecidableEq ι] {mu : ℝ} (hmu : 0 ≤ mu) (i : ι) :
    Pi.single i mu ∈ sourceShiftSimplex mu := by
  constructor
  · intro j
    by_cases hji : j = i
    · subst j; simpa using hmu
    · simp [hji]
  · simp [Pi.single_apply]

end LipschitzHilbert

end

end OAI
