import Mathlib
import OAI.Probability.SKBarriers.Calculus.CubeVariance
import OAI.Probability.SKBarriers.Calculus.CubeMeasures

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
namespace SK.Analytic
instance fiberNeZero : (n : ℕ) → (x : ℝ) → NeZero (fiberMeasure n x)
  | 0, x => inferInstanceAs (NeZero (Measure.dirac x))
  | n+1, x => by
    let := fiberNeZero n x
    refine ⟨Measure.measure_univ_ne_zero.mp ?_⟩
    change ((fiberMeasure n x).prod volume) univ ≠ 0
    rw [← univ_prod_univ, Measure.prod_prod]
    exact mul_ne_zero (NeZero.ne _) (NeZero.ne _)

theorem cubeSet_mono (n : ℕ) {a b a' b' : ℝ} (ha : a' ≤ a) (hb : b ≤ b') :
    cubeSet n a b ⊆ cubeSet n a' b' := by
  induction n with
  | zero => exact Subset.rfl
  | succ n ih =>
    intro z hz
    exact ⟨ih hz.1, ⟨ha.trans_lt hz.2.1, hz.2.2.trans hb⟩⟩

theorem mem_cubeSet_of_norm_lt (n : ℕ) (z : ParameterSpace n) {R : ℝ} (hR : ‖z‖ < R) :
    z ∈ cubeSet n (-R) R := by
  induction n with
  | zero => trivial
  | succ n ih =>
    refine ⟨ih z.1 ((norm_fst_le z).trans_lt hR), ?_⟩
    have hh := (norm_snd_le z).trans_lt hR
    rw [Real.norm_eq_abs] at hh
    exact ⟨(abs_lt.mp hh).1, (abs_lt.mp hh).2.le⟩

theorem cubeSet_iUnion (n : ℕ) : (⋃ R : ℕ, cubeSet n (-(R : ℝ)) R) = univ := by
  apply eq_univ_of_forall
  intro z
  obtain ⟨R, hR⟩ := exists_nat_gt ‖z‖
  exact mem_iUnion.mpr ⟨R, mem_cubeSet_of_norm_lt n z hR⟩

theorem tendsto_cubeIntegral (n : ℕ) (f : ParameterSpace n → ℝ) (hf : Continuous f)
    (x : ℝ) (hi : Integrable f (fiberMeasure n x)) :
    Tendsto (fun R : ℕ => cubeIntegral n f (-(R : ℝ)) R x) atTop
      (𝓝 (∫ z, f z ∂fiberMeasure n x)) := by
  have hmono : Monotone (fun R : ℕ => cubeSet n (-(R : ℝ)) R) := by
    intro R S hRS
    exact cubeSet_mono n (neg_le_neg (Nat.cast_le.mpr hRS)) (Nat.cast_le.mpr hRS)
  have h := tendsto_setIntegral_of_monotone (fun R : ℕ => cubeSet_measurable n (-(R : ℝ)) R)
    hmono (hi.integrableOn : IntegrableOn f (⋃ R : ℕ, cubeSet n (-(R : ℝ)) R) (fiberMeasure n x))
  rw [cubeSet_iUnion, Measure.restrict_univ] at h
  convert! h using 1
  funext R
  rw [cubeIntegral_eq_measureIntegral n f hf (by linarith [Nat.cast_nonneg (α := ℝ) R]), cubeMeasure_eq_restrict]

theorem linear_variance_le (n : ℕ) (V : ParameterSpace n → ℝ)
    (hV : ContDiff ℝ 2 V) (hV₀ : ∀ z, parameterDerivative n V z = 0)
    (L : ParameterSpace n →L[ℝ] ℝ) (hL₀ : L (parameterAxis n) = 0)
    {c A : ℝ} (hc : 0 < c) (hA : 0 ≤ A)
    (hL : ∀ u, (L u)^2 ≤ A*coordinateSquare n u)
    (hH : ∀ z u, c*coordinateSquare n u ≤ Hessian V z u u)
    (hI₀ : Integrable (fun z => Real.exp (-V z)) (fiberMeasure n 0))
    (hI₁ : Integrable (fun z => L z*Real.exp (-V z)) (fiberMeasure n 0))
    (hI₂ : Integrable (fun z => (L z)^2*Real.exp (-V z)) (fiberMeasure n 0)) :
    let Z := ∫ z, Real.exp (-V z) ∂fiberMeasure n 0
    (∫ z, (L z)^2*Real.exp (-V z) ∂fiberMeasure n 0)/Z -
      ((∫ z, L z*Real.exp (-V z) ∂fiberMeasure n 0)/Z)^2 ≤ A/c := by
  let w : ParameterSpace n → ℝ := fun z => Real.exp (-V z)
  have hw : Continuous w := hV.neg.exp.continuous
  have hw₁ : Continuous (fun z => L z*w z) := L.continuous.mul hw
  have hw₂ : Continuous (fun z => (L z)^2*w z) := (L.continuous.pow 2).mul hw
  have ht₀ := tendsto_cubeIntegral n w hw 0 hI₀
  have ht₁ := tendsto_cubeIntegral n (fun z => L z*w z) hw₁ 0 hI₁
  have ht₂ := tendsto_cubeIntegral n (fun z => (L z)^2*w z) hw₂ 0 hI₂
  have hZ : 0 < ∫ z, w z ∂fiberMeasure n 0 := integral_exp_pos hI₀
  apply le_of_tendsto ((ht₂.div ht₀ (ne_of_gt hZ)).sub
    ((ht₁.div ht₀ (ne_of_gt hZ)).pow 2))
  filter_upwards [eventually_ge_atTop 1] with R hR
  have hRp : (0 : ℝ) < R := Nat.cast_pos.mpr (by omega)
  exact cube_linear_variance_le n V hV hV₀ L hL₀ hc hA hL hH (by linarith)

end SK.Analytic

end
end
end
end
end

end OAI
