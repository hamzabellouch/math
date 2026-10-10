import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentConjugationDecay
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RescaledBasisChange

namespace OAI

/-! # Nilpotent linear flows in changing box coordinates -/

noncomputable section
namespace PolycyclicRecognition

open Module Filter
open scoped Topology BigOperators

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}

def coordinateEnd (b : Basis (Fin n) ℝ V) (D : Module.End ℝ V) :
    (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  LinearMap.toContinuousLinearMap (b.equivFun.conj D)

@[simp] theorem coordinateEnd_apply (b : Basis (Fin n) ℝ V) (D : Module.End ℝ V)
    (x : Fin n → ℝ) : coordinateEnd b D x = b.equivFun (D (b.equivFun.symm x)) := rfl

theorem coordinateEnd_pow_apply (b : Basis (Fin n) ℝ V) (D : Module.End ℝ V)
    (k : ℕ) (v : V) : (coordinateEnd b D ^ k) (b.equivFun v) = b.equivFun ((D ^ k) v) := by
  induction k with
  | zero => rfl
  | succ k hk =>
    rw [pow_succ', pow_succ', mul_apply_eq_comp, Module.End.mul_apply,
      hk, coordinateEnd_apply, LinearEquiv.symm_apply_apply]

theorem coordinateEnd_pow_zero (b : Basis (Fin n) ℝ V) (D : Module.End ℝ V)
    {k : ℕ} (hD : D ^ k = 0) : coordinateEnd b D ^ k = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨v, rfl⟩ := b.equivFun.surjective x
  simp only [coordinateEnd_pow_apply, hD, LinearMap.zero_apply, map_zero,
    zero_apply]

/-- The polynomial is independent of a norm or coordinates on the algebra. -/
def finiteEndFlow (D : Module.End ℝ V) (k : ℕ) (t : ℝ) (v : V) : V :=
  ∑ p ∈ Finset.range k, ((p.factorial : ℝ)⁻¹ * t ^ p) • ((D ^ p) v)

theorem finiteEndFlow_smul (D : Module.End ℝ V) (k : ℕ) (a t : ℝ) (v : V) :
    finiteEndFlow (a • D) k t v = finiteEndFlow D k (a * t) v := by
  simp only [finiteEndFlow, smul_pow, LinearMap.smul_apply, smul_smul, mul_pow]
  apply Finset.sum_congr rfl
  intro p _
  congr 1
  ring

theorem coordinate_finiteEndFlow (b : Basis (Fin n) ℝ V) (D : Module.End ℝ V)
    {k : ℕ} (hD : D ^ k = 0) (t : ℝ) (v : V) :
    b.equivFun (finiteEndFlow D k t v) =
      NormedSpace.exp (t • coordinateEnd b D) (b.equivFun v) := by
  have hzero : (t • coordinateEnd b D) ^ k = 0 := by
    rw [smul_pow, coordinateEnd_pow_zero b D hD, smul_zero]
  rw [exp_eq_finite_sum_of_pow_eq_zero _ hzero]
  simp only [finiteEndFlow, map_sum, map_smul, sum_apply,
    smul_apply, smul_pow, coordinateEnd_pow_apply, smul_smul]

theorem finiteEndFlow_map {W : Type*} [AddCommGroup W] [Module ℝ W]
    (f : V →ₗ[ℝ] W) (D : Module.End ℝ V) (E : Module.End ℝ W)
    (hf : ∀ v, f (D v) = E (f v)) (k : ℕ) (t : ℝ) (v : V) :
    f (finiteEndFlow D k t v) = finiteEndFlow E k t (f v) := by
  have hp (p : ℕ) (v : V) : f ((D ^ p) v) = (E ^ p) (f v) := by
    induction p with
    | zero => rfl
    | succ p hp => rw [pow_succ', pow_succ', Module.End.mul_apply,
        Module.End.mul_apply, hf, hp]
  simp only [finiteEndFlow, map_sum, map_smul, hp]

theorem finiteEndFlow_eq_exp {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [FiniteDimensional ℝ U] (D : Module.End ℝ U) {k : ℕ} (hD : D ^ k = 0)
    (t : ℝ) (v : U) : finiteEndFlow D k t v =
      NormedSpace.exp (t • Module.End.toContinuousLinearMap U D) v := by
  let e := Module.End.toContinuousLinearMap (𝕜 := ℝ) U
  have hzero : (t • e D) ^ k = 0 := by
    rw [smul_pow, ← map_pow, hD, map_zero, smul_zero]
  rw [exp_eq_finite_sum_of_pow_eq_zero _ hzero]
  simp only [finiteEndFlow, sum_apply, smul_apply, smul_pow, ← map_pow, smul_smul]
  rfl

/-- Uniformity over the shrinking input ball follows from the same
nilpotent exponential estimate, by choosing a violating vector if one exists. -/
theorem eventually_uniform_nilpotent_exp_ball [Nonempty (Fin n)]
    (D : ℝ → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (t : ℝ → ℝ) {m : ℕ}
    (hD : ∀ r, D r ^ (m + 1) = 0) {A α η : ℝ}
    (hA : 0 ≤ A) (hα : 0 ≤ α) (hgap : (m : ℝ) * α < η)
    (ε : ℝ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hbound : ∀ᶠ r in atTop, ‖D r‖ ≤ A)
    (ht : ∀ᶠ r in atTop, |t r| ≤ Real.exp ((α + ε r) * r)) :
    ∀ᶠ r in atTop, ∀ v : Fin n → ℝ, ‖v‖ ≤ Real.exp (-η * r) →
      ‖NormedSpace.exp (t r • D r) v‖ ≤ 1 := by
  classical
  let P := fun r (v : Fin n → ℝ) =>
    ‖v‖ ≤ Real.exp (-η * r) ∧ 1 < ‖NormedSpace.exp (t r • D r) v‖
  let v : ℝ → Fin n → ℝ := fun r => if h : ∃ x, P r x then h.choose else 0
  have hv (r : ℝ) : ‖v r‖ ≤ Real.exp (-η * r) := by
    dsimp only [v]
    split_ifs with h
    · exact h.choose_spec.1
    · simpa only [norm_zero] using (Real.exp_pos (-η * r)).le
  have hn (r : ℝ) : (t r • D r) ^ (m + 1) = 0 := by
    rw [smul_pow, hD, smul_zero]
  have hb : ∀ᶠ r in atTop, ‖t r • D r‖ ≤ A * Real.exp ((α + |ε r|) * r) := by
    filter_upwards [hbound, ht, eventually_ge_atTop (0 : ℝ)] with r hr ht hr0
    rw [norm_smul, Real.norm_eq_abs]
    apply (mul_le_mul ht hr (norm_nonneg _) (Real.exp_pos _).le).trans
    rw [mul_comm _ A]
    apply mul_le_mul_of_nonneg_left _ hA
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
      (by linarith [le_abs_self (ε r)]) hr0)
  have hv' : ∀ᶠ r in atTop, ‖v r‖ ≤ 1 * Real.exp ((-η + |ε r|) * r) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
    rw [one_mul]
    exact (hv r).trans (Real.exp_le_exp.mpr (by nlinarith [abs_nonneg (ε r)]))
  have hlim := nilpotent_exp_apply_tendsto_zero_of_subexponential_bounds
    (fun r => t r • D r) v hn hA zero_le_one hα hgap
    (fun r => |ε r|) (by simpa using hε.abs) hb hv'
  have hsmall : ∀ᶠ r in atTop, ‖NormedSpace.exp (t r • D r) (v r)‖ < 1 := by
    exact hlim.norm.eventually (eventually_lt_nhds (by simp))
  filter_upwards [hsmall] with r hr x hx
  by_contra h
  have hex : ∃ x, P r x := ⟨x, hx, lt_of_not_ge h⟩
  have hp : P r (v r) := by simpa only [v, dite_eq_left hex] using hex.choose_spec
  exact (not_lt_of_ge hp.2.le) hr

end PolycyclicRecognition

end

end OAI
