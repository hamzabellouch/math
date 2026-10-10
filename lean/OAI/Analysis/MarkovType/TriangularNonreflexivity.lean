import OAI.Analysis.MarkovType.FinitelyRepresentable
import OAI.Analysis.MarkovType.ScalarUltralimit
import Mathlib.LinearAlgebra.Span.Defs

namespace OAI

noncomputable section

open Filter
open scoped Topology

namespace MarkovSuperreflexivity

universe u

variable {Z : Type u} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

private theorem unit_eval_abs_le (e : ℕ → Z) (he : ∀ i, ‖e i‖ ≤ 1)
    (g : StrongDual ℝ Z) (i : ℕ) : |g (e i)| ≤ ‖g‖ := by
  calc
    |g (e i)| = ‖g (e i)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖g‖ * ‖e i‖ := g.le_opNorm (e i)
    _ ≤ ‖g‖ * 1 := mul_le_mul_of_nonneg_left (he i) (norm_nonneg g)
    _ = ‖g‖ := mul_one _

private theorem unit_eval_bounded (e : ℕ → Z) (he : ∀ i, ‖e i‖ ≤ 1)
    (g : StrongDual ℝ Z) : RealSeqBounded (fun i => g (e i)) :=
  ⟨‖g‖, unit_eval_abs_le e he g⟩

private theorem unit_eval_ulim_bound (e : ℕ → Z) (he : ∀ i, ‖e i‖ ≤ 1)
    (g : StrongDual ℝ Z) :
    |realULim freeUltrafilter (fun i => g (e i))| ≤ ‖g‖ := by
  rw [← realULim_abs freeUltrafilter (unit_eval_bounded e he g)]
  exact realULim_le_of_eventually_le freeUltrafilter (unit_eval_bounded e he g).abs
    (Filter.Eventually.of_forall (unit_eval_abs_le e he g))

private def unitSequenceBidualLinear (e : ℕ → Z) (he : ∀ i, ‖e i‖ ≤ 1) :
    StrongDual ℝ Z →ₗ[ℝ] ℝ where
  toFun g := realULim freeUltrafilter (fun i => g (e i))
  map_add' g h := by
    simpa only [add_apply] using
      realULim_add freeUltrafilter (unit_eval_bounded e he g) (unit_eval_bounded e he h)
  map_smul' c g := by
    simpa only [smul_apply, RingHom.id_apply, smul_eq_mul] using
      realULim_const_mul freeUltrafilter c (unit_eval_bounded e he g)

def unitSequenceBidual (e : ℕ → Z) (he : ∀ i, ‖e i‖ ≤ 1) :
    StrongDual ℝ (StrongDual ℝ Z) :=
  (unitSequenceBidualLinear e he).mkContinuous 1 (fun g => by
    change ‖realULim freeUltrafilter (fun i => g (e i))‖ ≤ 1 * ‖g‖
    simpa only [Real.norm_eq_abs, one_mul] using unit_eval_ulim_bound e he g)

@[simp]
theorem unitSequenceBidual_apply (e : ℕ → Z) (he : ∀ i, ‖e i‖ ≤ 1)
    (g : StrongDual ℝ Z) :
    unitSequenceBidual e he g = realULim freeUltrafilter (fun i => g (e i)) := rfl

theorem unitSequenceBidual_norm_le (e : ℕ → Z) (he : ∀ i, ‖e i‖ ≤ 1) :
    ‖unitSequenceBidual e he‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro g
  simpa only [unitSequenceBidual_apply, Real.norm_eq_abs, one_mul] using
    unit_eval_ulim_bound e he g

theorem unitSequenceBidual_eval_of_eventually_eq
    (e : ℕ → Z) (he : ∀ i, ‖e i‖ ≤ 1) (g : StrongDual ℝ Z) {a : ℝ}
    (h : ∀ᶠ i in atTop, g (e i) = a) : unitSequenceBidual e he g = a := by
  rw [unitSequenceBidual_apply]
  apply realULim_freeUltrafilter_eq_of_tendsto_atTop
  exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => a) atTop (𝓝 a)).congr' (h.mono fun _ hi => hi.symm)

private def eventualKernelSubmodule (f : ℕ → StrongDual ℝ Z) : Submodule ℝ Z where
  carrier := {x | ∀ᶠ j in atTop, f j x = 0}
  zero_mem' := Filter.Eventually.of_forall (fun j => (f j).map_zero)
  add_mem' := by
    intro x y hx hy
    exact (hx.and hy).mono (fun j hj => by rw [map_add, hj.1, hj.2, add_zero])
  smul_mem' := by
    intro c x hx
    exact hx.mono (fun j hj => by rw [map_smul, hj, smul_zero])

theorem triangular_eventually_zero_on_span
    (e : ℕ → Z) (f : ℕ → StrongDual ℝ Z) {θ : ℝ}
    (hpair : ∀ i j, f j (e i) = if j ≤ i then θ else 0)
    {x : Z} (hx : x ∈ Submodule.span ℝ (Set.range e)) :
    ∀ᶠ j in atTop, f j x = 0 := by
  have hspan : Submodule.span ℝ (Set.range e) ≤ eventualKernelSubmodule f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change ∀ᶠ j in atTop, f j (e i) = 0
    refine Filter.eventually_atTop.mpr ⟨i + 1, ?_⟩
    intro j hji
    rw [hpair]
    exact ite_eq_right (Nat.not_le_of_lt ((Nat.lt_succ_self i).trans_le hji))
  exact hspan hx

theorem triangular_functionals_tendsto_zero
    (e : ℕ → Z) (f : ℕ → StrongDual ℝ Z)
    (hf : ∀ j, ‖f j‖ ≤ 1) {θ : ℝ}
    (hpair : ∀ i j, f j (e i) = if j ≤ i then θ else 0)
    (hdense : Dense (Submodule.span ℝ (Set.range e) : Set Z)) (x : Z) :
    Tendsto (fun j => f j x) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := hdense.exists_dist_lt x hε
  apply (triangular_eventually_zero_on_span e f hpair hy).mono
  intro j hj
  calc
    dist (f j x) 0 = ‖f j x‖ := dist_zero_right _
    _ = ‖f j (x - y)‖ := by rw [map_sub, hj, sub_zero]
    _ ≤ ‖f j‖ * ‖x - y‖ := (f j).le_opNorm (x - y)
    _ ≤ 1 * ‖x - y‖ := mul_le_mul_of_nonneg_right (hf j) (norm_nonneg _)
    _ = dist x y := by rw [one_mul, dist_eq_norm]
    _ < ε := hxy

theorem not_canonicallyReflexive_of_triangular_dense
    (e : ℕ → Z) (he : ∀ i, ‖e i‖ ≤ 1)
    (f : ℕ → StrongDual ℝ Z) (hf : ∀ j, ‖f j‖ ≤ 1)
    {θ : ℝ} (hθ : 0 < θ)
    (hpair : ∀ i j, f j (e i) = if j ≤ i then θ else 0)
    (hdense : Dense (Submodule.span ℝ (Set.range e) : Set Z)) :
    ¬ CanonicallyReflexive Z := by
  intro hR
  obtain ⟨x, hx⟩ := hR (unitSequenceBidual e he)
  have hvalue (j : ℕ) : f j x = θ := by
    have hulim : unitSequenceBidual e he (f j) = θ := by
      apply unitSequenceBidual_eval_of_eventually_eq
      refine Filter.eventually_atTop.mpr ⟨j, ?_⟩
      intro i hji
      rw [hpair, ite_eq_left hji]
    have hxj := congrArg (fun v : StrongDual ℝ (StrongDual ℝ Z) => v (f j)) hx
    change f j x = unitSequenceBidual e he (f j) at hxj
    exact hxj.trans hulim
  have hzero := triangular_functionals_tendsto_zero e f hf hpair hdense x
  have hconstant : (fun j => f j x) = (fun _ : ℕ => θ) := funext hvalue
  rw [hconstant] at hzero
  have hθ0 : θ = 0 := tendsto_nhds_unique tendsto_const_nhds hzero
  exact (ne_of_gt hθ) hθ0

end MarkovSuperreflexivity

end

end OAI
