import OAI.Probability.SwitchChain.PairEqualityProjection

namespace OAI

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Problem315.PairEquality
open PairResampling

theorem projection_apply_eq_zero_on_inactive_fiber
    {n : ℕ} {d : Fin n → ℕ} (i j k l : Fin n) (f : StateSpace n d)
    (G H : GraphState n d) (hGH : SameFiber {i, j} G.val H.val)
    (hinactive : ¬ active i j k l G) :
    projection i j k l f H = 0 := by
  have hf := (equalitySpace (d := d) i j k l).starProjection_apply_mem f
  obtain ⟨c, hc⟩ := hf G
  simpa only [projection, ite_eq_right hinactive, mul_zero] using hc H hGH

theorem projection_apply_eq_zero_of_inactive
    {n : ℕ} {d : Fin n → ℕ} (i j k l : Fin n) (f : StateSpace n d)
    (G : GraphState n d) (hinactive : ¬ active i j k l G) :
    projection i j k l f G = 0 :=
  projection_apply_eq_zero_on_inactive_fiber i j k l f G G
    (SameFiber.refl _ _) hinactive

theorem sum_projection_sq_on_inactive_fiber
    {n : ℕ} {d : Fin n → ℕ} (i j k l : Fin n) (f : StateSpace n d)
    (G : GraphState n d) (hinactive : ¬ active i j k l G) :
    (∑ H ∈ fiberStates {i, j} G, (projection i j k l f H) ^ 2) = 0 := by
  apply Finset.sum_eq_zero
  intro H hH
  rw [projection_apply_eq_zero_on_inactive_fiber i j k l f G H
    ((mem_fiberStates {i, j} G H).mp hH) hinactive]
  norm_num

theorem projection_apply_eq_zero_of_centered_zero
    {n : ℕ} {d : Fin n → ℕ} (i j k l : Fin n) (f : StateSpace n d)
    (G H : GraphState n d) (hGH : SameFiber {i, j} G.val H.val)
    (hzero : centered (d := d) i j k l H = 0) :
    projection i j k l f H = 0 := by
  have hf := (equalitySpace (d := d) i j k l).starProjection_apply_mem f
  obtain ⟨c, hc⟩ := hf G
  simpa only [projection, hzero, ite_self, mul_zero] using hc H hGH

theorem centered_same_label
    {n : ℕ} {d : Fin n → ℕ} (i j k : Fin n) :
    centered (d := d) i j k k = 0 := by
  unfold centered
  apply (fluctuation_eq_zero_iff _ _).mpr
  have heq : observable (d := d) i k k =
      WithLp.toLp 2 (fun _ : GraphState n d => (1 : ℝ)) := by
    ext G
    simp [observable]
  rw [heq]
  exact constant_mem _ 1

theorem projection_same_label
    {n : ℕ} {d : Fin n → ℕ} (i j k : Fin n) :
    projection (d := d) i j k k = 0 := by
  ext f G
  apply projection_apply_eq_zero_of_centered_zero i j k k f G G
    (SameFiber.refl _ _)
  have hz := congrArg (fun v : StateSpace n d => v G)
    (centered_same_label (d := d) i j k)
  exact hz

end Problem315.PairEquality

end

end OAI
