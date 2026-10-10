import Mathlib

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped ContDiff
open Filter Set
open scoped Topology
open scoped Topology ContDiff
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory Metric
open scoped Topology Pointwise
open Set MeasureTheory Filter
open scoped Topology NNReal

namespace RVM
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma taylor_bound_lipschitz_derivative {f : E → E} {s : Set E} {L : ℝ≥0}
    (hs : Convex ℝ s) (hf : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hL : LipschitzOnWith L (fderiv ℝ f) s) {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    ‖f y-f x-fderiv ℝ f x (y-x)‖ ≤ L * ‖y-x‖^2 := by
  have hsub : segment ℝ x y ⊆ s := hs.segment_subset hx hy
  have hseg (z : E) (hz : z ∈ segment ℝ x y) : ‖z-x‖ ≤ ‖y-x‖ := by
    simpa only [Metric.mem_closedBall,dist_eq_norm] using ((convex_closedBall x ‖y-x‖).segment_subset (by simp : x ∈ Metric.closedBall x ‖y-x‖)
      (by simp [dist_eq_norm] : y ∈ Metric.closedBall x ‖y-x‖)) hz
  have h := (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le'
    (fun z hz => hf z (hsub hz))
    (fun z hz => (hL.norm_sub_le (hsub hz) hx).trans
      (mul_le_mul_of_nonneg_left (hseg z hz) L.2))
    (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  simpa [pow_two,mul_assoc] using h

lemma variational_remainder_bound
    {f : ℝ → E → E} {x y : ℝ → E} {A D : ℝ → E →L[ℝ] E}
    {a b K ε : ℝ} {v : E}
    (hx : ContinuousOn x (Icc a b)) (hy : ContinuousOn y (Icc a b))
    (hA : ContinuousOn A (Icc a b))
    (hxd : ∀ t ∈ Ico a b, HasDerivWithinAt x (f t (x t)) (Ici t) t)
    (hyd : ∀ t ∈ Ico a b, HasDerivWithinAt y (f t (y t)) (Ici t) t)
    (hAd : ∀ t ∈ Ico a b, HasDerivWithinAt A ((D t).comp (A t)) (Ici t) t)
    (hinit : y a-x a = A a v)
    (hK : ∀ t ∈ Ico a b, ‖D t‖ ≤ K)
    (hε : ∀ t ∈ Ico a b, ‖f t (y t)-f t (x t)-D t (y t-x t)‖ ≤ ε) :
    ∀ t ∈ Icc a b, ‖y t-x t-A t v‖ ≤ gronwallBound 0 K ε (t-a) := by
  have hd : ∀ t ∈ Ico a b, HasDerivWithinAt
      (fun s => y s-x s-A s v)
      (f t (y t)-f t (x t)-D t (A t v)) (Ici t) t := by
    intro t ht
    convert! ((hyd t ht).sub (hxd t ht)).sub ((hAd t ht).clm_apply (hasDerivWithinAt_const t (Ici t) v)) using 1; simp
  apply norm_le_gronwallBound_of_norm_deriv_right_le (δ := 0)
    ((hy.sub hx).sub (hA.clm_apply continuousOn_const)) hd
  · change ‖y a-x a-A a v‖ ≤ 0
    rw [hinit,sub_self,norm_zero]
  · intro t ht
    have heq : f t (y t)-f t (x t)-D t (A t v) =
        D t (y t-x t-A t v) + (f t (y t)-f t (x t)-D t (y t-x t)) := by
      simp only [map_sub]
      abel
    rw [heq]
    calc
      _ ≤ ‖D t (y t-x t-A t v)‖ + ‖f t (y t)-f t (x t)-D t (y t-x t)‖ := norm_add_le _ _
      _ ≤ K*‖y t-x t-A t v‖ + ε := add_le_add
        (((D t).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hK t ht) (norm_nonneg _)))
        (hε t ht)

lemma hasFDerivAt_of_quadratic_bound {g : E → E} {x : E} {A : E →L[ℝ] E}
    {C : ℝ} (_hC : 0 ≤ C)
    (h : ∀ᶠ y in 𝓝 x, ‖g y-g x-A (y-x)‖ ≤ C*‖y-x‖^2) : HasFDerivAt g A x := by
  rw [hasFDerivAt_iff_tendsto]
  apply squeeze_zero' (g := fun y => C*‖y-x‖) (Eventually.of_forall (fun y => mul_nonneg (inv_nonneg.mpr (norm_nonneg _))
    (norm_nonneg _))) ?_ ?_
  · filter_upwards [h] with y hy
    calc
      ‖y-x‖⁻¹*‖g y-g x-A (y-x)‖ ≤ ‖y-x‖⁻¹*(C*‖y-x‖^2) :=
        mul_le_mul_of_nonneg_left hy (inv_nonneg.mpr (norm_nonneg _))
      _ ≤ C*‖y-x‖ := by
        by_cases heq : y = x
        · simp [heq]
        · have hh : ‖y-x‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr heq)
          exact le_of_eq (by field_simp)
  · have ht : Tendsto (fun y : E => C*‖y-x‖) (𝓝 x) (𝓝 (C*‖x-x‖)) := by
      exact (continuous_const.mul (continuous_id.sub continuous_const).norm).tendsto x
    simpa using ht
end RVM

open Set MeasureTheory Metric ODE
open scoped Topology NNReal

namespace RVM

lemma picard_flow_with_range {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax}
    {x₀ : E} {a r L K : ℝ≥0}
    (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    ∃ α : E → ℝ → E,
      (∀ x ∈ closedBall x₀ r, α x t₀ = x ∧
        (∀ t ∈ Icc tmin tmax, HasDerivWithinAt (α x) (f t (α x t)) (Icc tmin tmax) t) ∧
        ∀ t, α x t ∈ closedBall x₀ a) ∧
      ∃ L' : ℝ≥0, ∀ t ∈ Icc tmin tmax, LipschitzOnWith L' (α · t) (closedBall x₀ r) := by
  classical
  have (x) (hx : x ∈ closedBall x₀ r) := FunSpace.exists_isFixedPt_next hf hx
  choose α hα using this
  set α' := fun (x : E) ↦ if hx : x ∈ closedBall x₀ r then
    α x hx |>.compProj else 0 with hα'
  refine ⟨α', fun x hx ↦ ⟨?_, fun t ht ↦ ?_, fun t => ?_⟩, ?_⟩
  · rw [hα']
    beta_reduce
    rw [dite_eq_left hx, FunSpace.compProj_val, ← hα, FunSpace.next_apply₀]
  · rw [hα']
    beta_reduce
    rw [dite_eq_left hx, FunSpace.compProj_apply]
    apply hasDerivWithinAt_picard_Icc t₀.2 hf.continuousOn_uncurry
      (α x hx |>.continuous_compProj.continuousOn)
      (fun _ ht' ↦ α x hx |>.compProj_mem_closedBall hf.mul_max_le)
      x ht |>.congr_of_mem _ ht
    intro t' ht'
    nth_rw 1 [← hα]
    rw [FunSpace.compProj_of_mem ht', FunSpace.next_apply]
  · simp only [hα',dite_eq_left hx]
    exact (α x hx).compProj_mem_closedBall hf.mul_max_le
  · obtain ⟨L', h⟩ := FunSpace.exists_forall_closedBall_funSpace_dist_le_mul hf
    refine ⟨L', fun t ht ↦ LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_⟩
    simp_rw [hα']
    rw [dite_eq_left hx, dite_eq_left hy, FunSpace.compProj_apply, FunSpace.compProj_apply,
      ← FunSpace.toContinuousMap_apply_eq_apply, ← FunSpace.toContinuousMap_apply_eq_apply]
    have : Nonempty (Icc tmin tmax) := ⟨t₀⟩
    apply ContinuousMap.dist_le_iff_of_nonempty.mp
    exact h x y hx hy (α x hx) (α y hy) (hα x hx) (hα y hy)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]

def variationalField (f : E → E) (z : E × (E →L[ℝ] E)) : E × (E →L[ℝ] E) :=
  (f z.1, (fderiv ℝ f z.1).comp z.2)

omit [FiniteDimensional ℝ E] in
lemma contDiff_variationalField {f : E → E} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 1 (variationalField f) := by
  exact ((hf.of_le (by norm_num)).comp contDiff_fst).prodMk
    (((hf.fderiv_right (by norm_num)).comp contDiff_fst).clm_comp contDiff_snd)

lemma exists_local_variational_flow {f : E → E} (hf : ContDiff ℝ 2 f) (x₀ : E) :
    ∃ ε > (0 : ℝ), ∃ α : E → ℝ → E, ∃ A : E → ℝ → (E →L[ℝ] E), ∃ L : ℝ≥0,
      (∀ x ∈ closedBall x₀ (1/2 : ℝ), α x 0 = x ∧ A x 0 = ContinuousLinearMap.id ℝ E ∧
        (∀ t ∈ Icc (-ε) ε, HasDerivWithinAt (α x) (f (α x t)) (Icc (-ε) ε) t) ∧
        (∀ t ∈ Icc (-ε) ε, HasDerivWithinAt (A x)
          ((fderiv ℝ f (α x t)).comp (A x t)) (Icc (-ε) ε) t) ∧
        ∀ t, α x t ∈ closedBall x₀ 1) ∧
      ∀ t ∈ Icc (-ε) ε, LipschitzOnWith L (α · t) (closedBall x₀ (1/2 : ℝ)) := by
  let z₀ : E × (E →L[ℝ] E) := (x₀,ContinuousLinearMap.id ℝ E)
  have hF := contDiff_variationalField hf
  obtain ⟨K,hK⟩ := hF.contDiffOn.exists_lipschitzOnWith (by norm_num)
    (convex_closedBall z₀ 1) (isCompact_closedBall z₀ 1)
  obtain ⟨M,hM⟩ := (isCompact_closedBall z₀ 1).bddAbove_image hF.continuous.norm.continuousOn
  let B := max 1 M
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let ε : ℝ := 1/(2*B)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hp : IsPicardLindelof (fun _ => variationalField f)
      (tmin := -ε) (tmax := ε) ⟨0,⟨by linarith, hε.le⟩⟩ z₀ 1 (1/2) ⟨B,hB.le⟩ K := by
    refine IsPicardLindelof.of_time_independent ?_ hK ?_
    · intro z hz
      exact (hM ⟨z,hz,rfl⟩).trans (le_max_right _ _)
    · change B * max (ε-0) (0-(-ε)) ≤ (1 : ℝ)-(1/2 : ℝ≥0)
      norm_num only [sub_zero,zero_sub,neg_neg,max_self,NNReal.coe_div,NNReal.coe_one,
        NNReal.coe_ofNat]
      dsimp [ε]
      field_simp
      norm_num
  obtain ⟨β,hβ,L,hL⟩ := picard_flow_with_range hp
  let α : E → ℝ → E := fun x t => (β (x,ContinuousLinearMap.id ℝ E) t).1
  let A : E → ℝ → (E →L[ℝ] E) := fun x t => (β (x,ContinuousLinearMap.id ℝ E) t).2
  have hmem {x : E} (hx : x ∈ closedBall x₀ (1/2 : ℝ)) :
      (x,ContinuousLinearMap.id ℝ E) ∈ closedBall z₀ ((1/2 : ℝ≥0) : ℝ) := by
    simpa [z₀,Prod.dist_eq] using hx
  refine ⟨ε,hε,α,A,L,?_,?_⟩
  · intro x hx
    have hh := hβ _ (hmem hx)
    refine ⟨congrArg Prod.fst hh.1,congrArg Prod.snd hh.1,?_,?_,?_⟩
    · intro t ht
      simpa [α,variationalField] using (hh.2.1 t ht).hasFDerivWithinAt.fst.hasDerivWithinAt
    · intro t ht
      simpa [α,A,variationalField] using (hh.2.1 t ht).hasFDerivWithinAt.snd.hasDerivWithinAt
    · intro t
      have hr := hh.2.2 t
      change dist (α x t) x₀ ≤ 1
      change max (dist (α x t) x₀) (dist (A x t) (ContinuousLinearMap.id ℝ E)) ≤ 1 at hr
      exact (le_max_left _ _).trans hr
  · intro t ht
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    exact (le_max_left _ _).trans (by
      simpa [Prod.dist_eq] using (hL t ht).dist_le_mul _ (hmem hx) _ (hmem hy))
end RVM

end

end OAI
