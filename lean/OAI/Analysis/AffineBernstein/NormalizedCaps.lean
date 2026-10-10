import Mathlib
import OAI.Analysis.AffineBernstein.NormedCompactInterior

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open Filter Metric
open scoped Topology Pointwise
open scoped Pointwise
open scoped Pointwise

open Filter Metric
open scoped Topology Pointwise

/- Quantitative cap transfer: a given limit radius costs only one unit.
The constant does not depend on the sequence or its limit set. -/
theorem LocalDistanceConverges.eventually_caps_radius
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {Cj : ℕ → Set E} {C : Set E} (h : LocalDistanceConverges Cj C)
    (hcl : IsClosed C) (hclj : ∀ j, IsClosed (Cj j))
    (hcvj : ∀ j, Convex ℝ (Cj j)) (hnej : ∀ j, (Cj j).Nonempty)
    (ell : E →L[ℝ] ℝ) (b R : ℝ)
    (hcap : C ∩ {x | ell x ≤ b} ⊆ closedBall 0 R)
    {q : E} (hq : q ∈ C) (hqb : ell q < b) :
    ∀ᶠ j in atTop, Cj j ∩ {x | ell x ≤ b} ⊆ ball 0 (R+1) := by
  have hqR : ‖q‖ < R+1 := by
    have := mem_closedBall_zero_iff.mp (hcap ⟨hq,hqb.le⟩)
    linarith
  let S : Set E := sphere (0 : E) (R+1) ∩ {x | ell x ≤ b}
  have hSc : IsCompact S := (isCompact_sphere (0 : E) (R+1)).inter_right
    (isClosed_le ell.continuous continuous_const)
  have hSd : Disjoint C S := by
    rw [Set.disjoint_left]
    intro x hx hxs
    have he : ‖x‖ = R+1 := mem_sphere_zero_iff_norm.mp hxs.1
    have hl := mem_closedBall_zero_iff.mp (hcap ⟨hx,hxs.2⟩)
    linarith
  obtain ⟨qj,hqj,hqjt⟩ := h.exists_approximating hclj hnej hq
  have hqjR : ∀ᶠ j in atTop, ‖qj j‖ < R+1 := hqjt.norm.eventually_lt_const hqR
  have hqjb : ∀ᶠ j in atTop, ell (qj j) < b :=
    (ell.continuous.tendsto q |>.comp hqjt).eventually_lt_const hqb
  filter_upwards [h.eventually_disjoint_compact hcl ⟨q,hq⟩ hSc hSd,hqjR,hqjb]
    with j hj hqRj hqbj
  intro p hp
  by_contra hn
  have hpR : R+1 ≤ ‖p‖ := by simpa [Metric.mem_ball,dist_zero_right,not_lt] using hn
  let f : ℝ → E := fun t => (1-t) • qj j+t • p
  have hf : Continuous f := by fun_prop
  have hf0 : f 0 = qj j := by simp [f]
  have hf1 : f 1 = p := by simp [f]
  have hRim : R+1 ∈ (fun t => ‖f t‖) '' Icc (0 : ℝ) 1 :=
    intermediate_value_Icc (by norm_num) hf.norm.continuousOn (by simp [hf0,hf1,hqRj.le,hpR])
  obtain ⟨t,ht,htR⟩ := hRim
  have hft : f t ∈ Cj j := hcvj j (hqj j) hp.1 (sub_nonneg.mpr ht.2) ht.1 (by ring)
  have hfb : ell (f t) ≤ b := by
    dsimp [f]
    simp only [map_add,map_smul,smul_eq_mul]
    have h1 := mul_le_mul_of_nonneg_left hqbj.le (sub_nonneg.mpr ht.2)
    have h2 := mul_le_mul_of_nonneg_left hp.2 ht.1
    nlinarith
  exact Set.disjoint_left.mp hj hft ⟨mem_sphere_zero_iff_norm.mpr htR,hfb⟩

/- The positive base functional occurring in normalized model caps. -/
def positiveBaseForm {k m : ℕ} (a : Fin k → ℝ) : (Space k × Space m) →L[ℝ] ℝ :=
  (∑ i, a i • EuclideanSpace.proj i).comp (ContinuousLinearMap.fst ℝ (Space k) (Space m))

@[simp] lemma positiveBaseForm_apply {k m : ℕ} (a : Fin k → ℝ) (p : Space k × Space m) :
    positiveBaseForm a p = ∑ i, a i * p.1 i := by
  simp [positiveBaseForm,PiLp.proj_apply]

lemma norm_le_sqrt_card_mul_of_coord_le {k : ℕ} {x : Space k} {T : ℝ}
    (hT : 0 < T) (hx : ∀ i, |x i| ≤ T) : ‖x‖ ≤ Real.sqrt k*T := by
  have hh := norm_le_sqrt_card_of_coordinate_le (T⁻¹ • x) (fun i => by
    change |T⁻¹ * x i| ≤ 1
    rw [abs_mul,abs_of_pos (inv_pos.mpr hT)]
    exact (inv_mul_le_iff₀ hT).mpr (by simpa using hx i))
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hT)] at hh
  exact (inv_mul_le_iff₀ hT).mp hh |>.trans_eq (mul_comm _ _)

lemma IsModelShape.normalized_cap_box {k m : ℕ} {C : Set (Space k × Space m)}
    (hC : IsModelShape C) {R B α : ℝ} {a : Fin k → ℝ}
    (hα : 0 < α) (ha : ∀ i, α ≤ a i)
    (hout : modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))) ⊆ closedBall 0 R) :
    C ∩ {p | positiveBaseForm a p ≤ B} ⊆
      {s : Space k | ∀ i, s i ∈ Icc 0 (max 1 (B/α))} ×ˢ
      closedBall (0 : Space m) (max 1 (B/α)*R) := by
  rintro ⟨s,y⟩ ⟨hp,hcap⟩
  have hs := hC.support (s,y) hp
  have hb (i : Fin k) : s i ≤ max 1 (B/α) := by
    have hi : α*s i ≤ B := calc
      _ ≤ a i*s i := mul_le_mul_of_nonneg_right (ha i) (hs i)
      _ ≤ ∑ j, a j*s j := Finset.single_le_sum (fun j _ => mul_nonneg (hα.le.trans (ha j)) (hs j)) (Finset.mem_univ i)
      _ ≤ B := by simpa using hcap
    exact ((le_div_iff₀ hα).mpr (by simpa [mul_comm] using hi)).trans (le_max_right _ _)
  exact ⟨fun i => ⟨hs i,hb i⟩,mem_closedBall_zero_iff.mpr
    (hC.fiber_box_bound (le_max_left _ _) hout hb hp)⟩

lemma IsModelShape.normalized_cap_radius {k m : ℕ} {C : Set (Space k × Space m)}
    (hC : IsModelShape C) {R B α : ℝ} {a : Fin k → ℝ}
    (hα : 0 < α) (ha : ∀ i, α ≤ a i)
    (hout : modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))) ⊆ closedBall 0 R) :
    C ∩ {p | positiveBaseForm a p ≤ B} ⊆
      closedBall 0 (max (Real.sqrt k * max 1 (B/α)) (max 1 (B/α)*R)) := by
  intro p hp
  have hh := hC.normalized_cap_box hα ha hout hp
  rw [mem_closedBall_zero_iff,Prod.norm_def]
  apply max_le_max
  · exact norm_le_sqrt_card_mul_of_coord_le (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
      (fun i => by rw [abs_of_nonneg (hh.1 i).1]; exact (hh.1 i).2)
  · exact mem_closedBall_zero_iff.mp hh.2

/- Uniform interior ball about (1,0), with an explicit positive radius. -/
lemma IsModelShape.normalized_center_ball {k m : ℕ} {C : Set (Space k × Space m)}
    (hC : IsModelShape C) {r : ℝ} (hr : 0 < r)
    (hin : closedBall (0 : Space m) r ⊆
      modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ)))) :
    closedBall ((WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))), (0 : Space m))
      (min (1/4) (r/4)) ⊆ interior C := by
  rintro ⟨s,y⟩ hp
  have hd := mem_closedBall.mp hp
  have hs : ‖s - WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))‖ ≤ min (1/4) (r/4) := by
    rw [← dist_eq_norm]
    exact le_trans (le_max_left _ _) hd
  have hy : ‖y‖ ≤ min (1/4) (r/4) := by
    simpa only [dist_zero_right] using le_trans (le_max_right _ _) hd
  apply hC.normalized_fiber_interior hr (a := 1/2) (by norm_num) (by norm_num) hin
  · intro i
    have hi := (PiLp.norm_apply_le (s - WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))) i).trans hs
    change |s i-1| ≤ min (1/4) (r/4) at hi
    linarith [le_abs_self (-(s i-1)),abs_neg (s i-1),min_le_left (1/4:ℝ) (r/4)]
  · linarith [hy.trans (min_le_right (1/4:ℝ) (r/4))]

/- Eventual cap bounds with constants fixed before the approximating sequence. -/
theorem LocalDistanceConverges.eventually_normalized_cap_radius
    {k m : ℕ} {Cj : ℕ → Set (Space k × Space m)} {C : Set (Space k × Space m)}
    (h : LocalDistanceConverges Cj C) (hC : IsModelShape C)
    (hclj : ∀ j, IsClosed (Cj j)) (hcvj : ∀ j, Convex ℝ (Cj j))
    (hnej : ∀ j, (Cj j).Nonempty) {R B α : ℝ} {a : Fin k → ℝ}
    (hB : 0 < B) (hα : 0 < α) (ha : ∀ i, α ≤ a i)
    (hout : modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))) ⊆ closedBall 0 R) :
    ∀ᶠ j in atTop, Cj j ∩ {p | positiveBaseForm a p ≤ B} ⊆
      ball 0 (max (Real.sqrt k * max 1 (B/α)) (max 1 (B/α)*R)+1) := by
  exact h.eventually_caps_radius hC.closed hclj hcvj hnej (positiveBaseForm a) B _
    (hC.normalized_cap_radius hα ha hout) hC.zero_mem (by simpa using hB)

/- Uniform outer fiber bounds on an entire fixed positive box. A single
containing cap gives one index, rather than using pointwise convergence. -/
theorem LocalDistanceConverges.eventually_normalized_fiber_outer
    {k m : ℕ} {Cj : ℕ → Set (Space k × Space m)} {C : Set (Space k × Space m)}
    (h : LocalDistanceConverges Cj C) (hC : IsModelShape C)
    (hclj : ∀ j, IsClosed (Cj j)) (hcvj : ∀ j, Convex ℝ (Cj j))
    (hnej : ∀ j, (Cj j).Nonempty) {R a b : ℝ} (hb : 1 ≤ b)
    (hout : modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))) ⊆ closedBall 0 R) :
    ∀ᶠ j in atTop, ∀ s : Space k, (∀ i, s i ∈ Icc a b) →
      modelFiber (Cj j) s ⊆ closedBall 0
        (max (Real.sqrt k * max 1 (k*b+1)) (max 1 (k*b+1)*R)+1) := by
  have hB : 0 < (k:ℝ)*b+1 := by
    have : 0 ≤ (k:ℝ)*b := mul_nonneg (Nat.cast_nonneg k) (by linarith)
    linarith
  filter_upwards [h.eventually_normalized_cap_radius hC hclj hcvj hnej
    (a := fun _ => (1:ℝ)) hB zero_lt_one (fun _ => le_rfl) hout]
    with j hj s hs y hy
  have hc : positiveBaseForm (fun _ : Fin k => (1:ℝ)) (s,y) ≤ (k:ℝ)*b+1 := by
    simp only [positiveBaseForm_apply,one_mul]
    have he : ∑ i : Fin k, s i ≤ (k:ℝ)*b := by
      calc
        _ ≤ ∑ _i : Fin k, b := Finset.sum_le_sum (fun i _ => (hs i).2)
        _ = _ := by simp
    linarith
  have hh := mem_ball.mp (hj ⟨hy,hc⟩)
  rw [mem_closedBall_zero_iff]
  exact le_trans (le_max_right ‖s‖ ‖y‖) (by simpa only [div_one,dist_zero_right,Prod.norm_def] using hh.le)

/- Simultaneous two-sided bounds and nonempty fiber interiors. The parameters
in the radii are fixed before an approximating index is chosen. -/
theorem LocalDistanceConverges.eventually_normalized_fibers
    {k m : ℕ} {Cj : ℕ → Set (Space k × Space m)} {C : Set (Space k × Space m)}
    (h : LocalDistanceConverges Cj C) (hC : IsModelShape C)
    (hclj : ∀ j, IsClosed (Cj j)) (hcvj : ∀ j, Convex ℝ (Cj j))
    (hnej : ∀ j, (Cj j).Nonempty) {r R a b : ℝ}
    (hr : 0 < r) (ha : 0 < a) (ha1 : a ≤ 1) (hb : 1 ≤ b)
    (hin : closedBall (0 : Space m) r ⊆
      modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))))
    (hout : modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))) ⊆ closedBall 0 R) :
    ∀ᶠ j in atTop, ∀ s : Space k, (∀ i, s i ∈ Icc a b) →
      closedBall (0 : Space m) (a*r/2) ⊆ modelFiber (Cj j) s ∧
      0 ∈ interior (modelFiber (Cj j) s) ∧
      modelFiber (Cj j) s ⊆ closedBall 0
        (max (Real.sqrt k * max 1 (k*b+1)) (max 1 (k*b+1)*R)+1) := by
  filter_upwards [h.eventually_normalized_fiber_inner hC hclj hcvj hnej hr ha ha1 hin,
    h.eventually_normalized_fiber_outer hC hclj hcvj hnej hb hout] with j hji hjo s hs
  refine ⟨hji s hs,?_,hjo s hs⟩
  apply mem_interior_iff_mem_nhds.mpr
  exact Filter.mem_of_superset (closedBall_mem_nhds (0 : Space m) (by positivity)) (hji s hs)

/- One explicit interior ball survives in every large approximant. -/
theorem LocalDistanceConverges.eventually_normalized_center_ball
    {k m : ℕ} {Cj : ℕ → Set (Space k × Space m)} {C : Set (Space k × Space m)}
    (h : LocalDistanceConverges Cj C) (hC : IsModelShape C)
    (hclj : ∀ j, IsClosed (Cj j)) (hcvj : ∀ j, Convex ℝ (Cj j))
    (hnej : ∀ j, (Cj j).Nonempty) {r : ℝ} (hr : 0 < r)
    (hin : closedBall (0 : Space m) r ⊆
      modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ)))) :
    ∀ᶠ j in atTop, closedBall
      ((WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))), (0 : Space m))
      (min (1/4) (r/4)) ⊆ Cj j := by
  exact h.eventually_normed_compact_subset hclj hcvj hnej
    (isCompact_closedBall _ _) (hC.normalized_center_ball hr hin)

end AffineBernstein
end

end OAI
