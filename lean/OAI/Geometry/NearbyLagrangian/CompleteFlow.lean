import Mathlib

namespace OAI

/-! Complete bounded Lipschitz flows, support and first integrals. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.ODE
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

structure CompleteFlow (F : E → E) where
  toFun : E × ℝ → E
  continuous_toFun : Continuous toFun
  initial : ∀ x, toFun (x,0) = x
  derivative : ∀ x t, HasDerivAt (fun s => toFun (x,s)) (F (toFun (x,t))) t

private theorem exists_local_box_flow (F : E → E) {L K : ℝ≥0}
    (hL : ∀ x, ‖F x‖ ≤ L) (hK : LipschitzWith K F) (n : ℕ) :
    ∃ α : E × ℝ → E,
      (∀ x ∈ closedBall (0:E) (n+1:ℝ), α (x,0) = x ∧
        ∀ t ∈ Icc (-(n+1:ℝ)) (n+1:ℝ),
          HasDerivWithinAt (fun s => α (x,s)) (F (α (x,t)))
            (Icc (-(n+1:ℝ)) (n+1:ℝ)) t) ∧
      ContinuousOn α (closedBall (0:E) (n+1:ℝ) ×ˢ Icc (-(n+1:ℝ)) (n+1:ℝ)) := by
  let r : ℝ≥0 := n+1
  let a : ℝ≥0 := r+L*r
  have hr : (r:ℝ) = (n:ℝ)+1 := by simp [r]
  let t₀ : Icc (-(n+1:ℝ)) (n+1:ℝ) := ⟨0, ⟨neg_nonpos.mpr (by positivity), by positivity⟩⟩
  have hf : IsPicardLindelof (fun _ => F) t₀ (0:E) a r L K := by
    refine ⟨fun _ _ => hK.lipschitzOnWith, fun _ _ => continuousOn_const,
      fun _ _ x _ => hL x, ?_⟩
    simp only [t₀, sub_zero, zero_sub, neg_neg, max_self, a, NNReal.coe_add,
      NNReal.coe_mul, hr]
    linarith
  simpa only [hr] using hf.exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn

omit [CompleteSpace E] in
private theorem box_flow_agree (F : E → E) {K : ℝ≥0} (hK : LipschitzWith K F)
    {α β : E × ℝ → E} {r s : ℝ} (hr : 0 < r) (hs : 0 < s) {x : E}
    (hα0 : α (x,0) = x) (hβ0 : β (x,0) = x)
    (hα : ∀ t ∈ Ioo (-r) r, HasDerivAt (fun t => α (x,t)) (F (α (x,t))) t)
    (hβ : ∀ t ∈ Ioo (-s) s, HasDerivAt (fun t => β (x,t)) (F (β (x,t))) t) :
    ∀ t ∈ Ioo (-r) r ∩ Ioo (-s) s, α (x,t) = β (x,t) := by
  let c := min r s
  have hc : 0 < c := lt_min hr hs
  have hcr : Ioo (-c) c ⊆ Ioo (-r) r := Ioo_subset_Ioo (neg_le_neg (min_le_left _ _))
    (min_le_left _ _)
  have hcs : Ioo (-c) c ⊆ Ioo (-s) s := Ioo_subset_Ioo (neg_le_neg (min_le_right _ _))
    (min_le_right _ _)
  have heq := ODE_solution_unique_of_mem_Ioo (v := fun _ => F) (s := fun _ => univ)
    (fun _ _ => hK.lipschitzOnWith) (show (0:ℝ) ∈ Ioo (-c) c from ⟨by linarith, hc⟩)
    (fun t ht => ⟨hα t (hcr ht), mem_univ _⟩)
    (fun t ht => ⟨hβ t (hcs ht), mem_univ _⟩) (hα0.trans hβ0.symm)
  intro t ht
  apply heq
  exact ⟨by
      have h : -t < min r s := lt_min (by linarith [ht.1.1]) (by linarith [ht.2.1])
      dsimp [c]
      linarith,
    lt_min ht.1.2 ht.2.2⟩

theorem exists_completeFlow (F : E → E) {L K : ℝ≥0}
    (hL : ∀ x, ‖F x‖ ≤ L) (hK : LipschitzWith K F) : Nonempty (CompleteFlow F) := by
  classical
  choose α hα using fun n => exists_local_box_flow F hL hK n
  let U (n : ℕ) : Set (E × ℝ) := ball (0:E) (n+1:ℝ) ×ˢ Ioo (-(n+1:ℝ)) (n+1:ℝ)
  have hU : ∀ n, IsOpen (U n) := fun _ => isOpen_ball.prod isOpen_Ioo
  have hcover : ∀ p : E × ℝ, ∃ n, p ∈ U n := by
    intro p
    obtain ⟨n,hn⟩ := exists_nat_gt (max ‖p.1‖ |p.2|)
    refine ⟨n, ?_⟩
    have hn0 : ‖p.1‖ < (n:ℝ)+1 := lt_trans (lt_of_le_of_lt (le_max_left _ _) hn) (by linarith)
    have hn1 : |p.2| < (n:ℝ)+1 := lt_trans (lt_of_le_of_lt (le_max_right _ _) hn) (by linarith)
    exact ⟨by simpa only [mem_ball, dist_zero_right] using hn0, abs_lt.mp hn1⟩
  have hD (n : ℕ) (x : E) (hx : ‖x‖ < (n:ℝ)+1) (t : ℝ)
      (ht : t ∈ Ioo (-(n+1:ℝ)) (n+1:ℝ)) :
      HasDerivAt (fun s => α n (x,s)) (F (α n (x,t))) t := by
    have hx' : x ∈ closedBall (0:E) (n+1:ℝ) := by
      simpa only [mem_closedBall, dist_zero_right] using hx.le
    exact ((hα n).1 x hx').2 t (Ioo_subset_Icc_self ht) |>.hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)
  have hagree (n m : ℕ) (p : E × ℝ) (hp : p ∈ U n ∩ U m) : α n p = α m p := by
    have hx (j) (hj : p ∈ U j) : p.1 ∈ closedBall (0:E) (j+1:ℝ) :=
      ball_subset_closedBall hj.1
    exact box_flow_agree F hK (by positivity) (by positivity)
      ((hα n).1 p.1 (hx n hp.1)).1 ((hα m).1 p.1 (hx m hp.2)).1
      (hD n p.1 (by simpa only [mem_ball, dist_zero_right] using hp.1.1))
      (hD m p.1 (by simpa only [mem_ball, dist_zero_right] using hp.2.1))
      p.2 ⟨hp.1.2,hp.2.2⟩
  choose j hj using hcover
  let Φ : E × ℝ → E := fun p => α (j p) p
  have hΦ (n : ℕ) : EqOn Φ (α n) (U n) := fun p hp => hagree (j p) n p ⟨hj p,hp⟩
  have hΦc : Continuous Φ := by
    rw [continuous_iff_continuousAt]
    intro p
    let n := j p
    have hp : p ∈ U n := hj p
    have hn : ContinuousOn (α n) (U n) := (hα n).2.mono fun x hx =>
      ⟨ball_subset_closedBall hx.1, Ioo_subset_Icc_self hx.2⟩
    exact ((hn p hp).continuousAt ((hU n).mem_nhds hp)).congr
      (Filter.eventuallyEq_of_mem ((hU n).mem_nhds hp) (hΦ n).symm)
  refine ⟨⟨Φ,hΦc,?_,?_⟩⟩
  · intro x
    let n := j (x,0)
    have hn : (x,0) ∈ U n := hj (x,0)
    rw [hΦ n hn]
    exact ((hα n).1 x (ball_subset_closedBall hn.1)).1
  · intro x t
    let n := j (x,t)
    have hn : (x,t) ∈ U n := hj (x,t)
    have he : (fun t => Φ (x,t)) =ᶠ[𝓝 t] (fun t => α n (x,t)) :=
      (Filter.eventuallyEq_of_mem ((hU n).mem_nhds hn) (hΦ n)).comp_tendsto
        ((continuous_const.prodMk continuous_id).tendsto t)
    rw [hΦ n hn]
    exact (hD n x (by simpa only [mem_ball, dist_zero_right] using hn.1) t hn.2).congr_of_eventuallyEq he

end NearbyLagrangian.ODE

namespace NearbyLagrangian.ODE
open Set Filter Metric
open scoped Topology ContDiff NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace CompleteFlow
variable {F : E → E} (φ : CompleteFlow F)

theorem add {K : ℝ≥0} (hK : LipschitzWith K F) (x : E) (s t : ℝ) :
    φ.toFun (φ.toFun (x,s),t) = φ.toFun (x,s+t) := by
  have hd (t : ℝ) : HasDerivAt (fun t => φ.toFun (x,s+t))
      (F (φ.toFun (x,s+t))) t := by
    simpa only [Function.comp_def, one_smul] using
      (φ.derivative x (s+t)).scomp t ((hasDerivAt_id t).const_add s)
  have heq := ODE_solution_unique_univ (v := fun _ => F) (s := fun _ => univ)
    (fun _ => hK.lipschitzOnWith)
    (fun t => ⟨φ.derivative (φ.toFun (x,s)) t, mem_univ _⟩)
    (fun t => ⟨hd t, mem_univ _⟩)
    (show φ.toFun (φ.toFun (x,s),0) = φ.toFun (x,s+0) by rw [φ.initial, add_zero])
  exact congr_fun heq t

def homeomorph {K : ℝ≥0} (hK : LipschitzWith K F) (t : ℝ) : E ≃ₜ E where
  toFun x := φ.toFun (x,t)
  invFun x := φ.toFun (x,-t)
  left_inv x := by
    change φ.toFun (φ.toFun (x,t),-t) = x
    rw [φ.add hK, add_neg_cancel, φ.initial]
  right_inv x := by
    change φ.toFun (φ.toFun (x,-t),t) = x
    rw [φ.add hK, neg_add_cancel, φ.initial]
  continuous_toFun := φ.continuous_toFun.comp (continuous_id.prodMk continuous_const)
  continuous_invFun := φ.continuous_toFun.comp (continuous_id.prodMk continuous_const)

theorem fixed {K : ℝ≥0} (hK : LipschitzWith K F) {x : E} (hx : F x = 0) (t : ℝ) :
    φ.toFun (x,t) = x := by
  have heq := ODE_solution_unique_univ (v := fun _ => F) (s := fun _ => univ)
    (fun _ => hK.lipschitzOnWith)
    (fun t => ⟨φ.derivative x t, mem_univ _⟩)
    (fun t => ⟨show HasDerivAt (fun _ : ℝ => x) (F x) t by
       rw [hx]; exact hasDerivAt_const t x, mem_univ _⟩) (φ.initial x)
  exact congr_fun heq t

theorem displacement_support_subset {K : ℝ≥0} (hK : LipschitzWith K F) (t : ℝ) :
    Function.support (fun x => φ.toFun (x,t) - x) ⊆ Function.support F := by
  intro x hx
  contrapose! hx
  simp only [Function.mem_support, not_not] at hx ⊢
  rw [φ.fixed hK hx, sub_self]

theorem first_integral {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → G} (hf : Differentiable ℝ f) (hF : ∀ x, fderiv ℝ f x (F x) = 0)
    (x : E) (t : ℝ) : f (φ.toFun (x,t)) = f x := by
  have hd (s : ℝ) : HasDerivAt (fun s => f (φ.toFun (x,s))) 0 s := by
    simpa only [Function.comp_def, hF] using
      (hf (φ.toFun (x,s))).hasFDerivAt.comp_hasDerivAt s (φ.derivative x s)
  have hc := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t 0
  simpa only [φ.initial] using hc

end CompleteFlow

theorem compact_field_bounds {F : E → E} (hs : HasCompactSupport F)
    (hF : ContDiff ℝ 1 F) :
    ∃ L K : ℝ≥0, (∀ x, ‖F x‖ ≤ L) ∧ LipschitzWith K F := by
  obtain ⟨L,hL⟩ := hs.exists_bound_of_continuous hF.continuous
  obtain ⟨K,hK⟩ := (hs.fderiv ℝ).exists_bound_of_continuous
    (hF.continuous_fderiv one_ne_zero)
  let L' : ℝ≥0 := ⟨max L 0, le_max_right _ _⟩
  let K' : ℝ≥0 := ⟨max K 0, le_max_right _ _⟩
  refine ⟨L',K',fun x => (hL x).trans (le_max_left _ _), ?_⟩
  apply lipschitzWith_of_nnnorm_fderiv_le (hF.differentiable one_ne_zero)
  intro x
  exact_mod_cast (hK x).trans (le_max_left K 0)

variable [CompleteSpace E]

theorem exists_completeFlow_of_compact {F : E → E} (hs : HasCompactSupport F)
    (hF : ContDiff ℝ 1 F) : Nonempty (CompleteFlow F) := by
  obtain ⟨L,K,hL,hK⟩ := compact_field_bounds hs hF
  exact exists_completeFlow F hL hK

end NearbyLagrangian.ODE

end

end OAI
