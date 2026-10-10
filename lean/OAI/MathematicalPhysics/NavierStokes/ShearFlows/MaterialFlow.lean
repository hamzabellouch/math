import OAI.MathematicalPhysics.NavierStokes.ShearFlows.Regularity
import OAI.MathematicalPhysics.NavierStokes.ShearFlows.ShearFlow

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff Topology

open Set MeasureTheory Metric
open scoped BigOperators ContDiff Topology NNReal
namespace ShearFlows

theorem smooth_periodic_lipschitz {L : ℝ} (hL : 0 < L) {V : Velocity}
    (hV : ContDiff ℝ ∞ V) (hs : SpatiallyPeriodic L V) (ht : TimePeriodic V) :
    ∃ K : ℝ≥0, LipschitzWith K V := by
  have hsp : SpatiallyPeriodic L (fderiv ℝ V) := by
    intro t x n
    have h (u : SpaceTime) : V (u + (0,latticeVector L n)) = V u := by
      simpa only [Prod.add_def, add_zero, zero_add, Prod.eta] using hs u.1 u.2 n
    simpa only [Prod.mk_add_mk, add_zero, zero_add] using
      fderiv_translation (hV.differentiable (by simp)) h (t,x)
  have htp : TimePeriodic (fderiv ℝ V) := by
    intro t x
    have h (u : SpaceTime) : V (u + (1,0)) = V u := by
      simpa only [Prod.add_def, add_zero, zero_add, Prod.eta] using ht u.1 u.2
    simpa only [Prod.mk_add_mk, add_zero, zero_add] using
      fderiv_translation (hV.differentiable (by simp)) h (t,x)
  obtain ⟨B,hB,hbound⟩ := periodic_uniform_bound hL (hV.continuous_fderiv (by simp)) hsp htp
  refine ⟨⟨B,hB⟩, lipschitzWith_of_nnnorm_fderiv_le (hV.differentiable (by simp)) ?_⟩
  intro x
  exact_mod_cast hbound x

theorem bounded_lipschitz_finite_solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {v : ℝ → E → E} {K B : ℝ≥0}
    (hv : ∀ t, LipschitzWith K (v t)) (hc : ∀ x, Continuous (fun t => v t x))
    (hb : ∀ t x, ‖v t x‖ ≤ B) {T : ℝ} (hT : 0 < T) (a : E) :
    ∃ γ : ℝ → E, γ 0 = a ∧ ∀ t ∈ Ioo (-T) T, HasDerivAt γ (v t (γ t)) t := by
  let T' : ℝ≥0 := ⟨T,hT.le⟩
  have hpic : IsPicardLindelof v (⟨0, by constructor <;> linarith⟩ : Icc (-T) T)
      a (B*T') 0 B K := {
    lipschitzOnWith := fun t _ => (hv t).lipschitzOnWith
    continuousOn := fun x _ => (hc x).continuousOn
    norm_le := fun t _ x _ => hb t x
    mul_max_le := by
      change (B : ℝ) * max (T - 0) (0 - -T) ≤ (B : ℝ) * T - 0
      simp }
  obtain ⟨γ,hγ,hode⟩ := hpic.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨γ,hγ,fun t ht => ?_⟩
  exact (hode t ⟨ht.1.le,ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

theorem bounded_lipschitz_global_solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {v : ℝ → E → E} {K B : ℝ≥0}
    (hv : ∀ t, LipschitzWith K (v t)) (hc : ∀ x, Continuous (fun t => v t x))
    (hb : ∀ t x, ‖v t x‖ ≤ B) (a : E) :
    ∃ γ : ℝ → E, γ 0 = a ∧ ∀ t, HasDerivAt γ (v t (γ t)) t := by
  let P := {T : ℝ // 0 < T}
  have hex (T : P) := bounded_lipschitz_finite_solution hv hc hb T.property a
  choose g hinit hode using hex
  have hcompat (S T : P) (t : ℝ) (hS : t ∈ Ioo (-S.val) S.val)
      (hT : t ∈ Ioo (-T.val) T.val) : g S t = g T t := by
    have hm : 0 < min S.val T.val := lt_min S.property T.property
    have hiS : Ioo (-min S.val T.val) (min S.val T.val) ⊆ Ioo (-S.val) S.val := by
      intro y hy
      exact ⟨(neg_le_neg (min_le_left _ _)).trans_lt hy.1,hy.2.trans_le (min_le_left _ _)⟩
    have hiT : Ioo (-min S.val T.val) (min S.val T.val) ⊆ Ioo (-T.val) T.val := by
      intro y hy
      exact ⟨(neg_le_neg (min_le_right _ _)).trans_lt hy.1,hy.2.trans_le (min_le_right _ _)⟩
    apply ODE_solution_unique_of_mem_Ioo (s := fun _ => univ)
      (fun y _ => (hv y).lipschitzOnWith)
      (show (0 : ℝ) ∈ Ioo (-min S.val T.val) (min S.val T.val) by constructor <;> linarith)
      (fun y hy => ⟨hode S y (hiS hy),mem_univ _⟩)
      (fun y hy => ⟨hode T y (hiT hy),mem_univ _⟩)
      ((hinit S).trans (hinit T).symm)
    exact ⟨by
      rcases le_total S.val T.val with h | h
      · rw [min_eq_left h]
        exact hS.1
      · rw [min_eq_right h]
        exact hT.1,lt_min hS.2 hT.2⟩
  let radius (t : ℝ) : P := ⟨|t|+1,by linarith [abs_nonneg t]⟩
  let γ : ℝ → E := fun t => g (radius t) t
  have hin (t : ℝ) : t ∈ Ioo (-(radius t).val) (radius t).val := by
    dsimp [radius]
    constructor <;> linarith [abs_le.mp (le_refl |t|), le_abs_self t, neg_abs_le t]
  have heqOn (T : P) : EqOn γ (g T) (Ioo (-T.val) T.val) := by
    intro t ht
    exact hcompat (radius t) T t (hin t) ht
  refine ⟨γ,hinit (radius 0),fun t => ?_⟩
  have he : γ =ᶠ[𝓝 t] g (radius t) :=
    Filter.eventually_of_mem (Ioo_mem_nhds (hin t).1 (hin t).2) (heqOn (radius t))
  have he0 : γ t = g (radius t) t := he.eq_of_nhds
  rw [he0]
  exact (hode (radius t) t (hin t)).congr_of_eventuallyEq he

theorem exists_materialFlow_of_bounded_lipschitz {L : ℝ} {V : Velocity} {K B : ℝ≥0}
    (hv : ∀ t, LipschitzWith K (fun x => V (t,x)))
    (hc : ∀ x, Continuous (fun t => V (t,x))) (hb : ∀ t x, ‖V (t,x)‖ ≤ B)
    (hp : SpatiallyPeriodic L V) :
    ∃ Φ : ℝ → Space → Space, IsMaterialFlow L V Φ := by
  have hex (a : Space) := bounded_lipschitz_global_solution hv hc hb a
  choose γ hinit hode using hex
  have hunique (a : Space) (f : ℝ → Space) (h0 : f 0 = a)
      (hf : ∀ t, HasDerivAt f (V (t,f t)) t) : f = γ a :=
    ODE_solution_unique_univ (s := fun _ => univ) (fun t => (hv t).lipschitzOnWith)
      (fun t => ⟨hf t,mem_univ _⟩) (fun t => ⟨hode a t,mem_univ _⟩) (h0.trans (hinit a).symm)
  refine ⟨fun t a => γ a t, ⟨hinit, fun t a => hode a t, ?_, ?_⟩⟩
  · intro t a n
    have he := hunique (a + latticeVector L n) (fun s => γ a s + latticeVector L n)
      (by rw [hinit]) (fun s => by
        rw [hp]
        exact (hode a s).add_const (latticeVector L n))
    exact (congrFun he t).symm
  · intro a f h0 hf t
    exact congrFun (hunique a f h0 hf) t

theorem smooth_periodic_materialFlow {L : ℝ} (hL : 0 < L) {V : Velocity}
    (hV : ContDiff ℝ ∞ V) (hs : SpatiallyPeriodic L V) (ht : TimePeriodic V) :
    ∃ Φ : ℝ → Space → Space, IsMaterialFlow L V Φ := by
  obtain ⟨K,hK⟩ := smooth_periodic_lipschitz hL hV hs ht
  obtain ⟨B,hB,hbound⟩ := periodic_uniform_bound hL hV.continuous hs ht
  have hl (t : ℝ) : LipschitzWith K (fun x => V (t,x)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa using hK.dist_le_mul (t,x) (t,y)
  exact exists_materialFlow_of_bounded_lipschitz (B := ⟨B,hB⟩) hl
    (fun x => hV.continuous.comp (continuous_id.prodMk continuous_const))
    (fun t x => hbound (t,x)) hs

theorem realizingVelocity_materialFlow {d : Input} (hd : ValidInput d) :
    ∃ Φ : ℝ → Space → Space, IsMaterialFlow d.period d.realizingVelocity Φ :=
  smooth_periodic_materialFlow (by exact_mod_cast hd.period_pos) (realizingVelocity_smooth hd)
    (realizingVelocity_spatially_periodic d) (realizingVelocity_time_periodic d)

end ShearFlows

end

end OAI
