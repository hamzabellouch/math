import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.FlowGlobalRegularity

namespace OAI

/-! Complete flows of bounded Lipschitz fields, obtained from the existing
Picard theorem on finite intervals and uniqueness on overlaps. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff NNReal
namespace ContinuumCoulomb

private theorem flow_interval_coherence {f : FlowPhase → FlowPhase} {K : ℝ≥0}
    (hLip : LipschitzWith K f) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (α β : ℝ → FlowPhase)
    (hα : ∀ t ∈ Icc (-a) a, HasDerivWithinAt α (f (α t)) (Icc (-a) a) t)
    (hβ : ∀ t ∈ Icc (-b) b, HasDerivWithinAt β (f (β t)) (Icc (-b) b) t)
    (h0 : α 0 = β 0) {t : ℝ} (ht : |t| < min a b) : α t = β t := by
  have hm : 0 < min a b := lt_min ha hb
  have heq : EqOn α β (Ioo (-(min a b)) (min a b)) := by
    apply ODE_solution_unique_of_mem_Ioo (s := fun _ => univ)
      (fun _ _ => hLip.lipschitzOnWith)
      (show (0:ℝ) ∈ Ioo (-(min a b)) (min a b) from ⟨neg_neg_of_pos hm,hm⟩)
    · intro u hu
      have hu' : u ∈ Ioo (-a) a :=
        ⟨lt_of_le_of_lt (neg_le_neg (min_le_left a b)) hu.1,
          hu.2.trans_le (min_le_left a b)⟩
      exact ⟨(hα u (Ioo_subset_Icc_self hu')).hasDerivAt
        (Icc_mem_nhds hu'.1 hu'.2),mem_univ _⟩
    · intro u hu
      have hu' : u ∈ Ioo (-b) b :=
        ⟨lt_of_le_of_lt (neg_le_neg (min_le_right a b)) hu.1,
          hu.2.trans_le (min_le_right a b)⟩
      exact ⟨(hβ u (Ioo_subset_Icc_self hu')).hasDerivAt
        (Icc_mem_nhds hu'.1 hu'.2),mem_univ _⟩
    · exact h0
  exact heq (abs_lt.mp ht)

theorem flow_bounded_global_exists {f : FlowPhase → FlowPhase} {K B : ℝ≥0}
    (hLip : LipschitzWith K f) (hB : ∀ x, ‖f x‖ ≤ B) :
    ∃ G : FlowPhase → ℝ → FlowPhase,
      (∀ x, G x 0 = x) ∧ ∀ x t, HasDerivAt (G x) (f (G x t)) t := by
  let Radius := {r : ℝ // 0 < r}
  have hex (x : FlowPhase) (r : Radius) :
      ∃ α : ℝ → FlowPhase, α 0 = x ∧
        ∀ t ∈ Icc (-r.val) r.val,
          HasDerivWithinAt α (f (α t)) (Icc (-r.val) r.val) t := by
    let t₀ : Icc (-r.val) r.val := ⟨0,by constructor <;> linarith [r.property]⟩
    have hp : IsPicardLindelof (fun _ : ℝ => f) t₀ x
        (⟨B*r.val,mul_nonneg B.coe_nonneg r.property.le⟩ : ℝ≥0) 0 B K := {
      lipschitzOnWith := fun _ _ => hLip.lipschitzOnWith
      continuousOn := fun _ _ => continuousOn_const
      norm_le := fun _ _ y _ => hB y
      mul_max_le := by
        change (B:ℝ) * max (r.val-0) (0-(-r.val)) ≤ (B:ℝ)*r.val-0
        simp only [sub_zero,zero_sub,neg_neg,max_self,le_refl] }
    exact hp.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  choose α hα0 hα using hex
  let radius : ℝ → Radius := fun t => ⟨|t|+1,by positivity⟩
  let G : FlowPhase → ℝ → FlowPhase := fun x t => α x (radius t) t
  refine ⟨G,fun x => hα0 x (radius 0),?_⟩
  intro x t
  let r := radius t
  have ht : |t| < r.val := by dsimp [r,radius]; linarith
  have heq : G x =ᶠ[𝓝 t] α x r := by
    filter_upwards [continuous_abs.continuousAt.eventually (Iio_mem_nhds ht)] with u hu
    exact flow_interval_coherence hLip (radius u).property r.property
      (α x (radius u)) (α x r) (hα x (radius u)) (hα x r)
      ((hα0 x (radius u)).trans (hα0 x r).symm)
      (lt_min (by dsimp [radius]; linarith) hu)
  have ht' := abs_lt.mp ht
  have hd := (hα x r t (Ioo_subset_Icc_self ht')).hasDerivAt
    (Icc_mem_nhds ht'.1 ht'.2)
  rw [←heq.self_of_nhds] at hd
  exact hd.congr_of_eventuallyEq heq

end ContinuumCoulomb

end

end OAI
