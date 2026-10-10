import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.ComputableInitial

namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry Set Filter
open scoped Topology

lemma EffectiveFamily.forwardEq {V W : Family Velocity} (hV : EffectiveFamily V)
    (h : ∀M w, ForwardEq (V M w) (W M w)) : EffectiveFamily W := by
  obtain ⟨E,b,R,hE,hb,hR,he,hB,hs⟩ := hV
  refine ⟨E,b,R,hE,hb,hR,?_,?_,?_⟩
  · intro M w a z n hz i
    rw [← (h M w).mixedD a _ (by exact_mod_cast hz)]
    exact he M w a z n hz i
  · intro M w a t ht x
    rw [← (h M w).mixedD a t ht]
    exact hB M w a t ht x
  · intro M w t ht x hx
    rw [← h M w t ht]
    exact hs M w t ht x hx

lemma ElementaryPieces.fullInertial {d : ℕ} {L V : (Fin d → ℝ) → Velocity}
    {κ : ℕ → Fin d → ℚ} {F : Family Velocity} (h : ElementaryPieces L V κ F) :
    ElementaryPieces (fun p => fullInertial (L p)) (fun p => fullInertial (V p)) κ
      (fun M w => fullInertial (F M w)) := by
  intro M w t ht
  have hh := h M w t ht
  split_ifs at hh ⊢ with hlt
  · exact timeGerm_fullInertial hh
  · simpa only [fullInertial_translate] using timeGerm_fullInertial hh

lemma ElementaryPieces.viscous {d : ℕ} {L V : (Fin d → ℝ) → Velocity}
    {κ : ℕ → Fin d → ℚ} {F : Family Velocity} (h : ElementaryPieces L V κ F) :
    ElementaryPieces (fun p => viscousCoefficient (L p)) (fun p => viscousCoefficient (V p)) κ
      (fun M w => viscousCoefficient (F M w)) := by
  intro M w t ht
  have hh := h M w t ht
  split_ifs at hh ⊢ with hlt
  · exact timeGerm_viscous hh
  · simpa only [viscous_translate] using timeGerm_viscous hh

theorem effective_loaded_family {κ : ℕ → Fin 3 → ℚ} (hκ : Computable κ)
    (C : ℕ) (hC : ∀n i, |(κ n i : ℝ)| ≤ C)
    {v : Velocity} {K : Set Space} (hK : IsCompact K)
    (hv : JointSmooth v) (hc : TimeCollars v) (hs : SpatiallySupported K v)
    (he : ElementaryField (fun _ : Fin 3 → ℝ => v)) :
    let U : Family Velocity := fun M w =>
      loadedRepeat (loadingVelocity (rationalSpace (κ (inputCode M w))) 1) v
    EffectiveFamily U ∧ EffectiveFamily (fun M w => inertialCoefficient (U M w)) ∧
      EffectiveFamily (fun M w => viscousCoefficient (U M w)) := by
  dsimp only
  let U : Family Velocity := fun M w =>
    loadedRepeat (loadingVelocity (rationalSpace (κ (inputCode M w))) 1) v
  have hU (M : FiniteMachine) (w : Input M) : JointSmooth (U M w) :=
    loadedRepeat_jointSmooth (loadingVelocity_jointSmooth _ _) hv hc
  have hp : ElementaryPieces (fun p : Fin 3 → ℝ => loadingVelocity p 1)
      (fun _ : Fin 3 → ℝ => v) κ U := by
    intro M w t ht
    split_ifs with hlt
    · exact loadedRepeat_germ_before hc hlt
    · exact loadedRepeat_germ_after (fun _ ht => loadingVelocity_zero ht) hc (le_of_not_gt hlt)
  obtain ⟨r,hr⟩ := hK.isBounded.subset_closedBall (0 : Space)
  obtain ⟨n,hn⟩ := exists_nat_ge r
  let R : ℕ := max n (C+6)
  have hS (M : FiniteMachine) (w : Input M) :
      SpatiallySupported (Metric.closedBall (0 : Space) R) (U M w) := by
    intro t x hx
    apply loadedRepeat_support (loadingVelocity_supported _ (by norm_num : (0 : ℝ) < 1)) hs t x
    intro hm
    apply hx
    rcases hm with hm | hm
    · exact Metric.closedBall_subset_closedBall (by exact_mod_cast (Nat.le_max_right n (C+6)))
        (loadingSupport_ball (hC (inputCode M w)) hm)
    · exact Metric.closedBall_subset_closedBall
        (hn.trans (by exact_mod_cast (Nat.le_max_left n (C+6)))) (hr hm)
  have el : ElementaryField (fun p : Fin 3 → ℝ => loadingVelocity p 1) :=
    elementary_loadingVelocity ⟨1, by simp⟩
  have sl := fun p : Fin 3 → ℝ => loadingVelocity_jointSmooth p 1
  have eu := effectiveFamily_of_elementary_pieces el he sl (fun _ => hv) hκ C R hC hU hS hp
  have e₀ := effectiveFamily_of_elementary_pieces el.fullInertial he.fullInertial
    (fun p => (sl p).fullInertial) (fun _ => hv.fullInertial) hκ C R hC
    (fun M w => (hU M w).fullInertial) (fun M w => (hS M w).fullInertial) hp.fullInertial
  have e₁ := effectiveFamily_of_elementary_pieces el.viscous he.viscous
    (fun p => (sl p).viscousCoefficient) (fun _ => hv.viscousCoefficient) hκ C R hC
    (fun M w => (hU M w).viscousCoefficient)
    (fun M w => (hS M w).viscousCoefficient Metric.isClosed_closedBall) hp.viscous
  exact ⟨eu,EffectiveFamily.forwardEq e₀ (fun M w => fullInertial_forwardEq (hU M w)),e₁⟩

end BalancedTransport.Effectivity
end

end OAI
