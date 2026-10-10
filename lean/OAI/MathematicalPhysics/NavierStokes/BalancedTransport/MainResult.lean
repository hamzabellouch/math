import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.UniversalMachine
import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.Realization
import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.ElementaryTemplate
import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.EffectiveConstruction

namespace OAI

noncomputable section
namespace BalancedTransport
open BalancedTransport.Geometry

theorem balanced_three_stack_realization :
    ∃ U f₀ f₁ : Family Velocity,
    ∃ X : Family MaterialFlow,
    ∃ repeated : FiniteMachine → Velocity,
      EffectiveFamily U ∧ EffectiveFamily f₀ ∧ EffectiveFamily f₁ ∧
      (∀ M, Function.Periodic (repeated M) 1) ∧
      ∀ (M : FiniteMachine) (w : Input M),
        Smooth (U M w) ∧ Smooth (f₀ M w) ∧ Smooth (f₁ M w) ∧
        f₀ M w = inertialCoefficient (U M w) ∧
        f₁ M w = viscousCoefficient (U M w) ∧
        CommonCompactSupport (U M w) (f₀ M w) (f₁ M w) ∧
        BoundedMixed (U M w) ∧
        PeriodicAfterOne (U M w) ∧
        (∀ t, 1 ≤ t → ∀ x, U M w t x = repeated M t x) ∧
        ComparisonClass (U M w) (fun _ _ => 0) ∧
        IsMaterialFlow (U M w) (X M w) ∧
        ((∃ t : ℝ, 0 ≤ t ∧ X M w t fixedLabel ∈ observer) ↔ Halts M w) ∧
        ∀ ν : ℝ, 0 < ν →
          let f := affineForce (f₀ M w) (f₁ M w) ν
          ZeroDataSolution ν f (U M w) (fun _ _ => 0) ∧
          Smooth f ∧ BoundedMixed f ∧ PeriodicAfterOne f ∧
          UniqueInComparison ν f (U M w) ∧
          (ComputableReal ν → EffectiveFieldIn ∅ f) ∧
          (∀ name : ℕ → ℚ, RealName name ν → EffectiveFieldIn {nameOracle name} f) := by
  obtain ⟨N, δ, hδ, hh⟩ := Universal.exists_universal_machine
  obtain ⟨v, K, hK, hv, hc, hs, hd, hg, he⟩ :=
    Effectivity.exists_elementary_guarded_template N.normalized 3
  let κ : ℕ → Fin 3 → ℚ := fun n =>
    Recorder.Checkpoint.rationalInitial N.normalized (some N.initial) (δ n)
  have hκ : Computable κ := (Effectivity.computable_rationalInitial N).comp hδ
  obtain ⟨C, hC⟩ := Effectivity.rationalInitial_bounded N
  let z : Family Space := fun M w => rationalSpace (κ (inputCode M w))
  let U : Family Velocity := fun M w => loadedRepeat (loadingVelocity (z M w) 1) v
  have hz (M : FiniteMachine) (w : Input M) : z M w =
      ((N.initialWork (δ (inputCode M w))).expand N.normalized).code N.normalized :=
    Recorder.Checkpoint.rationalInitial_cast N.normalized (some N.initial) (δ (inputCode M w))
  have hu (M : FiniteMachine) (w : Input M) :=
    loaded_template_realization (z M w) (by norm_num : (0 : ℝ) < 1) hK hv hc hs hd
  have hlc (M : FiniteMachine) (w : Input M) : TimeCollars (loadingVelocity (z M w) 1) :=
    fun _ ht => loadingVelocity_zero ht
  have hr (M : FiniteMachine) (w : Input M) :=
    prescribed_residual_realization ((loadingSupport_compact (z M w) 1).union hK)
      (hu M w).1 (hu M w).2.1 (loadedRepeat_repeats (hlc M w)) (hu M w).2.2.2.1
      (fun t (_ : 0 ≤ t) x => loadedRepeat_divergence
        (loadingVelocity_jointSmooth (z M w) 1) hv hc
        (loadingVelocity_divergence (z M w) 1) hd t x)
  have ef : EffectiveFamily U ∧
      EffectiveFamily (fun M w => inertialCoefficient (U M w)) ∧
      EffectiveFamily (fun M w => viscousCoefficient (U M w)) :=
    Effectivity.effective_loaded_family hκ C (fun n => hC (δ n)) hK hv hc hs he
  choose X hX using (fun M w => (hu M w).2.2.2.2.2.2.1)
  refine ⟨U, (fun M w => inertialCoefficient (U M w)),
    (fun M w => viscousCoefficient (U M w)), X, (fun _ => repeatTemplate v),
    ef.1, ef.2.1, ef.2.2, (fun _ => repeatTemplate_zero_period v), ?_⟩
  intro M w
  obtain ⟨hsm, hsm₀, hsm₁, hsupp, hb, _, _, hp, hclass, _, hres⟩ := hr M w
  refine ⟨hsm, hsm₀, hsm₁, rfl, rfl, hsupp, hb, hp, ?_, hclass, hX M w, ?_, ?_⟩
  · intro t ht x
    exact congrFun ((hu M w).2.2.2.2.2.1 t ht) x
  · have hx : IsMaterialFlow
        (loadedRepeat (loadingVelocity
          (((N.initialWork (δ (inputCode M w))).expand N.normalized).code N.normalized) 1) v)
        (X M w) := by
      rw [← hz M w]
      exact hX M w
    exact (N.compiled_continuous_halting_iff (δ (inputCode M w))
      (by norm_num : (0 : ℝ) < 1) hK hv hc hs hg hx).trans (hh M w)
  · intro ν hν
    obtain ⟨hsol, hsf, hbf, hpf, huniq⟩ := hres ν hν
    have heff := Effectivity.residual_effective_viscosity (fun M w => (hu M w).1)
      ef.2.1 ef.2.2 M w ν
    exact ⟨hsol, hsf, hbf, hpf, huniq, heff.1, heff.2⟩

end BalancedTransport
end

end OAI
