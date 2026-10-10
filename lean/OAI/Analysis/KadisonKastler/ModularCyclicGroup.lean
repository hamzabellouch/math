import OAI.Analysis.KadisonKastler.ModularCyclicPhase
import OAI.Analysis.KadisonKastler.ModularStrongContinuity

namespace OAI

/-! # The scalar cyclic modular group

The phase multipliers form a strongly continuous unitary group. The
cyclic isometry intertwines this group with the constructed original
group, so its laws require no additional modular-theory input.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

abbrev ModularCyclicSpace (M : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) (Ω x : H) :=
  ResolventCyclicL2 (graphResolvent M J Ω 1) (graphResolvent_positive J Ω 1).isSelfAdjoint x

def modularCyclicPhaseOperator (M : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) (Ω x : H)
    (t : ℝ) : ModularCyclicSpace M J Ω x →L[ℂ] ModularCyclicSpace M J Ω x :=
  resolventScalarMultiplier _ _ x (fun s => modularSpectralPhase t s.val)
    ((modularSpectralPhase_measurable t).comp measurable_subtype_coe) 1
    (fun s => (modularSpectralPhase_norm t s.val).le)

variable [TopologicalSpace.SeparableSpace H]
variable (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω)) (x : H)

include hsep hcyc

theorem modularCyclicPhaseOperator_intertwines (t : ℝ) (v : ModularCyclicSpace M J Ω x) :
    resolventCyclicIsometry _ (graphResolvent_positive J Ω 1).isSelfAdjoint x
      (modularCyclicPhaseOperator M J Ω x t v) =
    modularStrongLimit J Ω hsep hcyc t
      (resolventCyclicIsometry _ (graphResolvent_positive J Ω 1).isSelfAdjoint x v) :=
  modularStrongLimit_cyclic J Ω hsep hcyc x t v

theorem modularCyclicPhaseOperator_norm (t : ℝ) (v : ModularCyclicSpace M J Ω x) :
    ‖modularCyclicPhaseOperator M J Ω x t v‖ = ‖v‖ := by
  rw [← (resolventCyclicIsometry _ (graphResolvent_positive J Ω 1).isSelfAdjoint x).norm_map,
    modularCyclicPhaseOperator_intertwines J Ω hsep hcyc x,
    modularStrongLimit_norm_map, LinearIsometry.norm_map]

theorem modularCyclicPhaseOperator_zero : modularCyclicPhaseOperator M J Ω x 0 = 1 := by
  apply ContinuousLinearMap.ext
  intro v
  apply (resolventCyclicIsometry _ (graphResolvent_positive J Ω 1).isSelfAdjoint x).injective
  rw [modularCyclicPhaseOperator_intertwines J Ω hsep hcyc x,
    modularStrongLimit_zero, one_apply_eq_self, one_apply_eq_self]

theorem modularCyclicPhaseOperator_add (s t : ℝ) :
    modularCyclicPhaseOperator M J Ω x (s + t) =
      modularCyclicPhaseOperator M J Ω x s * modularCyclicPhaseOperator M J Ω x t := by
  apply ContinuousLinearMap.ext
  intro v
  apply (resolventCyclicIsometry _ (graphResolvent_positive J Ω 1).isSelfAdjoint x).injective
  rw [mul_apply_eq_comp, modularCyclicPhaseOperator_intertwines J Ω hsep hcyc x,
    modularCyclicPhaseOperator_intertwines J Ω hsep hcyc x,
    modularCyclicPhaseOperator_intertwines J Ω hsep hcyc x,
    modularStrongLimit_add, mul_apply_eq_comp]

def modularCyclicUnitary (t : ℝ) : unitary
    (ModularCyclicSpace M J Ω x →L[ℂ] ModularCyclicSpace M J Ω x) :=
  Unitary.linearIsometryEquiv.symm
    { (modularCyclicPhaseOperator M J Ω x t).toLinearMap with
      invFun := modularCyclicPhaseOperator M J Ω x (-t)
      left_inv := fun v => by
        change (modularCyclicPhaseOperator M J Ω x (-t) * modularCyclicPhaseOperator M J Ω x t) v = v
        rw [← modularCyclicPhaseOperator_add J Ω hsep hcyc x, neg_add_cancel,
          modularCyclicPhaseOperator_zero J Ω hsep hcyc x, one_apply_eq_self]
      right_inv := fun v => by
        change (modularCyclicPhaseOperator M J Ω x t * modularCyclicPhaseOperator M J Ω x (-t)) v = v
        rw [← modularCyclicPhaseOperator_add J Ω hsep hcyc x, add_neg_cancel,
          modularCyclicPhaseOperator_zero J Ω hsep hcyc x, one_apply_eq_self]
      norm_map' := modularCyclicPhaseOperator_norm J Ω hsep hcyc x t }

def modularCyclicGroup : Multiplicative ℝ →* unitary
    (ModularCyclicSpace M J Ω x →L[ℂ] ModularCyclicSpace M J Ω x) where
  toFun t := modularCyclicUnitary J Ω hsep hcyc x t.toAdd
  map_one' := by
    apply Subtype.ext
    exact modularCyclicPhaseOperator_zero J Ω hsep hcyc x
  map_mul' s t := by
    apply Subtype.ext
    exact modularCyclicPhaseOperator_add J Ω hsep hcyc x s.toAdd t.toAdd

theorem modularCyclicGroup_continuous (v : ModularCyclicSpace M J Ω x) :
    Continuous (fun t : ℝ => (modularCyclicGroup J Ω hsep hcyc x
      (Multiplicative.ofAdd t) : ModularCyclicSpace M J Ω x →L[ℂ] ModularCyclicSpace M J Ω x) v) := by
  apply (resolventCyclicIsometry _ (graphResolvent_positive J Ω 1).isSelfAdjoint x).isometry.comp_continuous_iff.mp
  change Continuous (fun t => resolventCyclicIsometry _
    (graphResolvent_positive J Ω 1).isSelfAdjoint x (modularCyclicPhaseOperator M J Ω x t v))
  simp_rw [modularCyclicPhaseOperator_intertwines J Ω hsep hcyc x]
  exact modularStrongLimit_continuous J Ω hsep hcyc _

theorem modularCyclicGroup_apply_ae (t : ℝ) (v : ModularCyclicSpace M J Ω x) :
    (modularCyclicGroup J Ω hsep hcyc x (Multiplicative.ofAdd t) :
      ModularCyclicSpace M J Ω x →L[ℂ] ModularCyclicSpace M J Ω x) v =ᵐ[
        resolventVectorMeasure (graphResolvent M J Ω 1)
          (graphResolvent_positive J Ω 1).isSelfAdjoint x]
      fun s => modularSpectralPhase t s.val * v s := by
  exact resolventScalarMultiplier_apply_ae (graphResolvent M J Ω 1)
    (graphResolvent_positive J Ω 1).isSelfAdjoint x (fun s => modularSpectralPhase t s.val)
    ((modularSpectralPhase_measurable t).comp measurable_subtype_coe) 1
    (fun s => (modularSpectralPhase_norm t s.val).le) v

end

end KadisonKastler

end OAI
