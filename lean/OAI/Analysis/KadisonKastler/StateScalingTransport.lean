import OAI.Analysis.KadisonKastler.StateScalingFiniteSum
import OAI.Analysis.FactorGeneration.ProjectionComparison

namespace OAI

/-! # Moving a state-scaling partial isometry by centralizer equivalences -/

namespace KadisonKastler

open Generator Generator.Tracial UltrapowerBridge

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

theorem exists_state_scaling_transport
    (hunit : ‖Ω‖=1) (hsep : Function.Injective (algebraVectorMap M Ω))
    (hf : ScalarCenter (stateCentralizerVonNeumann (M := M) Ω))
    {r : ℝ} (hr : r ≠ 0) (v : PartialIsometry M)
    (hv : StateScales M Ω r v.val.val)
    (p q : AlgebraProjection (stateCentralizerVonNeumann (M := M) Ω))
    (hp : (stateCentralizerTrace Ω hunit hsep).trace p.val =
      (stateCentralizerTrace Ω hunit hsep).trace (scalingSupport v hv hr).val)
    (hq : (stateCentralizerTrace Ω hunit hsep).trace q.val =
      (stateCentralizerTrace Ω hunit hsep).trace (scalingTarget v hv hr).val) :
    ∃ z : PartialIsometry M,
      z.support=includeCentralizerProjection p ∧
      z.target=includeCentralizerProjection q ∧ StateScales M Ω r z.val.val := by
  let N := stateCentralizerVonNeumann (M := M) Ω
  let τ := stateCentralizerTrace Ω hunit hsep
  have hf' : ∀ c : Algebra N, (∀ a : Algebra N, a*c=c*a) →
      ∃ z : ℂ, c=z • (1 : Algebra N) := by
    intro c hc
    obtain ⟨z,hz⟩ := hf c.val c.property
      (fun a ha => congrArg Subtype.val (hc ⟨a,ha⟩))
    exact ⟨z,Subtype.ext hz⟩
  obtain ⟨a,ha,haq⟩ := exists_partialIsometry_of_trace_eq τ hf'
    (scalingTarget v hv hr) q hq.symm
  let A : PartialIsometry N := ⟨scalingTarget v hv hr,a,ha⟩
  have hAT : A.target=q := Subtype.ext haq
  obtain ⟨b,hb,hbs⟩ := exists_partialIsometry_of_trace_eq τ hf'
    p (scalingSupport v hv hr) hp
  let B : PartialIsometry N := ⟨p,b,hb⟩
  have hBT : B.target=scalingSupport v hv hr := Subtype.ext hbs
  let A₁ := includeCentralizerPartialIsometry A
  let B₁ := includeCentralizerPartialIsometry B
  have hB : B₁.target=v.support := by
    rw [includeCentralizerPartialIsometry_target,hBT]
    rfl
  let w := v.compose B₁ (le_of_eq hB)
  have hw : w.target=v.target := partialIsometry_compose_target_of_eq v B₁ hB
  have hA : w.target=A₁.support := by rw [hw]; rfl
  let z := A₁.compose w (le_of_eq hA)
  refine ⟨z,rfl,?_,?_⟩
  · rw [partialIsometry_compose_target_of_eq A₁ w hA,
      includeCentralizerPartialIsometry_target,hAT]
  · have hwscale := stateScales_compose v B₁ hv
      (includeCentralizerPartialIsometry_scales B) (le_of_eq hB)
    have hzscale := stateScales_compose A₁ w
      (includeCentralizerPartialIsometry_scales A) hwscale (le_of_eq hA)
    simpa only [mul_one,one_mul] using hzscale

end

end KadisonKastler

end OAI
