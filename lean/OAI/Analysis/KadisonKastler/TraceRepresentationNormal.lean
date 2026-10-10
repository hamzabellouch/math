import OAI.Analysis.KadisonKastler.NormalRepresentationRange
import OAI.Analysis.KadisonKastler.ConcreteTraceHilbert
import OAI.Analysis.FactorGeneration.TraceTransport

namespace OAI

/-! # Bounded weak normality of the constructed trace representation -/

namespace KadisonKastler

open Generator.Tracial Filter
open scoped Topology

noncomputable section

universe u

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem boundedWeakNormal_of_ball_continuous (M : VonNeumannAlgebra H)
    (φ : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (hφ : ∀ (C : ℝ) (x y : K), Continuous (fun T : weakOperatorBall M C =>
      inner ℂ y (φ ⟨T.val.toCLM, T.property.1⟩ x))) : BoundedWeakNormal M φ := by
  classical
  intro ι l a b C ha hb x y
  let B := max C ‖b‖
  let c (i : ι) : Algebra M := if ‖a i‖ ≤ B then a i else b
  have hc (i : ι) : ‖c i‖ ≤ B := by
    by_cases h : ‖a i‖ ≤ B
    · have he : c i = a i := ite_eq_left h
      rw [he]
      exact h
    · have he : c i = b := ite_eq_right h
      rw [he]
      exact le_max_right _ _
  let d (i : ι) : weakOperatorBall M B :=
    ⟨ContinuousLinearMapWOT.ofCLM (c i).val, (c i).property, hc i⟩
  let d₀ : weakOperatorBall M B :=
    ⟨ContinuousLinearMapWOT.ofCLM b.val, b.property, le_max_right _ _⟩
  have hca : ∀ᶠ i in l, c i = a i := by
    filter_upwards [ha] with i hi
    exact ite_eq_left (hi.trans (le_max_left _ _))
  have hd : Tendsto d l (𝓝 d₀) := by
    apply tendsto_subtype_rng.mpr
    apply ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mpr
    intro v w
    exact (hb v w).congr' (hca.mono (fun i hi => by dsimp [d]; rw [hi]))
  have ht := ((hφ B x y).tendsto d₀).comp hd
  change Tendsto (fun i => inner ℂ y (φ (c i) x)) l
    (𝓝 (inner ℂ y (φ b x))) at ht
  exact ht.congr' (hca.mono (fun i hi => by rw [hi]))

theorem traceFreeHilbertAction_boundedWeakNormal {M : VonNeumannAlgebra H}
    (hM : Generator.IsII1Factor M.toStarSubalgebra) :
    BoundedWeakNormal M (traceFreeHilbertAction (traceHilbert_factor hM)
      hM.diffuse hM.finite (traceHilbert_nonzero hM)) := by
  apply boundedWeakNormal_of_ball_continuous
  exact traceFreeHilbertCoefficient_ball_continuous (traceHilbert_factor hM)
    hM.diffuse hM.finite (traceHilbert_nonzero hM)

theorem traceFreeHilbertEquiv_boundedWeakNormal {M : VonNeumannAlgebra H}
    (hM : Generator.IsII1Factor M.toStarSubalgebra) :
    BoundedWeakNormal M
      ((traceFreeHilbertClosure (traceHilbert_factor hM) hM.diffuse hM.finite
        (traceHilbert_nonzero hM)).toStarSubalgebra.subtype.comp
          (traceFreeHilbertEquiv (traceHilbert_factor hM) hM.diffuse hM.finite
            (traceHilbert_nonzero hM)).toStarAlgHom) :=
  traceFreeHilbertAction_boundedWeakNormal hM

end

end KadisonKastler

end OAI
