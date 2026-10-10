import OAI.Analysis.KadisonKastler.TracialQuotientDiffuse
import OAI.Analysis.KadisonKastler.ConcreteTraceUniqueness

namespace OAI

/-! # The common represented factor for the two tracial sequence inputs -/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

universe u

variable {B : ℕ → Type u} [∀ j, CStarAlgebra (B j)] [∀ j, Nontrivial (B j)]

structure TracialSequenceFactor (τ : ∀ j, FaithfulTracialState (B j)) (ω : Ultrafilter ℕ) where
  H : Type u
  [normedAddCommGroup : NormedAddCommGroup H]
  [innerProductSpace : InnerProductSpace ℂ H]
  [completeSpace : CompleteSpace H]
  algebra : VonNeumannAlgebra H
  factor : Generator.IsII1Factor algebra.toStarSubalgebra
  quotient : VaryingBoundedSequence B →⋆ₐ[ℂ] Algebra algebra
  surjective : Function.Surjective quotient
  trace_limit : ∀ x : VaryingBoundedSequence B,
    Tendsto (fun j => (τ j).toLinearMap (x j)) (ω : Filter ℕ)
    (𝓝 ((concreteFactorTrace factor).toLinearMap (quotient x)))

attribute [instance] TracialSequenceFactor.normedAddCommGroup
  TracialSequenceFactor.innerProductSpace TracialSequenceFactor.completeSpace

attribute [local irreducible] tracialSequenceAlgebra

def constructedTracialSequenceFactor (τ : ∀ j, FaithfulTracialState (B j))
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (hcontrol : CoordinateVarianceControl τ)
    (hinfinite : ¬ FiniteDimensional ℂ (TracialSequenceQuotient τ ω)) :
    TracialSequenceFactor τ ω := by
  letI : PartialOrder (TracialSequenceQuotient τ ω) := CStarAlgebra.spectralOrder _
  letI : StarOrderedRing (TracialSequenceQuotient τ ω) := CStarAlgebra.spectralOrderedRing _
  let e := tracialSequenceEquiv τ ω hω
  let q := tracialSequenceQuotientMap τ ω
  have hQ := tracialSequenceAlgebra_isII1 τ ω hω hcontrol hinfinite
  refine {
    H := TraceStateHilbert (tracialQuotientTrace τ ω)
    algebra := tracialSequenceAlgebra τ ω
    factor := hQ
    quotient := e.toStarAlgHom.comp q
    surjective := e.surjective.comp (tracialSequenceQuotientMap_surjective τ ω)
    trace_limit := ?_ }
  intro x
  have he : (concreteFactorTrace hQ).toLinearMap (e (q x)) =
      (tracialQuotientTrace τ ω).toLinearMap (q x) := by
    calc
      _ = (representedTracialQuotientTrace τ ω hω).toLinearMap (e (q x)) :=
        (faithfulTracialState_eq_concreteFactorTrace hQ _ _).symm
      _ = _ := representedTracialQuotientTrace_equiv τ ω hω _
  change Tendsto _ _ (𝓝 ((concreteFactorTrace hQ).toLinearMap (e (q x))))
  rw [he]
  exact tracialQuotientTrace_limit τ ω x

end

end KadisonKastler

end OAI
