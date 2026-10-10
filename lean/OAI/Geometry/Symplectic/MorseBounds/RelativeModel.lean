import OAI.Geometry.Symplectic.MorseBounds.ManifoldModel

namespace OAI

noncomputable section
open Set
open scoped Manifold ContDiff

namespace ArnoldCounterexample.Nondegenerate.MainProducer
noncomputable section

abbrev A5Power (k : ℕ) := Fin k → alternatingGroup (Fin 5)

def SymplecticBaseGoal : Prop :=
  ∀ k : ℕ, 0 < k →
    ∃ (X : ClosedManifold 4) (_omega : SymplecticForm X) (x : X),
      Nonempty (FundamentalGroup X x ≃* A5Power k)

abbrev Vertical := Fin 8 → ℝ
abbrev relativeModel := (model 4).prod 𝓘(ℝ, Vertical)

def radiusSq (w : Vertical) : ℝ := ∑ i, w i ^ 2

def Q (w : Vertical) : ℝ :=
  ∑ i : Fin 8, (if i.val < 4 then (-1 : ℝ) else 1) * w i ^ 2 / 2

def relativeCritical {X : ClosedManifold 4} (F : X × Vertical → ℝ) : Set (X × Vertical) :=
  {p | mfderiv relativeModel 𝓘(ℝ) F p = 0}

def RequiredRelativeInput {X : ClosedManifold 4} (F : X × Vertical → ℝ) : Prop :=
  ContMDiff relativeModel 𝓘(ℝ) ∞ F ∧
  (∀ p, 9 ≤ radiusSq p.2 → F p = Q p.2) ∧
  (∀ p ∈ relativeCritical F,
    Function.Injective
      (fderiv ℝ (fderiv ℝ (F ∘ (extChartAt relativeModel p).symm))
        ((extChartAt relativeModel p) p))) ∧
  (relativeCritical F).Finite ∧
  ((relativeCritical F).ncard : ℤ) = eulerChar X + 244

def MissingMainProducer : Prop :=
  ∀ k : ℕ, 0 < k →
    ∃ (X : ClosedManifold 4) (_omega : SymplecticForm X) (x : X)
      (F : X × Vertical → ℝ),
      Nonempty (FundamentalGroup X x ≃* A5Power k) ∧ RequiredRelativeInput F

example (k : ℕ) : Group.IsFinitelyPresented (A5Power k) := inferInstance

end
end ArnoldCounterexample.Nondegenerate.MainProducer

end

end OAI
