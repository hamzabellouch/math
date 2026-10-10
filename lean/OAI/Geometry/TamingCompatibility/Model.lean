import Mathlib

namespace OAI

noncomputable section
open scoped Manifold ContDiff

namespace TamingCompatibility

abbrev Space := EuclideanSpace ℝ (Fin 4)
abbrev Model := 𝓘(ℝ, Space)

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X]

abbrev TwoForm (X : Type*) [TopologicalSpace X] [ChartedSpace Space X] :=
  (x : X) → (TangentSpace Model x) [⋀^Fin 2]→L[ℝ] ℝ

structure AlmostComplexStructure (X : Type*) [TopologicalSpace X]
    [ChartedSpace Space X] [IsManifold Model ∞ X] where
  endomorphism : (x : X) → TangentSpace Model x →L[ℝ] TangentSpace Model x
  square : ∀ x v, endomorphism x (endomorphism x v) = -v
  smooth : ContMDiff Model.tangent Model.tangent ∞
    (fun p : TangentBundle Model X =>
      (⟨p.proj, endomorphism p.proj p.2⟩ : TangentBundle Model X))

def eval (α : TwoForm X) (x : X) (u v : TangentSpace Model x) : ℝ :=
  α x ![u, v]

noncomputable def pullback (α : TwoForm X) (f : Space → X) :
    Space → Space [⋀^Fin 2]→L[ℝ] ℝ :=
  fun y => (α (f y)).compContinuousLinearMap (mfderiv Model Model f y)

def IsSmooth (α : TwoForm X) : Prop :=
  ∀ (f : Space → X) (U : Set Space), IsOpen U →
    ContMDiffOn Model Model ∞ f U → ContDiffOn ℝ ∞ (pullback α f) U

def IsClosed (α : TwoForm X) : Prop :=
  ∀ (f : Space → X) (U : Set Space), IsOpen U →
    ContMDiffOn Model Model ∞ f U → ∀ y ∈ U,
      extDerivWithin (pullback α f) U y = 0

def IsNondegenerate (α : TwoForm X) : Prop :=
  ∀ x v, (∀ w, eval α x v w = 0) → v = 0

def IsSymplectic (α : TwoForm X) : Prop :=
  IsSmooth α ∧ IsClosed α ∧ IsNondegenerate α

def Tames (α : TwoForm X) (J : AlmostComplexStructure X) : Prop :=
  ∀ x v, v ≠ 0 → 0 < eval α x v (J.endomorphism x v)

def IsInvariant (α : TwoForm X) (J : AlmostComplexStructure X) : Prop :=
  ∀ x u v, eval α x (J.endomorphism x u) (J.endomorphism x v) = eval α x u v

def Compatible (α : TwoForm X) (J : AlmostComplexStructure X) : Prop :=
  Tames α J ∧ IsInvariant α J

end TamingCompatibility
end

end OAI
