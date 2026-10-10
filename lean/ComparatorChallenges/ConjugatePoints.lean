import Mathlib

namespace OAI

noncomputable section
open Set Manifold Bundle
open scoped ContDiff

namespace ThreeManifold

abbrev E3 := Fin 3 → ℝ
abbrev I3 := 𝓘(ℝ, E3)

variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M]

def OrientedAtlas : Prop :=
  ∀ (c d : OpenPartialHomeomorph M E3), c ∈ atlas E3 M → d ∈ atlas E3 M →
    ∀ x ∈ c.target, c.symm x ∈ d.source →
      0 < LinearMap.det (fderiv ℝ (d ∘ c.symm) x).toLinearMap

variable [IsManifold I3 ∞ M]

abbrev SmoothMetric (M : Type) [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold I3 ∞ M] :=
  ContMDiffRiemannianMetric I3 ∞ E3 (fun x : M => TangentSpace I3 x)

def basisVector (i : Fin 3) : E3 := Pi.single i 1

def metricMatrix (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3) (x : E3) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => g.inner (c.symm x)
    (mfderiv I3 I3 c.symm x (basisVector i))
    (mfderiv I3 I3 c.symm x (basisVector j))

def coordPartial (f : E3 → ℝ) (x : E3) (i : Fin 3) : ℝ :=
  fderiv ℝ f x (basisVector i)

def christoffel (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3)
    (x : E3) (i j k : Fin 3) : ℝ :=
  (1 / 2 : ℝ) * ∑ l : Fin 3, (metricMatrix g c x)⁻¹ i l *
    (coordPartial (fun y => metricMatrix g c y l k) x j +
     coordPartial (fun y => metricMatrix g c y l j) x k -
     coordPartial (fun y => metricMatrix g c y j k) x l)

def connectionTerm (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3)
    (x u v : E3) : E3 :=
  fun i => ∑ j : Fin 3, ∑ k : Fin 3, christoffel g c x i j k * u j * v k

def curvatureCoefficient (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3)
    (x : E3) (l k i j : Fin 3) : ℝ :=
  coordPartial (fun y => christoffel g c y l j k) x i -
  coordPartial (fun y => christoffel g c y l i k) x j +
    ∑ a : Fin 3, (christoffel g c x l i a * christoffel g c x a j k -
      christoffel g c x l j a * christoffel g c x a i k)

def curvatureTerm (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3)
    (x u v w : E3) : E3 :=
  fun l => ∑ k : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3,
    curvatureCoefficient g c x l k i j * w k * u i * v j

def NonpositiveSectionalCurvature (g : SmoothMetric M) : Prop :=
  ∀ (c : OpenPartialHomeomorph M E3), c ∈ atlas E3 M →
    ∀ x ∈ c.target, ∀ u v : E3,
      (∑ i : Fin 3, ∑ j : Fin 3,
        metricMatrix g c x i j * curvatureTerm g c x u v v i * u j) ≤ 0

def alongDerivative (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3)
    (x w : ℝ → E3) (s : ℝ) : E3 :=
  deriv w s + connectionTerm g c (x s) (deriv x s) (w s)

def IsGeodesicOn (g : SmoothMetric M) (γ : ℝ → M) (U : Set ℝ) : Prop :=
  ContMDiffOn 𝓘(ℝ, ℝ) I3 ∞ γ U ∧
    ∀ (c : OpenPartialHomeomorph M E3), c ∈ atlas E3 M →
      ∀ s ∈ U, γ s ∈ c.source →
        alongDerivative g c (c ∘ γ) (deriv (c ∘ γ)) s = 0

def fieldCoordinates (γ : ℝ → M) (J : ∀ s, TangentSpace I3 (γ s))
    (c : OpenPartialHomeomorph M E3) (s : ℝ) : E3 :=
  mfderiv I3 I3 c (γ s) (J s)

def IsJacobiFieldOn (g : SmoothMetric M) (γ : ℝ → M)
    (J : ∀ s, TangentSpace I3 (γ s)) (U : Set ℝ) : Prop :=
  ∀ (c : OpenPartialHomeomorph M E3), c ∈ atlas E3 M →
    ContDiffOn ℝ ∞ (fieldCoordinates γ J c) (U ∩ γ ⁻¹' c.source) ∧
    ∀ s ∈ U, γ s ∈ c.source →
      alongDerivative g c (c ∘ γ)
        (alongDerivative g c (c ∘ γ) (fieldCoordinates γ J c)) s +
      curvatureTerm g c (c (γ s)) (fieldCoordinates γ J c s)
        (deriv (c ∘ γ) s) (deriv (c ∘ γ) s) = 0

def NoConjugatePoints (g : SmoothMetric M) : Prop :=
  ∀ (U : Set ℝ), IsOpen U → OrdConnected U →
    ∀ (γ : ℝ → M), IsGeodesicOn g γ U →
      ∀ (J : ∀ s, TangentSpace I3 (γ s)), IsJacobiFieldOn g γ J U →
        ∀ a ∈ U, ∀ b ∈ U, a ≠ b → J a = 0 → J b = 0 → ∀ s ∈ U, J s = 0

def MainStatement : Prop :=
  ∃ (M : Type) (top : TopologicalSpace M),
    letI := top
    ∃ (_ : T2Space M) (_ : SecondCountableTopology M) (_ : CompactSpace M)
      (_ : ConnectedSpace M) (charts : ChartedSpace E3 M),
      letI := charts
      ∃ (smooth : IsManifold I3 ∞ M),
        letI := smooth
        OrientedAtlas (M := M) ∧
          (∃ g : SmoothMetric M, NoConjugatePoints g) ∧
          ¬ ∃ g : SmoothMetric M, NonpositiveSectionalCurvature g

theorem main_theorem : MainStatement := by
  sorry

end ThreeManifold

end

end OAI
