import Mathlib

namespace OAI

noncomputable section

open scoped Manifold ContDiff BigOperators ENNReal
open Bundle

namespace EinsteinFour

abbrev FourSpace := EuclideanSpace ℝ (Fin 4)
abbrev I4 := 𝓘(ℝ, FourSpace)

def coordinateVector (i : Fin 4) : FourSpace := EuclideanSpace.single i 1

abbrev RoundSphere4 := {x : EuclideanSpace ℝ (Fin 5) // ‖x‖ = 1}

abbrev ComplexProjective2 := Projectivization ℂ (EuclideanSpace ℂ (Fin 3))

abbrev RealProjective4 := Projectivization ℝ (EuclideanSpace ℝ (Fin 5))

def roundDistance (p q : RoundSphere4) : ℝ :=
  Real.arccos (inner ℝ p.val q.val)

def fubiniStudyDistance (p q : ComplexProjective2) : ℝ :=
  Real.arccos (‖inner ℂ p.rep q.rep‖ / (‖p.rep‖ * ‖q.rep‖))

def realProjectiveDistance (p q : RealProjective4) : ℝ :=
  Real.arccos (‖inner ℝ p.rep q.rep‖ / (‖p.rep‖ * ‖q.rep‖))

section Metric

variable (M : Type*) [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

abbrev SmoothMetric :=
  ContMDiffRiemannianMetric I4 ∞ FourSpace (TangentSpace I4 : M → Type _)

variable {M}

def metricInChart (g : SmoothMetric M) (c : M) (z : FourSpace) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  let e := chartAt FourSpace c
  let d := mfderiv I4 I4 e.symm z
  fun i j => g.inner (e.symm z) (d (coordinateVector i)) (d (coordinateVector j))

def partialDeriv (f : FourSpace → ℝ) (i : Fin 4) (z : FourSpace) : ℝ :=
  fderiv ℝ f z (coordinateVector i)

def christoffel (g : SmoothMetric M) (c : M) (z : FourSpace)
    (k i j : Fin 4) : ℝ :=
  (1 / 2 : ℝ) * ∑ l : Fin 4, (metricInChart g c z)⁻¹ k l *
    (partialDeriv (fun w => metricInChart g c w j l) i z +
     partialDeriv (fun w => metricInChart g c w i l) j z -
     partialDeriv (fun w => metricInChart g c w i j) l z)

def curvatureComponent (g : SmoothMetric M) (c : M) (z : FourSpace)
    (l i j k : Fin 4) : ℝ :=
  partialDeriv (fun w => christoffel g c w l j k) i z -
  partialDeriv (fun w => christoffel g c w l i k) j z +
  ∑ p : Fin 4,
    (christoffel g c z l i p * christoffel g c z p j k -
     christoffel g c z l j p * christoffel g c z p i k)

def ricciInChart (g : SmoothMetric M) (c : M) (z : FourSpace)
    (i j : Fin 4) : ℝ :=
  ∑ k : Fin 4, curvatureComponent g c z k k i j

def sectionalNumerator (g : SmoothMetric M) (c : M) (z : FourSpace)
    (u v : FourSpace) : ℝ :=
  ∑ l : Fin 4, ∑ m : Fin 4, ∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4,
    metricInChart g c z l m * curvatureComponent g c z l i j k *
      u i * v j * v k * u m

def IsEinstein (g : SmoothMetric M) : Prop :=
  ∃ lam : ℝ, ∀ (c : M) (i j : Fin 4),
    ricciInChart g c (chartAt FourSpace c c) i j =
      lam * metricInChart g c (chartAt FourSpace c c) i j

def HasPositiveSectionalCurvature (g : SmoothMetric M) : Prop :=
  ∀ (c : M) (u v : FourSpace), LinearIndependent ℝ ![u, v] →
    0 < sectionalNumerator g c (chartAt FourSpace c c) u v

def scaledEDistance (g : SmoothMetric M) (a : ℝ) (x y : M) : ℝ≥0∞ :=
  letI : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  ENNReal.ofReal (Real.sqrt a) * Manifold.riemannianEDist I4 x y

def ScaledIsometricTo {N : Type*} (g : SmoothMetric M) (a : ℝ)
    (modelDistance : N → N → ℝ) : Prop :=
  ∃ f : M ≃ N, ∀ x y : M,
    ENNReal.ofReal (modelDistance (f x) (f y)) = scaledEDistance g a x y

end Metric

end EinsteinFour

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env fun _ => {}

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

abbrev Mat4 := Matrix (Fin 4) (Fin 4) ℝ

def chartMetric (g : SmoothMetric M) (c : M) : Mat4 :=
  metricInChart g c (chartAt FourSpace c c)

structure OrthonormalFrame (g : SmoothMetric M) (c : M) where
  matrix : Mat4
  orthonormal : matrixᵀ * chartMetric g c * matrix = 1

def OrthonormalFrame.map {g : SmoothMetric M} {c : M} (e : OrthonormalFrame g c) :
    FourSpace →ₗ[ℝ] FourSpace :=
  (WithLp.linearEquiv 2 ℝ (Fin 4 → ℝ)).symm.toLinearMap ∘ₗ
    (Matrix.mulVecLin e.matrix) ∘ₗ (WithLp.linearEquiv 2 ℝ (Fin 4 → ℝ)).toLinearMap

def OrthonormalFrame.vector {g : SmoothMetric M} {c : M}
    (e : OrthonormalFrame g c) (i : Fin 4) : FourSpace :=
  WithLp.toLp 2 (fun a => e.matrix a i)

structure FrameBundle (g : SmoothMetric M) where
  base : M
  frame : OrthonormalFrame g base

def frameRealization {g : SmoothMetric M} (e : FrameBundle g) :
    M × (Fin 4 → TangentBundle I4 M) :=
  (e.base, fun i => ⟨e.base, e.frame.vector i⟩)

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env fun _ => {}

instance (g : SmoothMetric M) : TopologicalSpace (FrameBundle g) :=
  TopologicalSpace.induced frameRealization inferInstance

/-- An orientation is a clopen choice of determinant sign in every frame fiber. -/
structure FrameOrientation (g : SmoothMetric M) where
  positive : Set (FrameBundle g)
  clopen : IsClopen positive
  nonempty_fiber : ∀ c, ∃ e : OrthonormalFrame g c, (⟨c, e⟩ : FrameBundle g) ∈ positive
  compatible : ∀ c (e f : OrthonormalFrame g c),
    (⟨c, e⟩ : FrameBundle g) ∈ positive →
      ((⟨c, f⟩ : FrameBundle g) ∈ positive ↔ 0 < e.matrix.det * f.matrix.det)

end PositiveEinsteinFour.Geometry

namespace PositiveEinsteinFour

open EinsteinFour

universe u

/-- A connected closed oriented smooth Riemannian four-manifold. -/
structure ClosedOrientedMetricFour where
  manifold : ModelWithCorners.MfldCat.{u} I4 ∞
  [regular : T3Space manifold]
  [secondCountable : SecondCountableTopology manifold]
  [compact : CompactSpace manifold]
  [connected : ConnectedSpace manifold]
  metric : SmoothMetric manifold
  orientation : Geometry.FrameOrientation metric

attribute [instance] ClosedOrientedMetricFour.regular
  ClosedOrientedMetricFour.secondCountable ClosedOrientedMetricFour.compact
  ClosedOrientedMetricFour.connected

section ClassificationDefinitions

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- Positive rescaling identifies the metric with one of the three standard models. -/
def Classified (g : SmoothMetric M) : Prop :=
  ∃ a : ℝ, 0 < a ∧
    (ScaledIsometricTo g a roundDistance ∨
      ScaledIsometricTo g a fubiniStudyDistance ∨
      ScaledIsometricTo g a realProjectiveDistance)

def ClassificationOn (M : Type*) [TopologicalSpace M] [ChartedSpace FourSpace M]
    [IsManifold I4 ∞ M] [T2Space M] [SecondCountableTopology M]
    [CompactSpace M] [ConnectedSpace M] : Prop :=
  ∀ g : SmoothMetric M,
    IsEinstein g → HasPositiveSectionalCurvature g → Classified g

end ClassificationDefinitions

/-- The oriented classification has the round sphere and Fubini--Study models. -/
theorem orientedClassification (X : ClosedOrientedMetricFour.{u})
    (hEinstein : IsEinstein X.metric) (hpositive : HasPositiveSectionalCurvature X.metric) :
    ∃ a : ℝ, 0 < a ∧ (ScaledIsometricTo X.metric a roundDistance ∨
      ScaledIsometricTo X.metric a fubiniStudyDistance) := by
  sorry

section

variable (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [SecondCountableTopology M]
  [CompactSpace M] [ConnectedSpace M]

theorem classificationOn : ClassificationOn M := by
  sorry

end

/-- The connected closed classification includes the real projective quotient. -/
theorem classification (M : Type*) [TopologicalSpace M] [ChartedSpace FourSpace M]
    [IsManifold I4 ∞ M] [T2Space M] [SecondCountableTopology M]
    [CompactSpace M] [ConnectedSpace M] (g : SmoothMetric M)
    (hEinstein : IsEinstein g) (hpositive : HasPositiveSectionalCurvature g) :
    ∃ a : ℝ, 0 < a ∧
      (ScaledIsometricTo g a roundDistance ∨
        ScaledIsometricTo g a fubiniStudyDistance ∨
        ScaledIsometricTo g a realProjectiveDistance) := by
  sorry

end PositiveEinsteinFour

end

end OAI
