import OAI.Geometry.CylinderCovering.Angular.GeneralDefinitions
import OAI.Geometry.RuledCovering.Model
import OAI.Geometry.CylinderCovering.Beams.sDefinitions

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace

namespace ShortenedBeam.ProjectionFactor

open RuledApproximation CylinderCovering

abbrev Plane := RuledApproximation.Plane

def direction (β : ℝ) (v : Plane) : Space := vec3 (β * v 0) (β * v 1) 1

def axis (β : ℝ) (v : Plane) : Space := ‖direction β v‖⁻¹ • direction β v

def horizontal (β : ℝ) (p : Plane) : Space := vec3 (β * p 0) (β * p 1) 0

def base (β : ℝ) (v : Plane) (S : Set Plane) : Set Space :=
  TriangularCovering.projection (axis β v) '' (horizontal β '' S)

def Statement : Prop :=
  ∀ (v : Plane) (S : Set Plane), IsCompact S →
    let β : ℝ := 1 / Real.sqrt 2
    ‖axis β v‖ = 1 ∧
    IsCompact (base β v S) ∧
    Measure.euclideanHausdorffMeasure 2 (base β v S) ≠ ⊤ ∧
    (∀ z ∈ base β v S, inner ℝ (axis β v) z = 0) ∧
    AngularGeneral.carrier (axis β v) (base β v S) =
      {z | ∃ p ∈ S, ∃ t : ℝ, z = horizontal β p + t • direction β v} ∧
    TriangularCovering.area (base β v S) / (β ^ 2 / Real.sqrt 2) =
      volume.real S * Real.sqrt 2 / Real.sqrt (1 + ‖v‖ ^ 2 / 2)

end ShortenedBeam.ProjectionFactor

end

end OAI
