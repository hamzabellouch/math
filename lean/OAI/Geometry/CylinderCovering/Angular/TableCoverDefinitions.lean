import OAI.Geometry.CylinderCovering.Angular.TableDefinitions
import OAI.Geometry.CylinderCovering.Angular.TableGeometryDefinitions
import OAI.Geometry.CylinderCovering.Angular.OrdinaryCapsDefinitions
import OAI.Geometry.CylinderCovering.Convexity.SquaredCapDataDefinitions
import OAI.Geometry.CylinderCovering.Cartesian.CoverDefinitions

namespace OAI

noncomputable section
open Set
namespace CylinderCovering.AngularTableCover

open AngularTable

def node (m j : ℕ) : ℝ := -1 + 2 * (j : ℝ) / (m : ℝ)

inductive Cap where
  | midpoint | maximum | radial | squared | cartesian (b : ℝ)

def data (cap : Cap) (p : Parameters) : AngularGeneral.Data :=
  let D := AngularOrdinaryCaps.ordinaryData .radial p.sectors (node p.sectors) p.tilt p.margin
  match cap with
  | .midpoint => AngularOrdinaryCaps.ordinaryData .midpoint p.sectors (node p.sectors) p.tilt p.margin
  | .maximum => AngularOrdinaryCaps.ordinaryData .maximum p.sectors (node p.sectors) p.tilt p.margin
  | .radial => D
  | .squared => AngularCaps.withSquaredCaps p.tilt p.margin D
  | .cartesian _ => CartesianCaps.cartesianData p.sectors (node p.sectors) p.tilt p.margin

def normalizedCost (cap : Cap) (p : Parameters) : ℝ :=
  AngularTableGeometry.totalArea (p.edge/2) p.tilt (data cap p) /
    minimumShadowArea (AngularTableGeometry.body (p.edge/2))

def lowerFamilyArea (cap : Cap) (p : Parameters) : ℝ :=
  ∑ j : Fin p.sectors, TriangularCovering.area
    (AngularTableGeometry.lowerBase (p.edge/2) p.tilt (data cap p) j)

def upperFamilyArea (cap : Cap) (p : Parameters) : ℝ :=
  ∑ j : Fin p.sectors, TriangularCovering.area
    (AngularTableGeometry.upperBase (p.edge/2) p.tilt (data cap p) j)

def Shape (cap : Cap) (p : Parameters) : Prop :=
  (cap = .midpoint ∨ cap = .maximum) → ∀ j < p.sectors,
    AngularGeneral.IsNondegenerateTriangle
      (AngularTableGeometry.lowerBase (p.edge/2) p.tilt (data cap p) j) ∧
    AngularGeneral.IsNondegenerateTriangle
      (AngularTableGeometry.upperBase (p.edge/2) p.tilt (data cap p) j)

def ApertureLaw (cap : Cap) (p : Parameters) : Prop :=
  ∀ b, cap = .cartesian b → ∀ j < p.sectors,
    AngularGeneral.lowerIntercept (data cap p) j =
      {z | ∃ q ∈ Icc (node p.sectors j) (node p.sectors (j+1)),
        ∃ s ∈ CartesianCaps.aperture p.tilt p.margin b q,
          z = TriangularCovering.point 0 (q*s) s} ∧
    AngularGeneral.upperIntercept (data cap p) j =
      {z | ∃ q ∈ Icc (node p.sectors j) (node p.sectors (j+1)),
        ∃ s ∈ CartesianCaps.aperture p.tilt p.margin b q,
          z = TriangularCovering.point (q*s) 0 (1-s)}

def RowConclusion (cap : Cap) (p : Parameters) (Q A s : ℝ) : Prop :=
  AngularTableGeometry.Conclusion (p.edge/2) p.tilt p.margin A (data cap p) ∧
  |normalizedCost cap p - Q| ≤ A*s^4 ∧
  (data cap p).count = p.sectors ∧
  Shape cap p ∧ ApertureLaw cap p ∧
  lowerFamilyArea cap p = upperFamilyArea cap p ∧
  lowerFamilyArea cap p = AngularTableGeometry.totalArea (p.edge/2) p.tilt (data cap p)/2

def IntegerRow (cap : Cap) (p : ℕ → Parameters) (Q : ℕ → ℝ) : Prop :=
  ∃ N : ℕ, ∃ A : ℝ, 0 < N ∧ 0 < A ∧ ∀ n ≥ N,
    RowConclusion cap (p n) (Q n) A (1/(n:ℝ))

def RealRow (cap : Cap) (p : ℝ → Parameters) (Q : ℝ → ℝ) : Prop :=
  ∃ δ A : ℝ, 0 < δ ∧ 0 < A ∧ ∀ t : ℝ, 0 < t → t < δ →
    RowConclusion cap (p t) (Q t) A t

def Statement : Prop :=
  IntegerRow .midpoint midpointFour (fun n => 1/2-1/(80*(n:ℝ)^2)) ∧
  RealRow .midpoint midpointOne (fun t => 1/2-(13/6000:ℝ)*t^2) ∧
  IntegerRow .midpoint midpointTwo (fun n => 1/2-13/(6000*(n:ℝ)^2)) ∧
  (∃ δ A : ℝ, 0 < δ ∧ 0 < A ∧ ∀ c : ℝ, 0 < c → c < δ →
    ∀ m : ℕ, 2/c^2 ≤ (m:ℝ) →
      RowConclusion .radial (continuousTwo c m) (1/2-(13/6000:ℝ)*c^2) A c) ∧
  IntegerRow .squared squaredTwo (fun n => 1/2-1/(120*(n:ℝ)^2)) ∧
  IntegerRow .maximum maximumOne (fun n => 1/2-1/(7680*(n:ℝ)^2)) ∧
  RealRow (.cartesian (3/4)) cartesianThreeQuarters (fun t => 1/2-t^2/1920) ∧
  IntegerRow (.cartesian 1) cartesianOne (fun n => 1/2-13/(24000*(n:ℝ)^2))

end CylinderCovering.AngularTableCover

end

end OAI
