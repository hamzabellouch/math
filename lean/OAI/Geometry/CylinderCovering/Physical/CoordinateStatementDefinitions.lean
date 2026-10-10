import OAI.Geometry.CylinderCovering.Physical.CoordinatesDefinitions
import OAI.Geometry.CylinderCovering.Radial.CoordinatesDefinitions

namespace OAI

open Set MeasureTheory
noncomputable section
namespace RadialPhysical

structure PhysicalCoordinatesStatement : Prop where
  point_distance_squared (b x y t x' y' t' : ℝ) :
      ‖point b x y t - point b x' y' t'‖ ^ 2 =
        (x - x') ^ 2 + (y - y') ^ 2 + 2 * b ^ 2 * (t - t') ^ 2

  halfheight_distance {b : ℝ} (hb : 0 < b) (x y t x' y' t' : ℝ) :
      dist (canonicalPoint (2 * x / b) (2 * y / b) (2 * t - 1))
        (canonicalPoint (2 * x' / b) (2 * y' / b) (2 * t' - 1)) =
        (2 / b) * dist (point b x y t) (point b x' y' t')

  first_line_dictionary {b : ℝ} (hb : b ≠ 0) (eta x rho s : ℝ) :
      canonicalPoint (2 * x / b)
        (2 * (rho * s - eta * x * (s ^ 2 + b ^ 2) / 2) / b)
        (2 * (1 - rho + eta * x * s) - 1) =
      canonicalPoint (2 * x / b)
        ((2 * rho) * (s / b) - effectiveTilt b eta * (2 * x / b) * ((1 + (s / b) ^ 2) / 2))
        (1 - 2 * rho + effectiveTilt b eta * (2 * x / b) * (s / b))

  second_line_dictionary {b : ℝ} (hb : b ≠ 0) (eta y rho s : ℝ) :
      canonicalPoint (2 * (rho * s + eta * y * (s ^ 2 + b ^ 2) / 2) / b)
        (2 * y / b) (2 * (rho + eta * y * s) - 1) =
      canonicalPoint ((2 * rho) * (s / b) +
          effectiveTilt b eta * (2 * y / b) * ((1 + (s / b) ^ 2) / 2))
        (2 * y / b) (-1 + 2 * rho + effectiveTilt b eta * (2 * y / b) * (s / b))

  capPolynomial_angular_substitution (b beta r : ℝ) :
      capPolynomial b beta (b * r) = b ^ 4 * (canonicalProfile r + beta) / 2

  linearCap_dictionary (b eta beta r : ℝ) :
      2 * linearCap b eta beta (b * r) =
        1 + effectiveTilt b eta ^ 2 * (canonicalProfile r + beta)

  squareCap_dictionary (b eta beta r : ℝ) :
      2 * squareCap b eta beta (b * r) =
        Real.sqrt (1 + 2 * effectiveTilt b eta ^ 2 * (canonicalProfile r + beta))

  physical_speed_dictionary (b eta r : ℝ) :
      1 + eta ^ 2 * (((b * r) ^ 2 + b ^ 2) ^ 2 / 4 + height b ^ 2 * (b * r) ^ 2) =
        1 + effectiveTilt b eta ^ 2 * canonicalSpeed r

  scaledCost_dictionary {b : ℝ} (hb : 0 < b) (eta : ℝ) (T : ℝ → ℝ) :
      scaledCost b eta T = (b * height b / 2) *
        canonicalCost (effectiveTilt b eta) (fun r => 2 * T (b * r))

  mapToCanonical_point {b : ℝ} (hb : b ≠ 0) (x y t : ℝ) :
      mapToCanonical b (point b x y t) =
        canonicalPoint (2 * x / b) (2 * y / b) (2 * t - 1)

  mapToCanonical_tetrahedron {b : ℝ} (hb : 0 < b) :
      mapToCanonical b '' tetrahedron b = RadialCoordinates.canonicalTetrahedron

  scaled_table_rational_rows (tau : ℝ) :
      relativeQuadraticTerm 1 tau (1 / 120) = -tau ^ 2 / 60 ∧
      relativeQuadraticTerm (1 / 2) (tau / 2) (1 / 120) = -tau ^ 2 / 3840 ∧
      relativeQuadraticTerm (1 / 2) tau (4 / 625) = -(77 / 60000) * tau ^ 2 ∧
      relativeQuadraticTerm (1 / 2) (2 * tau) (1 / 120) = -tau ^ 2 / 240 ∧
      relativeQuadraticTerm 1 (2 * tau) (1 / 200) = -(7 / 75) * tau ^ 2

  scaled_cap_half_edge (s : ℝ) :
      capPolynomial (1 / 2) (4 / 625) s = s ^ 4 / 4 + s ^ 2 / 16 + 1 / 5000

  scaled_table_sqrt_row (tau : ℝ) :
      relativeQuadraticTerm (1 / Real.sqrt 2) tau (1 / 125) = -(13 / 3000) * tau ^ 2

  scaled_cap_sqrt_edge (s : ℝ) :
      capPolynomial (1 / Real.sqrt 2) (1 / 125) s = (s ^ 4 + s ^ 2 / 2) / 4 + 1 / 1000

  centered_distance {b : ℝ} (hb : 0 < b) (x y t x' y' t' : ℝ) :
      dist (canonicalPoint (x / b) (y / b) t)
        (canonicalPoint (x' / b) (y' / b) t') =
        (1 / b) * dist (point b x y t) (point b x' y' t')

  nonorthPoint_distance_squared (p q t p' q' t' : ℝ) :
      ‖nonorthPoint p q t - nonorthPoint p' q' t'‖ ^ 2 =
        (t - t') ^ 2 + ((p - p') ^ 2 + (q - q') ^ 2) / 2

  nonorth_distance (p q t p' q' t' : ℝ) :
      dist (canonicalPoint p q t) (canonicalPoint p' q' t') =
        Real.sqrt 2 * dist (nonorthPoint p q t) (nonorthPoint p' q' t')

  orthonormal_height_dictionary (x y z : ℝ) :
      canonicalPoint y x ((1 / Real.sqrt 2) * z) = (!₂[y, x, z] : Space)

  orthonormal_cubic_padding (tau H : ℝ) :
      (1 / Real.sqrt 2) * (tau ^ 2 * (1 / Real.sqrt 2) * H + 10 * tau ^ 3) =
        ((1 / Real.sqrt 2) * tau) ^ 2 * H + 20 * ((1 / Real.sqrt 2) * tau) ^ 3

  orthonormal_error_margin : 9 * (1 / Real.sqrt 2) ^ 2 < (20 : ℝ)

  halfedge_alternative_cap (tau s : ℝ) :
      linearCap (1 / 2) (tau / 2) (1 / 120) s =
        1 / 2 + tau ^ 2 * ((1 / 2) ^ 2 * s ^ 2 *
          ((1 / 2) * (1 / 8 + s ^ 2 / 2)) + (1 / 2) ^ 3 / 1920)

  halfedge_quadratic_cost (tau : ℝ) :
      quadraticCost (1 / 2) tau (4 / 625) =
        2 * height (1 / 2) * (1 / 8 - 77 / 480000 * tau ^ 2) ∧
      quadraticCost (1 / 2) (tau / 2) (1 / 120) =
        height (1 / 2) / 4 - height (1 / 2) * (1 / 2) ^ 4 / 960 * tau ^ 2

  centeredLinearCap_dictionary (b eta beta r : ℝ) :
      centeredLinearCap b eta beta (b * r) =
        1 + effectiveTilt b eta ^ 2 * (canonicalProfile r + beta)

  centered_sqrt_cap (eta s : ℝ) :
      centeredLinearCap (1 / Real.sqrt 2) eta (1 / 250) s =
        1 + eta ^ 2 * ((s ^ 4 + s ^ 2 / 2) / 2 + 1 / 1000)

  centered_quadratic_coefficient_neg {b : ℝ} (hb : 0 < b) :
      -b / 120 + 2 * b / 1000 < 0

  centeredCost_dictionary {b : ℝ} (hb : 0 < b) (eta : ℝ) (R : ℝ → ℝ) :
      scaledCost b eta R = 2 * b * height b *
        canonicalCost (effectiveTilt b eta) (fun r => R (b * r))

  mapCenteredToCanonical_point {b : ℝ} (hb : b ≠ 0) (x y t : ℝ) :
      mapCenteredToCanonical b (point b x y t) =
        canonicalPoint (x / b) (y / b) t

  mapCenteredToCanonical_tetrahedron {b : ℝ} (hb : 0 < b) :
      mapCenteredToCanonical b '' centeredTetrahedron b = RadialCoordinates.canonicalTetrahedron

  centered_first_line_dictionary {b : ℝ} (hb : b ≠ 0) (eta x rho s : ℝ) :
      canonicalPoint (x / b) ((rho * s - eta * x * (s ^ 2 + b ^ 2) / 2) / b)
          (1 - rho + eta * x * s) =
        canonicalPoint (x / b)
          (rho * (s / b) - effectiveTilt b eta * (x / b) * ((1 + (s / b) ^ 2) / 2))
          (1 - rho + effectiveTilt b eta * (x / b) * (s / b))

  centered_second_line_dictionary {b : ℝ} (hb : b ≠ 0) (eta y rho s : ℝ) :
      canonicalPoint ((rho * s + eta * y * (s ^ 2 + b ^ 2) / 2) / b) (y / b)
          (-1 + rho + eta * y * s) =
        canonicalPoint (rho * (s / b) +
            effectiveTilt b eta * (y / b) * ((1 + (s / b) ^ 2) / 2))
          (y / b) (-1 + rho + effectiveTilt b eta * (y / b) * (s / b))

  centered_fractional_padding {eta : ℝ} (heta : 0 < eta) :
      Real.rpow eta (5 / 2) = 4 * Real.sqrt 2 *
        Real.rpow (effectiveTilt (1 / Real.sqrt 2) eta) (5 / 2)

end RadialPhysical

end

end OAI
