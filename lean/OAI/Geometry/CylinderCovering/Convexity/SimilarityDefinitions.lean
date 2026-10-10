import Mathlib

namespace OAI

open Set MeasureTheory

noncomputable section
namespace CylinderCovering.Similarity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def map (t : E) (r : ℝ) (L : E ≃ₗᵢ[ℝ] E) (x : E) : E := t + r • L x

def affineMap (t : E) (r : ℝ) (L : E ≃ₗᵢ[ℝ] E) : E →ᵃ[ℝ] E :=
  (AffineEquiv.constVAdd ℝ E t).toAffineMap.comp
    (r • L.toLinearMap).toAffineMap

def project (u x : E) : E := x - (inner ℝ u x) • u

def carrier (B : Set E) (u : E) : Set E :=
  {x | ∃ b ∈ B, ∃ s : ℝ, x = b + s • u}

def baseMap (u t : E) (r : ℝ) (L : E ≃ₗᵢ[ℝ] E) (x : E) : E :=
  project (L u) t + r • L x

def transportedBase (B : Set E) (u t : E) (r : ℝ) (L : E ≃ₗᵢ[ℝ] E) : Set E :=
  baseMap u t r L '' B

variable [MeasurableSpace E] [BorelSpace E]

def area (B : Set E) : ℝ := (Measure.euclideanHausdorffMeasure 2 B).toReal

def shadowArea (K : Set E) (u : E) : ℝ := area (project u '' K)

def minimumArea (K : Set E) : ℝ :=
  sInf {a : ℝ | ∃ u : E, ‖u‖ = 1 ∧ a = shadowArea K u}

end CylinderCovering.Similarity

end

end OAI
