import OAI.Geometry.CylinderCovering.Barycentric.SectorNeighborhoodDefinitions
import OAI.Geometry.CylinderCovering.Radial.RiemannDefinitions
import OAI.Geometry.CylinderCovering.Angular.CapsDefinitions

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace RadialCoordinates.BarycentricSector
open CylinderCovering.RadialRiemann

def intercepts (k c l r : ℝ) : Set Plane :=
  {z | ∃ t ∈ Icc l r, ∃ S ∈ Icc (0:ℝ) (cap k t), ∃ p ∈ Icc (-1:ℝ) 1,
    z = S • ray t + (k*p) • (velocity t-velocity c)}

def canonicalCapBound (k : ℝ) : ℝ := 1/2+(501/1000)*k^2

structure EnclosureStatement : Prop where
  triangles : ∀ l r a b : ℝ, l ≤ r → 0 ≤ a → 0 ≤ b →
    IsCompact (signedSector l r a b) ∧
    signedSector l r a b = convexHull ℝ (range (vertices l r b)) ∪
      (fun z : Plane => -z) '' convexHull ℝ (range (vertices l r a)) ∧
    positiveSector l r b ∩ (fun z : Plane => -z) '' positiveSector l r a = {0}
  exactArea : ∀ l r a b : ℝ, l ≤ r → 0 ≤ a → 0 ≤ b →
    volume.real (signedSector l r a b) = (r-l)*(b^2+a^2)/2
  nondegenerate : ∀ l r A : ℝ, l < r → 0 < A →
    AffineIndependent ℝ (vertices l r A)
  uniformPerimeters : ∀ l r k M M₀ : ℝ,
    0 ≤ l → l ≤ r → r ≤ 1 → 0 ≤ k → 0 ≤ M → M ≤ M₀ →
    perimeter l r (2*k*(r-l)) + perimeter l r (M+2*k*(r-l)) ≤
      (2+Real.sqrt 2)*(M₀+4*k)
  actualIntercepts : ∀ l r c S k p t M : ℝ,
    0 ≤ k → |p| ≤ 1 → c ∈ Icc l r → t ∈ Icc l r → 0 ≤ S → S ≤ M →
    S • ray t + (k*p) • (velocity t-velocity c) ∈ neighborhood l r k M
  geometricError : ∀ l r k M M₀ : ℝ,
    0 ≤ l → l ≤ r → r ≤ 1 → 0 ≤ k → 0 ≤ M → M ≤ M₀ →
    IsCompact (neighborhood l r k M) ∧
    0 ≤ volume.real (neighborhood l r k M)-(r-l)*M^2/2 ∧
    volume.real (neighborhood l r k M)-(r-l)*M^2/2 ≤
      (18*k*M₀+162*k^2)*(r-l)^2
  weightedFinite : ∀ N : ℕ, 0 < N → ∀ k M₀ : ℝ, 0 ≤ k →
    ∀ M : Fin N → ℝ, (∀ i, 0 ≤ M i) → (∀ i, M i ≤ M₀) →
    ∀ S : Fin N → Set Plane,
      (∀ i, S i ⊆ neighborhood (point 0 1 N i) (point 0 1 N (i+1)) k (M i)) →
    ∀ W : Fin N → ℝ, (∀ i, 0 ≤ W i) → (∀ i, W i ≤ 1) →
    (∑ i : Fin N, W i * volume.real (S i)) ≤
      (∑ i : Fin N, W i * ((1/(N:ℝ))*(M i)^2/2)) +
        (18*k*M₀+162*k^2)/(N:ℝ)
  canonicalCompact : ∀ k c l r : ℝ, IsCompact (intercepts k c l r)
  canonicalFinite : ∀ N : ℕ, 0 < N → ∀ k : ℝ, 0 ≤ k →
    ∀ tag : Fin N → ℝ, IsTagged 0 1 N tag →
    ∀ W : Fin N → ℝ, (∀ i, 0 ≤ W i) → (∀ i, W i ≤ 1) →
    (∑ i : Fin N, W i * volume.real
      (intercepts k (tag i) (point 0 1 N i) (point 0 1 N (i+1)))) ≤
    (∑ i : Fin N, W i*((1/(N:ℝ))*(capMax (cap k) 0 1 N i)^2/2)) +
      (18*k*canonicalCapBound k+162*k^2)/(N:ℝ)

end RadialCoordinates.BarycentricSector

end

end OAI
