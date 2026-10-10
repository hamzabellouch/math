import OAI.Geometry.CylinderCovering.Convexity.IsometricCylinderEmbedding
import OAI.Geometry.CylinderCovering.Barycentric.LocalDictionary

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace RadialCoordinates
open CylinderCovering

lemma canonical_scaledMap :
    IsometricEmbedding.scaledMap canonicalCenter canonicalScale
      canonicalEmbeddingIsometry = canonicalToBary := by
  funext z
  exact (canonicalToBary_eq z).symm

lemma firstBase_area (k : ℝ) (N : ℕ) (i : Fin N) :
    BarycentricFinite.area (BarycentricFinite.firstBase k N i) =
      (1 / 8 : ℝ) * TriangularCovering.area
        (RadialPairedSweep.lowerActualBase (Real.sqrt 2) k (canonicalCap k) N
          (fun j => angular (BarycentricFinite.midpoint N j)) i) := by
  have h := IsometricEmbedding.scaled_projected_image_area
    (RadialPairedSweep.lowerLocalSweep (Real.sqrt 2) k (canonicalCap k) N i)
    (RadialPairedSweep.lowerAxis (Real.sqrt 2) k
      (angular (BarycentricFinite.midpoint N i))) canonicalCenter
    canonicalScale_pos.ne' canonicalEmbeddingIsometry
  change Similarity.area (Similarity.project
    (canonicalEmbedding (RadialPairedSweep.lowerAxis (Real.sqrt 2) k
      (angular (BarycentricFinite.midpoint N i)))) ''
      (IsometricEmbedding.scaledMap canonicalCenter canonicalScale
        canonicalEmbeddingIsometry '' _)) = _ at h
  rw [canonicalEmbedding_lowerAxis, canonical_scaledMap, lowerLocalSweep_image,
    canonicalScale_sq] at h
  exact h

lemma secondBase_area (k : ℝ) (N : ℕ) (i : Fin N) :
    BarycentricFinite.area (BarycentricFinite.secondBase k N i) =
      (1 / 8 : ℝ) * TriangularCovering.area
        (RadialPairedSweep.upperActualBase (Real.sqrt 2) k (canonicalCap k) N
          (fun j => angular (BarycentricFinite.midpoint N j)) i) := by
  have h := IsometricEmbedding.scaled_projected_image_area
    (RadialPairedSweep.upperLocalSweep (Real.sqrt 2) k (canonicalCap k) N i)
    (RadialPairedSweep.upperAxis (Real.sqrt 2) k
      (angular (BarycentricFinite.midpoint N i))) canonicalCenter
    canonicalScale_pos.ne' canonicalEmbeddingIsometry
  change Similarity.area (Similarity.project
    (canonicalEmbedding (RadialPairedSweep.upperAxis (Real.sqrt 2) k
      (angular (BarycentricFinite.midpoint N i)))) ''
      (IsometricEmbedding.scaledMap canonicalCenter canonicalScale
        canonicalEmbeddingIsometry '' _)) = _ at h
  rw [canonicalEmbedding_upperAxis, canonical_scaledMap, upperLocalSweep_image,
    canonicalScale_sq] at h
  exact h

lemma barycentric_totalArea_eq (k : ℝ) (N : ℕ) :
    BarycentricFinite.totalArea k N = (1 / 8 : ℝ) *
      RadialPairedSweep.pairedActualCost (Real.sqrt 2) k (canonicalCap k) N
        (fun i => angular (BarycentricFinite.midpoint N i))
        (fun i => angular (BarycentricFinite.midpoint N i)) := by
  unfold BarycentricFinite.totalArea RadialPairedSweep.pairedActualCost
  simp only [firstBase_area, secondBase_area, ← Finset.mul_sum]
  ring

end RadialCoordinates

end

end OAI
