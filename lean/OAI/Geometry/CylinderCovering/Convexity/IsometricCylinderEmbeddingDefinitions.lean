import OAI.Geometry.CylinderCovering.Convexity.SimilarityDefinitions

namespace OAI

noncomputable section
namespace CylinderCovering.IsometricEmbedding

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def map (t : F) (L : E →ₗᵢ[ℝ] F) (x : E) : F := t + L x

def baseMap (u : E) (t : F) (L : E →ₗᵢ[ℝ] F) (x : E) : F :=
  Similarity.project (L u) t + L x

def transportedBase (B : Set E) (u : E) (t : F) (L : E →ₗᵢ[ℝ] F) : Set F :=
  baseMap u t L '' B

def scaledMap (t : F) (r : ℝ) (L : E →ₗᵢ[ℝ] F) (x : E) : F := t + r • L x

def scaledBaseMap (u : E) (t : F) (r : ℝ) (L : E →ₗᵢ[ℝ] F) (x : E) : F :=
  Similarity.project (L u) t + r • L x

def scaledTransportedBase (B : Set E) (u : E) (t : F) (r : ℝ)
    (L : E →ₗᵢ[ℝ] F) : Set F := scaledBaseMap u t r L '' B

end CylinderCovering.IsometricEmbedding

end

end OAI
