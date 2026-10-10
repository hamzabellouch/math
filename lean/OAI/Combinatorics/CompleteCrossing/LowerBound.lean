import OAI.Combinatorics.CompleteCrossing.Isotropy
import OAI.Combinatorics.CompleteCrossing.TriangleFactors
import OAI.Combinatorics.CompleteCrossing.VertexEvaluation

namespace OAI

/-! Polynomial injectivity and the lower bound on crossing-tensor support. -/

section

/-! The polynomial lower-bound argument for complete graphs. -/
noncomputable section
namespace Paper170
section CrossingTensor

variable {s : ℕ} (hs : 2 ≤ s) (node : Fin (2 * s + 1) → ℝ)
    (hnode : Function.Injective node) (J : CrossingTensor (2 * s + 1))
    (orders : ∀ i : Fin (2 * s + 1), LinearOrder {j : Fin (2 * s + 1) // j ≠ i})
    (hloopLeft : ∀ i k q, J i i k q = 0)
    (hloopRight : ∀ i p k, J i p k k = 0)
    (hreverseLeft : ∀ i p k q, J p i k q = -J i p k q)
    (hreverseRight : ∀ i p k q, J i p q k = -J i p k q)
    (hskew : ∀ i p k q, J k q i p = -J i p k q)
    (hlocal : ∀ i (p q : {j : Fin (2 * s + 1) // j ≠ i}),
      J i p.val i q.val = halfOrder (orders i) p q)
    (htests : ∀ H ∈ box4 (2 * s - 1), polynomialTest node J H = 0)

include hs hnode orders hloopLeft hloopRight hreverseLeft hreverseRight hskew hlocal htests

theorem kernel_diagonal_vanishing (P : endpointSymmetricSpace s)
    (hP : supportEvaluation s node J P = 0) :
    diagonalSpecialization P.val = 0 :=
  diagonal_zero_of_vertices s node hnode P (kernel_vertex_vanishing hs node hnode J orders
    hloopLeft hloopRight hreverseLeft hreverseRight hskew hlocal htests P hP)

theorem kernel_collision_divisibility (P : endpointSymmetricSpace s)
    (hP : supportEvaluation s node J P = 0) : collisionFactor ∣ P.val :=
  collision_divides_of_diagonal_vanishing s P (kernel_diagonal_vanishing hs node hnode J orders
    hloopLeft hloopRight hreverseLeft hreverseRight hskew hlocal htests P hP)

theorem support_evaluation_injective : Function.Injective (supportEvaluation s node J) :=
  support_evaluation_injective_of_collision hs node hnode J
    (kernel_collision_divisibility hs node hnode J orders hloopLeft hloopRight
      hreverseLeft hreverseRight hskew hlocal htests)

theorem support_cardinality_lower_bound :
    2 * (Nat.choose s 2) ^ 2 ≤ (supportedPairs J).card :=
  support_cardinality_of_injective_isotropic hs node hnode J
    (support_evaluation_injective hs node hnode J orders hloopLeft hloopRight
      hreverseLeft hreverseRight hskew hlocal htests)
    (evaluation_image_isotropic hs node hnode J orders hloopLeft hloopRight
      hreverseLeft hreverseRight hskew hlocal htests)

end CrossingTensor
end Paper170

end
end

end OAI
