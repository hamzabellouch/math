import OAI.Combinatorics.Crossing.TruncatedChainPath
import OAI.Combinatorics.Crossing.RadialExterior

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem radial_segment_of_coefficients (o p q v : Plane) (r α β : ℝ)
    (hr : 0 < r) (hα : 0 < α) (hβ : 0 < β)
    (hp : p-o=α • v) (hq : q-p=β • v) (hc : squaredLength (p-o)=r^2) :
    segment ℝ p q ⊆ insert p {x | r^2 < squaredLength (x-o)} := by
  have he : q=p+(β/α) • (p-o) := by
    rw [hp,smul_smul,div_mul_cancel₀ _ (ne_of_gt hα)]
    rw [← hq]
    abel
  rw [he]
  exact radial_spur_exterior o p r (β/α) hc hr (div_pos hβ hα)

namespace PolygonalChain
variable {O : Set Plane} {a b : Plane}

theorem truncated_first_exterior (P : PolygonalChain O a b)
    (hmin : ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces) (hp : 0 < P.pieces)
    (r : ℝ) (hr : 0 < r)
    (hfirst : 4*r^2 < squaredLength (P.vertices 1-P.vertices 0))
    (hlast : 4*r^2 < squaredLength (P.vertices P.pieces-P.vertices (P.pieces-1))) :
    segment ℝ (P.truncatedVertices r 0) (P.truncatedVertices r 1) ⊆
      insert (P.startPort r) {x | r^2 < squaredLength (x-P.vertices 0)} := by
  have hα := (radialPort_parameter_half (P.vertices 0) (P.vertices 1) r hr hfirst).1
  have hβ := P.truncatedScale_pos r hr hfirst hlast 0
  rw [P.truncatedVertices_first]
  apply radial_segment_of_coefficients (P.vertices 0) (P.startPort r) (P.truncatedVertices r 1)
    (trackDirection P.vertices 0) r (P.startFraction r) (P.truncatedScale r 0) hr hα hβ
  · exact radialPort_sub (P.vertices 0) (P.vertices 1) r
  · simpa only [trackDirection,P.truncatedVertices_first] using P.truncated_direction r 0 hp
  · exact radialPort_on_circle (P.vertices 0) (P.vertices 1)
      (P.minimum_vertices_ne hmin 0 1 (by omega) hp) r

theorem truncated_last_exterior (P : PolygonalChain O a b)
    (hmin : ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces) (hp : 0 < P.pieces)
    (r : ℝ) (hr : 0 < r)
    (hfirst : 4*r^2 < squaredLength (P.vertices 1-P.vertices 0))
    (hlast : 4*r^2 < squaredLength (P.vertices P.pieces-P.vertices (P.pieces-1))) :
    segment ℝ (P.truncatedVertices r (P.pieces-1)) (P.truncatedVertices r P.pieces) ⊆
      insert (P.endPort r) {x | r^2 < squaredLength (x-P.vertices P.pieces)} := by
  have hi : P.pieces-1 < P.pieces := by omega
  have hα := (radialPort_parameter_half (P.vertices (P.pieces-1)) (P.vertices P.pieces) r hr hlast).1
  have hβ := P.truncatedScale_pos r hr hfirst hlast (P.pieces-1)
  rw [P.truncatedVertices_last hp,segment_symm]
  apply radial_segment_of_coefficients (P.vertices P.pieces) (P.endPort r)
    (P.truncatedVertices r (P.pieces-1)) (-(trackDirection P.vertices (P.pieces-1)))
    r (P.endFraction r) (P.truncatedScale r (P.pieces-1)) hr hα hβ
  · rw [P.endPort_eq_fraction]
    simp only [trackDirection,show P.pieces-1+1=P.pieces by omega,smul_neg]
    abel
  · have h := P.truncated_direction r (P.pieces-1) hi
    simp only [trackDirection,show P.pieces-1+1=P.pieces by omega,P.truncatedVertices_last hp] at h ⊢
    rw [smul_neg,← h]
    abel
  · have hn := Ne.symm (P.minimum_vertices_ne hmin (P.pieces-1) P.pieces hi (by omega))
    exact radialPort_on_circle (P.vertices P.pieces) (P.vertices (P.pieces-1)) hn r

end PolygonalChain
end Zarankiewicz

end

end OAI
