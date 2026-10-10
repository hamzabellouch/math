import OAI.Geometry.SingularHomology.BarycentricSubdivision
import OAI.Geometry.SingularHomology.SubdivisionSupportMesh

namespace OAI

noncomputable section

namespace Problem340.SingularSubdivision

open SimplexSubdivision

lemma mapVertices_eq_mapDomain {V W : Type*} (f : V → W) (n : ℕ) (c : Chains V n) :
    mapVertices f n c = c.mapDomain (fun p => f ∘ p) := by
  classical
  simp [mapVertices, Finsupp.linearCombination_apply, Finsupp.mapDomain, generator,
    Finsupp.sum]

lemma mem_support_mapVertices_iff_of_injective {V W : Type*} (f : V → W)
    (hf : Function.Injective f) (n : ℕ) (c : Chains V n) (p : Fin n → V) :
    f ∘ p ∈ (mapVertices f n c).support ↔ p ∈ c.support := by
  rw [mapVertices_eq_mapDomain, Finsupp.mem_support_iff, Finsupp.mapDomain_apply_of_injective,
    Finsupp.mem_support_iff]
  intro p q hpq
  funext i
  exact hf (congrFun hpq i)

lemma coe_simplexCenters (k n : ℕ) (v : Fin (n + 1) → StandardSimplex k) :
    ((simplexCenters k n v) : Fin (k + 1) → ℝ) =
      barycentricCenters n (fun i => (v i : Fin (k + 1) → ℝ)) := by
  change (AffineSimplex.simplexBarycenter v : Fin (k + 1) → ℝ) = _
  rw [AffineSimplex.simplexBarycenter_coe]
  change AffineSimplex.barycenter (fun i => (v i : Fin (k + 1) → ℝ)) =
    faceCenter (fun i => (v i : Fin (k + 1) → ℝ)) Finset.univ
  rw [AffineSimplex.barycenter_eq_sum, faceCenter_eq]
  simp

lemma coe_subdivision (k n : ℕ) (c : Chains (StandardSimplex k) n) :
    mapVertices RealSimplex.coordinates n (subdivision (simplexCenters k) n c) =
      subdivision barycentricCenters n (mapVertices RealSimplex.coordinates n c) :=
  mapVertices_subdivision RealSimplex.coordinates (simplexCenters k) barycentricCenters
    (coe_simplexCenters k) n c

lemma coe_subdivision_iterate (k n r : ℕ) (c : Chains (StandardSimplex k) n) :
    mapVertices RealSimplex.coordinates n (((subdivision (simplexCenters k) n)^[r]) c) =
      ((subdivision barycentricCenters n)^[r]) (mapVertices RealSimplex.coordinates n c) := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [Function.iterate_succ_apply', coe_subdivision, ih,
        Function.iterate_succ_apply']

theorem simplex_iterated_subdivision_support {k n r : ℕ}
    (v : Fin n → StandardSimplex k) {w : Fin n → StandardSimplex k}
    (h : w ∈ (((subdivision (simplexCenters k) n)^[r]) (generator v)).support) :
    (fun i => (w i : Fin (k + 1) → ℝ)) ∈
      (((subdivision barycentricCenters n)^[r])
        (generator (fun i => (v i : Fin (k + 1) → ℝ)))).support := by
  have hc := (mem_support_mapVertices_iff_of_injective RealSimplex.coordinates
    RealSimplex.coordinates_injective n _ w).2 h
  rw [coe_subdivision_iterate, mapVertices_generator] at hc
  exact hc

theorem simplex_subdivision_support_barycentricCell {k n : ℕ}
    (v : Fin (n + 1) → StandardSimplex k) {w : Fin (n + 1) → StandardSimplex k}
    (h : w ∈ (subdivision (simplexCenters k) (n + 1) (generator v)).support) :
    BarycentricCell n (fun i => (v i : Fin (k + 1) → ℝ))
      (fun i => (w i : Fin (k + 1) → ℝ)) := by
  apply subdivision_support_barycentricCell
  exact simplex_iterated_subdivision_support (r := 1) v h

end Problem340.SingularSubdivision

end

end OAI
