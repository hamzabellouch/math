import OAI.Geometry.SingularHomology.SubdivisionSupportMesh
import OAI.Geometry.SingularHomology.BarycentricSubdivision
import OAI.Geometry.SingularHomology.SubdivisionSubtypeMesh
import OAI.Geometry.SingularHomology.SimplexSubtypeMesh

namespace OAI

noncomputable section

open Set

namespace Problem340.SingularSubdivision

lemma mem_support_linearMap {α β : Type*}
    (L : (α →₀ ℝ) →ₗ[ℝ] (β →₀ ℝ)) (c : α →₀ ℝ) {q : β}
    (h : q ∈ (L c).support) :
    ∃ p ∈ c.support, q ∈ (L (Finsupp.single p 1)).support := by
  classical
  have hL : L = Finsupp.linearCombination ℝ (fun p => L (Finsupp.single p 1)) := by
    apply Finsupp.lhom_ext
    intro p r
    simp only [Finsupp.linearCombination_single]
    have hr : Finsupp.single p r = r • Finsupp.single p 1 := by simp
    rw [hr, map_smul]
  rw [hL, Finsupp.linearCombination_apply, Finsupp.sum] at h
  obtain ⟨p, hp, hq⟩ := Finsupp.mem_support_finsetSum q h
  exact ⟨p, hp, Finsupp.support_smul hq⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem iterate_subdivision_support_carrier_and_mesh {n : ℕ}
    (v : Fin (n + 1) → E) (D : ℝ) (hD : 0 ≤ D)
    (hvertices : ∀ i j, dist (v i) (v j) ≤ D)
    (k : ℕ) {w : Fin (n + 1) → E}
    (h : w ∈ ((subdivision barycentricCenters (n + 1))^[k] (generator v)).support) :
    range w ⊆ convexHull ℝ (range v) ∧
      ∀ i j, dist (w i) (w j) ≤ ((n : ℝ) / (n + 1)) ^ k * D := by
  induction k generalizing w with
  | zero =>
      have hw : w = v := by simpa [generator] using h
      subst w
      exact ⟨subset_convexHull ℝ _, by simpa using hvertices⟩
  | succ k ih =>
      rw [Function.iterate_succ_apply'] at h
      obtain ⟨u, hu, hw⟩ := mem_support_linearMap _ _ h
      obtain ⟨huc, hum⟩ := ih hu
      obtain ⟨hwc, hwm⟩ := (subdivision_support_barycentricCell u hw).carrier_and_mesh
        (((n : ℝ) / (n + 1)) ^ k * D) (by positivity) hum
      refine ⟨hwc.trans ?_, ?_⟩
      · exact convexHull_min huc (convex_convexHull ℝ _)
      · intro i j
        calc
          dist (w i) (w j) ≤ (n : ℝ) / (n + 1) *
              (((n : ℝ) / (n + 1)) ^ k * D) := hwm i j
          _ = ((n : ℝ) / (n + 1)) ^ (k + 1) * D := by ring

theorem iterate_subdivision_support_mesh {n : ℕ}
    (v : Fin (n + 1) → E) (D : ℝ) (hD : 0 ≤ D)
    (hvertices : ∀ i j, dist (v i) (v j) ≤ D)
    (k : ℕ) {w : Fin (n + 1) → E}
    (h : w ∈ ((subdivision barycentricCenters (n + 1))^[k] (generator v)).support)
    (i j : Fin (n + 1)) :
    dist (w i) (w j) ≤ ((n : ℝ) / (n + 1)) ^ k * D :=
  (iterate_subdivision_support_carrier_and_mesh v D hD hvertices k h).2 i j

theorem iterate_subdivision_support_carrier {n : ℕ}
    (v : Fin (n + 1) → E) (k : ℕ) {w : Fin (n + 1) → E}
    (h : w ∈ ((subdivision barycentricCenters (n + 1))^[k] (generator v)).support) :
    range w ⊆ convexHull ℝ (range v) :=
  (iterate_subdivision_support_carrier_and_mesh v (Metric.diam (range v))
    Metric.diam_nonneg (fun i j => Metric.dist_le_diam_of_mem
      (finite_range v).isBounded (mem_range_self i) (mem_range_self j)) k h).1

theorem simplex_iterate_subdivision_support_mesh {m n : ℕ}
    (v : Fin (n + 1) → StandardSimplex m) (D : ℝ) (hD : 0 ≤ D)
    (hvertices : ∀ i j, dist (v i) (v j) ≤ D)
    (k : ℕ) {w : Fin (n + 1) → StandardSimplex m}
    (h : w ∈ ((subdivision (simplexCenters m) (n + 1))^[k] (generator v)).support)
    (i j : Fin (n + 1)) :
    dist (w i) (w j) ≤ ((n : ℝ) / (n + 1)) ^ k * D :=
  iterate_subdivision_support_mesh (fun a => RealSimplex.coordinates (v a)) D hD hvertices k
    (simplex_iterated_subdivision_support v h) i j

theorem simplex_iterate_subdivision_realize_dist {m n : ℕ}
    (v : Fin (n + 1) → StandardSimplex m) (D : ℝ) (hD : 0 ≤ D)
    (hvertices : ∀ i j, dist (v i) (v j) ≤ D)
    (k : ℕ) {w : Fin (n + 1) → StandardSimplex m}
    (h : w ∈ ((subdivision (simplexCenters m) (n + 1))^[k] (generator v)).support)
    (x y : StandardSimplex n) :
    dist (AffineSimplex.simplexRealizeMap w x) (AffineSimplex.simplexRealizeMap w y) ≤
      ((n : ℝ) / (n + 1)) ^ k * D := by
  apply SimplexSubtypeMesh.dist_le_of_convex_carrier (fun i => RealSimplex.coordinates (w i))
    (fun point => RealSimplex.coordinateHomeomorph (AffineSimplex.simplexRealizeMap w point))
    _ _ _ x y
  · exact simplex_iterate_subdivision_support_mesh v D hD hvertices k h
  · intro a
    simpa only [RealSimplex.coordinateHomeomorph_apply, RealSimplex.coordinates,
      AffineSimplex.simplexRealizeMap_coe] using
      AffineSimplex.realize_mem_convexHull (fun i => RealSimplex.coordinates (w i)) a

theorem standardVertices_dist_le_one (n : ℕ) (i j : Fin (n + 1)) :
    dist (standardVertices n i) (standardVertices n j) ≤ 1 := by
  exact (Metric.dist_le_diam_of_mem
    (Convexity.StdSimplex.isBounded_range_toFun_comp_weights (Fin (n + 1)))
    (mem_range_self (standardVertices n i)) (mem_range_self (standardVertices n j))).trans
      (Convexity.StdSimplex.diam_range_toFun_comp_weights_subset_closedBall (Fin (n + 1)))

open Filter
open scoped Topology

theorem exists_iterated_subdivision_small_images
    {X I : Type} [TopologicalSpace X] (n : ℕ)
    (S : Finset C(StandardSimplex n, X)) (U : I → Set X)
    (hopen : ∀ i, IsOpen (U i)) (hcover : (univ : Set X) ⊆ ⋃ i, U i) :
    ∃ N : ℕ, ∀ k ≥ N, ∀ σ ∈ S,
      ∀ w ∈ ((subdivision (simplexCenters n) (n + 1))^[k]
        (generator (standardVertices n))).support,
      ∃ i, range (σ.comp (AffineSimplex.simplexRealizeMap w)) ⊆ U i := by
  obtain ⟨δ, hδ, hsmall⟩ := SingularSimplexLebesgue.exists_finite_reparametrization_radius
    S U hopen (fun _ _ => subset_trans (subset_univ _) hcover)
  have hr0 : (0 : ℝ) ≤ (n : ℝ) / (n + 1) := by positivity
  have hr1 : (n : ℝ) / (n + 1) < 1 := by
    apply (div_lt_one (by positivity)).2
    linarith
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hδ))
  refine ⟨N, ?_⟩
  intro k hk σ hσ w hw
  apply hsmall σ hσ (AffineSimplex.simplexRealizeMap w)
  intro x y
  have hdist := simplex_iterate_subdivision_realize_dist (standardVertices n) 1
    zero_le_one (standardVertices_dist_le_one n) k hw x y
  exact hdist.trans_lt (by simpa only [mul_one] using hN k hk)

end Problem340.SingularSubdivision

end

end OAI
