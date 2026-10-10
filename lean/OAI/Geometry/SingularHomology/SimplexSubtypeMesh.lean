import OAI.Geometry.SingularHomology.SimplexCoordinates
import OAI.Geometry.SingularHomology.SimplexSubdivisionMesh
import OAI.Geometry.SingularHomology.SingularSimplexLebesgue

namespace OAI

noncomputable section

open Set Filter
open scoped Topology

namespace Problem340.SimplexSubtypeMesh

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem dist_le_of_convex_carrier {ι A : Type*} {s : Set E}
    (v : ι → E) (ρ : A → s) (D : ℝ)
    (hvertices : ∀ i j, dist (v i) (v j) ≤ D)
    (hcarrier : ∀ a, (ρ a).val ∈ convexHull ℝ (range v))
    (a b : A) : dist (ρ a) (ρ b) ≤ D := by
  obtain ⟨x, ⟨i, rfl⟩, y, ⟨j, rfl⟩, h⟩ :=
    convexHull_exists_dist_ge2 (hcarrier a) (hcarrier b)
  exact h.trans (hvertices i j)

theorem diam_range_le_of_convex_carrier {ι A : Type*} {s : Set E}
    (v : ι → E) (ρ : A → s) (D : ℝ) (hD : 0 ≤ D)
    (hvertices : ∀ i j, dist (v i) (v j) ≤ D)
    (hcarrier : ∀ a, (ρ a).val ∈ convexHull ℝ (range v)) :
    Metric.diam (range ρ) ≤ D := by
  apply Metric.diam_le_of_forall_dist_le hD
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  exact dist_le_of_convex_carrier v ρ D hvertices hcarrier a b

theorem dist_le_of_nested_face_carrier {ι κ A : Type*} [DecidableEq ι]
    {s : Set E} (v : ι → E) (t : Finset ι) (faces : κ → Finset ι)
    (hne : ∀ k, (faces k).Nonempty) (hsub : ∀ k, faces k ⊆ t)
    (hchain : ∀ k l, faces k ⊆ faces l ∨ faces l ⊆ faces k)
    (n : ℕ) (hcard : t.card ≤ n + 1) (D : ℝ) (hD : 0 ≤ D)
    (hvertices : ∀ i ∈ t, ∀ j ∈ t, dist (v i) (v j) ≤ D)
    (ρ : A → s)
    (hcarrier : ∀ a, (ρ a).val ∈ convexHull ℝ
      (range (fun k => SimplexSubdivision.faceCenter v (faces k))))
    (a b : A) : dist (ρ a) (ρ b) ≤ (n : ℝ) / (n + 1) * D := by
  apply dist_le_of_convex_carrier _ ρ _ _ hcarrier a b
  intro k l
  rcases hchain k l with hkl | hlk
  · exact SimplexSubdivision.dist_faceCenter_nested_le_mesh v (hne k) hkl n
      ((Finset.card_le_card (hsub l)).trans hcard) D hD
      (fun i hi j hj => hvertices i (hsub l hi) j (hsub l hj))
  · rw [dist_comm]
    exact SimplexSubdivision.dist_faceCenter_nested_le_mesh v (hne l) hlk n
      ((Finset.card_le_card (hsub k)).trans hcard) D hD
      (fun i hi j hj => hvertices i (hsub k hi) j (hsub k hj))

open CategoryTheory Opposite
open scoped Simplicial

theorem exists_singular_small_stage_of_convex_mesh
    {X I A ι : Type} [TopologicalSpace X] [Nonempty A]
    (n : ℕ) (K : ℕ → Type)
    (S : Finset ((TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋n⦌)))
    (U : I → Set X) (hopen : ∀ i, IsOpen (U i))
    (hcover : (univ : Set X) ⊆ ⋃ i, U i)
    (v : ∀ k, K k → ι → (Fin (n + 1) → ℝ))
    (ρ : ∀ k, K k → A → Convexity.StdSimplex ℝ (Fin (n + 1)))
    (hcarrier : ∀ k c a, RealSimplex.coordinates (ρ k c a) ∈ convexHull ℝ (range (v k c)))
    (C r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hmesh : ∀ k c i j, dist (v k c i) (v k c j) ≤ C * r ^ k) :
    ∃ N : ℕ, ∀ k ≥ N, ∀ σ ∈ S, ∀ c : K k,
      ∃ i, range ((TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋n⦌) σ) ∘ ρ k c) ⊆ U i := by
  obtain ⟨δ, hδ, hsmall⟩ :=
    SingularSimplexLebesgue.exists_singular_reparametrization_radius n S U hopen hcover
  have hlim : Tendsto (fun k : ℕ => C * r ^ k) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hδ))
  refine ⟨N, ?_⟩
  intro k hk σ hσ c
  apply hsmall σ hσ (ρ k c)
  intro a b
  exact (dist_le_of_convex_carrier (v k c)
    (fun point => RealSimplex.coordinateHomeomorph (ρ k c point)) (C * r ^ k)
    (hmesh k c) (hcarrier k c) a b).trans_lt (hN k hk)

end Problem340.SimplexSubtypeMesh

end

end OAI
