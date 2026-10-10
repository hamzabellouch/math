import OAI.Geometry.SingularHomology.SimplexCoordinates
import Mathlib.AlgebraicTopology.SingularSet
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

noncomputable section

open Set Filter
open scoped Topology

namespace Problem340.SingularSimplexLebesgue

variable {D X I : Type*} [PseudoMetricSpace D] [CompactSpace D]
  [TopologicalSpace X]

theorem exists_small_image_radius (f : C(D, X)) (U : I → Set X)
    (hopen : ∀ i, IsOpen (U i)) (hcover : range f ⊆ ⋃ i, U i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : Set D, s.Nonempty →
      (∀ x ∈ s, ∀ y ∈ s, dist x y < δ) →
      ∃ i, f '' s ⊆ U i := by
  have hpre : (univ : Set D) ⊆ ⋃ i, f ⁻¹' U i := by
    intro x _
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover (mem_range_self x))
    exact mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric
    isCompact_univ (fun i => (hopen i).preimage f.continuous) hpre
  refine ⟨δ, hδ, ?_⟩
  intro s hs hsmall
  obtain ⟨x, hx⟩ := hs
  obtain ⟨i, hi⟩ := hball x (mem_univ x)
  refine ⟨i, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact hi (show y ∈ Metric.ball x δ from hsmall y hy x hx)

theorem exists_finite_small_image_radius (S : Finset C(D, X)) (U : I → Set X)
    (hopen : ∀ i, IsOpen (U i))
    (hcover : ∀ f ∈ S, range f ⊆ ⋃ i, U i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f ∈ S, ∀ s : Set D, s.Nonempty →
      (∀ x ∈ s, ∀ y ∈ s, dist x y < δ) →
      ∃ i, f '' s ⊆ U i := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      exact ⟨1, zero_lt_one, by simp⟩
  | @insert f S hf ih =>
      obtain ⟨δf, hδf, hsmallf⟩ := exists_small_image_radius f U hopen
        (hcover f (Finset.mem_insert_self f S))
      obtain ⟨δS, hδS, hsmallS⟩ := ih (fun g hg => hcover g (Finset.mem_insert_of_mem hg))
      refine ⟨min δf δS, lt_min hδf hδS, ?_⟩
      intro g hg s hs hsmall
      rcases Finset.mem_insert.mp hg with rfl | hg
      · exact hsmallf s hs (fun x hx y hy =>
          lt_of_lt_of_le (hsmall x hx y hy) (min_le_left _ _))
      · exact hsmallS g hg s hs (fun x hx y hy =>
          lt_of_lt_of_le (hsmall x hx y hy) (min_le_right _ _))

theorem exists_finite_reparametrization_radius (S : Finset C(D, X)) (U : I → Set X)
    (hopen : ∀ i, IsOpen (U i))
    (hcover : ∀ f ∈ S, range f ⊆ ⋃ i, U i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f ∈ S, ∀ {A : Type*} [Nonempty A] (ρ : A → D),
      (∀ x y, dist (ρ x) (ρ y) < δ) →
      ∃ i, range (f ∘ ρ) ⊆ U i := by
  obtain ⟨δ, hδ, hsmall⟩ := exists_finite_small_image_radius S U hopen hcover
  refine ⟨δ, hδ, ?_⟩
  intro f hf A _ ρ hρ
  obtain ⟨i, hi⟩ := hsmall f hf (range ρ) (range_nonempty ρ) (by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact hρ x y)
  exact ⟨i, by simpa only [range_comp] using hi⟩

theorem eventually_small_images_of_mesh_tendsto_zero
    (S : Finset C(D, X)) (U : I → Set X)
    (hopen : ∀ i, IsOpen (U i))
    (hcover : ∀ f ∈ S, range f ⊆ ⋃ i, U i)
    (cells : ℕ → Set (Set D)) (mesh : ℕ → ℝ)
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hdiam : ∀ k, ∀ s ∈ cells k, ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ mesh k) :
    ∀ᶠ k in atTop, ∀ f ∈ S, ∀ s ∈ cells k, s.Nonempty →
      ∃ i, f '' s ⊆ U i := by
  obtain ⟨δ, hδ, hsmall⟩ := exists_finite_small_image_radius S U hopen hcover
  filter_upwards [hmesh.eventually (gt_mem_nhds hδ)] with k hk
  intro f hf s hs hne
  exact hsmall f hf s hne (fun x hx y hy => (hdiam k s hs x hx y hy).trans_lt hk)

theorem exists_small_image_stage_of_geometric_mesh
    (S : Finset C(D, X)) (U : I → Set X)
    (hopen : ∀ i, IsOpen (U i))
    (hcover : ∀ f ∈ S, range f ⊆ ⋃ i, U i)
    (cells : ℕ → Set (Set D)) (C r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hdiam : ∀ k, ∀ s ∈ cells k, ∀ x ∈ s, ∀ y ∈ s,
      dist x y ≤ C * r ^ k) :
    ∃ N : ℕ, ∀ k ≥ N, ∀ f ∈ S, ∀ s ∈ cells k, s.Nonempty →
      ∃ i, f '' s ⊆ U i := by
  apply eventually_atTop.mp
  apply eventually_small_images_of_mesh_tendsto_zero S U hopen hcover cells
    (fun k => C * r ^ k) _ hdiam
  simpa only [mul_zero] using
    (tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1))

end Problem340.SingularSimplexLebesgue

namespace Problem340.SingularSimplexLebesgue

open CategoryTheory Opposite
open scoped Simplicial

variable {X I : Type} [TopologicalSpace X]

theorem exists_singular_reparametrization_radius (n : ℕ)
    (S : Finset ((TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋n⦌)))
    (U : I → Set X) (hopen : ∀ i, IsOpen (U i))
    (hcover : (univ : Set X) ⊆ ⋃ i, U i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ σ ∈ S,
      ∀ {A : Type*} [Nonempty A] (ρ : A → Convexity.StdSimplex ℝ (Fin (n + 1))),
      (∀ x y, dist (ρ x) (ρ y) < δ) →
      ∃ i, range ((TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋n⦌) σ) ∘ ρ) ⊆ U i := by
  classical
  let e := TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋n⦌)
  obtain ⟨δ, hδ, hsmall⟩ := exists_finite_reparametrization_radius (S.image e) U hopen
    (fun _ _ => subset_trans (subset_univ _) hcover)
  refine ⟨δ, hδ, ?_⟩
  intro σ hσ A _ ρ hρ
  exact hsmall (e σ) (Finset.mem_image.mpr ⟨σ, hσ, rfl⟩) ρ hρ

end Problem340.SingularSimplexLebesgue

end

end OAI
