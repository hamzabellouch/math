import OAI.Analysis.CircleDomains.Selection.ShiftedStaircase
import OAI.Analysis.CircleDomains.Modulus.GridIncidence
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Order.Compact

namespace OAI

/-!
# Staircases are constant on collars avoiding their grids

A compact connected collar has a compact connected real branch image.
If this image misses the translated lattice, it has positive distance
from that closed lattice. Every sufficiently narrow staircase therefore
has zero derivative on the image and is constant on the collar. The
width bound can be chosen simultaneously for finitely many collars.
-/

open Set Filter Metric
open scoped Topology

namespace CircleDomainRigidity.FiniteTransfer

def shiftedLattice (h θ : ℝ) : Set ℝ := Set.range (fun k : ℤ => θ + h * k)

theorem isClosed_shiftedLattice {h : ℝ} (hh : 0 < h) (θ : ℝ) :
    IsClosed (shiftedLattice h θ) := by
  let : Fact (0 < h) := ⟨hh⟩
  have heq : shiftedLattice h θ =
      ((↑) : ℝ → AddCircle h) ⁻¹' {(θ : AddCircle h)} := by
    ext x
    simp only [shiftedLattice, mem_range, mem_preimage, mem_singleton_iff,
      addCircle_eq_iff_exists_int]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, by ring⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by rw [hk]; ring⟩
  rw [heq]
  exact isClosed_singleton.preimage (AddCircle.continuous_mk' h)

theorem exists_uniform_lattice_distance {h θ : ℝ} (hh : 0 < h)
    {E : Set ℝ} (hE : IsCompact E) (havoid : Disjoint E (shiftedLattice h θ)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ E, ∀ k : ℤ, ρ ≤ |x - (θ + h * k)| := by
  have hne : (shiftedLattice h θ).Nonempty := ⟨θ + h * (0 : ℤ), ⟨0, rfl⟩⟩
  obtain ⟨ρ, hρ, hdist⟩ := hE.exists_forall_le'
    (continuous_infDist_pt (shiftedLattice h θ)).continuousOn
    (fun x hx => ((isClosed_shiftedLattice hh θ).notMem_iff_infDist_pos hne).mp
      (fun hxL => Set.disjoint_left.mp havoid hx hxL))
  refine ⟨ρ, hρ, fun x hx k => (hdist x hx).trans ?_⟩
  simpa only [Real.dist_eq] using
    infDist_le_dist_of_mem (x := x) (show θ + h * k ∈ shiftedLattice h θ from ⟨k, rfl⟩)

/-- The same positive width bound works for the whole collar, and
the proof yields both derivative vanishing and constancy. -/
theorem eventually_constant_staircase_on_collar
    {X : Type*} [TopologicalSpace X] {C : Set X} (hC : IsCompact C)
    (hconn : IsPreconnected C) (u : X → ℝ) (hu : ContinuousOn u C)
    {h θ : ℝ} (hh : 0 < h) (havoid : Disjoint (u '' C) (shiftedLattice h θ)) :
    ∀ᶠ δ : ℝ in 𝓝[>] 0,
      (∀ x ∈ C, deriv (shiftedStaircase h δ θ) (u x) = 0) ∧
      ∀ x ∈ C, ∀ y ∈ C, shiftedStaircase h δ θ (u x) = shiftedStaircase h δ θ (u y) := by
  obtain ⟨ρ, hρ, hdist⟩ := exists_uniform_lattice_distance hh
    (hC.image_of_continuousOn hu) havoid
  have hδbound : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ ∧ δ < min ρ (h / 4) := by
    have hp : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ := self_mem_nhdsWithin
    exact hp.and
      ((eventually_lt_nhds (lt_min hρ (by positivity))).filter_mono nhdsWithin_le_nhds)
  filter_upwards [hδbound] with δ hδ
  have hδh : δ < h / 4 := hδ.2.trans_le (min_le_right _ _)
  have hzero : ∀ z ∈ u '' C, deriv (shiftedStaircase h δ θ) z = 0 := by
    intro z hz
    apply deriv_shiftedStaircase_eq_zero hh hδ.1 hδh
    intro k
    exact (hδ.2.trans_le (min_le_left _ _)).le.trans (hdist z hz k)
  refine ⟨fun x hx => hzero (u x) ⟨x, hx, rfl⟩, ?_⟩
  intro x hx y hy
  have hdiff := (contDiff_shiftedStaircase hh hδ.1 hδh θ).differentiable (by simp)
  have hbound := Convex.norm_image_sub_le_of_norm_deriv_le (C := 0)
    (fun z (_ : z ∈ u '' C) => hdiff z)
    (fun z hz => by simp only [hzero z hz, norm_zero, le_refl])
    (hconn.image u hu).ordConnected.convex ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
  have heq : shiftedStaircase h δ θ (u y) - shiftedStaircase h δ θ (u x) = 0 := by
    apply norm_eq_zero.mp
    exact le_antisymm (by simpa only [zero_mul] using hbound) (norm_nonneg _)
  exact (sub_eq_zero.mp heq).symm

/-- Finitely many inactive collars impose one common eventual width
condition; the grid choice and all collars stay fixed. -/
theorem eventually_constant_staircases_on_finite_collars
    {X I : Type*} [TopologicalSpace X] [Fintype I]
    (C : I → Set X) (hC : ∀ i, IsCompact (C i))
    (hconn : ∀ i, IsPreconnected (C i)) (u : I → X → ℝ)
    (hu : ∀ i, ContinuousOn (u i) (C i)) {h : ℝ} (hh : 0 < h) (θ : I → ℝ)
    (havoid : ∀ i, Disjoint (u i '' C i) (shiftedLattice h (θ i))) :
    ∀ᶠ δ : ℝ in 𝓝[>] 0, ∀ i, ∀ x ∈ C i, ∀ y ∈ C i,
      shiftedStaircase h δ (θ i) (u i x) = shiftedStaircase h δ (θ i) (u i y) := by
  apply eventually_all.mpr
  intro i
  exact (eventually_constant_staircase_on_collar (hC i) (hconn i)
    (u i) (hu i) hh (havoid i)).mono (fun _ hδ => hδ.2)

end CircleDomainRigidity.FiniteTransfer

end OAI
