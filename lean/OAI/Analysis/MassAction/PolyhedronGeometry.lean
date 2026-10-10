import OAI.Analysis.MassAction.Model
import OAI.Analysis.MassAction.PlateauGeometry

namespace OAI

universe uIota

noncomputable section
namespace Problem326
variable {d : ℕ}

lemma continuous_dot (a : Fin d → ℝ) : Continuous (dot a) := by
  unfold dot
  fun_prop

lemma dot_add_right (a x y : Fin d → ℝ) : dot a (x + y) = dot a x + dot a y := by
  simp [dot, mul_add, Finset.sum_add_distrib]

lemma dot_smul_right (a x : Fin d → ℝ) (c : ℝ) : dot a (c • x) = c * dot a x := by
  simp [dot, Finset.mul_sum, mul_left_comm]

lemma dot_isLinearMap (a : Fin d → ℝ) : IsLinearMap ℝ (dot a) := by
  constructor
  · exact dot_add_right a
  · intro c x
    exact dot_smul_right a x c

lemma IsFinitePolyhedron.isClosed {K : Set (Fin d → ℝ)}
    (hK : IsFinitePolyhedron K) : IsClosed K := by
  rcases hK with ⟨n, a, b, rfl⟩
  have heq : {x | ∀ j, b j ≤ dot (a j) x} =
      ⋂ j, {x | b j ≤ dot (a j) x} := by ext x; simp
  rw [heq]
  exact isClosed_iInter fun j => isClosed_le continuous_const (continuous_dot (a j))

lemma IsFinitePolyhedron.convex {K : Set (Fin d → ℝ)}
    (hK : IsFinitePolyhedron K) : Convex ℝ K := by
  rcases hK with ⟨n, a, b, rfl⟩
  have heq : {x | ∀ j, b j ≤ dot (a j) x} =
      ⋂ j, {x | b j ≤ dot (a j) x} := by ext x; simp
  rw [heq]
  exact convex_iInter fun j => convex_halfSpace_ge (dot_isLinearMap (a j)) (b j)

lemma finiteAffine_superlevel_isFinitePolyhedron {ι : Type uIota} [Fintype ι]
    (a : ι → (Fin d → ℝ)) (c : ι → ℝ) (M : ℝ) :
    IsFinitePolyhedron {x | ∀ j, M ≤ dot (a j) x + c j} := by
  classical
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, (fun j => a (e.symm j)),
    (fun j => M - c (e.symm j)), ?_⟩
  ext x
  constructor
  · intro h j
    have := h (e.symm j)
    linarith
  · intro h j
    have hj := h (e j)
    simp only [Equiv.symm_apply_apply] at hj
    linarith

lemma finiteAffine_superlevel_isClosed {ι : Type uIota} [Fintype ι]
    (a : ι → (Fin d → ℝ)) (c : ι → ℝ) (M : ℝ) :
    IsClosed {x | ∀ j, M ≤ dot (a j) x + c j} :=
  (finiteAffine_superlevel_isFinitePolyhedron a c M).isClosed

lemma finiteAffine_superlevel_convex {ι : Type uIota} [Fintype ι]
    (a : ι → (Fin d → ℝ)) (c : ι → ℝ) (M : ℝ) :
    Convex ℝ {x | ∀ j, M ≤ dot (a j) x + c j} :=
  (finiteAffine_superlevel_isFinitePolyhedron a c M).convex

/-- A capped finite lower envelope has a polyhedral maximum set.
This interface is independent of the choice of finite-minimum notation. -/
lemma finiteAffine_plateau_eq {ι : Type uIota}
    (a : ι → (Fin d → ℝ)) (c : ι → ℝ) (F : (Fin d → ℝ) → ℝ) (M : ℝ)
    (hlower : ∀ x j, F x ≤ dot (a j) x + c j)
    (hattained : ∀ x, ∃ j, F x = dot (a j) x + c j)
    (hceiling : ∀ x, F x ≤ M) :
    {x | F x = M} = {x | ∀ j, M ≤ dot (a j) x + c j} := by
  ext x
  constructor
  · intro hx j
    change F x = M at hx
    simpa only [hx] using hlower x j
  · intro hx
    obtain ⟨j, hj⟩ := hattained x
    exact le_antisymm (hceiling x) (by simpa only [hj] using hx j)

lemma finiteAffine_plateau_isFinitePolyhedron {ι : Type uIota} [Fintype ι]
    (a : ι → (Fin d → ℝ)) (c : ι → ℝ) (F : (Fin d → ℝ) → ℝ) (M : ℝ)
    (hlower : ∀ x j, F x ≤ dot (a j) x + c j)
    (hattained : ∀ x, ∃ j, F x = dot (a j) x + c j)
    (hceiling : ∀ x, F x ≤ M) :
    IsFinitePolyhedron {x | F x = M} := by
  rw [finiteAffine_plateau_eq a c F M hlower hattained hceiling]
  exact finiteAffine_superlevel_isFinitePolyhedron a c M

/-- Finite affine barriers which exclude the boundary of a compact set
produce a compact convex polyhedron in its interior. -/
lemma compact_polyhedron_of_affine_barriers {ι : Type uIota} [Fintype ι]
    (a : ι → (Fin d → ℝ)) (c : ι → ℝ) (M : ℝ)
    (B : Set (Fin d → ℝ)) (x0 : Fin d → ℝ)
    (hB : IsCompact B) (hx0B : x0 ∈ interior B)
    (hx0 : ∀ j, M ≤ dot (a j) x0 + c j)
    (hboundary : ∀ x ∈ frontier B, ∃ j, dot (a j) x + c j < M) :
    ∃ K : Set (Fin d → ℝ), IsCompact K ∧ Convex ℝ K ∧
      IsFinitePolyhedron K ∧ x0 ∈ K ∧ K ⊆ interior B ∧
      ∀ x, x ∈ K ↔ ∀ j, M ≤ dot (a j) x + c j := by
  let K : Set (Fin d → ℝ) := {x | ∀ j, M ≤ dot (a j) x + c j}
  have hpoly : IsFinitePolyhedron K := finiteAffine_superlevel_isFinitePolyhedron a c M
  have hconv : Convex ℝ K := hpoly.convex
  have hdisjoint : Disjoint K (frontier B) := by
    rw [Set.disjoint_left]
    intro x hx hxB
    obtain ⟨j, hj⟩ := hboundary x hxB
    exact (not_lt_of_ge (hx j)) hj
  have hmeet : (K ∩ interior B).Nonempty := ⟨x0, hx0, hx0B⟩
  have hsub : K ⊆ interior B :=
    Geometry.subset_interior_of_disjoint_frontier hconv.isPreconnected hmeet hdisjoint
  have hcompact : IsCompact K :=
    hB.of_isClosed_subset hpoly.isClosed (hsub.trans interior_subset)
  exact ⟨K, hcompact, hconv, hpoly, hx0, hsub, fun _ => Iff.rfl⟩

/-- A zero slope active at the initial point supplies the ceiling level.
Excluding zero active slopes on the boundary gives all geometric conclusions. -/
lemma compact_polyhedron_of_zero_active_slope {ι : Type uIota} [Fintype ι]
    (a : ι → (Fin d → ℝ)) (c : ι → ℝ) (j0 : ι)
    (B : Set (Fin d → ℝ)) (x0 : Fin d → ℝ)
    (hB : IsCompact B) (hx0B : x0 ∈ interior B)
    (hzero : a j0 = 0)
    (hactive0 : ∀ j, dot (a j0) x0 + c j0 ≤ dot (a j) x0 + c j)
    (hboundary : ∀ x ∈ frontier B, ∀ j,
      (∀ k, dot (a j) x + c j ≤ dot (a k) x + c k) → a j ≠ 0) :
    ∃ K : Set (Fin d → ℝ), IsCompact K ∧ Convex ℝ K ∧
      IsFinitePolyhedron K ∧ x0 ∈ K ∧ K ⊆ interior B ∧
      ∀ x, x ∈ K ↔ ∀ j, c j0 ≤ dot (a j) x + c j := by
  apply compact_polyhedron_of_affine_barriers a c (c j0) B x0 hB hx0B
  · intro j
    simpa only [hzero, dot, Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add]
      using hactive0 j
  · intro x hxB
    classical
    by_contra hnot
    push Not at hnot
    have hj0active : ∀ k, dot (a j0) x + c j0 ≤ dot (a k) x + c k := by
      intro k
      simpa only [hzero, dot, Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add]
        using hnot k
    exact hboundary x hxB j0 hj0active hzero

end Problem326

end

end OAI
