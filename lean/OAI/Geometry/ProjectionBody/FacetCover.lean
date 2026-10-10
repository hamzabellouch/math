import Mathlib.Data.Finset.Max
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace OAI

/-! Finite-halfspace geometry underlying the visible-facet projection formula. -/

noncomputable section
open Set

namespace ProjectionCounterexample

variable {ι V W : Type*} [Fintype ι]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- A finite intersection of closed halfspaces. -/
def halfspaceBody (a : ι → V →ₗ[ℝ] ℝ) (b : ι → ℝ) : Set V :=
  {x | ∀ i, a i x ≤ b i}

/-- The part of the body on the bounding hyperplane of inequality `i`. -/
def boundingFace (a : ι → V →ₗ[ℝ] ℝ) (b : ι → ℝ) (i : ι) : Set V :=
  {x | x ∈ halfspaceBody a b ∧ a i x = b i}

/-- Moving in a direction with a positive halfspace slope reaches a visible face. -/
theorem ray_reaches_visible_face (a : ι → V →ₗ[ℝ] ℝ) (b : ι → ℝ)
    {y u : V} (hy : y ∈ halfspaceBody a b) (hu : ∃ i, 0 < a i u) :
    ∃ (t : ℝ) (i : ι), 0 ≤ t ∧ 0 < a i u ∧
      y + t • u ∈ boundingFace a b i := by
  classical
  let s := Finset.univ.filter fun i => 0 < a i u
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := hu
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  obtain ⟨i, hi, hmin⟩ :=
    s.exists_min_image (fun j => (b j - a j y) / a j u) hs
  have hiu : 0 < a i u := (Finset.mem_filter.mp hi).2
  let t := (b i - a i y) / a i u
  have ht : 0 ≤ t := div_nonneg (sub_nonneg.mpr (hy i)) hiu.le
  refine ⟨t, i, ht, hiu, ?_, ?_⟩
  · intro j
    rw [map_add, map_smul, smul_eq_mul]
    by_cases hju : 0 < a j u
    · have hle : t ≤ (b j - a j y) / a j u :=
        hmin j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hju⟩)
      have := (le_div_iff₀ hju).mp hle
      linarith
    · have hm : t * a j u ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht (le_of_not_gt hju)
      have := hy j
      linarith
  · rw [map_add, map_smul, smul_eq_mul]
    have hm : t * a i u = b i - a i y := div_mul_cancel₀ _ (ne_of_gt hiu)
    linarith

/-- The projected body is covered by the projections of its visible faces. -/
theorem image_halfspaceBody_eq_visible_faces
    (a : ι → V →ₗ[ℝ] ℝ) (b : ι → ℝ) (q : V →ₗ[ℝ] W)
    {u : V} (hqu : q u = 0) (hu : ∃ i, 0 < a i u) :
    q '' halfspaceBody a b =
      ⋃ i : {i : ι // 0 < a i u}, q '' boundingFace a b i.1 := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨t, i, _, hiu, hface⟩ := ray_reaches_visible_face a b hy hu
    apply Set.mem_iUnion.mpr
    refine ⟨⟨i, hiu⟩, y + t • u, hface, ?_⟩
    simp [map_add, map_smul, hqu]
  · intro hx
    obtain ⟨i, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
    exact ⟨y, hy.1, rfl⟩

omit [Fintype ι] in
/-- Two visible boundary points on the same line parallel to the direction coincide.
This will put overlaps of projected visible faces in their common lower-dimensional face. -/
theorem visible_face_line_unique
    (a : ι → V →ₗ[ℝ] ℝ) (b : ι → ℝ)
    {i j : ι} {y z u : V} {t : ℝ}
    (hy : y ∈ boundingFace a b i) (hz : z ∈ boundingFace a b j)
    (hi : 0 < a i u) (hj : 0 < a j u) (hline : z = y + t • u) : z = y := by
  have hti : t * a i u ≤ 0 := by
    have h := hz.1 i
    rw [hline, map_add, map_smul, smul_eq_mul, hy.2] at h
    linarith
  have htj : 0 ≤ t * a j u := by
    have h := hy.1 j
    have he := hz.2
    rw [hline, map_add, map_smul, smul_eq_mul] at he
    linarith
  have ht0 : t = 0 := by nlinarith
  simpa [ht0] using hline

omit [Fintype ι] in
/-- Overlaps of visible-face shadows are precisely shadows of the face intersections. -/
theorem image_visible_faces_inter
    (a : ι → V →ₗ[ℝ] ℝ) (b : ι → ℝ) (q : V →ₗ[ℝ] W)
    {u : V} (hker : LinearMap.ker q = Submodule.span ℝ {u})
    {i j : ι} (hi : 0 < a i u) (hj : 0 < a j u) :
    (q '' boundingFace a b i) ∩ (q '' boundingFace a b j) =
      q '' (boundingFace a b i ∩ boundingFace a b j) := by
  apply Set.Subset.antisymm
  · rintro x ⟨⟨y, hy, hyq⟩, ⟨z, hz, hzq⟩⟩
    have hdiff : z - y ∈ Submodule.span ℝ {u} := by
      rw [← hker, LinearMap.mem_ker, map_sub, hyq, hzq, sub_self]
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hdiff
    have hline : z = y + t • u := by
      rw [ht]
      simp [sub_eq_add_neg]
    have hzy := visible_face_line_unique a b hy hz hi hj hline
    exact ⟨y, ⟨hy, hzy ▸ hz⟩, hyq⟩
  · exact Set.image_inter_subset q _ _

end ProjectionCounterexample

end

end OAI
