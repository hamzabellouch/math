import Mathlib
import OAI.Geometry.Borsuk.Projectors.Tangent
import OAI.Geometry.Borsuk.Counterexample

namespace OAI

open Set MeasureTheory
namespace BorsukNine

abbrev Vector9 := EuclideanSpace ℝ (Fin 9)

noncomputable def coordinates9 (A : Matrix4) : Vector9 :=
  WithLp.toLp 2 ![(A (0, 0) - A (1, 1)) / Real.sqrt 2,
    (A (0, 0) + A (1, 1) - 2 * A (2, 2)) / Real.sqrt 6,
    (A (0, 0) + A (1, 1) + A (2, 2) - 3 * A (3, 3)) / Real.sqrt 12,
    Real.sqrt 2 * A (0, 1), Real.sqrt 2 * A (0, 2), Real.sqrt 2 * A (0, 3),
    Real.sqrt 2 * A (1, 2), Real.sqrt 2 * A (1, 3), Real.sqrt 2 * A (2, 3)]

theorem coordinates9_sub (A B : Matrix4) :
    coordinates9 (A - B) = coordinates9 A - coordinates9 B := by
  ext i
  fin_cases i <;> simp [coordinates9] <;> ring

theorem coordinates9_norm_sq (A : Matrix4)
    (hA : ∀ i j : Fin 4, A (i, j) = A (j, i))
    (htr : ∑ i : Fin 4, A (i, i) = 0) :
    ‖coordinates9 A‖ ^ 2 = ‖A‖ ^ 2 := by
  have h2 : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have h6 : (Real.sqrt 6) ^ 2 = (6 : ℝ) := Real.sq_sqrt (by norm_num)
  have h12 : (Real.sqrt 12) ^ 2 = (12 : ℝ) := Real.sq_sqrt (by norm_num)
  have h33 : A (3, 3) = -A (0, 0) - A (1, 1) - A (2, 2) := by
    norm_num [Fin.sum_univ_succ] at htr
    change A (0, 0) + (A (1, 1) + (A (2, 2) + A (3, 3))) = 0 at htr
    linarith
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp [coordinates9, Fintype.sum_prod_type, Fin.sum_univ_succ, div_pow, mul_pow,
    h2, h6, h12, hA 1 0, hA 2 0, hA 3 0, hA 2 1, hA 3 1, hA 3 2, h33]
  ring

theorem coordinates9_dist (A B : Matrix4)
    (hA : A ∈ traceOneSymmetric) (hB : B ∈ traceOneSymmetric) :
    dist (coordinates9 A) (coordinates9 B) = dist A B := by
  have hs : ∀ i j : Fin 4, (A - B) (i, j) = (A - B) (j, i) := by
    intro i j
    change A (i, j) - B (i, j) = A (j, i) - B (j, i)
    rw [hA.1 i j, hB.1 i j]
  have ht : ∑ i : Fin 4, (A - B) (i, i) = 0 := by
    change (∑ i : Fin 4, (A (i, i) - B (i, i))) = 0
    rw [Finset.sum_sub_distrib, hA.2, hB.2, sub_self]
  have hn := coordinates9_norm_sq (A - B) hs ht
  rw [coordinates9_sub] at hn
  rw [dist_eq_norm, dist_eq_norm]
  nlinarith [norm_nonneg (coordinates9 A - coordinates9 B), norm_nonneg (A - B)]

theorem coordinates9_isometry :
    Isometry (fun A : traceOneSymmetric => coordinates9 A.val) :=
  Isometry.of_dist_eq fun A B => coordinates9_dist A B A.property B.property

theorem continuous_coordinates9 : Continuous coordinates9 := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  fin_cases i <;> simp <;> fun_prop

theorem coordinates9_diam (S : Set Matrix4) (hS : S ⊆ traceOneSymmetric) :
    Metric.diam (coordinates9 '' S) = Metric.diam S := by
  let f : S → Vector9 := fun A => coordinates9 A.val
  have hf : Isometry f := Isometry.of_dist_eq fun A B =>
    coordinates9_dist A B (hS A.property) (hS B.property)
  have hr : Set.range f = coordinates9 '' S := by
    ext x
    constructor
    · rintro ⟨A, rfl⟩
      exact ⟨A.val, A.property, rfl⟩
    · rintro ⟨A, hA, rfl⟩
      exact ⟨⟨A, hA⟩, rfl⟩
  have hi : Isometry (fun A : S => (A : Matrix4)) := isometry_subtype_coe
  have hs : Set.range (fun A : S => (A : Matrix4)) = S := by
    ext x
    constructor
    · rintro ⟨A, rfl⟩
      exact A.property
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  calc
    Metric.diam (coordinates9 '' S) = Metric.diam (Set.range f) := by rw [hr]
    _ = Metric.diam (Set.univ : Set S) := hf.diam_range
    _ = Metric.diam (Set.range (fun A : S => (A : Matrix4))) := hi.diam_range.symm
    _ = Metric.diam S := by rw [hs]

theorem coordinates9_cover_pullback (S : Set Matrix4) (hS : S ⊆ traceOneSymmetric)
    (C : Fin 10 → Set Vector9) (hC : ∀ i, C i ⊆ coordinates9 '' S)
    (hcover : coordinates9 '' S ⊆ ⋃ i, C i)
    (hdiam : ∀ i, Metric.diam (C i) < Real.sqrt 2) :
    ∃ D : Fin 10 → Set Matrix4,
      (∀ i, D i ⊆ S) ∧ S ⊆ ⋃ i, D i ∧
      ∀ i, Metric.diam (D i) < Real.sqrt 2 := by
  let D : Fin 10 → Set Matrix4 := fun i => {A | A ∈ S ∧ coordinates9 A ∈ C i}
  have him : ∀ i, coordinates9 '' D i = C i := by
    intro i
    ext x
    constructor
    · rintro ⟨A, hA, rfl⟩
      exact hA.2
    · intro hx
      obtain ⟨A, hA, rfl⟩ := hC i hx
      exact ⟨A, ⟨hA, hx⟩, rfl⟩
  refine ⟨D, fun _ _ h => h.1, ?_, ?_⟩
  · intro A hA
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover ⟨A, hA, rfl⟩)
    exact Set.mem_iUnion.mpr ⟨i, hA, hi⟩
  · intro i
    have hD : D i ⊆ traceOneSymmetric := fun _ h => hS h.1
    rw [← coordinates9_diam (D i) hD, him i]
    exact hdiam i

theorem euclidean_nine_counterexample :
    ∃ X : Set (EuclideanSpace ℝ (Fin 9)),
      IsCompact X ∧ Metric.diam X = Real.sqrt 2 ∧
      ¬ (∃ C : Fin 10 → Set (EuclideanSpace ℝ (Fin 9)),
        (∀ i, C i ⊆ X) ∧ X ⊆ ⋃ i, C i ∧
        ∀ i, Metric.diam (C i) < Real.sqrt 2) := by
  obtain ⟨hcompact, htrace, hdiam, hnocover⟩ := main_theorem
  refine ⟨coordinates9 '' projectorSet, hcompact.image continuous_coordinates9, ?_, ?_⟩
  · rw [coordinates9_diam projectorSet htrace, hdiam]
  · rintro ⟨C, hC, hcover, hsmall⟩
    exact hnocover (coordinates9_cover_pullback projectorSet htrace C hC hcover hsmall)

end BorsukNine

end OAI
