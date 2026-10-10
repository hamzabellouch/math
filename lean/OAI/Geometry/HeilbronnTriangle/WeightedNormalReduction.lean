import OAI.Geometry.HeilbronnTriangle.PrimitiveNormal

namespace OAI


namespace Problem355.PrimitiveNormal

open Matrix
open scoped Matrix BigOperators

noncomputable def normalBox (X : ℤ) : Finset Vector := by
  classical
  exact (Finset.Icc (fun _ => -(2 * X ^ 2)) (fun _ => 2 * X ^ 2)).filter
    (fun w => IsPrimitive w ∧ ∀ i, w i ≠ 0)

lemma mem_normalBox (X : ℤ) (w : Vector) : w ∈ normalBox X ↔
    IsPrimitive w ∧ (∀ i, w i ≠ 0) ∧ (∀ i, |w i| ≤ 2 * X ^ 2) := by
  simp only [normalBox, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, hp, hn⟩
    exact ⟨hp, hn, fun i => abs_le.mpr ⟨hlo i, hhi i⟩⟩
  · rintro ⟨hp, hn, hb⟩
    exact ⟨⟨fun i => (abs_le.mp (hb i)).1, fun i => (abs_le.mp (hb i)).2⟩, hp, hn⟩

lemma normalBox_norm_bounds {X : ℤ} {w : Vector} (hw : w ∈ normalBox X) :
    1 ≤ ‖toEuclidean w‖ ∧ ‖toEuclidean w‖ ≤ 6 * (X : ℝ) ^ 2 := by
  obtain ⟨hp, _, hb⟩ := (mem_normalBox X w).mp hw
  refine ⟨one_le_norm_of_ne_zero w hp.ne_zero, ?_⟩
  have h := norm_le_three_mul_of_coordinate_bound w (2 * (X : ℝ) ^ 2)
    (by positivity) (fun i => by exact_mod_cast hb i)
  nlinarith

lemma exists_normalBox_kernel (A : Matrix (Fin 3) (Fin 3) ℤ)
    (hdet : A.det = 0) (hheight : ∀ i, A 2 i ≠ 0)
    (hproj : ∀ i j : Fin 3, i ≠ j →
      ((A 0 i : ℝ) / A 2 i, (A 1 i : ℝ) / A 2 i) ≠
      ((A 0 j : ℝ) / A 2 j, (A 1 j : ℝ) / A 2 j))
    (X : ℤ) (hX : 0 ≤ X) (hbound : ∀ i j, |A i j| ≤ X) :
    ∃ w ∈ normalBox X, A *ᵥ w = 0 := by
  obtain ⟨w, hp, hk, hn, hb⟩ :=
    exists_primitive_right_null_of_projections A hdet hheight hproj X hX hbound
  exact ⟨w, (mem_normalBox X w).mpr ⟨hp, hn, hb⟩, hk⟩

theorem weighted_count_le_sum_normal_fibers
    (S : Finset (Matrix (Fin 3) (Fin 3) ℤ))
    (W : Matrix (Fin 3) (Fin 3) ℤ → ℝ) (hW : ∀ A ∈ S, 0 ≤ W A)
    (hdet : ∀ A ∈ S, A.det = 0) (hheight : ∀ A ∈ S, ∀ i, A 2 i ≠ 0)
    (hproj : ∀ A ∈ S, ∀ i j : Fin 3, i ≠ j →
      ((A 0 i : ℝ) / A 2 i, (A 1 i : ℝ) / A 2 i) ≠
      ((A 0 j : ℝ) / A 2 j, (A 1 j : ℝ) / A 2 j))
    (X : ℤ) (hX : 0 ≤ X) (hbound : ∀ A ∈ S, ∀ i j, |A i j| ≤ X) :
    (∑ A ∈ S, W A) ≤
      ∑ w ∈ normalBox X, ∑ A ∈ S.filter (fun A => A *ᵥ w = 0), W A := by
  classical
  calc
    (∑ A ∈ S, W A) ≤ ∑ A ∈ S, ∑ w ∈ normalBox X,
        if A *ᵥ w = 0 then W A else 0 := by
      apply Finset.sum_le_sum
      intro A hA
      obtain ⟨w, hw, hk⟩ := exists_normalBox_kernel A (hdet A hA) (hheight A hA)
        (hproj A hA) X hX (hbound A hA)
      have hs := Finset.single_le_sum (s := normalBox X)
        (f := fun w => if A *ᵥ w = 0 then W A else 0)
        (fun x hx => by split_ifs <;> first | exact hW A hA | rfl) hw
      simpa [hk] using hs
    _ = ∑ w ∈ normalBox X, ∑ A ∈ S.filter (fun A => A *ᵥ w = 0), W A := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro w hw
      rw [Finset.sum_filter]

end Problem355.PrimitiveNormal

end OAI
