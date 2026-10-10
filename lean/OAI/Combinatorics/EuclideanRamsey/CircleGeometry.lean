import OAI.Combinatorics.EuclideanRamsey.Model

namespace OAI

noncomputable section
namespace EuclideanRamsey.CircleConsequence

/-- Three points on a real circle cannot occupy three distinct parameters
on a secant. No positive-radius assumption is needed. -/
theorem circle_parameter_eq_zero_or_one
    (x₀ x₁ y₀ y₁ c₀ c₁ R t : ℝ)
    (hx : (x₀-c₀)^2 + (x₁-c₁)^2 = R)
    (hy : (y₀-c₀)^2 + (y₁-c₁)^2 = R)
    (hz : (x₀+t*(y₀-x₀)-c₀)^2 + (x₁+t*(y₁-x₁)-c₁)^2 = R)
    (hxy : x₀ ≠ y₀ ∨ x₁ ≠ y₁) : t = 0 ∨ t = 1 := by
  have hnorm : (y₀-x₀)^2 + (y₁-x₁)^2 ≠ 0 := by
    intro h
    have h₀ : y₀-x₀ = 0 := by nlinarith [sq_nonneg (y₁-x₁)]
    have h₁ : y₁-x₁ = 0 := by nlinarith [sq_nonneg (y₀-x₀)]
    rcases hxy with hxy | hxy <;> apply hxy <;> linarith
  have hprod : t * (t-1) * ((y₀-x₀)^2 + (y₁-x₁)^2) = 0 := by
    linear_combination hz - (1-t)*hx - t*hy
  rcases mul_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hnorm) with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

/-- The determinant of a secant line is nonzero at a third distinct
point on the same circle. Distinctness excludes radius zero. -/
theorem secant_nonzero
    (x₀ x₁ y₀ y₁ z₀ z₁ c₀ c₁ R : ℝ)
    (hx : (x₀-c₀)^2 + (x₁-c₁)^2 = R)
    (hy : (y₀-c₀)^2 + (y₁-c₁)^2 = R)
    (hz : (z₀-c₀)^2 + (z₁-c₁)^2 = R)
    (hxy : x₀ ≠ y₀ ∨ x₁ ≠ y₁)
    (hxz : x₀ ≠ z₀ ∨ x₁ ≠ z₁)
    (hyz : y₀ ≠ z₀ ∨ y₁ ≠ z₁) :
    (y₀-x₀)*(z₁-x₁) - (y₁-x₁)*(z₀-x₀) ≠ 0 := by
  intro hdet
  by_cases hdx : y₀-x₀ = 0
  · have hdy : y₁-x₁ ≠ 0 := by
      intro hdy
      rcases hxy with hxy | hxy <;> apply hxy <;> linarith
    have hzx : z₀ = x₀ := by
      have : (y₁-x₁)*(z₀-x₀) = 0 := by rw [hdx] at hdet; nlinarith
      have := (mul_eq_zero.mp this).resolve_left hdy
      linarith
    let t := (z₁-x₁)/(y₁-x₁)
    have ht : x₁+t*(y₁-x₁) = z₁ := by dsimp [t]; field_simp; ring
    have htx : x₀+t*(y₀-x₀) = z₀ := by rw [hdx]; simp [hzx]
    have he := circle_parameter_eq_zero_or_one x₀ x₁ y₀ y₁ c₀ c₁ R t hx hy
      (by rw [ht, htx]; exact hz) hxy
    rcases he with he | he
    · rcases hxz with h | h <;> apply h <;> simp_all
    · rcases hyz with h | h
      · apply h
        calc
          y₀ = x₀ := sub_eq_zero.mp hdx
          _ = z₀ := hzx.symm
      · apply h
        simpa [he] using ht
  · let t := (z₀-x₀)/(y₀-x₀)
    have ht : x₀+t*(y₀-x₀) = z₀ := by dsimp [t]; field_simp; ring
    have hty : x₁+t*(y₁-x₁) = z₁ := by
      dsimp [t]
      apply (mul_right_cancel₀ hdx)
      field_simp
      nlinarith [hdet]
    have he := circle_parameter_eq_zero_or_one x₀ x₁ y₀ y₁ c₀ c₁ R t hx hy
      (by rw [ht, hty]; exact hz) hxy
    rcases he with he | he
    · rcases hxz with h | h <;> apply h <;> simp_all
    · rcases hyz with h | h <;> apply h <;> simp_all

/-- Restriction of a Ramsey configuration preserves its distances. -/
theorem ramsey_restrict {s t d : ℕ} (a : Fin t → Space d)
    (f : Fin s → Fin t) (ha : Ramsey a) : Ramsey (a ∘ f) := by
  intro r hr
  obtain ⟨D, hD, h⟩ := ha r hr
  refine ⟨D, hD, ?_⟩
  intro c
  obtain ⟨b, hb, k, hk⟩ := h c
  exact ⟨b ∘ f, fun i j => hb (f i) (f j), k, fun i => hk (f i)⟩

/-- A circle of zero radius is a singleton; repeated labels are allowed. -/
theorem zero_radius_ramsey {s : ℕ} (a : Fin s → Space 2)
    (c : Space 2) (h : ∀ i, dist (a i) c = 0) : Ramsey a := by
  intro r hr
  refine ⟨1, by omega, ?_⟩
  intro coloring
  refine ⟨fun _ => 0, ?_, coloring 0, fun _ => rfl⟩
  intro i j
  have hi : a i = c := dist_eq_zero.mp (h i)
  have hj : a j = c := dist_eq_zero.mp (h j)
  simp [hi, hj]

/-- The metric circle equation implies the scalar coordinate equation. -/
theorem circle_coordinates {s : ℕ} (a : Fin s → Space 2)
    (c : Space 2) (r : ℝ) (hc : ∀ i, dist (a i) c = r) :
    ∀ i, (a i 0-c 0)^2 + (a i 1-c 1)^2 = r^2 := by
  intro i
  have h := congrArg (fun x : ℝ => x^2) (hc i)
  simpa [dist_eq_norm, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two,
    Real.norm_eq_abs, sq_abs] using h

end EuclideanRamsey.CircleConsequence

end

end OAI
