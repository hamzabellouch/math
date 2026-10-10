import OAI.Combinatorics.EuclideanRamsey.CircleInterpolation

namespace OAI
noncomputable section
namespace EuclideanRamsey.CircleConsequence

/-- Three actual distinct circle points already affinely span the plane.
The inverse two-by-two determinant is written explicitly. -/
theorem circle_five_affineSpan (a : Fin 5 → Space 2)
    (ha : Function.Injective a) (c : Space 2) (r : ℝ)
    (hc : ∀ i, dist (a i) c = r) : affineSpan ℝ (Set.range a) = ⊤ := by
  classical
  let A := affineSpan ℝ (Set.range a)
  have hp (i : Fin 5) : a i ∈ A := mem_affineSpan ℝ (Set.mem_range_self i)
  let u := a 1 - a 0
  let v := a 2 - a 0
  let D : ℝ := u 0 * v 1 - v 0 * u 1
  have hfield := secantValue_ne_zero a ha c (r^2) (circle_coordinates a c r hc)
    0 1 2 (by decide) (by decide) (by decide)
  have hD : D ≠ 0 := by
    intro h
    apply hfield
    apply Subtype.ext
    simpa [D, u, v, secantValue, coordinate, mul_comm] using h
  have hu : u ∈ A.direction := by
    simpa [u, vsub_eq_sub] using AffineSubspace.vsub_mem_direction (hp 1) (hp 0)
  have hv : v ∈ A.direction := by
    simpa [v, vsub_eq_sub] using AffineSubspace.vsub_mem_direction (hp 2) (hp 0)
  apply top_unique
  intro x hx
  let w := x - a 0
  let α : ℝ := (w 0 * v 1 - v 0 * w 1) / D
  let β : ℝ := (u 0 * w 1 - w 0 * u 1) / D
  have hcomb : α • u + β • v = w := by
    ext j
    fin_cases j <;>
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] <;>
      dsimp [α, β] <;>
      field_simp [hD] <;>
      dsimp [D] <;> ring
  have hm : α • u + β • v ∈ A.direction :=
    A.direction.add_mem (A.direction.smul_mem α hu) (A.direction.smul_mem β hv)
  have he := AffineSubspace.vadd_mem_of_mem_direction hm (hp 0)
  simpa [hcomb, w, vadd_eq_add] using he
end EuclideanRamsey.CircleConsequence

end

end OAI
