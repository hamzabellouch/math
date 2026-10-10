import OAI.Geometry.HeilbronnTriangle.OrbitCardinality

namespace OAI


namespace Problem355.OrbitUniform

variable {G X : Type*} [Group G] [MulAction G X]

theorem orbit_fiber_probability [Finite G] (x y : X)
    (hy : y ∈ MulAction.orbit G x) :
    (Nat.card {g : G // g • x = y} : ℝ) / Nat.card G =
      1 / Nat.card (MulAction.orbit G x) := by
  rw [OrbitCardinality.card_orbit_fiber x y hy,
    ← OrbitCardinality.orbit_card_mul_stabilizer_card (G := G) x, Nat.cast_mul]
  have hs : (Nat.card (MulAction.stabilizer G x) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := MulAction.stabilizer G x)).ne'
  rw [mul_comm (Nat.card (MulAction.orbit G x) : ℝ), div_mul_eq_div_div,
    div_self hs]

theorem uniform_mass_eq_fiber_probability [Fintype G] [DecidableEq X] (x y : X) :
    (∑ g : G, if g • x = y then (1 / (Nat.card G : ℝ)) else 0) =
      (Nat.card {g : G // g • x = y} : ℝ) / Nat.card G := by
  classical
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
    mul_one_div]
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem uniform_mass_of_mem_orbit [Fintype G] [DecidableEq X] (x y : X)
    (hy : y ∈ MulAction.orbit G x) :
    (∑ g : G, if g • x = y then (1 / (Nat.card G : ℝ)) else 0) =
      1 / Nat.card (MulAction.orbit G x) := by
  rw [uniform_mass_eq_fiber_probability]
  exact orbit_fiber_probability x y hy

theorem uniform_mass_of_not_mem_orbit [Fintype G] [DecidableEq X] (x y : X)
    (hy : y ∉ MulAction.orbit G x) :
    (∑ g : G, if g • x = y then (1 / (Nat.card G : ℝ)) else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro g _
  apply ite_eq_right
  intro hg
  exact hy ⟨g, hg⟩

end Problem355.OrbitUniform

end OAI
