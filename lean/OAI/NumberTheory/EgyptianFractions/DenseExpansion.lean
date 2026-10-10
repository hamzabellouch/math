import OAI.NumberTheory.EgyptianFractions.DensePairing

namespace OAI
namespace Problem337

/-- Scaling every unit denominator divides the represented rational by the
same scale. Repetitions in the list are allowed. -/
theorem reciprocal_sum_map_mul (ds : List ℕ) (g : ℕ) :
    ((ds.map (fun d : ℕ => g * d)).map (fun d : ℕ => (1 : ℚ) / (d : ℚ))).sum =
      (ds.map (fun d : ℕ => (1 : ℚ) / (d : ℚ))).sum / (g : ℚ) := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
      simp only [List.map_cons, List.sum_cons, ih, Nat.cast_mul]
      rw [add_div]
      congr 1
      rw [mul_comm, div_mul_eq_div_div]

/-- The dense-family additive argument for rational unit-fraction lists.
The lists supplied for good numerators may contain repeated denominators;
distinctification can be applied after adjoining a greedy prefix. -/
theorem dense_expansion_of_lists
    (X : ℝ) (a C M L : ℕ) (G : Finset ℕ)
    (ha : 0 < a) (hC : 0 < C) (hM : 0 < M) (hX : 4 < X)
    (haM : ((a * M : ℕ) : ℝ) ≤ X)
    (hdense : ((Finset.Icc 1 ⌊X⌋₊ \ G).card : ℝ) ≤ X / 8)
    (hG : ∀ u ∈ G, ∃ ds : List ℕ,
      (∀ d ∈ ds, 2 ≤ d) ∧ ds.length ≤ L ∧
      (ds.map (fun d : ℕ => (1 : ℚ) / (d : ℚ))).sum =
        (u : ℚ) / ((M * C : ℕ) : ℚ)) :
    ∃ ds : List ℕ, (∀ d ∈ ds, 2 ≤ d) ∧ ds.length ≤ 2 * L ∧
      (ds.map (fun d : ℕ => (1 : ℚ) / (d : ℚ))).sum = (a : ℚ) / (C : ℚ) := by
  classical
  let d := a * M
  let g := ⌊X / (d : ℝ)⌋₊
  have hd : 0 < d := Nat.mul_pos ha hM
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hdX : (d : ℝ) ≤ X := haM
  have hg : 1 ≤ g := Nat.le_floor ((le_div_iff₀ hdR).mpr (by simpa using hdX))
  have hbounds := floor_multiple_bounds hdR hdX
  have hnlow : X / 2 ≤ ((g * d : ℕ) : ℝ) := by
    simpa only [Nat.cast_mul] using hbounds.1
  have hnup : ((g * d : ℕ) : ℝ) ≤ X := by
    simpa only [Nat.cast_mul] using hbounds.2
  obtain ⟨u, hu, v, hv, huv⟩ := dense_pairing_real X G (g * d) hX hnlow hnup hdense
  obtain ⟨us, hus, hlenU, hsumU⟩ := hG u hu
  obtain ⟨vs, hvs, hlenV, hsumV⟩ := hG v hv
  refine ⟨(us ++ vs).map (fun q => g * q), ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
    have hr2 : 2 ≤ r := (List.mem_append.mp hr).elim (hus r) (hvs r)
    have : r ≤ g * r := by simpa using Nat.mul_le_mul_right r hg
    omega
  · simp only [List.length_map, List.length_append]
    omega
  · rw [reciprocal_sum_map_mul]
    simp only [List.map_append, List.sum_append, hsumU, hsumV]
    have hg0 : (g : ℚ) ≠ 0 := by exact_mod_cast (by omega : g ≠ 0)
    have hM0 : (M : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
    have hC0 : (C : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hC)
    have hcast : (u : ℚ) + (v : ℚ) = (g : ℚ) * ((a : ℚ) * (M : ℚ)) := by
      exact_mod_cast huv
    push_cast
    rw [← add_div, hcast]
    field_simp

end Problem337

end OAI
