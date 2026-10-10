import OAI.NumberTheory.Ostmann.Construction.GoodCellTargets

namespace OAI

/-! # Rounding target sums to the actual cell lattice -/

namespace Ostmann

private theorem nat_lattice_rounddown (g : ℕ) (hg : 0 < g) (T : ℝ) (hT : 0 ≤ T) :
    ∃ t : ℕ, g ∣ t ∧ (t : ℝ) ≤ T ∧ T < (t : ℝ) + g := by
  let j := ⌊T / g⌋₊
  have hgr : (0 : ℝ) < g := by exact_mod_cast hg
  have hlo : (j : ℝ) * g ≤ T :=
    (le_div_iff₀ hgr).mp (Nat.floor_le (div_nonneg hT hgr.le))
  have hhi : T < ((j : ℝ) + 1) * g :=
    (div_lt_iff₀ hgr).mp (Nat.lt_floor_add_one (T / g))
  refine ⟨g * j, dvd_mul_right _ _, ?_, ?_⟩
  · push_cast
    nlinarith
  · push_cast
    nlinarith

/-- An interior real target can be realized to bounded accuracy. The error
bound depends only on the density of good cells, not on their scale. -/
theorem dense_cell_approximate_sum (δ : ℝ) (hδ : 0 < δ) :
    ∃ r : ℕ, 0 < r ∧ ∀ (I : Finset ℕ) (a b : ℕ),
      a < b → a ∈ I → b ∈ I → (∀ x ∈ I, a ≤ x ∧ x ≤ b) →
      δ * (b - a : ℕ) + 1 ≤ I.card → ∀ n : ℕ, r ≤ n → ∀ T : ℝ,
      (n * a + r * (b - a) + (cellDifferences I a).gcd id : ℕ) ≤ T →
      T ≤ (n * a + (n - r) * (b - a) : ℕ) →
      ∃ w : List ℕ, w.length = n ∧ (∀ x ∈ w, x ∈ I) ∧
        |(w.sum : ℝ) - T| < δ⁻¹ := by
  classical
  obtain ⟨r, hr, hcover⟩ := dense_cell_exact_sum δ hδ
  refine ⟨r, hr, ?_⟩
  intro I a b hab ha hb hbounds hdensity n hrn T hlo hhi
  let A := cellDifferences I a
  let s := b - a
  let g : ℕ := A.gcd id
  have hs : 0 < s := Nat.sub_pos_of_lt hab
  have hend : s ∈ A := Finset.mem_image.mpr ⟨b, hb, rfl⟩
  have hbound : ∀ x ∈ A, x ≤ s := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact Nat.sub_le_sub_right (hbounds y hy).2 a
  have hcard : A.card = I.card := cellDifferences_card I a (fun x hx => (hbounds x hx).1)
  have hd : δ * s + 1 ≤ A.card := by rwa [hcard]
  have hspacing : δ * (g : ℝ) ≤ 1 := dense_difference_gcd_bound A s hs hend hbound δ hd
  have hgs : g ∣ s := Finset.gcd_dvd hend
  have hg : 0 < g := by
    by_contra! h
    have : g = 0 := Nat.eq_zero_of_le_zero h
    rw [this, zero_dvd_iff] at hgs
    omega
  have hlo' : (n * a : ℕ) + (r * s : ℕ) + (g : ℝ) ≤ T := by
    exact_mod_cast hlo
  have hhi' : T ≤ (n * a : ℕ) + ((n - r) * s : ℕ) := by
    exact_mod_cast hhi
  obtain ⟨t, htdiv, htlo, hthi⟩ := nat_lattice_rounddown g hg (T - (n * a : ℕ))
    (by
      have hnon : (0 : ℝ) ≤ (r * s : ℕ) := by positivity
      have hgnon : (0 : ℝ) ≤ g := by positivity
      linarith)
  have htl : r * s ≤ t := by
    have hh : (r * s : ℕ) ≤ (t : ℝ) := by linarith
    exact_mod_cast hh
  have htu : t ≤ (n - r) * s := by
    have hh : (t : ℝ) ≤ ((n - r) * s : ℕ) := by linarith
    exact_mod_cast hh
  change r * (b - a) ≤ t at htl
  change t ≤ (n - r) * (b - a) at htu
  obtain ⟨w, hwlen, hwmem, hwsum⟩ := hcover I a b hab ha hb hbounds hdensity n hrn
    (n * a + t) (by simpa using htdiv) (by omega) (by omega)
  refine ⟨w, hwlen, hwmem, ?_⟩
  have hsum : (w.sum : ℝ) = (n * a : ℕ) + (t : ℝ) := by exact_mod_cast hwsum
  have hdiff : |(w.sum : ℝ) - T| < (g : ℝ) := by
    rw [hsum, abs_of_nonpos (by linarith)]
    linarith
  rw [← one_div]
  apply (lt_div_iff₀ hδ).mpr
  calc
    |(w.sum : ℝ) - T| * δ < (g : ℝ) * δ := mul_lt_mul_of_pos_right hdiff hδ
    _ ≤ 1 := by nlinarith [hspacing]

end Ostmann

end OAI
