import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationResidues

namespace OAI

/-!
# Simultaneous occupancy for the actual nested prime sampler

All three moduli are prefixes of one sampled factor tuple. Projection to
the first one or two factors has the exact uniform marginal. The three
energy estimates are therefore combined by a union bound on that one space.
-/

namespace LowSpaceSubsetSum

open scoped BigOperators

theorem triple_prefixTwo_probability (a b c : ℕ) (P : ℕ × ℕ → Prop) :
    finiteUniformProbability (fun z : ↥(tripleRange a b c) => P z.val.1) =
      finiteUniformProbability (fun z : ↥(factorRange a ×ˢ factorRange b) => P z.val) := by
  let : Nonempty ↥(factorRange c) :=
    ⟨⟨(factorRange_nonempty c).choose, (factorRange_nonempty c).choose_spec⟩⟩
  have h := finiteUniformProbability_equiv
    (Equiv.Finset.prod (factorRange a ×ˢ factorRange b) (factorRange c))
    (fun z : ↥(factorRange a ×ˢ factorRange b) × ↥(factorRange c) => P z.1.val)
  exact h.trans (finiteUniformProbability_fst
    (Ω := ↥(factorRange a ×ˢ factorRange b)) (Ψ := ↥(factorRange c))
    (fun z => P z.val))

theorem triple_prefixOne_probability (a b c : ℕ) (P : ℕ → Prop) :
    finiteUniformProbability (fun z : ↥(tripleRange a b c) => P z.val.1.1) =
      finiteUniformProbability (fun z : ↥(factorRange a) => P z.val) := by
  have hprefix := triple_prefixTwo_probability a b c (fun z : ℕ × ℕ => P z.1)
  let : Nonempty ↥(factorRange b) :=
    ⟨⟨(factorRange_nonempty b).choose, (factorRange_nonempty b).choose_spec⟩⟩
  have h := finiteUniformProbability_equiv (Equiv.Finset.prod (factorRange a) (factorRange b))
    (fun z : ↥(factorRange a) × ↥(factorRange b) => P z.1.val)
  exact hprefix.trans (h.trans (finiteUniformProbability_fst
    (Ω := ↥(factorRange a)) (Ψ := ↥(factorRange b)) (fun z => P z.val)))

theorem nested_uniform_collision_probability {a b c u : ℕ} {L : ℝ}
    (hu : 256 ≤ u) (ha : a ≤ u) (hb : b ≤ u) (hc : c ≤ u)
    (hL : L < ((a + b + c : ℕ) : ℝ) + 1) {x y : ℤ} (hxy : x ≠ y)
    (hbits : (x - y).natAbs < 2 ^ (2 * u)) :
    finiteUniformProbability (fun z : ↥(tripleRange a b c) =>
      x % (tripleModulus z.val : ℤ) = y % (tripleModulus z.val : ℤ)) ≤
        (u : ℝ) ^ 10 / (2 : ℝ) ^ L := by
  classical
  have hiff (z : (ℕ × ℕ) × ℕ) :
      x % (tripleModulus z : ℤ) = y % (tripleModulus z : ℤ) ↔
        tripleModulus z ∣ (x - y).natAbs := by
    rw [Int.emod_eq_emod_iff_emod_sub_eq_zero, ← Int.dvd_iff_emod_eq_zero, Int.natCast_dvd]
  rw [finiteUniformProbability_finset (tripleRange a b c)
    (fun z => x % (tripleModulus z : ℤ) = y % (tripleModulus z : ℤ))]
  simp_rw [hiff]
  exact nested_divisor_probability_le hu ha hb hc hL
    (Int.natAbs_pos.mpr (sub_ne_zero.mpr hxy)) hbits

def prefixModulus (z : (ℕ × ℕ) × ℕ) : Fin 3 → ℕ :=
  ![tripleModulus z, z.1.1 * z.1.2, z.1.1]

def prefixExponent (a b c : ℕ) : Fin 3 → ℕ := ![a + b + c, a + b, a]

theorem factorRange_pos {ell p : ℕ} (hp : p ∈ factorRange ell) : 0 < p := by
  by_cases h : ell < 4
  · have hp1 : p = 1 := by simpa [factorRange, h] using hp
    omega
  · exact (primeRange_prime (by simpa [factorRange, h] using hp)).pos

theorem prefixModulus_pos {a b c : ℕ} (z : ↥(tripleRange a b c)) (i : Fin 3) :
    0 < prefixModulus z.val i := by
  obtain ⟨hab, hzc⟩ := Finset.mem_product.mp z.property
  obtain ⟨hza, hzb⟩ := Finset.mem_product.mp hab
  have hA := factorRange_pos hza
  have hB := factorRange_pos hzb
  have hC := factorRange_pos hzc
  fin_cases i
  · exact Nat.mul_pos (Nat.mul_pos hA hB) hC
  · exact Nat.mul_pos hA hB
  · exact hA

theorem prefixModulus_nested (z : (ℕ × ℕ) × ℕ) :
    prefixModulus z 1 ∣ prefixModulus z 0 ∧ prefixModulus z 2 ∣ prefixModulus z 0 := by
  have h := cumulative_moduli_dvd z
  exact ⟨h.2, h.1.trans h.2⟩

theorem nested_prefix_collision_probability {a b c u : ℕ}
    (hu : 256 ≤ u) (ha : a ≤ u) (hb : b ≤ u) (hc : c ≤ u)
    (L : Fin 3 → ℝ) (hL : ∀ i, L i < (prefixExponent a b c i : ℝ) + 1)
    (i : Fin 3) {x y : ℤ} (hxy : x ≠ y) (hbits : (x - y).natAbs < 2 ^ (2 * u)) :
    finiteUniformProbability (fun z : ↥(tripleRange a b c) =>
      x % (prefixModulus z.val i : ℤ) = y % (prefixModulus z.val i : ℤ)) ≤
        (u : ℝ) ^ 10 / (2 : ℝ) ^ L i := by
  fin_cases i
  · exact nested_uniform_collision_probability hu ha hb hc (hL 0) hxy hbits
  · have hsmall := nested_uniform_collision_probability (a := a) (b := b) (c := 0)
      hu ha hb (by omega) (by simpa [prefixExponent] using hL 1) hxy hbits
    have hp : (fun z : ↥(tripleRange a b 0) =>
        x % (tripleModulus z.val : ℤ) = y % (tripleModulus z.val : ℤ)) =
        (fun z => x % (z.val.1.1 * z.val.1.2 : ℕ) = y % (z.val.1.1 * z.val.1.2 : ℕ)) := by
      funext z
      have hlast : z.val.2 = 1 := by
        have hmem := (Finset.mem_product.mp z.property).2
        simpa [factorRange] using hmem
      simp only [tripleModulus, hlast, mul_one]
    rw [hp, triple_prefixTwo_probability a b 0
      (fun z : ℕ × ℕ => x % (z.1 * z.2 : ℕ) = y % (z.1 * z.2 : ℕ))] at hsmall
    change finiteUniformProbability (fun z : ↥(tripleRange a b c) =>
      x % (z.val.1.1 * z.val.1.2 : ℕ) = y % (z.val.1.1 * z.val.1.2 : ℕ)) ≤ _
    rw [triple_prefixTwo_probability a b c
      (fun z : ℕ × ℕ => x % (z.1 * z.2 : ℕ) = y % (z.1 * z.2 : ℕ))]
    exact hsmall
  · have hsmall := nested_uniform_collision_probability (a := a) (b := 0) (c := 0)
      hu ha (by omega) (by omega) (by simpa [prefixExponent] using hL 2) hxy hbits
    have hp : (fun z : ↥(tripleRange a 0 0) =>
        x % (tripleModulus z.val : ℤ) = y % (tripleModulus z.val : ℤ)) =
        (fun z => x % (z.val.1.1 : ℤ) = y % (z.val.1.1 : ℤ)) := by
      funext z
      have hlast : z.val.2 = 1 := by
        have hmem := (Finset.mem_product.mp z.property).2
        simpa [factorRange] using hmem
      have hmiddle : z.val.1.2 = 1 := by
        have hmem := (Finset.mem_product.mp (Finset.mem_product.mp z.property).1).2
        simpa [factorRange] using hmem
      simp only [tripleModulus, hlast, hmiddle, mul_one]
    rw [hp, triple_prefixOne_probability a 0 0
      (fun z : ℕ => x % (z : ℤ) = y % (z : ℤ))] at hsmall
    change finiteUniformProbability (fun z : ↥(tripleRange a b c) =>
      x % (z.val.1.1 : ℤ) = y % (z.val.1.1 : ℤ)) ≤ _
    rw [triple_prefixOne_probability a b c
      (fun z : ℕ => x % (z : ℤ) = y % (z : ℤ))]
    exact hsmall

theorem nested_simultaneous_energy_probability {a b c u : ℕ}
    (hu : 256 ≤ u) (ha : a ≤ u) (hb : b ≤ u) (hc : c ≤ u)
    (X : Fin 3 → Finset ℤ) (L : Fin 3 → ℝ)
    (hL : ∀ i, L i < (prefixExponent a b c i : ℝ) + 1)
    (hsize : ∀ i, (2 : ℝ) ^ L i / (u : ℝ) ^ 14 ≤ (X i).card)
    (hbits : ∀ i x, x ∈ X i → ∀ y, y ∈ X i → (x - y).natAbs < 2 ^ (2 * u)) :
    1 - 3 / (u : ℝ) ≤ finiteUniformProbability
      (fun z : ↥(tripleRange a b c) => ∀ i,
        (collisionEnergy (X i) (fun x => x % (prefixModulus z.val i : ℤ)) : ℝ) ≤
          (u : ℝ) ^ 16 * ((X i).card : ℝ) ^ 2 / (2 : ℝ) ^ L i) := by
  let : Nonempty ↥(tripleRange a b c) :=
    ⟨⟨(tripleRange_nonempty a b c).choose, (tripleRange_nonempty a b c).choose_spec⟩⟩
  apply three_moduli_energy_probability X _ L (u : ℝ) (by exact_mod_cast (by omega : 2 ≤ u)) hsize
  intro i x hx y hy hxy
  exact nested_prefix_collision_probability hu ha hb hc L hL i hxy (hbits i x hx y hy)

theorem occupied_of_retained_energy (X : Finset ℤ) (f : ℤ → ℤ) (L u : ℝ)
    (hu : 0 < u) (hsize : (2 : ℝ) ^ L / u ^ 14 ≤ X.card)
    (henergy : (collisionEnergy X f : ℝ) ≤ u ^ 16 * (X.card : ℝ) ^ 2 / (2 : ℝ) ^ L) :
    (2 : ℝ) ^ L / u ^ 16 ≤ (X.image f).card := by
  have hE : 0 < (2 : ℝ) ^ L := Real.rpow_pos_of_pos (by norm_num) _
  have hX : (0 : ℝ) < X.card := (div_pos hE (pow_pos hu 14)).trans_le hsize
  have hT : 0 < u ^ 16 * (X.card : ℝ) ^ 2 / (2 : ℝ) ^ L := by positivity
  have h := occupied_ge_of_energy_le X f hT henergy
  have hr : (X.card : ℝ) ^ 2 / (u ^ 16 * (X.card : ℝ) ^ 2 / (2 : ℝ) ^ L) =
      (2 : ℝ) ^ L / u ^ 16 := by field_simp
  rwa [hr] at h

theorem nested_simultaneous_occupancy_probability {a b c u : ℕ}
    (hu : 256 ≤ u) (ha : a ≤ u) (hb : b ≤ u) (hc : c ≤ u)
    (X : Fin 3 → Finset ℤ) (L : Fin 3 → ℝ)
    (hL : ∀ i, L i < (prefixExponent a b c i : ℝ) + 1)
    (hsize : ∀ i, (2 : ℝ) ^ L i / (u : ℝ) ^ 14 ≤ (X i).card)
    (hbits : ∀ i x, x ∈ X i → ∀ y, y ∈ X i → (x - y).natAbs < 2 ^ (2 * u)) :
    1 - 3 / (u : ℝ) ≤ finiteUniformProbability
      (fun z : ↥(tripleRange a b c) => ∀ i,
        (2 : ℝ) ^ L i / (u : ℝ) ^ 16 ≤
          ((X i).image (fun x => x % (prefixModulus z.val i : ℤ))).card) := by
  apply (nested_simultaneous_energy_probability hu ha hb hc X L hL hsize hbits).trans
  apply finiteUniformProbability_mono
  intro z hz i
  exact occupied_of_retained_energy (X i) _ (L i) (u : ℝ)
    (by exact_mod_cast (by omega : 0 < u)) (hsize i) (hz i)

theorem prefixModulus_upper {a b c u : ℕ} (hu : 1 ≤ u)
    (ha : a ≤ u) (hb : b ≤ u) (hc : c ≤ u)
    (L : Fin 3 → ℝ) (hL : ∀ i, (prefixExponent a b c i : ℝ) ≤ L i)
    (z : ↥(tripleRange a b c)) (i : Fin 3) :
    (prefixModulus z.val i : ℝ) ≤ (2 : ℝ) ^ L i := by
  obtain ⟨hab, hzc⟩ := Finset.mem_product.mp z.property
  obtain ⟨hza, hzb⟩ := Finset.mem_product.mp hab
  have hA := (factor_size_bounds hu ha hza).2
  have hB := (factor_size_bounds hu hb hzb).2
  fin_cases i
  · apply (triple_size_bounds hu ha hb hc z.property).2.trans
    have he := hL 0
    change ((a + b + c : ℕ) : ℝ) ≤ L 0 at he
    have hr := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) he
    rw [Real.rpow_natCast] at hr
    exact hr
  · have hprod := mul_le_mul hA hB (Nat.cast_nonneg _) (by positivity)
    have hcast : (prefixModulus z.val 1 : ℝ) ≤ (2 : ℝ) ^ (a + b) := by
      change ((z.val.1.1 * z.val.1.2 : ℕ) : ℝ) ≤ _
      simpa only [Nat.cast_mul, pow_add] using hprod
    apply hcast.trans
    have he := hL 1
    change ((a + b : ℕ) : ℝ) ≤ L 1 at he
    have hr := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) he
    rw [Real.rpow_natCast] at hr
    exact hr
  · apply hA.trans
    have he := hL 2
    change (a : ℝ) ≤ L 2 at he
    have hr := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) he
    rw [Real.rpow_natCast] at hr
    exact hr

/-- The normalized occupied-class fraction feeds the following uniform
top/child residue experiment. -/
theorem nested_simultaneous_fraction_probability {a b c u : ℕ}
    (hu : 256 ≤ u) (ha : a ≤ u) (hb : b ≤ u) (hc : c ≤ u)
    (X : Fin 3 → Finset ℤ) (L : Fin 3 → ℝ)
    (hL0 : ∀ i, (prefixExponent a b c i : ℝ) ≤ L i)
    (hL1 : ∀ i, L i < (prefixExponent a b c i : ℝ) + 1)
    (hsize : ∀ i, (2 : ℝ) ^ L i / (u : ℝ) ^ 14 ≤ (X i).card)
    (hbits : ∀ i x, x ∈ X i → ∀ y, y ∈ X i → (x - y).natAbs < 2 ^ (2 * u)) :
    1 - 3 / (u : ℝ) ≤ finiteUniformProbability
      (fun z : ↥(tripleRange a b c) => ∀ i,
        (prefixModulus z.val i : ℝ) / (u : ℝ) ^ 16 ≤
          ((X i).image (fun x => x % (prefixModulus z.val i : ℤ))).card) := by
  apply (nested_simultaneous_occupancy_probability hu ha hb hc X L hL1 hsize hbits).trans
  apply finiteUniformProbability_mono
  intro z hz i
  exact (div_le_div_of_nonneg_right
    (prefixModulus_upper (by omega : 1 ≤ u) ha hb hc L hL0 z i) (by positivity)).trans (hz i)

/-- On each good common prime seed, the subsequent actual uniform residue
draws retain compatible representatives with probability at least `u⁻⁴⁸`. -/
theorem nested_seed_compatible_probability {a b c : ℕ} (z : ↥(tripleRange a b c))
    (X : Fin 3 → Finset ℤ) (c0 t : ℤ) (cL cR : ℤ → ℤ) (u : ℝ) (hu : 0 < u)
    (hoccupied : ∀ i, (prefixModulus z.val i : ℝ) / u ^ 16 ≤
      ((X i).image (fun x => x % (prefixModulus z.val i : ℤ))).card) :
    1 / u ^ 48 ≤ finiteUniformProbability
      (compatibleRepresentativeResidues
        (p0 := prefixModulus z.val 0) (pL := prefixModulus z.val 1)
        (pR := prefixModulus z.val 2) (X 0) (X 1) (X 2) c0 t cL cR) :=
  compatibleRepresentativeResidues_probability (prefixModulus_pos z 0)
    (prefixModulus_pos z 1) (prefixModulus_pos z 2)
    (prefixModulus_nested z.val).1 (prefixModulus_nested z.val).2
    (X 0) (X 1) (X 2) c0 t cL cR u hu (hoccupied 0) (hoccupied 1) (hoccupied 2)

end LowSpaceSubsetSum

end OAI
