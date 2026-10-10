import OAI.Analysis.OInfinity.NegativeGlobal
import OAI.Analysis.OInfinity.CentralBuffer

namespace OAI

/-! # Shrinking zero-unit rows against the actual third buffer

The initial corner, its complementary isometry and the isometry inside it
remain explicit. These are the data supplied by the finite vacuum split;
no equivalence of arbitrary projections is assumed.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

/-- A full binary row in any supported corner can be shrunk against an
orthogonal commuting buffer row, with no change in its finite-word error. -/
lemma exists_commuting_binary_corner_shrink
    (q : E) (hq : star q = q) (hqq : q * q = q) (hq0 : q ≠ 0)
    (a r : Fin 2 → E)
    (ha : ∀ i j, star (a i) * a j = if i = j then q else 0)
    (has : (∑ i, a i * star (a i)) = q)
    (hr : ∀ i j, star (r i) * r j = if i = j then 1 else 0)
    (har : bergRowsCommute a r)
    (hqr : ∀ j, Commute q (r j))
    (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ c : E, q * c = c ∧ c * q = c ∧ star c * c = q ∧
      c * star c = q * (1 - r 0 * star (r 0)) ∧
      ∀ i ≤ m, ‖c * (a 0 ^ i * a 1) * star c -
        (a 0 ^ i * a 1) * (1 - r 0 * star (r 0))‖ < ε := by
  let R : Fin 2 → E := fun i => r i * q
  have hasp (i : Fin 2) : q * a i = a i ∧ a i * q = a i :=
    ⟨finiteRow_left_support q a hq hqq ha has i,
      finiteRow_right_support q a hq hqq ha i⟩
  have hRsp (i : Fin 2) : q * R i = R i ∧ R i * q = R i := by
    constructor
    · change q * (r i * q) = r i * q
      rw [← mul_assoc, (hqr i).eq, mul_assoc, hqq]
    · change (r i * q) * q = r i * q
      rw [mul_assoc, hqq]
  have hR (i j : Fin 2) : star (R i) * R j = if i = j then q else 0 := by
    change star (r i * q) * (r j * q) = _
    rw [star_mul, hq]
    calc
      _ = q * (star (r i) * r j) * q := by noncomm_ring
      _ = _ := by rw [hr]; split_ifs <;> simp only [mul_one, mul_zero, zero_mul, hqq]
  have haR : bergRowsCommute a R := by
    intro i j
    have haq : Commute (a i) q := (hasp i).2.trans (hasp i).1.symm
    constructor
    · exact (har i j).1.mul_right haq
    · change Commute (a i) (star (r j * q))
      rw [star_mul, hq]
      exact haq.mul_right (har i j).2
  have hfinal : q - R 0 * star (R 0) = q * (1 - r 0 * star (r 0)) := by
    change q - (r 0 * q) * star (r 0 * q) = _
    rw [star_mul, hq]
    have he : (r 0 * q) * (q * star (r 0)) = q * (r 0 * star (r 0)) := by
      calc
        _ = r 0 * (q * q) * star (r 0) := by noncomm_ring
        _ = _ := by rw [hqq, ← (hqr 0).eq]; noncomm_ring
    rw [he]
    noncomm_ring
  obtain ⟨c, hcl, hcr, hcg, hcc, he⟩ := exists_relative_binary_encoded_shrink
    q hq hqq hq0 R a hRsp hasp hR ha has haR m ε hε
  refine ⟨c, hcl, hcr, hcg, hcc.trans hfinal, fun i hi => ?_⟩
  have hxq : (a 0 ^ i * a 1) * q = a 0 ^ i * a 1 := by
    rw [mul_assoc, (hasp 1).2]
  have hh := he i hi
  have hsimp : (a 0 ^ i * a 1) * (q * (1 - r 0 * star (r 0))) =
      (a 0 ^ i * a 1) * (1 - r 0 * star (r 0)) := by
    rw [← mul_assoc, hxq]
  rw [hfinal, hsimp] at hh
  exact hh

/-- Every element of the buffer's closed row algebra inherits its exact
commutation with the supplied finite construction data. -/
lemma closedCanonicalRowAlgebra_commutes_element
    (r : ℕ → E) (x : E)
    (hx : ∀ i, Commute (r i) x ∧ Commute (star (r i)) x)
    (b : closedCanonicalRowAlgebra r) : Commute (b : E) x := by
  have hxc : x ∈ StarSubalgebra.centralizer ℂ (Set.range r) := by
    apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨(hx i).1.eq, (hx i).2.eq⟩
  have hbc : (b : E) ∈ StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ (Set.range r) : Set E) :=
    StarSubalgebra.topologicalClosure_adjoin_le_centralizer_centralizer ℂ (Set.range r) b.property
  exact (((StarSubalgebra.mem_centralizer_iff ℂ).mp hbc) x hxc).1.symm

/-- The explicit complement isometry and an isometry inside `q` give the
reverse shrink. The initial corner is `p`; the final corner is exactly `pq`.
No equivalence of an unspecified complementary projection is required. -/
lemma exists_complementary_binary_corner_shrink
    (p q w z : E)
    (hp : star p = p) (hpp : p * p = p) (hp0 : p ≠ 0)
    (hw : star w * w = 1) (hww : w * star w = 1 - q)
    (hz : star z * z = 1) (hqz : q * z = z)
    (hpw : Commute p w) (hpz : Commute p z)
    (b : Fin 2 → E)
    (hb : ∀ i j, star (b i) * b j = if i = j then p else 0)
    (hbs : (∑ i, b i * star (b i)) = p)
    (hbw : ∀ i, Commute (b i) w ∧ Commute (b i) (star w))
    (hbz : ∀ i, Commute (b i) z ∧ Commute (b i) (star z))
    (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ d : E, p * d = d ∧ d * p = d ∧ star d * d = p ∧
      d * star d = p * q ∧
      ∀ i ≤ m, ‖d * (b 0 ^ i * b 1) * star d - (b 0 ^ i * b 1) * q‖ < ε := by
  let v : Fin 2 → E := ![w, z]
  have hwz : star w * z = 0 := by
    have hwq : star w * q = 0 := by
      calc
        _ = star w * (1 - w * star w) := by rw [hww]; noncomm_ring
        _ = 0 := by rw [mul_sub, mul_one, ← mul_assoc, hw, one_mul, sub_self]
    calc
      _ = star w * (q * z) := by rw [hqz]
      _ = 0 := by rw [← mul_assoc, hwq, zero_mul]
  have hzw : star z * w = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star hwz
  have hv : ∀ i j, star (v i) * v j = if i = j then 1 else 0 := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [v, hw, hz, hwz, hzw]
  have hbv : bergRowsCommute b v := by
    intro i j
    fin_cases j
    · exact hbw i
    · exact hbz i
  have hpv (i : Fin 2) : Commute p (v i) := by
    fin_cases i
    · exact hpw
    · exact hpz
  obtain ⟨d, hdl, hdr, hdg, hdf, he⟩ :=
    exists_commuting_binary_corner_shrink p hp hpp hp0 b v hb hbs hv hbv hpv m ε hε
  have hfinal : 1 - v 0 * star (v 0) = q := by
    change 1 - w * star w = q
    rw [hww]
    noncomm_ring
  refine ⟨d, hdl, hdr, hdg, ?_, fun i hi => ?_⟩
  · exact hdf.trans (congrArg (fun x : E => p * x) hfinal)
  · simpa only [hfinal] using he i hi

/-- A third canonical row supplies its finite binary encoding inside the
closed buffer algebra. Consequently all supplied construction data commute
with the encoding, including their adjoints. -/
lemma exists_buffer_binary_encoding [Nontrivial E]
    (r : ℕ → E)
    (hr : ∀ i j, star (r i) * r j = if i = j then 1 else 0)
    (m : ℕ) :
    ∃ b : Fin 2 → closedCanonicalRowAlgebra r,
      (∀ i j, star (b i : E) * (b j : E) =
        if i = j then canonicalTailProjection r 1 else 0) ∧
      (∑ i, (b i : E) * star (b i : E)) = canonicalTailProjection r 1 ∧
      ∀ i ≤ m, (b 0 : E) ^ i * (b 1 : E) = canonicalNegativeRow r i := by
  let C := closedCanonicalRowAlgebra r
  let R : ℕ → C := fun i => ⟨r i, mem_closedCanonicalRowAlgebra r i⟩
  have hR (i j : ℕ) : star (R i) * R j = if i = j then 1 else 0 := by
    by_cases hij : i = j
    · rw [ite_eq_left hij]
      apply Subtype.ext
      change star (r i) * r j = 1
      simpa only [ite_eq_left hij] using hr i j
    · rw [ite_eq_right hij]
      apply Subtype.ext
      change star (r i) * r j = 0
      simpa only [ite_eq_right hij] using hr i j
  obtain ⟨b0, b1, h0, h1, h01, hsum, he⟩ :=
    exists_canonicalNegative_binary_encoding R hR m
  let b : Fin 2 → C := ![b0, b1]
  have h10 : star b1 * b0 = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star h01
  have hb (i j : Fin 2) : star (b i) * b j =
      if i = j then canonicalTailProjection R 1 else 0 := by
    fin_cases i <;> fin_cases j <;> simp [b, h0, h1, h01, h10]
  refine ⟨b, fun i j => ?_, ?_, fun i hi => ?_⟩
  · have h := congrArg C.subtype (hb i j)
    simpa only [map_mul, map_star, apply_ite, map_zero,
      StarSubalgebra.subtype_apply, canonicalTailProjection_coe] using h
  · have h := congrArg C.subtype hsum
    simpa only [Fin.sum_univ_two, b, Matrix.cons_val_zero, Matrix.cons_val_one,
      map_add, map_mul, map_star, StarSubalgebra.subtype_apply,
      canonicalTailProjection_coe] using h
  · have h := congrArg C.subtype (he i hi)
    simpa only [map_mul, map_pow, StarSubalgebra.subtype_apply,
      canonicalNegativeRow_coe, b, Matrix.cons_val_zero, Matrix.cons_val_one] using h

end WeakPureInfiniteness

end

end OAI
