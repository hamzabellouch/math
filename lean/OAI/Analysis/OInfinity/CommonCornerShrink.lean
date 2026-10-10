import OAI.Analysis.OInfinity.CanonicalShift
import OAI.Analysis.OInfinity.ZeroUnitCompletion
import OAI.Analysis.OInfinity.NegativeComparison

namespace OAI

/-! # Quantitative shrinking to a common corner

The explicit coisometry filler turns the canonical-shift
implementer into a partial isometry. Its initial and final projections
are exact, and its conjugation error is the shift error itself.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

lemma finiteCuntzTransfer_conjugate_commuting {I : Type*} [Fintype I] [DecidableEq I]
    (r a : I → E)
    (hr : ∀ i j, star (r i) * r j = if i = j then 1 else 0)
    (x : E) (hx : ∀ i, Commute x (r i)) :
    finiteCuntzTransfer r a 1 * x * star (finiteCuntzTransfer r a 1) =
      finiteRowShift a x := by
  let A := finiteCuntzTransfer r a 1
  have hAs : star A = finiteCuntzTransfer a r 1 := by
    simpa only [A, star_one] using finiteCuntzTransfer_star r a 1
  change A * x * star A = _
  rw [hAs]
  change A * x * (∑ i, r i * 1 * star (a i)) = _
  rw [Finset.mul_sum]
  simp only [mul_one]
  change (∑ i, A * x * (r i * star (a i))) = ∑ i, a i * x * star (a i)
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = (A * (x * r i)) * star (a i) := by noncomm_ring
    _ = (A * (r i * x)) * star (a i) := by rw [(hx i).eq]
    _ = (A * r i) * x * star (a i) := by noncomm_ring
    _ = _ := by rw [finiteCuntzTransfer_mul r a hr 1 i, mul_one]

/-- Exact error formula for the inserted-unitary shrink. -/
lemma binary_shift_shrink_difference (r a : Fin 2 → E)
    (hr : ∀ i j, star (r i) * r j = if i = j then 1 else 0)
    (ha : ∀ i j, star (a i) * a j = if i = j then 1 else 0)
    (has : (∑ i, a i * star (a i)) = 1) (u : unitary E)
    (x : E) (hx : ∀ i, Commute x (r i) ∧ Commute x (star (r i))) :
    let v := (u : E) * finiteCuntzTransfer r a 1
    let C := 1 - star v * v + r 1 * v
    C * x * star C - x * (1 - r 0 * star (r 0)) =
      r 1 * ((u : E) * finiteRowShift a x * star (u : E) - x) * star (r 1) := by
  intro v C
  let A := finiteCuntzTransfer r a 1
  have hAs : star A = finiteCuntzTransfer a r 1 := by
    simpa only [A, star_one] using finiteCuntzTransfer_star r a 1
  have hAA : A * star A = 1 := by
    have h := finiteCuntzTransfer_star_mul a r hr 1
    rw [← hAs, star_star] at h
    simpa only [star_one, one_mul, mul_one, has] using h
  have hAp : star A * A = ∑ i, r i * star (r i) := by
    simpa only [A, star_one, one_mul, mul_one] using finiteCuntzTransfer_star_mul r a ha 1
  have hvv : v * star v = 1 := by
    change ((u : E) * A) * star ((u : E) * A) = 1
    rw [star_mul]
    calc
      _ = (u : E) * (A * star A) * star (u : E) := by noncomm_ring
      _ = 1 := by rw [hAA, mul_one, u.property.2]
  have hvp : star v * v = ∑ i, r i * star (r i) := by
    change star ((u : E) * A) * ((u : E) * A) = _
    rw [star_mul]
    calc
      _ = star A * (star (u : E) * (u : E)) * A := by noncomm_ring
      _ = _ := by rw [u.property.1, mul_one, hAp]
  have hpx : Commute (star v * v) x := by
    rw [hvp]
    exact Commute.sum_left _ _ _ (fun i _ => (hx i).1.symm.mul_left (hx i).2.symm)
  have hinner : v * x * star v = (u : E) * finiteRowShift a x * star (u : E) := by
    change ((u : E) * A) * x * star ((u : E) * A) = _
    rw [star_mul]
    calc
      _ = (u : E) * (A * x * star A) * star (u : E) := by noncomm_ring
      _ = _ := by rw [finiteCuntzTransfer_conjugate_commuting r a hr x (fun i => (hx i).1)]
  have hconj := coisometry_range_filler_conjugation v (r 1) x hvv hpx
  change C * x * star C = _ at hconj
  rw [hconj, hvp, hinner, Fin.sum_univ_two]
  have hzero : (r 0 * star (r 0)) * x = x * (r 0 * star (r 0)) :=
    ((hx 0).1.symm.mul_left (hx 0).2.symm).eq
  have hone : (r 1 * star (r 1)) * x = r 1 * x * star (r 1) := by
    rw [mul_assoc, ← (hx 1).2.eq, ← mul_assoc]
  calc
    _ = (x * (r 0 * star (r 0)) - (r 0 * star (r 0)) * x) +
        r 1 * ((u : E) * finiteRowShift a x * star (u : E)) * star (r 1) -
        (r 1 * star (r 1)) * x := by noncomm_ring
    _ = _ := by rw [hzero, sub_self, zero_add, hone]; noncomm_ring

lemma binary_shift_shrink_error [Nontrivial E] (r a : Fin 2 → E)
    (hr : ∀ i j, star (r i) * r j = if i = j then 1 else 0)
    (ha : ∀ i j, star (a i) * a j = if i = j then 1 else 0)
    (has : (∑ i, a i * star (a i)) = 1) (u : unitary E)
    (x : E) (hx : ∀ i, Commute x (r i) ∧ Commute x (star (r i))) :
    let v := (u : E) * finiteCuntzTransfer r a 1
    let C := 1 - star v * v + r 1 * v
    ‖C * x * star C - x * (1 - r 0 * star (r 0))‖ ≤
      ‖(u : E) * finiteRowShift a x * star (u : E) - x‖ := by
  intro v C
  rw [binary_shift_shrink_difference r a hr ha has u x hx]
  let d := (u : E) * finiteRowShift a x * star (u : E) - x
  have hn : ‖r 1‖ ≤ 1 := by
    have h := congrArg norm (show star (r 1) * r 1 = 1 by simpa only [ite_true] using hr 1 1)
    rw [CStarRing.norm_star_mul_self, norm_one] at h
    nlinarith [norm_nonneg (r 1)]
  have hfirst : ‖r 1 * d‖ ≤ ‖d‖ := by
    calc
      _ ≤ ‖r 1‖ * ‖d‖ := norm_mul_le _ _
      _ ≤ 1 * ‖d‖ := mul_le_mul_of_nonneg_right hn (norm_nonneg _)
      _ = _ := one_mul _
  calc
    _ ≤ ‖r 1 * d‖ * ‖star (r 1)‖ := norm_mul_le _ _
    _ ≤ ‖d‖ * 1 := mul_le_mul hfirst (by simpa only [norm_star] using hn)
      (norm_nonneg _) (norm_nonneg _)
    _ = _ := mul_one _

/-- The inverse shift implementer controls every prescribed encoded
prefix element, with its tolerance chosen after the prefix length. -/
lemma exists_canonicalShift_prefix_inverse [Nontrivial E]
    (a : Fin 2 → E)
    (ha : ∀ i j, star (a i) * a j = if i = j then 1 else 0)
    (has : (∑ i, a i * star (a i)) = 1) (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ u : unitary E, ∀ i ≤ m,
      ‖(u : E) * finiteRowShift a (a 0 ^ i * a 1) * star (u : E) -
        (a 0 ^ i * a 1)‖ < ε := by
  let δ := ε / ((m : ℝ) + 2)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  obtain ⟨u, _hu, huclose⟩ := exists_connected_canonicalShift_conjugacy a ha has δ hδ
  let φ := finiteCuntzDiagonalHom a ha
  have han (j : Fin 2) : ‖a j‖ ≤ 1 := by
    have h := congrArg norm (show star (a j) * a j = 1 by simpa only [ite_true] using ha j j)
    rw [CStarRing.norm_star_mul_self, norm_one] at h
    nlinarith [norm_nonneg (a j)]
  have hun (j : Fin 2) : ‖(u : E) * a j * star (u : E)‖ ≤ 1 := by
    rw [mul_assoc, CStarRing.norm_coe_unitary_mul]
    change ‖a j * (star u : unitary E)‖ ≤ 1
    rw [CStarRing.norm_mul_coe_unitary]
    exact han j
  have hφn (j : Fin 2) : ‖φ (a j)‖ ≤ 1 :=
    (NonUnitalStarAlgHom.norm_apply_le φ _).trans (han j)
  have hclose (i : ℕ) (hi : i ≤ m) :
      ‖(u : E) * (a 0 ^ i * a 1) * star (u : E) -
        φ (a 0 ^ i * a 1)‖ < ε := by
    let j : Fin (m + 1) := ⟨i, by omega⟩
    have hp := zeroCornerRow_perturbation 1
      ((u : E) * a 0 * star (u : E)) ((u : E) * a 1 * star (u : E))
      (φ (a 0)) (φ (a 1)) δ hδ.le (by simp) (hun 0) (hun 1) (hφn 0)
      (huclose 0).le (huclose 1).le (m + 1) j.castSucc
    rw [← zeroCornerRow_conjugate] at hp
    simp only [zeroCornerRow_castSucc] at hp
    rw [← nonunital_map_pow_mul] at hp
    apply hp.trans_lt
    have he : ((m : ℝ) + 2) * δ = ε := by dsimp only [δ]; field_simp
    push_cast
    nlinarith
  refine ⟨star u, fun i hi => ?_⟩
  let x := a 0 ^ i * a 1
  have hid : (star (u : E)) * φ x * (u : E) - x =
      star (u : E) * (φ x - (u : E) * x * star (u : E)) * (u : E) := by
    rw [mul_sub, sub_mul]
    have hcan : star (u : E) * ((u : E) * x * star (u : E)) * (u : E) = x := by
      calc
        _ = (star (u : E) * (u : E)) * x * (star (u : E) * (u : E)) := by noncomm_ring
        _ = x := by rw [u.property.1, one_mul, mul_one]
    rw [hcan]
  change ‖star (u : E) * φ x * star (star (u : E)) - x‖ < ε
  rw [star_star]
  rw [hid, CStarRing.norm_mul_coe_unitary]
  change ‖(star u : unitary E) * (φ x - (u : E) * x * star (u : E))‖ < ε
  rw [CStarRing.norm_coe_unitary_mul, norm_sub_rev]
  exact hclose i hi

/-- A concrete partial isometry shrinks the whole unit past `r₀`, while
approximating the prescribed finite encoded row on the resulting corner. -/
lemma exists_binary_encoded_shrink [Nontrivial E]
    (r a : Fin 2 → E)
    (hr : ∀ i j, star (r i) * r j = if i = j then 1 else 0)
    (ha : ∀ i j, star (a i) * a j = if i = j then 1 else 0)
    (has : (∑ i, a i * star (a i)) = 1)
    (hc : bergRowsCommute a r) (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : E, star C * C = 1 ∧ C * star C = 1 - r 0 * star (r 0) ∧
      ∀ i ≤ m, ‖C * (a 0 ^ i * a 1) * star C -
        (a 0 ^ i * a 1) * (1 - r 0 * star (r 0))‖ < ε := by
  obtain ⟨u, hu⟩ := exists_canonicalShift_prefix_inverse a ha has m ε hε
  let v := (u : E) * finiteCuntzTransfer r a 1
  let C := 1 - star v * v + r 1 * v
  obtain ⟨hC, hCC⟩ := binary_shift_shrink_products r a hr ha has u
  refine ⟨C, hC, hCC, fun i hi => ?_⟩
  have hx (j : Fin 2) : Commute (a 0 ^ i * a 1) (r j) ∧
      Commute (a 0 ^ i * a 1) (star (r j)) := by
    exact ⟨((hc 0 j).1.pow_left i).mul_left (hc 1 j).1,
      ((hc 0 j).2.pow_left i).mul_left (hc 1 j).2⟩
  exact (binary_shift_shrink_error r a hr ha has u _ hx).trans_lt (hu i hi)

/-- The same shrink inside an actual projection corner. Both support
identities and both Murray--von Neumann projections are part of the output. -/
lemma exists_relative_binary_encoded_shrink
    (q : E) (hq : star q = q) (hqq : q * q = q) (hq0 : q ≠ 0)
    (r a : Fin 2 → E)
    (hrs : ∀ i, q * r i = r i ∧ r i * q = r i)
    (hasp : ∀ i, q * a i = a i ∧ a i * q = a i)
    (hr : ∀ i j, star (r i) * r j = if i = j then q else 0)
    (ha : ∀ i j, star (a i) * a j = if i = j then q else 0)
    (has : (∑ i, a i * star (a i)) = q)
    (hc : bergRowsCommute a r) (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : E, q * C = C ∧ C * q = C ∧ star C * C = q ∧
      C * star C = q - r 0 * star (r 0) ∧
      ∀ i ≤ m, ‖C * (a 0 ^ i * a 1) * star C -
        (a 0 ^ i * a 1) * (q - r 0 * star (r 0))‖ < ε := by
  let : NeZero q := ⟨hq0⟩
  let R : Fin 2 → ProjectionCorner q hq hqq := fun i =>
    projectionCornerElement q hq hqq (r i) (hrs i)
  let A : Fin 2 → ProjectionCorner q hq hqq := fun i =>
    projectionCornerElement q hq hqq (a i) (hasp i)
  have hR := projectionCornerElement_gram q hq hqq r hrs hr
  have hA := projectionCornerElement_gram q hq hqq a hasp ha
  have hAs := projectionCornerElement_range_sum q hq hqq a hasp has
  have hAR : bergRowsCommute A R := by
    intro i j
    constructor
    · change A i * R j = R j * A i
      apply Subtype.ext
      exact (hc i j).1.eq
    · change A i * star (R j) = star (R j) * A i
      apply Subtype.ext
      exact (hc i j).2.eq
  obtain ⟨C, hC, hCC, he⟩ := exists_binary_encoded_shrink R A hR hA hAs hAR m ε hε
  let f := projectionCornerInclusion q hq hqq
  have hpow (i : ℕ) : f (A 0 ^ i * A 1) = a 0 ^ i * a 1 := by
    rw [nonunital_map_pow_mul]
    rfl
  refine ⟨C, C.property.1, C.property.2, ?_, ?_, fun i hi => ?_⟩
  · exact congrArg f hC
  · exact congrArg f hCC
  · have h := he i hi
    change ‖f (C * (A 0 ^ i * A 1) * star C -
      (A 0 ^ i * A 1) * (1 - R 0 * star (R 0)))‖ < ε at h
    simp only [map_sub, map_mul, map_star, hpow] at h
    exact h

/-- Concrete transfer from the first stabilized unit to the common unit.
The binary encoding is chosen inside the source algebra, so it commutes
with the other canonical row without an added uniqueness hypothesis. -/
lemma exists_canonicalNegative_common_shrink [Nontrivial E]
    (C D : StarSubalgebra ℂ E) [IsClosed (C : Set E)] [IsClosed (D : Set E)]
    (hc : ∀ x : C, ∀ y : D, Commute (x : E) (y : E))
    (s : ℕ → C) (t : ℕ → D)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    let S : ℕ → E := fun i => s i
    let T : ℕ → E := fun i => t i
    let P := canonicalTailProjection S 1
    let Q := canonicalTailProjection T 1
    ∃ v : E, P * v = v ∧ v * P = v ∧ star v * v = P ∧ v * star v = P * Q ∧
      ∀ i ≤ m, ‖v * canonicalNegativeRow S i * star v - canonicalNegativeRow S i * Q‖ < ε := by
  intro S T P Q
  let p := canonicalTailProjection s 1
  have hp : star p = p := canonicalTailProjection_star s 1
  have hpp : p * p = p := canonicalTailProjection_idempotent s hs 1
  have hpc : (p : E) = P := canonicalTailProjection_coe C s 1
  have hP : star P = P := by
    have h := congrArg C.subtype hp
    simpa only [map_star, StarSubalgebra.subtype_apply, hpc] using h
  have hPP : P * P = P := by
    have h := congrArg C.subtype hpp
    simpa only [map_mul, StarSubalgebra.subtype_apply, hpc] using h
  have hP0 : P ≠ 0 := by
    have hS (i j : ℕ) : star (S i) * S j = if i = j then 1 else 0 := by
      have h := congrArg C.subtype (hs i j)
      simpa only [map_mul, map_star, apply_ite, map_one, map_zero,
        StarSubalgebra.subtype_apply] using h
    exact canonicalTailProjection_ne_zero S hS 1
  obtain ⟨a0, a1, ha0, ha1, haa, has, hae⟩ := exists_canonicalNegative_binary_encoding s hs m
  let aC : Fin 2 → C := ![a0, a1]
  have haa' : star a1 * a0 = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star haa
  have haC (i j : Fin 2) : star (aC i) * aC j = if i = j then p else 0 := by
    fin_cases i <;> fin_cases j <;> simp [aC, p, ha0, ha1, haa, haa']
  have hasC : (∑ i, aC i * star (aC i)) = p := by
    simpa only [Fin.sum_univ_two, aC, Matrix.cons_val_zero, Matrix.cons_val_one] using has
  let a : Fin 2 → E := fun i => aC i
  have ha (i j : Fin 2) : star (a i) * a j = if i = j then P else 0 := by
    have h := congrArg C.subtype (haC i j)
    simpa only [map_mul, map_star, apply_ite, map_zero,
      StarSubalgebra.subtype_apply, hpc] using h
  have hasE : (∑ i, a i * star (a i)) = P := by
    have h := congrArg C.subtype hasC
    simpa only [map_sum, map_mul, map_star, StarSubalgebra.subtype_apply, hpc] using h
  have hasp (i : Fin 2) : P * a i = a i ∧ a i * P = a i := by
    constructor
    · have h := congrArg C.subtype (finiteRow_left_support p aC hp hpp haC hasC i)
      simpa only [map_mul, StarSubalgebra.subtype_apply, hpc] using h
    · have h := congrArg C.subtype (finiteRow_right_support p aC hp hpp haC i)
      simpa only [map_mul, StarSubalgebra.subtype_apply, hpc] using h
  let f := commutingProjectionRestriction D P hP hPP (fun y => by
    simpa only [hpc] using (hc p y).symm)
  let r : Fin 2 → E := fun i => f (t i)
  have ht' (i j : Fin 2) : star (t i) * t j = if i = j then 1 else 0 := by
    simpa only [Fin.ext_iff] using ht i j
  have hr (i j : Fin 2) : star (r i) * r j = if i = j then P else 0 := by
    change star (f (t i)) * f (t j) = _
    rw [← map_star, ← map_mul, ht']
    split_ifs with hij
    · change (1 : E) * P = P
      exact one_mul P
    · exact map_zero f
  have hrs (i : Fin 2) : P * r i = r i ∧ r i * P = r i := by
    change P * ((t i : E) * P) = (t i : E) * P ∧
      ((t i : E) * P) * P = (t i : E) * P
    have hpt : P * (t i : E) = (t i : E) * P := by
      simpa only [hpc] using (hc p (t i)).eq
    constructor
    · rw [← mul_assoc, hpt, mul_assoc, hPP]
    · rw [mul_assoc, hPP]
  have har : bergRowsCommute a r := by
    intro i j
    have hap : Commute (a i) P := (hasp i).2.trans (hasp i).1.symm
    constructor
    · exact (hc (aC i) (t j)).mul_right hap
    · change Commute (a i) (star ((t j : E) * P))
      rw [star_mul, hP]
      exact hap.mul_right (hc (aC i) (star (t j)))
  have hfinal : P - r 0 * star (r 0) = P * Q := by
    change P - ((t 0 : E) * P) * star ((t 0 : E) * P) = P * Q
    have hpt : Commute P (t 0 : E) := by simpa only [hpc] using hc p (t 0)
    rw [star_mul, hP]
    calc
      _ = P - P * ((t 0 : E) * star (t 0 : E)) := by
        have he : ((t 0 : E) * P) * (P * star (t 0 : E)) =
            P * ((t 0 : E) * star (t 0 : E)) := by
          calc
            _ = (t 0 : E) * (P * P) * star (t 0 : E) := by noncomm_ring
            _ = _ := by rw [hPP, ← hpt.eq]; noncomm_ring
        rw [he]
      _ = P * (1 - (t 0 : E) * star (t 0 : E)) := by noncomm_ring
      _ = _ := by
        change P * (1 - (t 0 : E) * star (t 0 : E)) =
          P * (1 - ∑ i : Fin 1, T i * star (T i))
        rw [Fin.sum_univ_one]
        rfl
  obtain ⟨v, hvl, hvr, hv, hvv, he⟩ := exists_relative_binary_encoded_shrink
    P hP hPP hP0 r a hrs hasp hr ha hasE har m ε hε
  refine ⟨v, hvl, hvr, hv, hvv.trans hfinal, fun i hi => ?_⟩
  have heq : a 0 ^ i * a 1 = canonicalNegativeRow S i := by
    have h := congrArg C.subtype (hae i hi)
    simpa only [map_mul, map_pow, StarSubalgebra.subtype_apply,
      canonicalNegativeRow_coe, a, aC, Matrix.cons_val_zero, Matrix.cons_val_one] using h
  have hsupport : canonicalNegativeRow S i * P = canonicalNegativeRow S i := by
    have h := congrArg C.subtype (canonicalNegativeRow_support s hs i).2
    simpa only [map_mul, StarSubalgebra.subtype_apply, canonicalNegativeRow_coe, canonicalTailProjection_coe] using h
  have herr := he i hi
  rw [heq, hfinal, ← mul_assoc, hsupport] at herr
  exact herr

/-- The shrink for the two given canonical rows; no chosen encoding or
extra commutant hypothesis occurs in this application. -/
lemma exists_canonicalNegative_shrink [Nontrivial E]
    (s t : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (hc : bergRowsCommute s t) (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    let P := canonicalTailProjection s 1
    let Q := canonicalTailProjection t 1
    ∃ v : E, P * v = v ∧ v * P = v ∧ star v * v = P ∧ v * star v = P * Q ∧
      ∀ i ≤ m, ‖v * canonicalNegativeRow s i * star v - canonicalNegativeRow s i * Q‖ < ε := by
  let S : ℕ → closedCanonicalRowAlgebra s := fun i => ⟨s i, mem_closedCanonicalRowAlgebra s i⟩
  let T : ℕ → closedCanonicalRowAlgebra t := fun i => ⟨t i, mem_closedCanonicalRowAlgebra t i⟩
  have hS (i j : ℕ) : star (S i) * S j = if i = j then 1 else 0 := by
    by_cases hij : i = j
    · rw [ite_eq_left hij]
      apply Subtype.ext
      change star (s i) * s j = 1
      simpa only [ite_eq_left hij] using hs i j
    · rw [ite_eq_right hij]
      apply Subtype.ext
      change star (s i) * s j = 0
      simpa only [ite_eq_right hij] using hs i j
  have hT (i j : ℕ) : star (T i) * T j = if i = j then 1 else 0 := by
    by_cases hij : i = j
    · rw [ite_eq_left hij]
      apply Subtype.ext
      change star (t i) * t j = 1
      simpa only [ite_eq_left hij] using ht i j
    · rw [ite_eq_right hij]
      apply Subtype.ext
      change star (t i) * t j = 0
      simpa only [ite_eq_right hij] using ht i j
  exact exists_canonicalNegative_common_shrink
    (closedCanonicalRowAlgebra s) (closedCanonicalRowAlgebra t)
    (closedCanonicalRowAlgebras_commute s t hc) S T hS hT m ε hε

end WeakPureInfiniteness

end

end OAI
