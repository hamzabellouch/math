import OAI.Analysis.OInfinity.ClockTransport

namespace OAI

/-! # Clock correction of the actual cyclic bands

A clock which cycles the projection partition turns a band of degree `d`
into a block diagonal element after multiplication by its inverse `d`th
power. The clock and the partition can be constructed inside a prescribed
closed row algebra. This does not assert the endpoint cocycle equation.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

lemma clock_cycles_pow {N : ℕ} [NeZero N] (u : E) (e : ZMod N → E)
    (hc : ∀ j, u * e j = e (j + 1) * u) (d : ℕ) (j : ZMod N) :
    u ^ d * e j = e (j + (d : ZMod N)) * u ^ d := by
  induction d generalizing j with
  | zero => simp
  | succ d ih =>
      calc
        u ^ (d + 1) * e j = u ^ d * (u * e j) := by rw [pow_succ, mul_assoc]
        _ = u ^ d * (e (j + 1) * u) := by rw [hc]
        _ = e ((j + 1) + (d : ZMod N)) * (u ^ d * u) := by
          rw [← mul_assoc, ih, mul_assoc]
        _ = e (j + ((d + 1 : ℕ) : ZMod N)) * u ^ (d + 1) := by
          rw [pow_succ]
          congr 2
          push_cast
          abel

lemma clock_inverse_pow_cycles {N : ℕ} [NeZero N] (u : E) (e : ZMod N → E)
    (he : ∀ j, star (e j) = e j)
    (hc : ∀ j, u * e j = e (j + 1) * u) (d : ℕ) (j : ZMod N) :
    star (u ^ d) * e (j + (d : ZMod N)) = e j * star (u ^ d) := by
  simpa only [star_mul, he] using (congrArg star (clock_cycles_pow u e hc d j)).symm

/-- Exact removal of the outer band degree. Coefficients remain literal. -/
lemma clocked_band_diagonal {N : ℕ} [NeZero N] (u : E) (e : ZMod N → E)
    (he : ∀ j, star (e j) = e j)
    (hc : ∀ j, u * e j = e (j + 1) * u) (d : ℕ) (x : ZMod N → E) :
    star (u ^ d) * towerBand e (Equiv.addRight (d : ZMod N)) x =
      ∑ j, e j * (star (u ^ d) * x j) * e j := by
  unfold towerBand
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change star (u ^ d) * (e (j + (d : ZMod N)) * x j * e j) = _
  rw [← mul_assoc, ← mul_assoc, clock_inverse_pow_cycles u e he hc]
  simp only [mul_assoc]

/-- The inverse clock makes the band commute with every projection cell. -/
lemma clocked_band_commute {N : ℕ} [NeZero N] (u : E) (e : ZMod N → E)
    (he : ∀ j, IsStarProjection (e j))
    (ho : ∀ i j, i ≠ j → e i * e j = 0)
    (hc : ∀ j, u * e j = e (j + 1) * u) (d : ℕ) (x : ZMod N → E) (k : ZMod N) :
    Commute (star (u ^ d) * towerBand e (Equiv.addRight (d : ZMod N)) x) (e k) := by
  rw [clocked_band_diagonal u e (fun j => (he j).isSelfAdjoint.star_eq) hc]
  apply Commute.sum_left
  intro j _
  change (e j * (star (u ^ d) * x j) * e j) * e k =
    e k * (e j * (star (u ^ d) * x j) * e j)
  by_cases hjk : j = k
  · subst k
    have hl : (e j * (star (u ^ d) * x j) * e j) * e j =
        e j * (star (u ^ d) * x j) * e j := by
      rw [mul_assoc _ (e j) (e j), (he j).isIdempotentElem.eq]
    rw [hl]
    symm
    calc
      e j * (e j * (star (u ^ d) * x j) * e j) =
          (e j * e j) * (star (u ^ d) * x j) * e j := by noncomm_ring
      _ = e j * (star (u ^ d) * x j) * e j := by rw [(he j).isIdempotentElem.eq]
  · have hl : (e j * (star (u ^ d) * x j) * e j) * e k = 0 := by
      rw [mul_assoc _ (e j) (e k), ho j k hjk, mul_zero]
    have hr : e k * (e j * (star (u ^ d) * x j) * e j) = 0 := by
      calc
        e k * (e j * (star (u ^ d) * x j) * e j) =
            (e k * e j) * (star (u ^ d) * x j) * e j := by noncomm_ring
        _ = 0 := by rw [ho k j (Ne.symm hjk), zero_mul, zero_mul]
    exact hl.trans hr.symm

lemma clocked_masked_band_commute {N : ℕ} [NeZero N] (u : E) (e : ZMod N → E)
    (he : ∀ j, IsStarProjection (e j))
    (ho : ∀ i j, i ≠ j → e i * e j = 0)
    (hc : ∀ j, u * e j = e (j + 1) * u) (d : ℕ) (x : ZMod N → E)
    (o k : ZMod N) :
    Commute (star (u ^ d) * maskedTowerBand e (Equiv.addRight (d : ZMod N)) x o) (e k) :=
  clocked_band_commute u e he ho hc d (maskedBandCoefficients x o) k

/-- The norm and initial Gram are unchanged by multiplication by a unitary clock. -/
lemma clocked_band_gram (u x : E) (hu : u ∈ unitary E) (d : ℕ) :
    star (star (u ^ d) * x) * (star (u ^ d) * x) = star x * x := by
  have hpow : u ^ d ∈ unitary E := (unitary E).pow_mem hu d
  simp only [star_mul, star_star]
  calc
    _ = star x * (u ^ d * star (u ^ d)) * x := by noncomm_ring
    _ = _ := by rw [hpow.2, mul_one]

lemma clocked_band_norm (u x : E) (hu : u ∈ unitary E) (d : ℕ) :
    ‖star (u ^ d) * x‖ = ‖x‖ := by
  exact CStarRing.norm_mem_unitary_mul x (Unitary.star_mem ((unitary E).pow_mem hu d))

lemma evenRohlinClock_cycles_mod {n : ℕ} (r : Fin 2 × Fin n → E)
    (hr : ∀ i j, star (r i) * r j = if i = j then 1 else 0)
    (hsum : (∑ i, r i * star (r i)) = 1) (L : ℕ) (hL : 0 < L)
    (m : ℕ) (j : ZMod (2 ^ m)) :
    evenRohlinClock r L m * evenRohlinProjection 1 r L m j.val *
      star (evenRohlinClock r L m) = evenRohlinProjection 1 r L m (j + 1).val := by
  rw [evenRohlinClock_cycles r hr hsum L hL]
  have hval : (j + 1).val = (j.val + 1) % (2 ^ m) := by
    have he : j + 1 = ((j.val + 1 : ℕ) : ZMod (2 ^ m)) := by
      simp only [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
    rw [he, ZMod.val_natCast]
  rw [hval]
  by_cases hlt : j.val + 1 < 2 ^ m
  · rw [Nat.mod_eq_of_lt hlt]
  · have heq : j.val + 1 = 2 ^ m := by have := j.val_lt; omega
    rw [heq, Nat.mod_self]
    simpa only [zero_add] using (evenRohlinProjection_period 1 r L m 0)

lemma evenRohlinClock_transports {n : ℕ} (r : Fin 2 × Fin n → E)
    (hr : ∀ i j, star (r i) * r j = if i = j then 1 else 0)
    (hsum : (∑ i, r i * star (r i)) = 1) (L : ℕ) (hL : 0 < L)
    (m : ℕ) (j : ZMod (2 ^ m)) :
    evenRohlinClock r L m * evenRohlinProjection 1 r L m j.val =
      evenRohlinProjection 1 r L m (j + 1).val * evenRohlinClock r L m := by
  have h := congrArg (fun x : E => x * evenRohlinClock r L m)
    (evenRohlinClock_cycles_mod r hr hsum L hL m j)
  simpa only [mul_assoc, (evenRohlinClock_mem_unitary r hr hsum L hL m).1, mul_one] using h

private lemma clock_small_sqrt (C ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℕ, 0 < L ∧ C * Real.sqrt (18 / (L : ℝ)) < ε := by
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  obtain ⟨L, hL⟩ := exists_nat_gt (18 * C ^ 2 / ε ^ 2 + 1)
  have hLpos : 0 < L := by
    have hnonneg : 0 ≤ 18 * C ^ 2 / ε ^ 2 := by positivity
    exact_mod_cast (show (0 : ℝ) < (L : ℝ) by linarith)
  have hLreal : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hLpos
  have hbound : 18 * C ^ 2 < (L : ℝ) * ε ^ 2 := by
    apply (div_lt_iff₀ hεsq).mp
    linarith
  have hbound' : 18 * C ^ 2 / (L : ℝ) < ε ^ 2 := (div_lt_iff₀ hLreal).mpr (by nlinarith)
  have hsqrt := Real.sq_sqrt (show 0 ≤ 18 / (L : ℝ) by positivity)
  have he : (C * Real.sqrt (18 / (L : ℝ))) ^ 2 = 18 * C ^ 2 / (L : ℝ) := by
    rw [mul_pow, hsqrt]
    ring
  refine ⟨L, hLpos, ?_⟩
  nlinarith

/-- The clock and all cells are constructed in `B`; their row commutators
and shift errors have an arbitrary prescribed tolerance. -/
lemma exists_even_clock_partition_in {n : ℕ} (B : StarSubalgebra ℂ E)
    [IsClosed (B : Set E)] (r : Fin 2 × Fin n → E)
    (hr : ∀ i j, star (r i) * r j = if i = j then 1 else 0)
    (hsum : (∑ i, r i * star (r i)) = 1) (hmem : ∀ i, r i ∈ B)
    (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (u : E) (e : ZMod (2 ^ m) → E),
      u ∈ B ∧ u ∈ unitary E ∧ u ^ (2 ^ m) = 1 ∧
      (∀ j, e j ∈ B) ∧ (∀ j, IsStarProjection (e j)) ∧ (∑ j, e j) = 1 ∧
      (∀ i j, i ≠ j → e i * e j = 0) ∧
      (∀ j, u * e j = e (j + 1) * u) ∧
      ‖evenRowShift r u - u‖ < ε ∧
      (∀ i, ‖u * r i - r i * u‖ < ε) ∧
      (∀ j, ‖evenRowShift r (e j) - e (j + 1)‖ < ε) := by
  let R : Fin 2 × Fin n → B := fun i => ⟨r i, hmem i⟩
  have hR (i j : Fin 2 × Fin n) : star (R i) * R j = if i = j then 1 else 0 := by
    by_cases hij : i = j
    · subst j
      rw [ite_eq_left rfl]
      apply Subtype.ext
      change star (r i) * r i = 1
      simpa only [ite_true] using hr i i
    · rw [ite_eq_right hij]
      apply Subtype.ext
      change star (r i) * r j = 0
      simpa only [ite_eq_right hij] using hr i j
  have hRsum : (∑ i, R i * star (R i)) = 1 := by
    apply Subtype.ext
    change B.subtype (∑ i, R i * star (R i)) = B.subtype 1
    simp only [map_sum, map_mul, map_star, map_one]
    exact hsum
  obtain ⟨L, hL, hsmall⟩ := clock_small_sqrt
    (4 * (m : ℝ) * (4 * (m : ℝ) + 1)) ε hε
  let U : B := evenRohlinClock R L m
  let P : ℕ → B := evenRohlinProjection 1 R L m
  let e : ZMod (2 ^ m) → E := fun j => (P j.val : E)
  have hU := evenRohlinClock_mem_unitary R hR hRsum L hL m
  have hmap (b : B) : ((evenRowShift R b : B) : E) = evenRowShift r (b : E) := by
    change B.subtype (∑ i, R i * b * star (R i)) = ∑ i, r i * (b : E) * star (r i)
    simp only [map_sum, map_mul, map_star, R]
    rfl
  have hsmallP : (m : ℝ) * (4 * (m : ℝ) + 1) * Real.sqrt (18 / (L : ℝ)) < ε := by
    apply lt_of_le_of_lt _ hsmall
    nlinarith [mul_nonneg (show 0 ≤ (m : ℝ) * (4 * (m : ℝ) + 1) by positivity)
      (Real.sqrt_nonneg (18 / (L : ℝ)))]
  obtain ⟨hp, hpsum, hpo⟩ := evenRohlinProjection_partition 1 R (star_one _) (one_mul _) hR hRsum L hL m
  refine ⟨(U : E), e, U.property, ?_, ?_, (fun j => (P j.val).property), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · exact congrArg B.subtype hU.1
    · exact congrArg B.subtype hU.2
  · exact congrArg B.subtype (evenRohlinClock_order R hR hRsum L hL m)
  · intro j
    exact ⟨congrArg B.subtype (hp j.val).isIdempotentElem.eq,
      congrArg B.subtype (hp j.val).isSelfAdjoint.star_eq⟩
  · change (∑ j : ZMod (2 ^ m), (P j.val : E)) = 1
    rw [sum_zmod_val (N := 2 ^ m) (fun j => (P j : E))]
    change (∑ j ∈ Finset.range (2 ^ m), B.subtype (P j)) = B.subtype 1
    rw [← map_sum]
    exact congrArg B.subtype hpsum
  · intro i j hij
    have hv : i.val ≠ j.val := by
      intro h
      apply hij
      rw [← ZMod.natCast_zmod_val i, ← ZMod.natCast_zmod_val j, h]
    exact congrArg B.subtype (hpo i.val j.val i.val_lt j.val_lt hv)
  · intro j
    exact congrArg B.subtype (evenRohlinClock_transports R hR hRsum L hL m j)
  · rw [← hmap]
    exact (evenRohlinClock_shift_bound R hR hRsum L hL m).trans_lt hsmall
  · intro i
    exact (evenRohlinClock_generator_commutator R hR hRsum L hL m i).trans_lt hsmall
  · intro j
    have hval : (j + 1).val = (j.val + 1) % (2 ^ m) := by
      have hcast : j + 1 = ((j.val + 1 : ℕ) : ZMod (2 ^ m)) := by
        simp only [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
      rw [hcast, ZMod.val_natCast]
    change ‖evenRowShift r (P j.val : E) - (P (j + 1).val : E)‖ < ε
    rw [hval, ← hmap]
    exact (evenRohlinProjection_cyclic_error 1 R (star_one _) (one_mul _) hR hRsum
      L hL m j.val j.val_lt).trans_lt hsmallP

/-- In the two-row application the clock and source partition commute
exactly with the opposite row, because they lie in the generated source
algebra. The source-generator estimate is quantitative. -/
lemma exists_binary_clock_commuting (s t : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (hsum : (∑ i, s i * star (s i)) = 1)
    (hcomm : bergRowsCommute s t) (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (u : E) (e : ZMod (2 ^ m) → E),
      u ∈ unitary E ∧ u ^ (2 ^ m) = 1 ∧
      (∀ j, IsStarProjection (e j)) ∧ (∑ j, e j) = 1 ∧
      (∀ i j, i ≠ j → e i * e j = 0) ∧
      (∀ j, u * e j = e (j + 1) * u) ∧
      ‖finiteRowShift s u - u‖ < ε ∧
      (∀ i, ‖u * s i - s i * u‖ < ε) ∧
      (∀ i, Commute u (t i)) ∧ (∀ j i, Commute (e j) (t i)) ∧
      (∀ j, ‖finiteRowShift s (e j) - e (j + 1)‖ < ε) := by
  let r : Fin 2 × Fin 1 → E := fun i => s i.1
  have hr (i j : Fin 2 × Fin 1) : star (r i) * r j = if i = j then 1 else 0 := by
    rcases i with ⟨i, i'⟩
    rcases j with ⟨j, j'⟩
    have he : i' = j' := Subsingleton.elim _ _
    subst j'
    simpa only [r, Prod.mk.injEq, and_true] using hs i j
  have hrsum : (∑ i, r i * star (r i)) = 1 := by
    simpa only [r, Fintype.sum_prod_type, Fin.sum_univ_one] using hsum
  obtain ⟨u, e, huB, hu, huN, heB, he, hesum, heo, hcycle, hshift, hgen, hp⟩ :=
    exists_even_clock_partition_in (closedCuntzRowAlgebra s) r hr hrsum
      (fun i => mem_closedCuntzRowAlgebra s i.1) m ε hε
  refine ⟨u, e, hu, huN, he, hesum, heo, hcycle, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [r, binary_evenRowShift] using hshift
  · intro i
    exact hgen (i, 0)
  · intro i
    exact closedCuntzRowAlgebras_commute s t hcomm u (t i) huB
      (mem_closedCuntzRowAlgebra t i)
  · intro j i
    exact closedCuntzRowAlgebras_commute s t hcomm (e j) (t i) (heB j)
      (mem_closedCuntzRowAlgebra t i)
  · intro j
    simpa only [r, binary_evenRowShift] using hp j

end WeakPureInfiniteness

end

end OAI
