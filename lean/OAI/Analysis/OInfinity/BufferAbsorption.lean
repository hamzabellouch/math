import OAI.Analysis.OInfinity.FiniteRowDefect

namespace OAI

/-! # An ambient unitary for finite-row absorption

A coisometric binary row in a corner and an isometry onto its complement
give an explicit ambient unitary.  Applied to the finite Fock isometry,
this unitary absorbs the coisometric target row with a vanishing error.
Its path component is recorded by an explicit, fixed anchor; connectedness
of that anchor is not inferred from the corner relations.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

/-- The exact corner data used by the absorption formula. -/
structure BufferAbsorptionCorner (E : Type*) [CStarAlgebra E] where
  q : E
  w : E
  a : E
  b : E
  projection : IsStarProjection q
  w_gram : star w * w = 1
  w_range : w * star w = 1 - q
  w_orthogonal : q * w = 0
  a_gram : star a * a = q
  b_gram : star b * b = q
  orthogonal : star a * b = 0
  ranges : a * star a + b * star b = q

namespace BufferAbsorptionCorner

variable (D : BufferAbsorptionCorner E)

lemma a_right : D.a * D.q = D.a :=
  relativeIsometry_mul_support D.a D.q D.a_gram
    D.projection.isSelfAdjoint.star_eq D.projection.isIdempotentElem.eq

lemma b_right : D.b * D.q = D.b :=
  relativeIsometry_mul_support D.b D.q D.b_gram
    D.projection.isSelfAdjoint.star_eq D.projection.isIdempotentElem.eq

lemma reverse_orthogonal : star D.b * D.a = 0 := by
  simpa only [star_mul, star_star, star_zero] using congrArg star D.orthogonal

lemma a_left : D.q * D.a = D.a := by
  rw [← D.ranges, add_mul, mul_assoc, D.a_gram, D.a_right,
    mul_assoc, D.reverse_orthogonal, mul_zero, add_zero]

lemma b_left : D.q * D.b = D.b := by
  rw [← D.ranges, add_mul, mul_assoc, D.orthogonal, mul_zero,
    mul_assoc, D.b_gram, D.b_right, zero_add]

lemma a_star_right : star D.a * D.q = star D.a := by
  simpa only [star_mul, D.projection.isSelfAdjoint.star_eq] using
    congrArg star D.a_left

lemma b_star_right : star D.b * D.q = star D.b := by
  simpa only [star_mul, D.projection.isSelfAdjoint.star_eq] using
    congrArg star D.b_left

lemma a_star_left : D.q * star D.a = star D.a := by
  simpa only [star_mul, D.projection.isSelfAdjoint.star_eq] using
    congrArg star D.a_right

lemma b_star_left : D.q * star D.b = star D.b := by
  simpa only [star_mul, D.projection.isSelfAdjoint.star_eq] using
    congrArg star D.b_right

lemma a_w : D.a * D.w = 0 := by
  rw [← D.a_right, mul_assoc, D.w_orthogonal, mul_zero]

lemma b_w : D.b * D.w = 0 := by
  rw [← D.b_right, mul_assoc, D.w_orthogonal, mul_zero]

lemma a_star_w : star D.a * D.w = 0 := by
  rw [← D.a_star_right, mul_assoc, D.w_orthogonal, mul_zero]

lemma b_star_w : star D.b * D.w = 0 := by
  rw [← D.b_star_right, mul_assoc, D.w_orthogonal, mul_zero]

/-- The coisometry filling the complement of the first binary range. -/
def remainder : E := star D.b + (1 - D.q)

lemma remainder_gram : star D.remainder * D.remainder =
    D.b * star D.b + (1 - D.q) := by
  have h₁ : D.b * (1 - D.q) = 0 := by rw [mul_sub, mul_one, D.b_right, sub_self]
  have h₂ : (1 - D.q) * star D.b = 0 := by
    rw [sub_mul, one_mul, D.b_star_left, sub_self]
  dsimp only [remainder]
  rw [star_add, star_star, star_sub, star_one, D.projection.isSelfAdjoint.star_eq,
    add_mul, mul_add, mul_add, h₁, h₂,
    D.projection.one_sub.isIdempotentElem.eq]
  abel

lemma remainder_range : D.remainder * star D.remainder = 1 := by
  have h₁ : star D.b * (1 - D.q) = 0 := by
    rw [mul_sub, mul_one, D.b_star_right, sub_self]
  have h₂ : (1 - D.q) * D.b = 0 := by rw [sub_mul, one_mul, D.b_left, sub_self]
  dsimp only [remainder]
  rw [star_add, star_star, star_sub, star_one, D.projection.isSelfAdjoint.star_eq,
    add_mul, mul_add, mul_add, D.b_gram, h₁, h₂,
    D.projection.one_sub.isIdempotentElem.eq]
  abel

lemma remainder_a : D.remainder * D.a = 0 := by
  dsimp only [remainder]
  rw [add_mul, D.reverse_orthogonal, sub_mul, one_mul, D.a_left]
  abel

/-- The fixed anchor and its deformation by an arbitrary ambient unitary. -/
def rotationValue (u : unitary E) : E :=
  star D.a + D.w * (u : E) * D.remainder

lemma rotationValue_mem_unitary (u : unitary E) :
    D.rotationValue u ∈ unitary E := by
  have hcross : D.a * (D.w * (u : E) * D.remainder) = 0 := by
    calc
      _ = (D.a * D.w) * (u : E) * D.remainder := by noncomm_ring
      _ = 0 := by rw [D.a_w, zero_mul, zero_mul]
  have hcross' : star (D.w * (u : E) * D.remainder) * star D.a = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star hcross
  have hcross₂ : star D.a * star D.remainder = 0 := by
    simpa only [star_mul, star_zero] using congrArg star D.remainder_a
  have hgram : star (D.rotationValue u) * D.rotationValue u = 1 := by
    dsimp only [rotationValue]
    rw [star_add, star_star, add_mul, mul_add, mul_add, hcross, hcross']
    have htail : star (D.w * (u : E) * D.remainder) *
        (D.w * (u : E) * D.remainder) = star D.remainder * D.remainder := by
      rw [star_mul, star_mul]
      calc
        _ = star D.remainder * star (u : E) * (star D.w * D.w) *
            (u : E) * D.remainder := by noncomm_ring
        _ = star D.remainder * (star (u : E) * (u : E)) * D.remainder := by
          rw [D.w_gram]; noncomm_ring
        _ = _ := by rw [Unitary.star_mul_self_of_mem u.property, mul_one]
    rw [htail, D.remainder_gram]
    rw [show D.a * star D.a + 0 + (0 + (D.b * star D.b + (1 - D.q))) =
      (D.a * star D.a + D.b * star D.b) + (1 - D.q) by abel, D.ranges]
    abel
  have hrange : D.rotationValue u * star (D.rotationValue u) = 1 := by
    dsimp only [rotationValue]
    rw [star_add, star_star, add_mul, mul_add, mul_add, D.a_gram]
    have h₁ : star D.a * star (D.w * (u : E) * D.remainder) = 0 := by
      rw [star_mul]
      calc
        _ = (star D.a * star D.remainder) * star (D.w * (u : E)) := by noncomm_ring
        _ = 0 := by rw [hcross₂, zero_mul]
    have h₂ : (D.w * (u : E) * D.remainder) * D.a = 0 := by
      rw [mul_assoc, D.remainder_a, mul_zero]
    have htail : (D.w * (u : E) * D.remainder) *
        star (D.w * (u : E) * D.remainder) = D.w * star D.w := by
      rw [star_mul, star_mul]
      calc
        _ = D.w * (u : E) * (D.remainder * star D.remainder) *
            star (u : E) * star D.w := by noncomm_ring
        _ = D.w * ((u : E) * star (u : E)) * star D.w := by
          rw [D.remainder_range]; noncomm_ring
        _ = _ := by rw [Unitary.mul_star_self_of_mem u.property, mul_one]
    rw [h₁, h₂, htail, D.w_range]
    abel
  exact ⟨hgram, hrange⟩

def rotation (u : unitary E) : unitary E :=
  ⟨D.rotationValue u, D.rotationValue_mem_unitary u⟩

/-- This value, rather than the identity, is the immediate path anchor. -/
def anchor : unitary E := D.rotation 1

def absorption (u : unitary E) : unitary E := D.rotation u * star u

lemma absorption_continuous : Continuous D.absorption := by
  have hrot : Continuous D.rotation := by
    apply Continuous.subtype_mk
    change Continuous (fun u : unitary E => star D.a + D.w * (u : E) * D.remainder)
    fun_prop
  exact hrot.mul continuous_star

lemma absorption_joined_anchor (u : unitary E) (hu : Joined (1 : unitary E) u) :
    Joined D.anchor (D.absorption u) := by
  simpa only [absorption, star_one, mul_one, anchor] using
    hu.map D.absorption_continuous

lemma absorption_expansion (u : unitary E) (v : E) (hu : (u : E) * D.q = v) :
    (D.absorption u : E) =
      star D.a * star v + D.w * v * star D.b * star v +
        D.w * (1 - v * star v) := by
  have hvstar : D.q * star (u : E) = star v := by
    simpa only [star_mul, D.projection.isSelfAdjoint.star_eq] using congrArg star hu
  have ha : star D.a * star (u : E) = star D.a * star v := by
    calc
      _ = (star D.a * D.q) * star (u : E) := by rw [D.a_star_right]
      _ = star D.a * (D.q * star (u : E)) := by noncomm_ring
      _ = _ := by rw [hvstar]
  have hb : (u : E) * star D.b * star (u : E) = v * star D.b * star v := by
    have hqbq : D.q * star D.b * D.q = star D.b := by
      rw [D.b_star_left, D.b_star_right]
    calc
      _ = (u : E) * (D.q * star D.b * D.q) * star (u : E) := by rw [hqbq]
      _ = ((u : E) * D.q) * star D.b * (D.q * star (u : E)) := by noncomm_ring
      _ = _ := by rw [hu, hvstar]
  have hq : (u : E) * D.q * star (u : E) = v * star v := by
    calc
      _ = (u : E) * (D.q * D.q) * star (u : E) := by
        rw [D.projection.isIdempotentElem.eq]
      _ = ((u : E) * D.q) * (D.q * star (u : E)) := by noncomm_ring
      _ = _ := by rw [hu, hvstar]
  change (star D.a + D.w * (u : E) * (star D.b + (1 - D.q))) * star (u : E) = _
  rw [mul_add, add_mul, ha]
  calc
    _ = star D.a * star v + D.w * ((u : E) * star D.b * star (u : E)) +
        D.w * ((u : E) * (1 - D.q) * star (u : E)) := by noncomm_ring
    _ = _ := by
      rw [hb, mul_sub, mul_one, sub_mul, Unitary.mul_star_self_of_mem u.property, hq]
      noncomm_ring

lemma absorption_error_formula (u : unitary E) (v s t : E)
    (hu : (u : E) * D.q = v) (htq : t * D.q = t)
    (hat : Commute (star D.a) t) :
    (D.absorption u : E) * s - (t + D.w * s * star D.w) * (D.absorption u : E) =
      star D.a * (star v * s - t * star v) +
        D.w * ((v * star D.b * star v) * s - s * (v * star D.b * star v)) +
        D.w * (s * (v * star v) - (v * star v) * s) := by
  have htw : t * D.w = 0 := by
    rw [← htq, mul_assoc, D.w_orthogonal, mul_zero]
  have hwa : star D.w * star D.a = 0 := by
    simpa only [star_mul, star_zero] using congrArg star D.a_w
  have hleft : (t + D.w * s * star D.w) * (D.absorption u : E) =
      t * star D.a * star v + D.w * s * (v * star D.b * star v) +
        D.w * s * (1 - v * star v) := by
    rw [D.absorption_expansion u v hu, mul_add, mul_add, add_mul, add_mul, add_mul]
    have h₁ : t * (D.w * v * star D.b * star v) = 0 := by
      calc
        _ = (t * D.w) * v * star D.b * star v := by noncomm_ring
        _ = 0 := by rw [htw, zero_mul, zero_mul, zero_mul]
    have h₂ : t * (D.w * (1 - v * star v)) = 0 := by
      rw [← mul_assoc, htw, zero_mul]
    have h₃ : (D.w * s * star D.w) * (star D.a * star v) = 0 := by
      calc
        _ = D.w * s * (star D.w * star D.a) * star v := by noncomm_ring
        _ = 0 := by rw [hwa, mul_zero, zero_mul]
    have h₄ : (D.w * s * star D.w) * (D.w * v * star D.b * star v) =
        D.w * s * (v * star D.b * star v) := by
      calc
        _ = D.w * s * (star D.w * D.w) * v * star D.b * star v := by noncomm_ring
        _ = _ := by rw [D.w_gram, mul_one]; noncomm_ring
    have h₅ : (D.w * s * star D.w) * (D.w * (1 - v * star v)) =
        D.w * s * (1 - v * star v) := by
      calc
        _ = D.w * s * (star D.w * D.w) * (1 - v * star v) := by noncomm_ring
        _ = _ := by rw [D.w_gram, mul_one]
    rw [h₁, h₂, h₃, h₄, h₅]
    noncomm_ring
  rw [hleft, D.absorption_expansion u v hu]
  have hta : t * star D.a = star D.a * t := hat.eq.symm
  noncomm_ring [hta]

private lemma transported_commutator_bound (v c s t : E)
    (hv : ‖v‖ ≤ 1) (hc : ‖c‖ ≤ 1) (hct : Commute c t) :
    ‖(v * c * star v) * s - s * (v * c * star v)‖ ≤
      ‖s * v - v * t‖ + ‖star v * s - t * star v‖ := by
  have he : (v * c * star v) * s - s * (v * c * star v) =
      v * c * (star v * s - t * star v) - (s * v - v * t) * c * star v := by
    calc
      _ = v * c * (star v * s - t * star v) - (s * v - v * t) * c * star v +
          v * (c * t - t * c) * star v := by noncomm_ring
      _ = _ := by rw [hct.eq, sub_self, mul_zero, zero_mul, add_zero]
  rw [he]
  calc
    _ ≤ ‖v * c * (star v * s - t * star v)‖ +
        ‖(s * v - v * t) * c * star v‖ := norm_sub_le _ _
    _ ≤ ‖star v * s - t * star v‖ + ‖s * v - v * t‖ := by
      apply add_le_add
      · exact (norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _)
          ((norm_mul_le _ _).trans ((mul_le_of_le_one_right (norm_nonneg _) hc).trans hv)))
      · exact (norm_mul_le _ _).trans ((mul_le_of_le_one_right (norm_nonneg _)
          (by simpa only [norm_star] using hv)).trans
          ((norm_mul_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _) hc)))
    _ = _ := add_comm _ _

lemma absorption_error_bound [Nontrivial E] (u : unitary E) (v s t : E)
    (hu : (u : E) * D.q = v) (htq : t * D.q = t)
    (hat : Commute (star D.a) t) (hbt : Commute (star D.b) t)
    (hv : ‖v‖ ≤ 1) :
    ‖(D.absorption u : E) * s - (t + D.w * s * star D.w) * (D.absorption u : E)‖ ≤
      2 * ‖s * v - v * t‖ + 3 * ‖star v * s - t * star v‖ := by
  have hw : ‖D.w‖ ≤ 1 := by
    have h := congrArg norm D.w_gram
    rw [CStarRing.norm_star_mul_self, norm_one] at h
    nlinarith [norm_nonneg D.w]
  have hn (x : E) (hx : star x * x = D.q) : ‖x‖ ≤ 1 := by
    have h := congrArg norm hx
    rw [CStarRing.norm_star_mul_self] at h
    have hq := IsStarProjection.norm_le D.q D.projection
    nlinarith [norm_nonneg x]
  have ha : ‖star D.a‖ ≤ 1 := by simpa only [norm_star] using hn D.a D.a_gram
  have hb : ‖star D.b‖ ≤ 1 := by simpa only [norm_star] using hn D.b D.b_gram
  have hf : ‖s * (v * star v) - (v * star v) * s‖ ≤
      ‖s * v - v * t‖ + ‖star v * s - t * star v‖ := by
    have he : s * (v * star v) - (v * star v) * s =
        (s * v - v * t) * star v - v * (star v * s - t * star v) := by noncomm_ring
    rw [he]
    calc
      _ ≤ ‖(s * v - v * t) * star v‖ + ‖v * (star v * s - t * star v)‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add
        ((norm_mul_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _)
          (by simpa only [norm_star] using hv)))
        ((norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) hv))
  rw [D.absorption_error_formula u v s t hu htq hat]
  calc
    _ ≤ (‖star D.a * (star v * s - t * star v)‖ +
        ‖D.w * ((v * star D.b * star v) * s - s * (v * star D.b * star v))‖) +
        ‖D.w * (s * (v * star v) - (v * star v) * s)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ‖star v * s - t * star v‖ +
        (‖s * v - v * t‖ + ‖star v * s - t * star v‖) +
        (‖s * v - v * t‖ + ‖star v * s - t * star v‖) := by
      apply add_le_add
      · apply add_le_add
        · exact (norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) ha)
        · exact ((norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) hw)).trans
            (transported_commutator_bound v (star D.b) s t hv hb hbt)
      · exact ((norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) hw)).trans hf
    _ = _ := by ring

end BufferAbsorptionCorner

section FiniteRows

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma finiteRowWordSum_left_of_commute (s t : I → E) (r q : E)
    (hq : q * q = q) (hqr : Commute q r) (hqs : ∀ i, Commute q (s i)) (m : ℕ) :
    q * finiteRowWordSum s t r q m = finiteRowWordSum s t r q m := by
  induction m with
  | zero =>
    change q * (r * q) = r * q
    rw [← mul_assoc, hqr.eq, mul_assoc, hq]
  | succ m ih =>
    change q * (r * q + finiteCuntzTransfer t s (finiteRowWordSum s t r q m)) = _
    rw [mul_add, ← mul_assoc q r, hqr.eq, mul_assoc r q q, hq]
    congr 1
    simp only [finiteCuntzTransfer, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = (q * s i) * finiteRowWordSum s t r q m * star (t i) := by noncomm_ring
      _ = s i * (q * finiteRowWordSum s t r q m) * star (t i) := by
        rw [(hqs i).eq]; noncomm_ring
      _ = _ := by rw [ih]

omit [DecidableEq I] in
lemma finiteRowIsometry_left_of_commute (s t : I → E) (r q : E)
    (hq : q * q = q) (hqr : Commute q r) (hqs : ∀ i, Commute q (s i)) (m : ℕ) :
    q * finiteRowIsometry s t r q m = finiteRowIsometry s t r q m := by
  rw [finiteRowIsometry, mul_smul_comm,
    finiteRowWordSum_left_of_commute s t r q hq hqr hqs]

/-- An actual ambient unitary absorbs a finite coisometric row.  The unitary
is connected to the fixed, explicit buffer anchor. -/
lemma BufferAbsorptionCorner.exists_finite_absorption [Nontrivial E]
    (D : BufferAbsorptionCorner E) (s t : I → E) (r : E)
    (hrr : star r * r = 1) (hr : ∀ i, star r * s i = 0)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (hqr : Commute D.q r) (hqs : ∀ i, Commute D.q (s i))
    (htq : ∀ i, t i * D.q = t i) (ht : ∑ i, t i * star (t i) = D.q)
    (htt : ∀ i j, star (t i) * t j = if i = j then D.q else 0)
    (hat : ∀ i, Commute (star D.a) (t i))
    (hbt : ∀ i, Commute (star D.b) (t i))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ W : unitary E, Joined D.anchor W ∧
      ∀ i, ‖(W : E) * s i - (t i + D.w * s i * star D.w) * (W : E)‖ < ε := by
  let δ := ε / 6
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  obtain ⟨m, hm⟩ := exists_nat_gt (2 / δ ^ 2)
  have hsmall : 2 / ((m : ℝ) + 1) < δ ^ 2 := by
    have hδsq : 0 < δ ^ 2 := sq_pos_of_pos hδ
    have hm' : 2 < (m : ℝ) * δ ^ 2 := (div_lt_iff₀ hδsq).mp hm
    apply (div_lt_iff₀ (by positivity : 0 < (m : ℝ) + 1)).mpr
    nlinarith
  let v := finiteRowIsometry s t r D.q m
  have hvg : star v * v = D.q := finiteRowIsometry_gram s t r D.q
    D.projection.isIdempotentElem.eq D.projection.isSelfAdjoint.star_eq hrr hr hs htq ht m
  have hvq : v * D.q = v := relativeIsometry_mul_support v D.q hvg
    D.projection.isSelfAdjoint.star_eq D.projection.isIdempotentElem.eq
  have hqv : D.q * v = v := finiteRowIsometry_left_of_commute s t r D.q
    D.projection.isIdempotentElem.eq hqr hqs m
  have hvstarq : star v * D.q = star v := by
    simpa only [star_mul, D.projection.isSelfAdjoint.star_eq] using congrArg star hqv
  have hvw : star v * D.w = 0 := by
    rw [← hvstarq, mul_assoc, D.w_orthogonal, mul_zero]
  obtain ⟨u, hu, _, huv⟩ := exists_explicit_connected_unitary_extension v D.w
    (by rw [mul_assoc, hvg, hvq]) D.w_gram (by rw [hvg]; exact D.w_orthogonal)
    (by rw [mul_assoc, hvw, mul_zero])
  have huq : (u : E) * D.q = v := by simpa only [hvg] using huv
  have hvn : ‖v‖ ≤ 1 := finiteRowIsometry_norm_le s t r D.q
    D.projection.isIdempotentElem.eq D.projection.isSelfAdjoint.star_eq hrr hr hs htq ht m
  refine ⟨D.absorption u, D.absorption_joined_anchor u hu, ?_⟩
  intro i
  have hf : ‖s i * v - v * t i‖ < δ := by
    have h := finiteRowIsometry_forward_norm_sq s t r D.q
      D.projection.isIdempotentElem.eq D.projection.isSelfAdjoint.star_eq
      hrr hr hs htq ht htt m i
    change ‖s i * v - v * t i‖ ^ 2 ≤ _ at h
    nlinarith [norm_nonneg (s i * v - v * t i)]
  have hb : ‖star v * s i - t i * star v‖ < δ := by
    have h := finiteRowIsometry_backward_norm_sq s t r D.q
      D.projection.isIdempotentElem.eq D.projection.isSelfAdjoint.star_eq
      hrr hr hs htq ht htt m i
    have he : star v * s i - t i * star v =
        star (star (s i) * v - v * star (t i)) := by
      simp only [star_sub, star_mul, star_star]
    rw [he, norm_star]
    have hone : ((m : ℝ) + 1)⁻¹ ≤ 2 / ((m : ℝ) + 1) := by
      rw [← one_div]
      exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
    change ‖star (s i) * v - v * star (t i)‖ ^ 2 ≤ _ at h
    nlinarith [norm_nonneg (star (s i) * v - v * star (t i))]
  calc
    _ ≤ 2 * ‖s i * v - v * t i‖ + 3 * ‖star v * s i - t i * star v‖ :=
      D.absorption_error_bound u v (s i) (t i) huq (htq i) (hat i) (hbt i) hvn
    _ < ε := by dsimp only [δ] at hf hb; linarith

end FiniteRows

end WeakPureInfiniteness

end

end OAI
