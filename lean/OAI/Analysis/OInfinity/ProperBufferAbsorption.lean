import OAI.Analysis.OInfinity.BufferAnchor
import OAI.Analysis.OInfinity.ZeroUnitRows

namespace OAI

/-! # Connected absorption of an arbitrary finite proper row

The target row is completed inside the zero-unit buffer corner.  Only the
prescribed original entries must commute with the binary buffer; the
auxiliary completing entry is never included in that requirement.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

section Selected
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The finite Fock estimate only needs coefficient commutation at the
indices at which an intertwining estimate is requested. -/
lemma BufferAbsorptionCorner.exists_finite_absorption_on [Nontrivial E]
    (D : BufferAbsorptionCorner E) (s t : I → E) (r : E) (P : I → Prop)
    (hrr : star r * r = 1) (hr : ∀ i, star r * s i = 0)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (hqr : Commute D.q r) (hqs : ∀ i, Commute D.q (s i))
    (htq : ∀ i, t i * D.q = t i) (ht : ∑ i, t i * star (t i) = D.q)
    (htt : ∀ i j, star (t i) * t j = if i = j then D.q else 0)
    (hat : ∀ i, P i → Commute (star D.a) (t i))
    (hbt : ∀ i, P i → Commute (star D.b) (t i))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ W : unitary E, Joined D.anchor W ∧
      ∀ i, P i → ‖(W : E) * s i - (t i + D.w * s i * star D.w) * (W : E)‖ < ε := by
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
  intro i hi
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
      D.absorption_error_bound u v (s i) (t i) huq (htq i) (hat i hi) (hbt i hi) hvn
    _ < ε := by dsimp only [δ] at hf hb; linarith

end Selected

lemma BufferAbsorptionCorner.extend_finite_proper_row
    (D : BufferAbsorptionCorner E) (n : ℕ) (x : Fin (n + 1) → E)
    (hxs : ∀ i, D.q * x i = x i ∧ x i * D.q = x i)
    (hx : ∀ i j, star (x i) * x j = if i = j then D.q else 0) :
    ∃ t : Fin (n + 1) → E,
      (∀ i : Fin n, t i.succ = x i.castSucc) ∧
      (∀ i, D.q * t i = t i ∧ t i * D.q = t i) ∧
      (∀ i j, star (t i) * t j = if i = j then D.q else 0) ∧
      (∑ i, t i * star (t i)) = D.q := by
  let C := ProjectionCorner D.q D.projection.isSelfAdjoint.star_eq
    D.projection.isIdempotentElem.eq
  let x' : Fin (n + 1) → C := fun i => ⟨x i, hxs i⟩
  let a' : C := ⟨D.a, D.a_left, D.a_right⟩
  let b' : C := ⟨D.b, D.b_left, D.b_right⟩
  have hx' (i j : Fin (n + 1)) : star (x' i) * x' j = if i = j then 1 else 0 := by
    apply Subtype.ext
    change star (x i) * x j = ↑(if i = j then (1 : C) else 0)
    split_ifs with h
    · change star (x i) * x j = D.q
      simpa only [h, ite_true] using hx i j
    · change star (x i) * x j = 0
      simpa only [h, ite_false] using hx i j
  have hlast (i : Fin n) : star (x' (Fin.last n)) * x' i.castSucc = 0 := by
    rw [hx']
    have hne : Fin.last n ≠ i.castSucc := by
      intro h
      have hh := congrArg Fin.val h
      change n = (i : ℕ) at hh
      omega
    rw [ite_eq_right hne]
  obtain ⟨t, htx, ht, hts⟩ := finite_zero_unit_full_row
    (fun i : Fin n => x' i.castSucc) (x' (Fin.last n)) a' b'
    (fun i j => by simpa only [Fin.castSucc_inj] using hx' i.castSucc j.castSucc)
    (by simpa only [ite_true] using hx' (Fin.last n) (Fin.last n)) hlast
    (Subtype.ext D.a_gram) (Subtype.ext D.b_gram)
    (Subtype.ext D.orthogonal) (Subtype.ext D.ranges)
  refine ⟨fun i => (t i : E), fun i => congrArg (fun y : C => (y : E)) (htx i),
    fun i => (t i).property, ?_, ?_⟩
  · intro i j
    by_cases hij : i = j
    · subst j
      simp only [ite_true]
      have h := ht i i
      simp only [ite_true] at h
      have he := congrArg (fun y : C => (y : E)) h
      change star (t i : E) * (t i : E) = D.q at he
      exact he
    · rw [ite_eq_right hij]
      have h := ht i j
      rw [ite_eq_right hij] at h
      have he := congrArg (fun y : C => (y : E)) h
      change star (t i : E) * (t j : E) = 0 at he
      exact he

  · have h := congrArg (projectionCornerInclusion D.q D.projection.isSelfAdjoint.star_eq
      D.projection.isIdempotentElem.eq) hts
    simp only [map_sum, map_mul, map_star, projectionCornerInclusion_one] at h
    exact h

/-- Connected absorption of any finite original proper-row prefix. The
complementary source row remains as an explicit summand. -/
lemma exists_connected_proper_buffer_absorption [Nontrivial E]
    (s t r : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (hr : ∀ i j, star (r i) * r j = if i = j then 1 else 0)
    (hrs : bergRowsCommute r s) (hrt : bergRowsCommute r t)
    (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ U : unitary E, Joined (1 : unitary E) U ∧
      ∀ i : Fin n,
        ‖(U : E) * s i * star (U : E) -
          (t i * (1 - r 0 * star (r 0)) + s i * (r 0 * star (r 0)))‖ < ε := by
  have rc (i j : ℕ) : Commute (r i) (s j) ∧ Commute (star (r i)) (s j) :=
    ⟨(hrs i j).1, by simpa only [star_star] using (hrs i j).2.star_star⟩
  have tc (i j : ℕ) : Commute (r i) (t j) ∧ Commute (star (r i)) (t j) :=
    ⟨(hrt i j).1, by simpa only [star_star] using (hrt i j).2.star_star⟩
  obtain ⟨D, hDq, hDw, _, hDjoin, hDc⟩ := exists_connected_buffer_corner (r 0) (r 1) (r 2)
    (by simpa only [ite_true] using hr 0 0)
    (by simpa only [ite_true] using hr 1 1)
    (by simpa only [ite_true] using hr 2 2)
    (by simpa using hr 0 1) (by simpa using hr 0 2) (by simpa using hr 1 2)
  have hqs (i : ℕ) : Commute D.q (s i) := by
    rw [hDq]
    exact (Commute.one_left _).sub_left ((rc 0 i).1.mul_left (rc 0 i).2)
  have hqt (i : ℕ) : Commute D.q (t i) := by
    rw [hDq]
    exact (Commute.one_left _).sub_left ((tc 0 i).1.mul_left (tc 0 i).2)
  let x : Fin (n + 1) → E := fun i => t i * D.q
  have hxs (i : Fin (n + 1)) : D.q * x i = x i ∧ x i * D.q = x i := by
    constructor
    · change D.q * (t i * D.q) = t i * D.q
      rw [← mul_assoc, (hqt i).eq, mul_assoc, D.projection.isIdempotentElem.eq]
    · change (t i * D.q) * D.q = t i * D.q
      rw [mul_assoc, D.projection.isIdempotentElem.eq]
  have hx (i j : Fin (n + 1)) : star (x i) * x j = if i = j then D.q else 0 := by
    change star (t i * D.q) * (t j * D.q) = _
    rw [star_mul, D.projection.isSelfAdjoint.star_eq]
    calc
      _ = D.q * (star (t i) * t j) * D.q := by noncomm_ring
      _ = _ := by
        by_cases hij : i = j
        · subst j
          simp only [ht, ite_true, mul_one, D.projection.isIdempotentElem.eq]
        · rw [ht, ite_eq_right (fun h => hij (Fin.ext h)),
            ite_eq_right hij, mul_zero, zero_mul]
  obtain ⟨T, hTx, hTq, hT, hTs⟩ := D.extend_finite_proper_row n x hxs hx
  let S : Fin (n + 1) → E := Fin.cons (s n) (fun i : Fin n => s i)
  have hS (i j : Fin (n + 1)) : star (S i) * S j = if i = j then 1 else 0 := by
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simpa only [S, Fin.cons_zero, ite_true] using hs n n
    · have hne : n ≠ (j : ℕ) := by omega
      simpa only [S, Fin.cons_zero, Fin.cons_succ, hne, ite_false,
        (Fin.succ_ne_zero j).symm] using hs n j
    · have hne : (i : ℕ) ≠ n := by omega
      simpa only [S, Fin.cons_zero, Fin.cons_succ, hne, ite_false,
        Fin.succ_ne_zero] using hs i n
    · simpa only [S, Fin.cons_succ, Fin.succ_inj, Fin.ext_iff, Fin.val_succ, Nat.succ.injEq] using hs i j
  have hroot (i : Fin (n + 1)) : star (s (n + 1)) * S i = 0 := by
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [S, Fin.cons_zero, Nat.add_one_ne_self, ite_false] using hs (n + 1) n
    · have hne : n + 1 ≠ (j : ℕ) := by omega
      simpa only [S, Fin.cons_succ, hne, ite_false] using hs (n + 1) j
  have hqS (i : Fin (n + 1)) : Commute D.q (S i) := by
    refine Fin.cases (hqs n) (fun j => hqs j) i
  have haT (i : Fin (n + 1)) (hi : 0 < (i : ℕ)) : Commute (star D.a) (T i) := by
    revert hi
    refine Fin.cases ?_ (fun j => ?_) i
    · intro h; exact (Nat.lt_irrefl 0 h).elim
    · intro _
      rw [hTx]
      change Commute (star D.a) (t j * D.q)
      exact ((hDc (t j) (tc 0 j).1 (tc 0 j).2 (tc 1 j).1 (tc 1 j).2
        (tc 2 j).1 (tc 2 j).2).2.1).mul_right
          (D.a_star_right.trans D.a_star_left.symm)
  have hbT (i : Fin (n + 1)) (hi : 0 < (i : ℕ)) : Commute (star D.b) (T i) := by
    revert hi
    refine Fin.cases ?_ (fun j => ?_) i
    · intro h; exact (Nat.lt_irrefl 0 h).elim
    · intro _
      rw [hTx]
      change Commute (star D.b) (t j * D.q)
      exact ((hDc (t j) (tc 0 j).1 (tc 0 j).2 (tc 1 j).1 (tc 1 j).2
        (tc 2 j).1 (tc 2 j).2).2.2.2).mul_right
          (D.b_star_right.trans D.b_star_left.symm)
  obtain ⟨U, hU, hUi⟩ := D.exists_finite_absorption_on S T (s (n + 1))
    (fun i => 0 < (i : ℕ)) (by simpa only [ite_true] using hs (n + 1) (n + 1))
    hroot hS (hqs (n + 1)) hqS (fun i => (hTq i).2) hTs hT haT hbT ε hε
  refine ⟨U, hDjoin.trans hU, fun i => ?_⟩
  have hi := hUi i.succ (by simp)
  rw [hTx] at hi
  have he : D.w * s i * star D.w = s i * (r 0 * star (r 0)) := by
    rw [hDw, (rc 0 i).1.eq, mul_assoc]
  change ‖(U : E) * s i - (x i.castSucc + D.w * s i * star D.w) * (U : E)‖ < ε at hi
  have hmul : ((U : E) * s i - (x i.castSucc + D.w * s i * star D.w) * (U : E)) *
      star (U : E) = (U : E) * s i * star (U : E) -
        (x i.castSucc + D.w * s i * star D.w) := by
    rw [sub_mul, mul_assoc _ (U : E), Unitary.mul_star_self_of_mem U.property, mul_one]
  have hnorm := CStarRing.norm_mul_mem_unitary
    ((U : E) * s i - (x i.castSucc + D.w * s i * star D.w) * (U : E))
    (Unitary.star_mem U.property)
  rw [hmul] at hnorm
  have hc : ‖(U : E) * s i * star (U : E) -
      (x i.castSucc + D.w * s i * star D.w)‖ < ε := by
    rw [hnorm]
    exact hi
  simpa only [x, Fin.val_castSucc, hDq, he] using hc

end WeakPureInfiniteness

end

end OAI
