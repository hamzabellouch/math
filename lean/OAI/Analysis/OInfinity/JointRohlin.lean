import OAI.Analysis.OInfinity.RohlinPolar

namespace OAI

/-! # Joint source-target cyclic partitions

Convolving two commuting cyclic projection partitions produces one partition
approximately shifted by both endomorphisms. This is the joint phase needed
to control the row cocycle. The coefficient-path commutators are a separate
requirement; no degree-zero property of the fragmentation path is asserted.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E] {N : ℕ} [NeZero N]

def jointRohlinProjection (p q : ZMod N → E) (k : ZMod N) : E :=
  ∑ i, p i * q (k - i)

lemma jointRohlinProjection_star (p q : ZMod N → E)
    (hp : ∀ i, IsStarProjection (p i)) (hq : ∀ i, IsStarProjection (q i))
    (hc : ∀ i j, Commute (p i) (q j)) (k : ZMod N) :
    star (jointRohlinProjection p q k) = jointRohlinProjection p q k := by
  simp only [jointRohlinProjection, star_sum, star_mul,
    fun i => (hp i).isSelfAdjoint.star_eq, fun i => (hq i).isSelfAdjoint.star_eq]
  apply Finset.sum_congr rfl
  intro i hi
  exact (hc i (k - i)).eq.symm

lemma jointRohlinProjection_mul (p q : ZMod N → E)
    (hpp : ∀ i, p i * p i = p i)
    (hpo : ∀ i j, i ≠ j → p i * p j = 0)
    (hc : ∀ i j, Commute (p i) (q j)) (k l : ZMod N) :
    jointRohlinProjection p q k * jointRohlinProjection p q l =
      ∑ i, p i * (q (k - i) * q (l - i)) := by
  have hterm (i j : ZMod N) :
      (p i * q (k - i)) * (p j * q (l - j)) =
        if i = j then p i * (q (k - i) * q (l - i)) else 0 := by
    calc
      _ = p i * (q (k - i) * p j) * q (l - j) := by noncomm_ring
      _ = (p i * p j) * (q (k - i) * q (l - j)) := by
        rw [← (hc j (k - i)).eq]
        noncomm_ring
      _ = _ := by
        split_ifs with hij
        · subst j
          rw [hpp]
        · rw [hpo i j hij, zero_mul]
  simp only [jointRohlinProjection, Finset.sum_mul, Finset.mul_sum, hterm,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

lemma jointRohlinProjection_isStarProjection (p q : ZMod N → E)
    (hp : ∀ i, IsStarProjection (p i)) (hq : ∀ i, IsStarProjection (q i))
    (hpo : ∀ i j, i ≠ j → p i * p j = 0)
    (hc : ∀ i j, Commute (p i) (q j)) (k : ZMod N) :
    IsStarProjection (jointRohlinProjection p q k) := by
  refine ⟨?_, jointRohlinProjection_star p q hp hq hc k⟩
  change jointRohlinProjection p q k * jointRohlinProjection p q k = _
  rw [jointRohlinProjection_mul p q (fun i => (hp i).isIdempotentElem.eq) hpo hc]
  simp only [fun i => (hq i).isIdempotentElem.eq, jointRohlinProjection]

lemma jointRohlinProjection_orthogonal (p q : ZMod N → E)
    (hpp : ∀ i, p i * p i = p i)
    (hpo : ∀ i j, i ≠ j → p i * p j = 0)
    (hqo : ∀ i j, i ≠ j → q i * q j = 0)
    (hc : ∀ i j, Commute (p i) (q j)) (k l : ZMod N) (hkl : k ≠ l) :
    jointRohlinProjection p q k * jointRohlinProjection p q l = 0 := by
  rw [jointRohlinProjection_mul p q hpp hpo hc]
  apply Finset.sum_eq_zero
  intro i hi
  have hne : k - i ≠ l - i := by
    intro h
    apply hkl
    simpa only [sub_add_cancel] using congrArg (fun z : ZMod N => z + i) h
  rw [hqo (k - i) (l - i) hne, mul_zero]

lemma jointRohlinProjection_sum (p q : ZMod N → E)
    (hp : (∑ i, p i) = 1) (hq : (∑ i, q i) = 1) :
    (∑ k, jointRohlinProjection p q k) = 1 := by
  have htranslate (i : ZMod N) : (∑ k, q (k - i)) = 1 := by
    calc
      _ = ∑ k, q k := Fintype.sum_equiv (Equiv.subRight i) _ _ (fun _ => rfl)
      _ = 1 := hq
  simp only [jointRohlinProjection]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, htranslate, mul_one, hp]

lemma jointRohlinProjection_shift_left (φ : E →⋆ₙₐ[ℂ] E)
    (p q : ZMod N → E) (hfix : ∀ i, φ (q i) = q i) (k : ZMod N) :
    φ (jointRohlinProjection p q k) - jointRohlinProjection p q (k + 1) =
      ∑ i, (φ (p i) - p (i + 1)) * q (k - i) := by
  have hreindex : (∑ i, p (i + 1) * q (k - i)) =
      jointRohlinProjection p q (k + 1) := by
    unfold jointRohlinProjection
    apply Fintype.sum_equiv (Equiv.addRight 1)
    intro i
    change p (i + 1) * q (k - i) = p (i + 1) * q (k + 1 - (i + 1))
    congr 2
    abel
  rw [← hreindex]
  simp only [jointRohlinProjection, map_sum, map_mul, hfix,
    ← Finset.sum_sub_distrib, sub_mul]

lemma jointRohlinProjection_shift_left_le (φ : E →⋆ₙₐ[ℂ] E)
    (p q : ZMod N → E) (hfix : ∀ i, φ (q i) = q i)
    (hq : ∀ i, IsStarProjection (q i)) (η : ℝ)
    (hshift : ∀ i, ‖φ (p i) - p (i + 1)‖ ≤ η) (k : ZMod N) :
    ‖φ (jointRohlinProjection p q k) - jointRohlinProjection p q (k + 1)‖ ≤
      (N : ℝ) * η := by
  rw [jointRohlinProjection_shift_left φ p q hfix]
  calc
    _ ≤ ∑ i, ‖(φ (p i) - p (i + 1)) * q (k - i)‖ := norm_sum_le _ _
    _ ≤ ∑ _ : ZMod N, η := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        _ ≤ ‖φ (p i) - p (i + 1)‖ * ‖q (k - i)‖ := norm_mul_le _ _
        _ ≤ ‖φ (p i) - p (i + 1)‖ * 1 :=
          mul_le_mul_of_nonneg_left (IsStarProjection.norm_le _ (hq (k - i))) (norm_nonneg _)
        _ ≤ η := by simpa only [mul_one] using hshift i
    _ = _ := by simp

lemma jointRohlinProjection_comm (p q : ZMod N → E)
    (hc : ∀ i j, Commute (p i) (q j)) (k : ZMod N) :
    jointRohlinProjection p q k = jointRohlinProjection q p k := by
  unfold jointRohlinProjection
  apply Fintype.sum_equiv (Equiv.subLeft k)
  intro i
  simp only [Equiv.subLeft_apply]
  rw [show k - (k - i) = i by abel]
  exact (hc i (k - i)).eq

lemma jointRohlinProjection_shift_right_le (ψ : E →⋆ₙₐ[ℂ] E)
    (p q : ZMod N → E) (hfix : ∀ i, ψ (p i) = p i)
    (hp : ∀ i, IsStarProjection (p i))
    (hc : ∀ i j, Commute (p i) (q j)) (η : ℝ)
    (hshift : ∀ i, ‖ψ (q i) - q (i + 1)‖ ≤ η) (k : ZMod N) :
    ‖ψ (jointRohlinProjection p q k) - jointRohlinProjection p q (k + 1)‖ ≤
      (N : ℝ) * η := by
  rw [jointRohlinProjection_comm p q hc k, jointRohlinProjection_comm p q hc (k + 1)]
  exact jointRohlinProjection_shift_left_le ψ q p hfix hp η hshift k

omit [NeZero N] in
lemma finiteRowShiftIterate_cyclic_error (s : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (e : ZMod N → E) (η : ℝ)
    (hshift : ∀ k, ‖finiteRowShift s (e k) - e (k + 1)‖ ≤ η)
    (k : ZMod N) (n : ℕ) :
    ‖finiteRowShiftIterate s n (e k) - e (k + (n : ZMod N))‖ ≤ (n : ℝ) * η := by
  let x : ℕ → E := fun j => e (k + (j : ZMod N))
  have hstep (j : ℕ) (_hj : j < n) :
      ‖finiteRowShift s (x j) - x (j + 1)‖ ≤ η := by
    simpa only [x, Nat.cast_add, Nat.cast_one, add_assoc] using hshift (k + (j : ZMod N))
  simpa only [x, Nat.cast_zero, add_zero] using
    finiteRowShiftIterate_cycle_error s hs x n η hstep n le_rfl

omit [NeZero N] in
/-- A common cyclic shift for both rows controls every actual cocycle product.
Unlike a source-only tower, this estimates all finite products. -/
lemma binaryRowCocycle_joint_commutator_le (s t : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (hsum : (∑ i, s i * star (s i)) = 1)
    (htsum : (∑ i, t i * star (t i)) = 1)
    (e : ZMod N → E) (ηs ηt : ℝ)
    (hshiftS : ∀ k, ‖finiteRowShift s (e k) - e (k + 1)‖ ≤ ηs)
    (hshiftT : ∀ k, ‖finiteRowShift t (e k) - e (k + 1)‖ ≤ ηt)
    (k : ZMod N) (n : ℕ) :
    ‖(binaryRowCocycleUnitary s t hs ht hsum htsum n : E) * e k -
      e k * (binaryRowCocycleUnitary s t hs ht hsum htsum n : E)‖ ≤
        (n : ℝ) * (ηs + ηt) := by
  let u := binaryRowCocycleUnitary s t hs ht hsum htsum n
  let a := e (k - (n : ZMod N))
  have hS : ‖finiteRowShiftIterate s n a - e k‖ ≤ (n : ℝ) * ηs := by
    simpa only [a, sub_add_cancel] using
      finiteRowShiftIterate_cyclic_error s hs e ηs hshiftS (k - (n : ZMod N)) n
  have hT : ‖finiteRowShiftIterate t n a - e k‖ ≤ (n : ℝ) * ηt := by
    simpa only [a, sub_add_cancel] using
      finiteRowShiftIterate_cyclic_error t ht e ηt hshiftT (k - (n : ZMod N)) n
  have hi : (u : E) * finiteRowShiftIterate s n a = finiteRowShiftIterate t n a * (u : E) :=
    binaryRowCocycle_iterate_intertwining s t hs ht hsum htsum n a
  have hid : (u : E) * e k - e k * (u : E) =
      (u : E) * (e k - finiteRowShiftIterate s n a) +
        (finiteRowShiftIterate t n a - e k) * (u : E) := by
    rw [mul_sub, sub_mul, hi]
    noncomm_ring
  change ‖(u : E) * e k - e k * (u : E)‖ ≤ _
  rw [hid]
  calc
    _ ≤ ‖(u : E) * (e k - finiteRowShiftIterate s n a)‖ +
        ‖(finiteRowShiftIterate t n a - e k) * (u : E)‖ := norm_add_le _ _
    _ = ‖finiteRowShiftIterate s n a - e k‖ + ‖finiteRowShiftIterate t n a - e k‖ := by
      rw [CStarRing.norm_coe_unitary_mul, CStarRing.norm_mul_coe_unitary, norm_sub_rev]
    _ ≤ (n : ℝ) * ηs + (n : ℝ) * ηt := add_le_add hS hT
    _ = _ := by ring

lemma binaryRowCocycle_jointRohlin_commutator_le (s t : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (hsum : (∑ i, s i * star (s i)) = 1)
    (htsum : (∑ i, t i * star (t i)) = 1)
    (p q : ZMod N → E) (hp : ∀ i, IsStarProjection (p i))
    (hq : ∀ i, IsStarProjection (q i)) (hc : ∀ i j, Commute (p i) (q j))
    (hSfix : ∀ i j, Commute (s i) (q j))
    (hTfix : ∀ i j, Commute (t i) (p j)) (ηs ηt : ℝ)
    (hshiftS : ∀ k, ‖finiteRowShift s (p k) - p (k + 1)‖ ≤ ηs)
    (hshiftT : ∀ k, ‖finiteRowShift t (q k) - q (k + 1)‖ ≤ ηt)
    (k : ZMod N) (n : ℕ) :
    ‖(binaryRowCocycleUnitary s t hs ht hsum htsum n : E) * jointRohlinProjection p q k -
      jointRohlinProjection p q k * (binaryRowCocycleUnitary s t hs ht hsum htsum n : E)‖ ≤
        (n : ℝ) * (N : ℝ) * (ηs + ηt) := by
  have hS (j : ZMod N) := jointRohlinProjection_shift_left_le
    (finiteCuntzDiagonalHom s hs) p q
    (fun l => finiteRowShift_fixed_of_commutes s hsum (q l) (fun i => hSfix i l))
    hq ηs hshiftS j
  have hT (j : ZMod N) := jointRohlinProjection_shift_right_le
    (finiteCuntzDiagonalHom t ht) p q
    (fun l => finiteRowShift_fixed_of_commutes t htsum (p l) (fun i => hTfix i l))
    hp hc ηt hshiftT j
  have h := binaryRowCocycle_joint_commutator_le s t hs ht hsum htsum
    (jointRohlinProjection p q) ((N : ℝ) * ηs) ((N : ℝ) * ηt) hS hT k n
  calc
    _ ≤ (n : ℝ) * ((N : ℝ) * ηs + (N : ℝ) * ηt) := h
    _ = _ := by ring

end WeakPureInfiniteness

end

end OAI
