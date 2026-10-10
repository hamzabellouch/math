import OAI.Analysis.OInfinity.MixedComplement

namespace OAI

/-! # Paths of the actual inserted-unitary shrinks

The inverse canonical-shift implementer can be chosen in the identity
component. Varying that implementer to one preserves both support
projections of the shrink. This supplies a path to the literal base
formula; the base fixed-complement extension is not asserted connected.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

/-- Retain the connectedness supplied by the canonical-shift construction
when passing to inverse conjugation and a finite encoded prefix. -/
lemma exists_connected_canonicalShift_prefix_inverse [Nontrivial E]
    (a : Fin 2 → E)
    (ha : ∀ i j, star (a i) * a j = if i = j then 1 else 0)
    (has : (∑ i, a i * star (a i)) = 1) (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ u : unitary E, Joined 1 u ∧ ∀ i ≤ m,
      ‖(u : E) * finiteRowShift a (a 0 ^ i * a 1) * star (u : E) -
        (a 0 ^ i * a 1)‖ < ε := by
  let δ := ε / ((m : ℝ) + 2)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  obtain ⟨u, hu, huclose⟩ := exists_connected_canonicalShift_conjugacy a ha has δ hδ
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
      ‖(u : E) * (a 0 ^ i * a 1) * star (u : E) - φ (a 0 ^ i * a 1)‖ < ε := by
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
  refine ⟨star u, ?_, fun i hi => ?_⟩
  · simpa only [star_one] using hu.map (continuous_star : Continuous (star : unitary E → unitary E))
  · let x := a 0 ^ i * a 1
    have hid : (star (u : E)) * φ x * (u : E) - x =
        star (u : E) * (φ x - (u : E) * x * star (u : E)) * (u : E) := by
      rw [mul_sub, sub_mul]
      have hcan : star (u : E) * ((u : E) * x * star (u : E)) * (u : E) = x := by
        calc
          _ = (star (u : E) * (u : E)) * x * (star (u : E) * (u : E)) := by noncomm_ring
          _ = x := by rw [u.property.1, one_mul, mul_one]
      rw [hcan]
    change ‖star (u : E) * φ x * star (star (u : E)) - x‖ < ε
    rw [star_star, hid, CStarRing.norm_mul_coe_unitary]
    change ‖(star u : unitary E) * (φ x - (u : E) * x * star (u : E))‖ < ε
    rw [CStarRing.norm_coe_unitary_mul, norm_sub_rev]
    exact hclose i hi

def binaryShrinkValue (r a : Fin 2 → E) (u : unitary E) : E :=
  let v := (u : E) * finiteCuntzTransfer r a 1
  1 - star v * v + r 1 * v

lemma binaryShrinkValue_continuous (r a : Fin 2 → E) : Continuous (binaryShrinkValue r a) := by
  unfold binaryShrinkValue
  fun_prop

lemma binaryShrinkValue_one (r a : Fin 2 → E) :
    binaryShrinkValue r a 1 = 1 - star (finiteCuntzTransfer r a 1) *
      finiteCuntzTransfer r a 1 + r 1 * finiteCuntzTransfer r a 1 := by
  simp only [binaryShrinkValue, OneMemClass.coe_one, one_mul]

/-- The actual shrink follows a continuous path with constant initial and
final projections from its explicit base formula to the required estimate. -/
lemma exists_binary_shrink_path [Nontrivial E]
    (r a : Fin 2 → E)
    (hr : ∀ i j, star (r i) * r j = if i = j then 1 else 0)
    (ha : ∀ i j, star (a i) * a j = if i = j then 1 else 0)
    (has : (∑ i, a i * star (a i)) = 1)
    (hc : bergRowsCommute a r) (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : unitInterval → E, Continuous C ∧
      C 0 = binaryShrinkValue r a 1 ∧
      (∀ t, star (C t) * C t = 1 ∧ C t * star (C t) = 1 - r 0 * star (r 0)) ∧
      ∀ i ≤ m, ‖C 1 * (a 0 ^ i * a 1) * star (C 1) -
        (a 0 ^ i * a 1) * (1 - r 0 * star (r 0))‖ < ε := by
  obtain ⟨u, hu, he⟩ := exists_connected_canonicalShift_prefix_inverse a ha has m ε hε
  let p : Path (1 : unitary E) u := hu.somePath
  let C : unitInterval → E := fun t => binaryShrinkValue r a (p t)
  refine ⟨C, (binaryShrinkValue_continuous r a).comp p.continuous, ?_, ?_, ?_⟩
  · change binaryShrinkValue r a (p 0) = _
    rw [p.source]
  · intro t
    exact binary_shift_shrink_products r a hr ha has (p t)
  · intro i hi
    have hx (j : Fin 2) : Commute (a 0 ^ i * a 1) (r j) ∧
        Commute (a 0 ^ i * a 1) (star (r j)) :=
      ⟨((hc 0 j).1.pow_left i).mul_left (hc 1 j).1,
        ((hc 0 j).2.pow_left i).mul_left (hc 1 j).2⟩
    change ‖binaryShrinkValue r a (p 1) * _ * star (binaryShrinkValue r a (p 1)) - _‖ < ε
    rw [p.target]
    exact (binary_shift_shrink_error r a hr ha has u _ hx).trans_lt (he i hi)

/-- The same actual deformation inside a projection corner, including both
support equations at every time. -/
lemma exists_relative_binary_shrink_path
    (q : E) (hq : star q = q) (hqq : q * q = q) (hq0 : q ≠ 0)
    (r a : Fin 2 → E)
    (hrs : ∀ i, q * r i = r i ∧ r i * q = r i)
    (hasp : ∀ i, q * a i = a i ∧ a i * q = a i)
    (hr : ∀ i j, star (r i) * r j = if i = j then q else 0)
    (ha : ∀ i j, star (a i) * a j = if i = j then q else 0)
    (has : (∑ i, a i * star (a i)) = q)
    (hc : bergRowsCommute a r) (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : unitInterval → E, Continuous C ∧
      C 0 = q - star (finiteCuntzTransfer r a q) * finiteCuntzTransfer r a q +
        r 1 * finiteCuntzTransfer r a q ∧
      (∀ t, q * C t = C t ∧ C t * q = C t ∧ star (C t) * C t = q ∧
        C t * star (C t) = q - r 0 * star (r 0)) ∧
      ∀ i ≤ m, ‖C 1 * (a 0 ^ i * a 1) * star (C 1) -
        (a 0 ^ i * a 1) * (q - r 0 * star (r 0))‖ < ε := by
  let : NeZero q := ⟨hq0⟩
  let H := ProjectionCorner q hq hqq
  let R : Fin 2 → H := fun i => projectionCornerElement q hq hqq (r i) (hrs i)
  let A : Fin 2 → H := fun i => projectionCornerElement q hq hqq (a i) (hasp i)
  have hR := projectionCornerElement_gram q hq hqq r hrs hr
  have hA := projectionCornerElement_gram q hq hqq a hasp ha
  have hAs := projectionCornerElement_range_sum q hq hqq a hasp has
  have hAR : bergRowsCommute A R := by
    intro i j
    exact ⟨Subtype.ext (hc i j).1.eq, Subtype.ext (hc i j).2.eq⟩
  obtain ⟨C, hC, hC0, hgram, he⟩ := exists_binary_shrink_path R A hR hA hAs hAR m ε hε
  let f := projectionCornerInclusion q hq hqq
  have hf1 : f 1 = q := rfl
  have hfR (i : Fin 2) : f (R i) = r i := rfl
  have htransfer : f (finiteCuntzTransfer R A 1) = finiteCuntzTransfer r a q := by
    simp only [finiteCuntzTransfer, map_sum, map_mul, map_star]
    rfl
  have hfc : Continuous (fun x : H => f x) := continuous_subtype_val
  refine ⟨fun t => f (C t), hfc.comp hC, ?_, ?_, fun i hi => ?_⟩
  · change f (C 0) = _
    rw [hC0, binaryShrinkValue_one, map_add, map_sub, map_mul, map_star, map_mul,
      hf1, htransfer]
    rfl
  · intro t
    exact ⟨(C t).property.1, (C t).property.2,
      congrArg f (hgram t).1, congrArg f (hgram t).2⟩
  · have hpow : f (A 0 ^ i * A 1) = a 0 ^ i * a 1 := by
      rw [nonunital_map_pow_mul]
      rfl
    have hh := he i hi
    change ‖f (C 1 * (A 0 ^ i * A 1) * star (C 1) -
      (A 0 ^ i * A 1) * (1 - R 0 * star (R 0)))‖ < ε at hh
    simpa only [map_sub, map_mul, map_star, hpow, hf1, hfR] using hh

end WeakPureInfiniteness

end

end OAI
