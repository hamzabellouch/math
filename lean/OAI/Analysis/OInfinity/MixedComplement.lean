import OAI.Analysis.OInfinity.MixedSwap

namespace OAI

/-! # The complementary action in mixed cancellation

An exact corner comparison determines a unitary on the complementary full
isometric copy. The full error is the sum of the mixed-corner error and
this concrete complementary conjugation error. A fixed-complement extension
of a partial isometry is also given; connectedness is not inferred from its
unitary identities.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

/-- Exact projection transport by a unitary implies commutation with the
projection when its initial and final projections agree. -/
lemma unitary_commutes_of_conjugation_eq (u : unitary E) (q : E)
    (hq : (u : E) * q * star (u : E) = q) : Commute (u : E) q := by
  change (u : E) * q = q * (u : E)
  calc
    _ = ((u : E) * q * star (u : E)) * (u : E) := by
      rw [mul_assoc, mul_assoc, u.property.1, mul_one]
    _ = _ := by rw [hq]

/-- Compressing a projection-preserving unitary to its complementary full
isometry gives an actual unitary, with the exact intertwining relation. -/
lemma exists_complementary_compression_unitary (r : E) (hr : star r * r = 1)
    (u : unitary E) (hp : Commute (u : E) (r * star r)) :
    ∃ h : unitary E, (h : E) = star r * (u : E) * r ∧ (u : E) * r = r * (h : E) := by
  let h := star r * (u : E) * r
  have hpu : (u : E) * (r * star r) * star (u : E) = r * star r := by
    rw [hp.eq, mul_assoc, u.property.2, mul_one]
  have hpus : star (u : E) * (r * star r) * (u : E) = r * star r := by
    calc
      _ = star (u : E) * ((u : E) * (r * star r)) := by rw [hp.eq]; noncomm_ring
      _ = _ := by rw [← mul_assoc, u.property.1, one_mul]
  have hg : star h * h = 1 := by
    dsimp only [h]
    rw [star_mul, star_mul, star_star]
    calc
      _ = star r * (star (u : E) * (r * star r) * (u : E)) * r := by noncomm_ring
      _ = star r * (r * star r) * r := by rw [hpus]
      _ = (star r * r) * (star r * r) := by noncomm_ring
      _ = 1 := by rw [hr, one_mul]
  have hgr : h * star h = 1 := by
    dsimp only [h]
    rw [star_mul, star_mul, star_star]
    calc
      _ = star r * ((u : E) * (r * star r) * star (u : E)) * r := by noncomm_ring
      _ = star r * (r * star r) * r := by rw [hpu]
      _ = (star r * r) * (star r * r) := by noncomm_ring
      _ = 1 := by rw [hr, one_mul]
  refine ⟨⟨h, hg, hgr⟩, rfl, ?_⟩
  change (u : E) * r = r * (star r * (u : E) * r)
  calc
    _ = (u : E) * ((r * star r) * r) := by rw [mul_assoc r, hr, mul_one]
    _ = _ := by rw [← mul_assoc, hp.eq]; noncomm_ring

lemma complementary_conjugation_decomposition (r x y z : E) (u h : unitary E)
    (hur : (u : E) * r = r * (h : E)) :
    (u : E) * (r * y * star r + x) * star (u : E) - (r * y * star r + z) =
      r * ((h : E) * y * star (h : E) - y) * star r +
        ((u : E) * x * star (u : E) - z) := by
  have hrs : star r * star (u : E) = star (h : E) * star r := by
    simpa only [star_mul] using congrArg star hur
  calc
    _ = ((u : E) * r) * y * (star r * star (u : E)) - r * y * star r +
        ((u : E) * x * star (u : E) - z) := by noncomm_ring
    _ = _ := by rw [hur, hrs]; noncomm_ring

/-- The remaining term is an actual conjugation by the compressed unitary.
It is not estimated by zero merely because the mixed corner is controlled. -/
lemma exists_mixed_complement_unitary [Nontrivial E] (s t : ℕ → E)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (u : unitary E)
    (huq : (u : E) * canonicalTailProjection t 1 * star (u : E) = canonicalTailProjection t 1) :
    ∃ h : unitary E, (h : E) = star (t 0) * (u : E) * t 0 ∧
      (u : E) * t 0 = t 0 * (h : E) ∧
      ∀ i, ‖(u : E) * mixedSwappedRow s t i * star (u : E) - mixedStabilizedRow t t i‖ ≤
        ‖(h : E) * t i * star (h : E) - t i‖ +
          ‖(u : E) * mixedNegativeRow s t i * star (u : E) - canonicalNegativeRow t i‖ := by
  have hqdef : canonicalTailProjection t 1 = 1 - t 0 * star (t 0) := by
    rw [show (1 : ℕ) = 0 + 1 by rfl, canonicalTailProjection_succ, canonicalTailProjection_zero]
  have hc := unitary_commutes_of_conjugation_eq u _ huq
  have hp : Commute (u : E) (t 0 * star (t 0)) := by
    have hh := (Commute.one_right (u : E)).sub_right hc
    simpa only [hqdef, sub_sub_cancel] using hh
  have hr : star (t 0) * t 0 = 1 := by simpa only [ite_true] using ht 0 0
  obtain ⟨h, he, hrel⟩ := exists_complementary_compression_unitary (t 0) hr u hp
  have hn : ‖t 0‖ ≤ 1 := by
    have hh := congrArg norm hr
    rw [CStarRing.norm_star_mul_self, norm_one] at hh
    nlinarith [norm_nonneg (t 0)]
  refine ⟨h, he, hrel, fun i => ?_⟩
  rw [mixedSwappedRow, mixedStabilizedRow,
    complementary_conjugation_decomposition (t 0) (mixedNegativeRow s t i)
      (t i) (canonicalNegativeRow t i) u h hrel]
  apply (norm_add_le _ _).trans
  refine add_le_add ?_ le_rfl
  calc
    _ ≤ (‖t 0‖ * ‖(h : E) * t i * star (h : E) - t i‖) * ‖star (t 0)‖ :=
      (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1 * ‖(h : E) * t i * star (h : E) - t i‖) * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
        (by simpa only [norm_star] using hn) (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- The prescribed complementary isometries provide the literal extension
`W + z w*`. This theorem asserts unitarity and both exact actions only. -/
lemma exists_fixed_complement_unitary_extension (q p W w z : E)
    (hq : star q = q) (hp : star p = p)
    (hW : star W * W = q) (hWW : W * star W = p) (hWq : W * q = W)
    (hw : star w * w = 1) (hww : w * star w = 1 - q)
    (hz : star z * z = 1) (hzz : z * star z = 1 - p) :
    ∃ u : unitary E, (u : E) = W + z * star w ∧ (u : E) * q = W ∧ (u : E) * w = z := by
  have hqw : q * w = 0 := by
    calc
      _ = (1 - w * star w) * w := by rw [hww]; noncomm_ring
      _ = 0 := by rw [sub_mul, one_mul, mul_assoc, hw, mul_one, sub_self]
  have hswq : star w * q = 0 := by
    simpa only [star_mul, hq, star_zero] using congrArg star hqw
  have hpz : p * z = 0 := by
    calc
      _ = (1 - z * star z) * z := by rw [hzz]; noncomm_ring
      _ = 0 := by rw [sub_mul, one_mul, mul_assoc, hz, mul_one, sub_self]
  have hsp : star W * p = star W := by
    have hpW : p * W = W := by rw [← hWW, mul_assoc, hW, hWq]
    simpa only [star_mul, hp] using congrArg star hpW
  have hWz : star W * z = 0 := by
    calc
      _ = (star W * p) * z := by rw [hsp]
      _ = 0 := by rw [mul_assoc, hpz, mul_zero]
  have hzw : star z * W = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star hWz
  have hWw : W * w = 0 := by rw [← hWq, mul_assoc, hqw, mul_zero]
  have hwW : star w * star W = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star hWw
  let u := W + z * star w
  have hug : star u * u = 1 := by
    change star (W + z * star w) * (W + z * star w) = 1
    rw [star_add, star_mul, star_star, add_mul, mul_add, mul_add, hW]
    calc
      _ = q + (star W * z) * star w + w * (star z * W) + w * (star z * z) * star w := by noncomm_ring
      _ = 1 := by rw [hWz, hzw, hz, zero_mul, mul_zero, mul_one, hww]; noncomm_ring
  have hur : u * star u = 1 := by
    change (W + z * star w) * star (W + z * star w) = 1
    rw [star_add, star_mul, star_star, add_mul, mul_add, mul_add, hWW]
    calc
      _ = p + (W * w) * star z + z * (star w * star W) + z * (star w * w) * star z := by noncomm_ring
      _ = 1 := by rw [hWw, hwW, hw, zero_mul, mul_zero, mul_one, hzz]; noncomm_ring
  refine ⟨⟨u, hug, hur⟩, rfl, ?_, ?_⟩
  · change (W + z * star w) * q = W
    rw [add_mul, hWq, mul_assoc, hswq, mul_zero, add_zero]
  · change (W + z * star w) * w = z
    rw [add_mul, hWw, mul_assoc, hw, mul_one, zero_add]

end WeakPureInfiniteness

end

end OAI
