import OAI.Analysis.OInfinity.CanonicalBufferAbsorption

namespace OAI

/-! # Iterating the concrete buffered absorption

The successive conjugacies move the residual representation into powers of
the complementary isometry.  Both the accumulated error and the entire
terminal representation are retained.  No norm decay is assigned to the
terminal projection.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

/-- The exact target after `n` buffered absorptions. -/
def bufferedAbsorptionValue (w t x : E) (n : ℕ) : E :=
  t * (1 - w ^ n * star (w ^ n)) + w ^ n * x * star (w ^ n)

@[simp] lemma bufferedAbsorptionValue_zero (w t x : E) :
    bufferedAbsorptionValue w t x 0 = x := by
  simp only [bufferedAbsorptionValue, pow_zero, star_one, one_mul, sub_self,
    mul_zero, zero_add, mul_one]

lemma bufferedAbsorptionValue_one (w t x : E) :
    bufferedAbsorptionValue w t x 1 = t * (1 - w * star w) + w * x * star w := by
  simp only [bufferedAbsorptionValue, pow_one]

lemma bufferedAbsorptionValue_succ (w t x : E) (htw : Commute t w) (n : ℕ) :
    bufferedAbsorptionValue w t x (n + 1) =
      t * (1 - w * star w) + w * bufferedAbsorptionValue w t x n * star w := by
  unfold bufferedAbsorptionValue
  rw [pow_succ', star_mul]
  calc
    _ = t - t * (w * w ^ n * star (w ^ n) * star w) +
        w * w ^ n * x * star (w ^ n) * star w := by noncomm_ring
    _ = t - (t * w) * w ^ n * star (w ^ n) * star w +
        w * w ^ n * x * star (w ^ n) * star w := by noncomm_ring
    _ = _ := by
      simp only [mul_sub, mul_one, ← mul_assoc, htw.eq]
      noncomm_ring

/-- The inner conjugation used at the next absorption step. -/
lemma bufferedAbsorption_conjugate (w t x : E) (hw : star w * w = 1)
    (htw : Commute t w) (htsw : Commute t (star w)) (v : unitary E) :
    (binaryCornerUnitary w hw v : E) *
        (t * (1 - w * star w) + w * x * star w) *
        star (binaryCornerUnitary w hw v : E) =
      t * (1 - w * star w) + w * ((v : E) * x * star (v : E)) * star w := by
  let q := 1 - w * star w
  have hqw : q * w = 0 := by
    dsimp only [q]
    rw [sub_mul, one_mul, mul_assoc, hw, mul_one, sub_self]
  have hswq : star w * q = 0 := by
    dsimp only [q]
    rw [mul_sub, mul_one, ← mul_assoc, hw, one_mul, sub_self]
  have hqstar : star q = q := by simp only [q, star_sub, star_one, star_mul, star_star]
  have hqq : q * q = q := by
    dsimp only [q]
    calc
      _ = 1 - w * star w - w * star w + w * (star w * w) * star w := by noncomm_ring
      _ = _ := by rw [hw]; noncomm_ring
  have htq : Commute t q := (Commute.one_right _).sub_right (htw.mul_right htsw)
  have hsw_tq : star w * (t * q) = 0 := by
    rw [← mul_assoc, ← htsw.eq, mul_assoc, hswq, mul_zero]
  have htq_w : (t * q) * w = 0 := by rw [mul_assoc, hqw, mul_zero]
  have hq_tq : q * (t * q) = t * q := by rw [← mul_assoc, ← htq.eq, mul_assoc, hqq]
  change (w * (v : E) * star w + q) * (t * q + w * x * star w) *
    star (w * (v : E) * star w + q) = _
  rw [star_add, star_mul, star_mul, star_star, hqstar]
  have hl : (w * (v : E) * star w + q) * (t * q + w * x * star w) =
      t * q + w * (v : E) * x * star w := by
    calc
      _ = w * (v : E) * (star w * (t * q)) +
          w * (v : E) * (star w * w) * x * star w + q * (t * q) +
          (q * w) * x * star w := by noncomm_ring
      _ = _ := by rw [hsw_tq, hw, hq_tq, hqw]; noncomm_ring
  rw [hl]
  calc
    _ = (t * q) * w * star (v : E) * star w + t * (q * q) +
        w * (v : E) * x * (star w * w) * star (v : E) * star w +
        w * (v : E) * x * (star w * q) := by noncomm_ring
    _ = _ := by rw [htq_w, hqq, hw, hswq]; dsimp only [q]; noncomm_ring

private lemma buffered_sandwich_norm (w x : E) (hw : star w * w = 1) :
    ‖w * x * star w‖ ≤ ‖x‖ := by
  have hwn : ‖w‖ ≤ 1 := by
    have h := congrArg norm hw
    rw [CStarRing.norm_star_mul_self] at h
    have h1 : ‖(1 : E)‖ ≤ 1 := by
      have hh := congrArg norm (show star (1 : E) * 1 = 1 by simp)
      rw [CStarRing.norm_star_mul_self] at hh
      nlinarith [norm_nonneg (1 : E)]
    nlinarith [norm_nonneg w]
  calc
    _ ≤ ‖w‖ * ‖x‖ * ‖w‖ := by
      simpa only [norm_star] using (norm_mul_le (w * x) (star w)).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le w x) (norm_nonneg _))
    _ ≤ 1 * ‖x‖ * 1 := by gcongr
    _ = _ := by ring

/-- Repeated absorption is implemented by actual connected unitaries.
The error is at most `m * ε`; its target keeps the full terminal copy. -/
lemma exists_connected_buffered_iteration {I : Type*}
    (s t : I → E) (w : E) (hw : star w * w = 1)
    (htw : ∀ i, Commute (t i) w) (htsw : ∀ i, Commute (t i) (star w))
    (u : unitary E) (hu : Joined (1 : unitary E) u)
    (ε : ℝ)
    (he : ∀ i, ‖(u : E) * s i * star (u : E) -
      bufferedAbsorptionValue w (t i) (s i) 1‖ ≤ ε)
    (m : ℕ) :
    ∃ v : unitary E, Joined (1 : unitary E) v ∧
      ∀ i, ‖(v : E) * s i * star (v : E) -
        bufferedAbsorptionValue w (t i) (s i) m‖ ≤ m * ε := by
  induction m with
  | zero =>
      refine ⟨1, Joined.refl _, fun i => ?_⟩
      simp only [OneMemClass.coe_one, one_mul, star_one, mul_one,
        bufferedAbsorptionValue_zero, sub_self, norm_zero, Nat.cast_zero, zero_mul, le_refl]
  | succ m ih =>
      obtain ⟨v, hv, hvi⟩ := ih
      let a := binaryCornerUnitary w hw v
      have ha : Joined (1 : unitary E) a := by
        simpa only [binaryCornerUnitary_one] using hv.map (binaryCornerUnitary_continuous w hw)
      refine ⟨a * u, ?_, fun i => ?_⟩
      · simpa only [one_mul] using ha.mul hu
      · let d := (u : E) * s i * star (u : E) - bufferedAbsorptionValue w (t i) (s i) 1
        let e := (v : E) * s i * star (v : E) - bufferedAbsorptionValue w (t i) (s i) m
        have hidentity : ((a * u : unitary E) : E) * s i * star ((a * u : unitary E) : E) -
            bufferedAbsorptionValue w (t i) (s i) (m + 1) =
            (a : E) * d * star (a : E) + w * e * star w := by
          have hc : (a : E) * bufferedAbsorptionValue w (t i) (s i) 1 * star (a : E) =
              t i * (1 - w * star w) + w * ((v : E) * s i * star (v : E)) * star w := by
            rw [bufferedAbsorptionValue_one]
            exact bufferedAbsorption_conjugate w (t i) (s i) hw (htw i) (htsw i) v
          calc
            _ = (a : E) * d * star (a : E) +
                ((a : E) * bufferedAbsorptionValue w (t i) (s i) 1 * star (a : E) -
                  bufferedAbsorptionValue w (t i) (s i) (m + 1)) := by
              change (a : E) * (u : E) * s i * star ((a : E) * (u : E)) - _ = _
              rw [star_mul]
              dsimp only [d]
              noncomm_ring
            _ = _ := by
              rw [hc, bufferedAbsorptionValue_succ w (t i) (s i) (htw i)]
              dsimp only [e]
              noncomm_ring
        rw [hidentity]
        have hd : ‖(a : E) * d * star (a : E)‖ ≤ ε := by
          rw [mul_assoc, CStarRing.norm_coe_unitary_mul]
          change ‖d * (star a : unitary E)‖ ≤ ε
          rw [CStarRing.norm_mul_coe_unitary]
          exact he i
        calc
          _ ≤ ‖(a : E) * d * star (a : E)‖ + ‖w * e * star w‖ := norm_add_le _ _
          _ ≤ ε + m * ε := add_le_add hd ((buffered_sandwich_norm w e hw).trans (hvi i))
          _ = _ := by push_cast; ring

/-- One actual source corner works at every finite iteration depth.  The
chosen unitary depends on the depth and requested final error. -/
lemma exists_canonical_buffered_iterations [Nontrivial E]
    (s t : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (hst : bergRowsCommute s t) (n : ℕ) (κ : ℝ) (hκ : 0 < κ) :
    ∃ D : BufferAbsorptionCorner E,
      D.q ≠ 0 ∧
      (∀ i : Fin (n + 1), ‖s i * D.q - D.q * s i‖ < κ) ∧
      (∀ i : Fin (n + 1),
        ‖D.q * s i * D.q - zeroCornerRow D.q D.a D.b n i‖ < κ) ∧
      ∀ (m : ℕ) (ε : ℝ), 0 < ε →
        ∃ v : unitary E, Joined (1 : unitary E) v ∧
          ∀ i : Fin n, ‖(v : E) * s i * star (v : E) -
            bufferedAbsorptionValue D.w (t i) (s i) m‖ < ε := by
  obtain ⟨D, hanchor, hqne, hqz, hqc, hcomp, hcomm⟩ :=
    exists_canonical_connected_absorption_corner s hs n κ hκ
  have htc (i : ℕ) : ∀ j, Commute (s j) (t i) ∧ Commute (star (s j)) (t i) := by
    intro j
    exact ⟨(hst j i).1, by simpa only [star_star] using (hst j i).2.star_star⟩
  have htcs (i : ℕ) : ∀ j, Commute (s j) (star (t i)) ∧
      Commute (star (s j)) (star (t i)) := by
    intro j
    exact ⟨(hst j i).2, (hst j i).1.star_star⟩
  have hqt (i : ℕ) := (hcomm (t i) (htc i)).1
  have hat (i : ℕ) : Commute (star D.a) (t i) := by
    simpa only [star_star] using (hcomm (star (t i)) (htcs i)).2.2.1.star_star
  have hbt (i : ℕ) : Commute (star D.b) (t i) := by
    simpa only [star_star] using (hcomm (star (t i)) (htcs i)).2.2.2.star_star
  have htw (i : ℕ) : Commute (t i) D.w := (hcomm (t i) (htc i)).2.1.symm
  have htsw (i : ℕ) : Commute (t i) (star D.w) := by
    simpa only [star_star] using (hcomm (star (t i)) (htcs i)).2.1.star_star.symm
  refine ⟨D, hqne, hqc, hcomp, fun m ε hε => ?_⟩
  let δ := ε / ((m : ℝ) + 1)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  obtain ⟨u, hu, hui⟩ := D.exists_proper_vacuum_absorption
    s t hs ht n hqz hqt hat hbt δ hδ
  have hstep (i : Fin n) : ‖(u : E) * s i * star (u : E) -
      bufferedAbsorptionValue D.w (t i) (s i) 1‖ ≤ δ := by
    simpa only [bufferedAbsorptionValue_one, D.w_range, sub_sub_cancel] using (hui i).le
  obtain ⟨v, hv, hvi⟩ := exists_connected_buffered_iteration
    (fun i : Fin n => s i) (fun i : Fin n => t i) D.w D.w_gram
    (fun i => htw i) (fun i => htsw i) u (hanchor.trans hu) δ hstep m
  refine ⟨v, hv, fun i => (hvi i).trans_lt ?_⟩
  have hden : 0 < (m : ℝ) + 1 := by positivity
  have hid : ((m : ℝ) + 1) * δ = ε := by
    dsimp only [δ]
    field_simp
  nlinarith

end WeakPureInfiniteness

end

end OAI
