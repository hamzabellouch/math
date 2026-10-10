import OAI.Analysis.OInfinity.ControlledAbsorption

namespace OAI

/-! # Exact relocation of the whole buffered tail

An actual unit-isometry in the canonical vacuum corner exchanges its range
with the full terminal range of `w^(m+1)`. The swap commutes with the target
family and has a uniform path. Its formula retains the residual source copy;
relocation itself does not estimate that copy by zero.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

lemma buffered_isometry_pow_gram (w : E) (hw : star w * w = 1) (m : ℕ) :
    star (w ^ m) * w ^ m = 1 := by
  induction m with
  | zero => simp only [pow_zero, star_one, one_mul]
  | succ m ih =>
      rw [pow_succ', star_mul]
      calc
        _ = star (w ^ m) * (star w * w) * w ^ m := by noncomm_ring
        _ = 1 := by rw [hw, mul_one, ih]

/-- Two orthogonal full isometries have a self-adjoint swap. Its commutant
property is stated for both isometries and adjoints, not inferred from
unstarred commutation alone. -/
lemma exists_controlled_isometry_swap [Nontrivial E] (r z : E)
    (hr : star r * r = 1) (hz : star z * z = 1) (hzr : star z * r = 0) :
    ∃ u : unitary E, (u : E) * r = z ∧ (u : E) * z = r ∧
      star (u : E) = (u : E) ∧
      (∀ x : E, Commute r x → Commute (star r) x →
        Commute z x → Commute (star z) x → Commute (u : E) x) ∧
      ∃ p : Path (1 : unitary E) u,
        ∀ a b, ‖(p a : E) - p b‖ ≤ (2 * Real.pi) * |(a : ℝ) - b| := by
  have hrz : star r * z = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star hzr
  let v := z * star r
  have hv : v * star v * v = v := by
    dsimp only [v]
    rw [star_mul, star_star]
    calc
      _ = z * (star r * r) * (star z * z) * star r := by noncomm_ring
      _ = _ := by rw [hr, hz, mul_one, mul_one]
  have hvv : v * v = 0 := by
    change (z * star r) * (z * star r) = 0
    calc
      _ = z * (star r * z) * star r := by noncomm_ring
      _ = 0 := by rw [hrz, mul_zero, zero_mul]
  let u := partialIsometrySwapUnitary v hv hvv
  have hus : star (u : E) = (u : E) := partialIsometrySwap_star v
  have hug : (u : E) * (u : E) = 1 := by
    calc
      _ = star (u : E) * (u : E) := by rw [hus]
      _ = 1 := u.prop.1
  have hvr : star v * v = r * star r := by
    dsimp only [v]
    rw [star_mul, star_star]
    calc
      _ = r * (star z * z) * star r := by noncomm_ring
      _ = _ := by rw [hz, mul_one]
  have hur : (u : E) * r = z := by
    calc
      _ = (u : E) * ((r * star r) * r) := by rw [mul_assoc r, hr, mul_one]
      _ = ((u : E) * (star v * v)) * r := by rw [hvr]; noncomm_ring
      _ = v * r := by rw [show (u : E) * (star v * v) = v from
        partialIsometrySwap_mul_initial v hv hvv]
      _ = z := by change z * star r * r = z; rw [mul_assoc, hr, mul_one]
  have huz : (u : E) * z = r := by
    rw [← hur, ← mul_assoc, hug, one_mul]
  refine ⟨u, hur, huz, hus, ?_, ?_⟩
  · intro x hrx hsrx hzx hszx
    have hvx : Commute v x := hzx.mul_left hsrx
    have hsvx : Commute (star v) x := by
      simpa only [v, star_mul, star_star] using hrx.mul_left hszx
    change Commute (v + star v + (1 - star v * v - v * star v)) x
    exact (hvx.add_left hsvx).add_left
      (((Commute.one_left x).sub_left (hsvx.mul_left hvx)).sub_left (hvx.mul_left hsvx))
  · exact exists_controlled_selfadjoint_unitary_path u hus

/-- Conjugation by a target-commuting unitary relocates the whole source
summand exactly. -/
lemma bufferedAbsorptionValue_relocate (w z t x : E) (m : ℕ) (u : unitary E)
    (hut : Commute (u : E) t) (hur : (u : E) * w ^ m = z) :
    (u : E) * bufferedAbsorptionValue w t x m * star (u : E) =
      t * (1 - z * star z) + z * x * star z := by
  have hrs : star (w ^ m) * star (u : E) = star z := by
    simpa only [star_mul] using congrArg star hur
  unfold bufferedAbsorptionValue
  calc
    _ = ((u : E) * t) * (1 - w ^ m * star (w ^ m)) * star (u : E) +
        ((u : E) * w ^ m) * x * (star (w ^ m) * star (u : E)) := by noncomm_ring
    _ = (t * (u : E)) * (1 - w ^ m * star (w ^ m)) * star (u : E) +
        z * x * star z := by rw [hut.eq, hur, hrs]
    _ = t * ((u : E) * star (u : E)) -
        t * ((u : E) * w ^ m) * (star (w ^ m) * star (u : E)) +
        z * x * star z := by noncomm_ring
    _ = _ := by rw [u.prop.2, hur, hrs]; noncomm_ring

/-- A single target-commuting swap moves every tested generator's terminal
copy to the same fixed internal range, with cost `2π`, independently of depth. -/
lemma exists_controlled_buffered_tail_swap [Nontrivial E] {I : Type*}
    (w z : E) (hw : star w * w = 1) (hz : star z * z = 1)
    (hzw : star z * w = 0) (t : I → E)
    (htw : ∀ i, Commute w (t i)) (htsw : ∀ i, Commute (star w) (t i))
    (htz : ∀ i, Commute z (t i)) (htsz : ∀ i, Commute (star z) (t i))
    (m : ℕ) :
    ∃ u : unitary E,
      (∀ i x, (u : E) * bufferedAbsorptionValue w (t i) x (m + 1) * star (u : E) =
        t i * (1 - z * star z) + z * x * star z) ∧
      ∃ p : Path (1 : unitary E) u,
        ∀ a b, ‖(p a : E) - p b‖ ≤ (2 * Real.pi) * |(a : ℝ) - b| := by
  have hzr : star z * w ^ (m + 1) = 0 := by
    rw [pow_succ', ← mul_assoc, hzw, zero_mul]
  obtain ⟨u, hur, _, _, huc, p, hp⟩ := exists_controlled_isometry_swap
    (w ^ (m + 1)) z (buffered_isometry_pow_gram w hw (m + 1)) hz hzr
  refine ⟨u, ?_, p, hp⟩
  intro i x
  have hr := (htw i).pow_left (m + 1)
  have hsr : Commute (star (w ^ (m + 1))) (t i) := by
    simpa only [star_pow] using (htsw i).pow_left (m + 1)
  exact bufferedAbsorptionValue_relocate w z (t i) x (m + 1) u
    (huc (t i) hr hsr (htz i) (htsz i)) hur


/-- All support and commutant conditions for the terminal swap come from
the actual canonical vacuum split. The relocated source copy is explicit. -/
lemma exists_canonical_controlled_tail_swaps [Nontrivial E]
    (s t : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (hst : bergRowsCommute s t) (n : ℕ) (κ : ℝ) (hκ : 0 < κ) :
    ∃ (D : BufferAbsorptionCorner E) (z : E),
      star z * z = 1 ∧ D.q * z = z ∧ D.q ≠ 0 ∧
      (∀ i : Fin (n + 1), ‖s i * D.q - D.q * s i‖ < κ) ∧
      (∀ i : Fin (n + 1),
        ‖D.q * s i * D.q - zeroCornerRow D.q D.a D.b n i‖ < κ) ∧
      ∀ m, ∃ u : unitary E,
        (∀ (i : ℕ) (x : E),
          (u : E) * bufferedAbsorptionValue D.w (t i) x (m + 1) * star (u : E) =
            t i * (1 - z * star z) + z * x * star z) ∧
        ∃ p : Path (1 : unitary E) u,
          ∀ a b, ‖(p a : E) - p b‖ ≤ (2 * Real.pi) * |(a : ℝ) - b| := by
  obtain ⟨D, _, hqne, _, hqc, hcomp, ⟨z, hz, hqz, hzcomm⟩, hcomm⟩ :=
    exists_canonical_connected_absorption_corner_with_commuting_isometry s hs n κ hκ
  have htc (i : ℕ) : ∀ j, Commute (s j) (t i) ∧ Commute (star (s j)) (t i) := by
    intro j
    exact ⟨(hst j i).1, by simpa only [star_star] using (hst j i).2.star_star⟩
  have htcs (i : ℕ) : ∀ j, Commute (s j) (star (t i)) ∧
      Commute (star (s j)) (star (t i)) := by
    intro j
    exact ⟨(hst j i).2, (hst j i).1.star_star⟩
  have htw (i : ℕ) := (hcomm (t i) (htc i)).2.1
  have htsw (i : ℕ) : Commute (star D.w) (t i) := by
    simpa only [star_star] using (hcomm (star (t i)) (htcs i)).2.1.star_star
  have htz (i : ℕ) := hzcomm (t i) (htc i)
  have htsz (i : ℕ) : Commute (star z) (t i) := by
    simpa only [star_star] using (hzcomm (star (t i)) (htcs i)).star_star
  have hzw : star z * D.w = 0 := by
    have hszq : star z * D.q = star z := by
      simpa only [star_mul, D.projection.isSelfAdjoint.star_eq] using congrArg star hqz
    calc
      _ = (star z * D.q) * D.w := by rw [hszq]
      _ = 0 := by rw [mul_assoc, D.w_orthogonal, mul_zero]
  exact ⟨D, z, hz, hqz, hqne, hqc, hcomp,
    fun m => exists_controlled_buffered_tail_swap D.w z D.w_gram hz hzw t
      htw htsw htz htsz m⟩

end WeakPureInfiniteness

end

end OAI
