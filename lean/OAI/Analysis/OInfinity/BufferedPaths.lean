import OAI.Analysis.OInfinity.BufferedIteration
import OAI.Analysis.OInfinity.FixedSpareStabilization

namespace OAI

/-! # Uniform paths for actual buffered iterates

The compression of every connected unitary fixes the same full isometry
inside the complementary corner. The fixed-spare construction gives these
compressions a uniform `9π` path bound. The resulting iterates have a bound
independent of depth, with the fixed base path cost retained. Their terminal
representation is still the entire isometric copy.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

/-- A connected unitary has some finite Lipschitz path, by its finite
self-adjoint exponential decomposition. No uniform bound is asserted here. -/
lemma exists_lipschitz_joined_unitary_path (u : unitary E)
    (hu : Joined (1 : unitary E) u) :
    ∃ (L : ℝ), 0 ≤ L ∧ ∃ p : Path (1 : unitary E) u,
      ∀ a b, ‖(p a : E) - p b‖ ≤ L * |(a : ℝ) - b| := by
  obtain ⟨l, hl⟩ := Unitary.mem_pathComponentOne_iff.mp hu
  suffices h : ∀ l : List (selfAdjoint E), ∃ (L : ℝ), 0 ≤ L ∧
      ∃ p : Path (1 : unitary E) (l.map selfAdjoint.expUnitary).prod,
        ∀ a b, ‖(p a : E) - p b‖ ≤ L * |(a : ℝ) - b| by
    obtain ⟨L, hL, p, hp⟩ := h l
    exact ⟨L, hL, p.cast rfl hl.symm, hp⟩
  intro l
  induction l with
  | nil =>
      change ∃ (L : ℝ), 0 ≤ L ∧ ∃ p : Path (1 : unitary E) 1,
        ∀ a b, ‖(p a : E) - p b‖ ≤ L * |(a : ℝ) - b|
      refine ⟨0, le_rfl, Path.refl 1, fun a b => ?_⟩
      change ‖(1 : E) - 1‖ ≤ 0 * |(a : ℝ) - b|
      rw [sub_self, norm_zero, zero_mul]
  | cons x xs ih =>
      obtain ⟨L, hL, p, hp⟩ := ih
      let e := selfAdjoint.expUnitaryPathToOne x
      have he (a b : unitInterval) :
          ‖(e a : E) - e b‖ ≤ ‖x‖ * |(a : ℝ) - b| := by
        simpa only [e, selfAdjoint.expUnitaryPathToOne_apply, mul_comm] using
          selfAdjoint_expUnitary_sub_norm_le x (a : ℝ) (b : ℝ)
      refine ⟨‖x‖ + L, add_nonneg (norm_nonneg _) hL,
        (e.mul p).cast (by simp) rfl, ?_⟩
      exact unitaryPath_mul_sub_norm_le e p ‖x‖ L he hp

lemma binaryCornerUnitary_fixes (w z : E) (hw : star w * w = 1)
    (hswz : star w * z = 0) (u : unitary E) :
    (binaryCornerUnitary w hw u : E) * z = z := by
  change (w * (u : E) * star w + (1 - w * star w)) * z = z
  calc
    _ = w * (u : E) * (star w * z) + z - w * (star w * z) := by noncomm_ring
    _ = z := by rw [hswz]; simp only [mul_zero, zero_add, sub_zero]

/-- The compressed unitary has a uniform path once a genuine unit-isometry
in its fixed corner is supplied. -/
lemma exists_uniform_binaryCorner_path [Nontrivial E]
    (s : ℕ → E) (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (w z : E) (hw : star w * w = 1) (hz : star z * z = 1)
    (hswz : star w * z = 0) (u : unitary E) (hu : Joined (1 : unitary E) u) :
    ∃ p : Path (1 : unitary E) (binaryCornerUnitary w hw u),
      ∀ a b, ‖(p a : E) - p b‖ ≤ (9 * Real.pi) * |(a : ℝ) - b| := by
  obtain ⟨L, _, p, hp⟩ := exists_lipschitz_joined_unitary_path u hu
  let q : Path (1 : unitary E) (binaryCornerUnitary w hw u) :=
    (binaryCornerPath w hw p).cast (binaryCornerUnitary_one w hw).symm rfl
  have hqfix (a : unitInterval) : (q a : E) * z = z :=
    binaryCornerUnitary_fixes w z hw hswz (p a)
  have hq (a b : unitInterval) : ‖(q a : E) - q b‖ ≤ L * |(a : ℝ) - b| :=
    binaryCornerPath_sub_norm_le w hw p L hp a b
  exact exists_uniform_fixedSpare_path s hs z hz _ q hqfix L hq

/-- The actual unitary recursion used in buffered absorption. -/
def bufferedIterationUnitary (w : E) (hw : star w * w = 1)
    (u : unitary E) : ℕ → unitary E
  | 0 => 1
  | n + 1 => binaryCornerUnitary w hw (bufferedIterationUnitary w hw u n) * u

lemma bufferedIterationUnitary_joined (w : E) (hw : star w * w = 1)
    (u : unitary E) (hu : Joined (1 : unitary E) u) (n : ℕ) :
    Joined (1 : unitary E) (bufferedIterationUnitary w hw u n) := by
  induction n with
  | zero => exact Joined.refl _
  | succ n ih =>
      have hc := ih.map (binaryCornerUnitary_continuous w hw)
      simpa only [bufferedIterationUnitary, binaryCornerUnitary_one, one_mul] using hc.mul hu

/-- Only the base path cost appears beside `9π`; the iteration depth does
not enter the bound. This statement does not bound that base cost uniformly. -/
lemma exists_uniform_bufferedIteration_paths [Nontrivial E]
    (s : ℕ → E) (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (w z : E) (hw : star w * w = 1) (hz : star z * z = 1)
    (hswz : star w * z = 0) (u : unitary E)
    (L : ℝ) (hL : 0 ≤ L) (p : Path (1 : unitary E) u)
    (hp : ∀ a b, ‖(p a : E) - p b‖ ≤ L * |(a : ℝ) - b|) :
    ∀ n, ∃ q : Path (1 : unitary E) (bufferedIterationUnitary w hw u n),
      ∀ a b, ‖(q a : E) - q b‖ ≤ (9 * Real.pi + L) * |(a : ℝ) - b| := by
  intro n
  cases n with
  | zero =>
      change ∃ q : Path (1 : unitary E) 1,
        ∀ a b, ‖(q a : E) - q b‖ ≤ (9 * Real.pi + L) * |(a : ℝ) - b|
      refine ⟨Path.refl 1, fun a b => ?_⟩
      change ‖(1 : E) - 1‖ ≤ (9 * Real.pi + L) * |(a : ℝ) - b|
      rw [sub_self, norm_zero]
      positivity
  | succ n =>
      obtain ⟨q, hq⟩ := exists_uniform_binaryCorner_path s hs w z hw hz hswz
        (bufferedIterationUnitary w hw u n)
        (bufferedIterationUnitary_joined w hw u ⟨p⟩ n)
      refine ⟨(q.mul p).cast (by simp) rfl, ?_⟩
      exact unitaryPath_mul_sub_norm_le q p (9 * Real.pi) L hq hp

/-- The exact residual formula and accumulated error for the concrete
recursion whose paths were constructed above. -/
lemma bufferedIterationUnitary_error {I : Type*}
    (s t : I → E) (w : E) (hw : star w * w = 1)
    (htw : ∀ i, Commute (t i) w) (htsw : ∀ i, Commute (t i) (star w))
    (u : unitary E) (ε : ℝ)
    (he : ∀ i, ‖(u : E) * s i * star (u : E) -
      bufferedAbsorptionValue w (t i) (s i) 1‖ ≤ ε) (n : ℕ) :
    ∀ i, ‖(bufferedIterationUnitary w hw u n : E) * s i *
        star (bufferedIterationUnitary w hw u n : E) -
      bufferedAbsorptionValue w (t i) (s i) n‖ ≤ n * ε := by
  induction n with
  | zero =>
      intro i
      simp only [bufferedIterationUnitary, OneMemClass.coe_one, one_mul, star_one,
        mul_one, bufferedAbsorptionValue_zero, sub_self, norm_zero,
        Nat.cast_zero, zero_mul, le_refl]
  | succ n ih =>
      intro i
      let v := bufferedIterationUnitary w hw u n
      let a := binaryCornerUnitary w hw v
      let d := (u : E) * s i * star (u : E) - bufferedAbsorptionValue w (t i) (s i) 1
      let e := (v : E) * s i * star (v : E) - bufferedAbsorptionValue w (t i) (s i) n
      have hid : (bufferedIterationUnitary w hw u (n + 1) : E) * s i *
          star (bufferedIterationUnitary w hw u (n + 1) : E) -
          bufferedAbsorptionValue w (t i) (s i) (n + 1) =
          (a : E) * d * star (a : E) + w * e * star w := by
        have hc : (a : E) * bufferedAbsorptionValue w (t i) (s i) 1 * star (a : E) =
            t i * (1 - w * star w) + w * ((v : E) * s i * star (v : E)) * star w := by
          rw [bufferedAbsorptionValue_one]
          exact bufferedAbsorption_conjugate w (t i) (s i) hw (htw i) (htsw i) v
        calc
          _ = (a : E) * d * star (a : E) +
              ((a : E) * bufferedAbsorptionValue w (t i) (s i) 1 * star (a : E) -
                bufferedAbsorptionValue w (t i) (s i) (n + 1)) := by
            change (a : E) * (u : E) * s i * star ((a : E) * (u : E)) - _ = _
            rw [star_mul]
            dsimp only [d]
            noncomm_ring
          _ = _ := by
            rw [hc, bufferedAbsorptionValue_succ w (t i) (s i) (htw i)]
            dsimp only [e]
            noncomm_ring
      rw [hid]
      have hd : ‖(a : E) * d * star (a : E)‖ ≤ ε := by
        rw [mul_assoc, CStarRing.norm_coe_unitary_mul]
        change ‖d * (star a : unitary E)‖ ≤ ε
        rw [CStarRing.norm_mul_coe_unitary]
        exact he i
      have hnorm : ‖w * e * star w‖ ≤ ‖e‖ := by
        have hwn : ‖w‖ ≤ 1 := by
          have h := congrArg norm hw
          rw [CStarRing.norm_star_mul_self] at h
          have h1 : ‖(1 : E)‖ ≤ 1 := by
            have hh := congrArg norm (show star (1 : E) * 1 = 1 by simp)
            rw [CStarRing.norm_star_mul_self] at hh
            nlinarith [norm_nonneg (1 : E)]
          nlinarith [norm_nonneg w]
        calc
          _ ≤ ‖w‖ * ‖e‖ * ‖w‖ := by
            simpa only [norm_star] using (norm_mul_le (w * e) (star w)).trans
              (mul_le_mul_of_nonneg_right (norm_mul_le w e) (norm_nonneg _))
          _ ≤ 1 * ‖e‖ * 1 := by gcongr
          _ = _ := by ring
      calc
        _ ≤ ‖(a : E) * d * star (a : E)‖ + ‖w * e * star w‖ := norm_add_le _ _
        _ ≤ ε + n * ε := add_le_add hd (hnorm.trans (ih i))
        _ = _ := by push_cast; ring


/-- For each fixed one-step accuracy the canonical construction has one
path bound for all depths. The accumulated error is exactly retained as
`m * η`; choosing a new accuracy may also change the base path bound. -/
lemma exists_canonical_buffered_path_iterations [Nontrivial E]
    (s t : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (hst : bergRowsCommute s t) (n : ℕ) (κ : ℝ) (hκ : 0 < κ) :
    ∃ D : BufferAbsorptionCorner E, D.q ≠ 0 ∧
      (∀ i : Fin (n + 1), ‖s i * D.q - D.q * s i‖ < κ) ∧
      (∀ i : Fin (n + 1),
        ‖D.q * s i * D.q - zeroCornerRow D.q D.a D.b n i‖ < κ) ∧
      ∀ η : ℝ, 0 < η → ∃ L : ℝ, 0 ≤ L ∧ ∀ m : ℕ,
        ∃ v : unitary E,
          (∀ i : Fin n, ‖(v : E) * s i * star (v : E) -
            bufferedAbsorptionValue D.w (t i) (s i) m‖ ≤ m * η) ∧
          ∃ p : Path (1 : unitary E) v,
            ∀ a b, ‖(p a : E) - p b‖ ≤ L * |(a : ℝ) - b| := by
  obtain ⟨D, hanchor, hqne, hqz, hqc, hcomp, ⟨z, hz, hqz'⟩, hcomm⟩ :=
    exists_canonical_connected_absorption_corner_with_isometry s hs n κ hκ
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
  have hswq : star D.w * D.q = 0 := by
    have heq : D.q = 1 - D.w * star D.w := by rw [D.w_range]; abel
    rw [heq, mul_sub, mul_one, ← mul_assoc, D.w_gram, one_mul, sub_self]
  have hswz : star D.w * z = 0 := by
    calc
      _ = star D.w * (D.q * z) := by rw [hqz']
      _ = (star D.w * D.q) * z := by rw [mul_assoc]
      _ = 0 := by rw [hswq, zero_mul]
  refine ⟨D, hqne, hqc, hcomp, fun η hη => ?_⟩
  obtain ⟨u, hu, hui⟩ := D.exists_proper_vacuum_absorption
    s t hs ht n hqz hqt hat hbt η hη
  obtain ⟨L, hL, p, hp⟩ := exists_lipschitz_joined_unitary_path u (hanchor.trans hu)
  have hpaths := exists_uniform_bufferedIteration_paths s hs D.w z D.w_gram hz hswz
    u L hL p hp
  refine ⟨9 * Real.pi + L, by positivity, fun m => ?_⟩
  obtain ⟨q, hq⟩ := hpaths m
  refine ⟨bufferedIterationUnitary D.w D.w_gram u m, ?_, q, hq⟩
  apply bufferedIterationUnitary_error (fun i : Fin n => s i) (fun i : Fin n => t i)
    D.w D.w_gram (fun i => htw i) (fun i => htsw i) u η
  intro i
  simpa only [bufferedAbsorptionValue_one, D.w_range, sub_sub_cancel] using (hui i).le

end WeakPureInfiniteness

end

end OAI
