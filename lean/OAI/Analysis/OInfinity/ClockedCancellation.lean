import OAI.Analysis.OInfinity.JointClock

namespace OAI

/-! # Actual clock-corrected quarter paths on the joint tower

The clock removes the two off-diagonal transport degrees of the actual
length-two/length-one cancellation. Every surviving commutator is bounded
from the supplied rows and the actual joint cyclic partition.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

private lemma clock_left_commutator_norm (v : unitary E) (x e f : E)
    (he : e * (v : E) = (v : E) * f) :
    ‖((v : E) * x) * e - e * ((v : E) * x)‖ = ‖x * e - f * x‖ := by
  have hid : ((v : E) * x) * e - e * ((v : E) * x) = (v : E) * (x * e - f * x) := by
    calc
      _ = (v : E) * (x * e) - (e * (v : E)) * x := by noncomm_ring
      _ = _ := by rw [he]; noncomm_ring
  rw [hid, CStarRing.norm_coe_unitary_mul]

lemma clockDegreeCorrection_one_commutator {N : ℕ} [NeZero N]
    (k : unitary E) (e : ZMod N → E) (he : ∀ j, star (e j) = e j)
    (hk : ∀ j, (k : E) * e j = e (j + 1) * (k : E)) (x : E) (j : ZMod N) :
    ‖clockDegreeCorrection k 1 x * e j - e j * clockDegreeCorrection k 1 x‖ =
      ‖x * e j - e (j + 1) * x‖ := by
  have hcell : e j * ((k⁻¹ : unitary E) : E) = ((k⁻¹ : unitary E) : E) * e (j + 1) := by
    have h := clock_inverse_pow_cycles (k : E) e he hk 1 j
    simpa only [pow_one, Nat.cast_one, ← Unitary.coe_star, Unitary.star_eq_inv] using h.symm
  simpa only [clockDegreeCorrection, zpow_neg_one] using
    clock_left_commutator_norm (k⁻¹) x (e j) (e (j + 1)) hcell

lemma clockDegreeCorrection_neg_one_commutator {N : ℕ} [NeZero N]
    (k : unitary E) (e : ZMod N → E)
    (hk : ∀ j, (k : E) * e j = e (j + 1) * (k : E)) (x : E) (j : ZMod N) :
    ‖clockDegreeCorrection k (-1) x * e j - e j * clockDegreeCorrection k (-1) x‖ =
      ‖x * e j - e (j - 1) * x‖ := by
  have hcell : e j * (k : E) = (k : E) * e (j - 1) := by
    simpa only [sub_add_cancel] using (hk (j - 1)).symm
  simpa only [clockDegreeCorrection, neg_neg, zpow_one] using
    clock_left_commutator_norm k x (e j) (e (j - 1)) hcell

private lemma clocked_isometry_norm (x : E) (hx : star x * x = 1) : ‖x‖ ≤ 1 := by
  have h := congrArg norm hx
  rw [CStarRing.norm_star_mul_self] at h
  nlinarith [norm_nonneg x, (IsStarProjection.one E).norm_le]

/-- The two corrected off-diagonal terms now have degree zero with respect
to the actual cyclic cells. -/
lemma clockCorrectedCancellation_cell_commutator {N : ℕ} [NeZero N]
    (k : unitary E) (e : ZMod N → E) (he : ∀ j, star (e j) = e j)
    (hk : ∀ j, (k : E) * e j = e (j + 1) * (k : E))
    (a b : E) (u : unitary E) (ha : star a * a = 1) (hb : star b * b = 1)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hat : ∀ j, ‖a * e j - e (j + 2) * a‖ ≤ δ)
    (hbt : ∀ j, ‖b * e j - e (j + 1) * b‖ ≤ δ)
    (hut : ∀ j, ‖(u : E) * e j - e j * (u : E)‖ ≤ δ)
    (θ : ℝ) (j : ZMod N) :
    ‖clockCorrectedCancellation k a b u θ * e j -
      e j * clockCorrectedCancellation k a b u θ‖ ≤ 20 * δ := by
  have han := clocked_isometry_norm a ha
  have hbn := clocked_isometry_norm b hb
  have hun := clocked_isometry_norm (u : E) u.prop.1
  have hum : ‖(u : E) - 1‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by linarith [(IsStarProjection.one E).norm_le])
  have hus : ‖star (u : E) - 1‖ ≤ 2 := by
    calc
      _ = ‖star ((u : E) - 1)‖ := by rw [star_sub, star_one]
      _ = ‖(u : E) - 1‖ := norm_star _
      _ ≤ 2 := hum
  have huc (j : ZMod N) : ‖((u : E) - 1) * e j - e j * ((u : E) - 1)‖ ≤ δ := by
    convert hut j using 1; congr 1; noncomm_ring
  have husc (j : ZMod N) : ‖(star (u : E) - 1) * e j - e j * (star (u : E) - 1)‖ ≤ δ := by
    have h := (adjoint_unitary_commutator_norm u (e j) (he j)).le.trans (hut j)
    convert h using 1; congr 1; noncomm_ring
  let A := a * ((u : E) - 1) * star a
  let B := b * (star (u : E) - 1) * star b
  let X := a * ((u : E) - 1) * star b
  let Y := b * (star (u : E) - 1) * star a
  have hA : ‖A * e j - e j * A‖ ≤ 5 * δ := by
    simpa only [add_sub_cancel_right] using
      tower_sandwich_transport e he a a ((u : E) - 1) 2 2 δ hδ han han hum hat hat huc j
  have hB : ‖B * e j - e j * B‖ ≤ 5 * δ := by
    simpa only [add_sub_cancel_right] using
      tower_sandwich_transport e he b b (star (u : E) - 1) 1 1 δ hδ hbn hbn hus hbt hbt husc j
  have hX : ‖X * e j - e (j + 1) * X‖ ≤ 5 * δ := by
    simpa only [show j + (2 : ZMod N) - 1 = j + 1 by ring] using
      tower_sandwich_transport e he a b ((u : E) - 1) 2 1 δ hδ han hbn hum hat hbt huc j
  have hY : ‖Y * e j - e (j - 1) * Y‖ ≤ 5 * δ := by
    simpa only [show j + (1 : ZMod N) - 2 = j - 1 by ring] using
      tower_sandwich_transport e he b a (star (u : E) - 1) 1 2 δ hδ hbn han hus hbt hat husc j
  have hAB : ‖(A + B) * e j - e j * (A + B)‖ ≤ 10 * δ := by
    have hid : (A + B) * e j - e j * (A + B) =
        (A * e j - e j * A) + (B * e j - e j * B) := by noncomm_ring
    rw [hid]
    exact (norm_add_le _ _).trans (by linarith)
  have hX' : ‖clockDegreeCorrection k 1 X * e j - e j * clockDegreeCorrection k 1 X‖ ≤ 5 * δ := by
    rw [clockDegreeCorrection_one_commutator k e he hk]
    exact hX
  have hY' : ‖clockDegreeCorrection k (-1) Y * e j - e j * clockDegreeCorrection k (-1) Y‖ ≤ 5 * δ := by
    rw [clockDegreeCorrection_neg_one_commutator k e hk]
    exact hY
  have hcos : |Real.cos θ ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.sin θ)]
  have hsc : |Real.sin θ * Real.cos θ| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul (Real.abs_sin_le_one θ) (Real.abs_cos_le_one θ)
      (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have hid : clockCorrectedCancellation k a b u θ * e j -
      e j * clockCorrectedCancellation k a b u θ =
      (Real.cos θ ^ 2) • ((A + B) * e j - e j * (A + B)) +
      (Real.sin θ * Real.cos θ) • (clockDegreeCorrection k 1 X * e j - e j * clockDegreeCorrection k 1 X) -
      (Real.sin θ * Real.cos θ) • (clockDegreeCorrection k (-1) Y * e j - e j * clockDegreeCorrection k (-1) Y) := by
    change (1 + (Real.cos θ ^ 2) • (A + B) +
      (Real.sin θ * Real.cos θ) • (clockDegreeCorrection k 1 X - clockDegreeCorrection k (-1) Y)) * e j -
      e j * (1 + (Real.cos θ ^ 2) • (A + B) +
      (Real.sin θ * Real.cos θ) • (clockDegreeCorrection k 1 X - clockDegreeCorrection k (-1) Y)) = _
    simp only [add_mul, sub_mul, mul_add, mul_sub, one_mul, mul_one,
      smul_mul_assoc, mul_smul_comm, smul_sub]
    module
  rw [hid]
  apply (norm_sub_le _ _).trans
  apply (add_le_add (norm_add_le _ _) le_rfl).trans
  simp only [norm_smul, Real.norm_eq_abs]
  calc
    _ ≤ 1 * (10 * δ) + 1 * (5 * δ) + 1 * (5 * δ) := add_le_add
      (add_le_add (mul_le_mul hcos hAB (norm_nonneg _) (by norm_num))
        (mul_le_mul hsc hX' (norm_nonneg _) (by norm_num)))
      (mul_le_mul hsc hY' (norm_nonneg _) (by norm_num))
    _ = _ := by ring

private lemma clocked_near_commutator (x y e : E) (he : ‖e‖ ≤ 1) :
    ‖x * e - e * x‖ ≤ 2 * ‖x - y‖ + ‖y * e - e * y‖ := by
  have hid : x * e - e * x = (x - y) * e - e * (x - y) + (y * e - e * y) := by noncomm_ring
  rw [hid]
  calc
    _ ≤ ‖(x - y) * e - e * (x - y)‖ + ‖y * e - e * y‖ := norm_add_le _ _
    _ ≤ (‖(x - y) * e‖ + ‖e * (x - y)‖) + ‖y * e - e * y‖ :=
      add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ (‖x - y‖ * ‖e‖ + ‖e‖ * ‖x - y‖) + ‖y * e - e * y‖ := by gcongr <;> apply norm_mul_le
    _ ≤ (‖x - y‖ * 1 + 1 * ‖x - y‖) + ‖y * e - e * y‖ := by gcongr
    _ = _ := by ring


/-- Actual quarter-cancellation paths for every relevant pair of source
words, on one jointly constructed clock and cyclic partition. The path,
its endpoints, cell commutators and sample bound are all supplied here. -/
lemma exists_joint_clocked_quarter_paths [Nontrivial E] (s t : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (hsum : (∑ i, s i * star (s i)) = 1)
    (htsum : (∑ i, t i * star (t i)) = 1)
    (hcomm : bergRowsCommute s t) (m n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (k : unitary E) (e : ZMod (2 ^ m) → E),
      (k : E) ^ (2 ^ m) = 1 ∧
      (∀ j, IsStarProjection (e j)) ∧ (∑ j, e j) = 1 ∧
      (∀ j l, j ≠ l → e j * e l = 0) ∧
      (∀ j, (k : E) * e j = e (j + 1) * (k : E)) ∧
      ‖finiteRowShift s k - (k : E)‖ < ε ∧
      (∀ j, ‖finiteRowShift s (e j) - e (j + 1)‖ < ε) ∧
      (∀ j, ‖finiteRowShift t (e j) - e (j + 1)‖ < ε) ∧
      ∀ i r l : Fin 2, i ≠ l → ∃ p : ℝ → unitary E, Continuous p ∧
        (p 0 : E) = cornerCompression (s i * s r)
          (binaryRowCocycleUnitary s t hs ht hsum htsum n : E) *
          cornerCompression (s l) (star (binaryRowCocycleUnitary s t hs ht hsum htsum n : E)) ∧
        (p (Real.pi / 2) : E) = 1 ∧ (∀ θ, Joined (1 : unitary E) (p θ)) ∧
        (∀ θ j, ‖(p θ : E) * e j - e j * (p θ : E)‖ < ε) ∧
        ∀ θ φ, ‖(p θ : E) - p φ‖ ≤ 16 * |θ - φ| + ε := by
  let γ := ε / 8
  have hγ : 0 < γ := by dsimp only [γ]; positivity
  obtain ⟨δ, hδ, hpolar⟩ := exists_clockCorrected_unitary_path (E := E) γ hγ
  let η := min (δ / ((n : ℝ) + 2)) (ε / (160 * ((n : ℝ) + 1)))
  have hη : 0 < η := by dsimp only [η]; positivity
  have hcδ : ((n : ℝ) + 2) * η ≤ δ := by
    have h := min_le_left (δ / ((n : ℝ) + 2)) (ε / (160 * ((n : ℝ) + 1)))
    change η ≤ δ / ((n : ℝ) + 2) at h
    calc
      ((n : ℝ) + 2) * η = η * ((n : ℝ) + 2) := mul_comm _ _
      _ ≤ δ := (le_div_iff₀ (by positivity)).mp h
  have htε : 40 * ((n : ℝ) + 1) * η ≤ ε / 4 := by
    have h := min_le_right (δ / ((n : ℝ) + 2)) (ε / (160 * ((n : ℝ) + 1)))
    change η ≤ ε / (160 * ((n : ℝ) + 1)) at h
    have hh := (le_div_iff₀ (show 0 < 160 * ((n : ℝ) + 1) by positivity)).mp h
    nlinarith
  have hηε : η < ε := by
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hη.le]
  obtain ⟨K, e, hK, hKN, he, hesum, heo, hcycle, hKshift, hKgen, hKt,
      _hKfixed, hS, hT, hVcell, hVK⟩ :=
    exists_joint_binary_clock s t hs ht hsum htsum hcomm m η hη
  let k : unitary E := ⟨K, hK⟩
  let u := binaryRowCocycleUnitary s t hs ht hsum htsum n
  have hsn (i : Fin 2) : ‖s i‖ ≤ 1 :=
    clocked_isometry_norm _ (by simpa only [ite_true] using hs i i)
  have hgen (i : Fin 2) : ‖s i * K - K * s i‖ ≤ η := by
    rw [norm_sub_rev]
    exact (hKgen i).le
  have hprod (i r : Fin 2) : ‖(s i * s r) * K - K * (s i * s r)‖ ≤ 2 * η := by
    have hid : (s i * s r) * K - K * (s i * s r) =
        s i * (s r * K - K * s r) + (s i * K - K * s i) * s r := by noncomm_ring
    rw [hid]
    calc
      _ ≤ ‖s i * (s r * K - K * s r)‖ + ‖(s i * K - K * s i) * s r‖ := norm_add_le _ _
      _ ≤ ‖s i‖ * ‖s r * K - K * s r‖ + ‖s i * K - K * s i‖ * ‖s r‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ 1 * η + η * 1 := add_le_add
        (mul_le_mul (hsn i) (hgen r) (norm_nonneg _) (by norm_num))
        (mul_le_mul (hgen i) (hsn r) (norm_nonneg _) hη.le)
      _ = _ := by ring
  refine ⟨k, e, hKN, he, hesum, heo, hcycle, hKshift.trans hηε,
    (fun j => (hS j).trans hηε), (fun j => (hT j).trans hηε), ?_⟩
  intro i r l hil
  have haa : star (s i * s r) * (s i * s r) = 1 :=
    binaryProduct_isometry _ _ (by simpa only [ite_true] using hs i i)
      (by simpa only [ite_true] using hs r r)
  have hbb : star (s l) * s l = 1 := by simpa only [ite_true] using hs l l
  have hab : star (s i * s r) * s l = 0 := by
    rw [star_mul, mul_assoc, hs i l, ite_eq_right hil, mul_zero]
  have hca : ‖(s i * s r) * (k : E) - (k : E) * (s i * s r)‖ ≤ δ :=
    (hprod i r).trans (by nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hη.le])
  have hcb : ‖s l * (k : E) - (k : E) * s l‖ ≤ δ :=
    (hgen l).trans (by nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hη.le])
  have hcu : ‖(u : E) * (k : E) - (k : E) * (u : E)‖ ≤ δ :=
    (hVK n).trans (by nlinarith)
  obtain ⟨p, hp, hp0, hp1, hpjoin, hpnear⟩ :=
    hpolar k (s i * s r) (s l) u haa hbb hab u.prop hca hcb hcu
  let β := 2 * ((n : ℝ) + 1) * η
  have hβ : 0 ≤ β := by dsimp only [β]; positivity
  have hA (j : ZMod (2 ^ m)) : ‖(s i * s r) * e j - e (j + 2) * (s i * s r)‖ ≤ β :=
    (cyclic_row_two_letter_transport s hs e η (fun q => (hS q).le) i r j).trans (by
      dsimp only [β]
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hη.le])
  have hB (j : ZMod (2 ^ m)) : ‖s l * e j - e (j + 1) * s l‖ ≤ β :=
    (cyclic_row_generator_transport s hs e η (fun q => (hS q).le) l j).trans (by
      dsimp only [β]
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hη.le])
  have hU (j : ZMod (2 ^ m)) : ‖(u : E) * e j - e j * (u : E)‖ ≤ β :=
    (hVcell j n).trans (by dsimp only [β]; nlinarith)
  refine ⟨p, hp, hp0, hp1, hpjoin, ?_, ?_⟩
  · intro θ j
    have hz := clockCorrectedCancellation_cell_commutator k e
      (fun q => (he q).isSelfAdjoint.star_eq) hcycle (s i * s r) (s l) u
      haa hbb β hβ hA hB hU θ j
    have hnear := clocked_near_commutator (p θ : E)
      (clockCorrectedCancellation k (s i * s r) (s l) u θ) (e j) (he j).norm_le
    have hsmall : 20 * β ≤ ε / 4 := by dsimp only [β]; nlinarith [htε]
    have hn := hpnear θ
    change ‖(p θ : E) - clockCorrectedCancellation k (s i * s r) (s l) u θ‖ < γ at hn
    dsimp only [γ] at hn
    nlinarith
  · intro θ φ
    have hsample := clockCorrected_near_path_sample_bound k (s i * s r) (s l) u haa hbb u.prop
      p γ (fun q => (hpnear q).le) θ φ
    dsimp only [γ] at hsample
    linarith

end WeakPureInfiniteness

end

end OAI
