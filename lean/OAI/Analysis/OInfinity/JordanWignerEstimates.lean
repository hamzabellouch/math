import OAI.Analysis.OInfinity.RohlinPartitions

namespace OAI

/-! # Quantitative stability of the finite Jordan–Wigner construction

The occupation parity is Lipschitz on normalized modes. Telescoping the
finite parity prefixes gives the explicit `(4k + 1)δ` estimate, while scalar
phases pass exactly through the construction. These estimates do not assert
a unitary cocycle or a bound on its exponential length.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

lemma carNormalizedMode_norm_le_one (q a : E) (hqa : q * a = a) (haa : a * a = 0)
    (hgram : star a * a + a * star a = q) : ‖a‖ ≤ 1 := by
  have h := squareZero_norm_sq_le a q 1 (by norm_num) haa hqa (by simpa using hgram)
  nlinarith [norm_nonneg a]

lemma carSelfAdjointSquare_norm_le_one (q x : E) (hqnorm : ‖q‖ ≤ 1)
    (hxstar : star x = x) (hxx : x * x = q) : ‖x‖ ≤ 1 := by
  have h : ‖star x * x‖ = ‖x‖ * ‖x‖ := CStarRing.norm_star_mul_self
  rw [hxstar, hxx] at h
  nlinarith [norm_nonneg x]

lemma carOccupation_sub_norm_le (a b : E) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖star a * a - star b * b‖ ≤ 2 * ‖a - b‖ := by
  have he : star a * a - star b * b = star a * (a - b) + (star a - star b) * b := by
    noncomm_ring
  rw [he]
  calc
    _ ≤ ‖star a * (a - b)‖ + ‖(star a - star b) * b‖ := norm_add_le _ _
    _ ≤ ‖star a‖ * ‖a - b‖ + ‖star a - star b‖ * ‖b‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = ‖a‖ * ‖a - b‖ + ‖a - b‖ * ‖b‖ := by rw [norm_star, ← star_sub, norm_star]
    _ ≤ 1 * ‖a - b‖ + ‖a - b‖ * 1 := by gcongr
    _ = _ := by ring

lemma carModeParity_sub_norm_le (q a b : E) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖carModeParity q a - carModeParity q b‖ ≤ 4 * ‖a - b‖ := by
  have he : carModeParity q a - carModeParity q b =
      -((star a * a - star b * b) + (star a * a - star b * b)) := by
    unfold carModeParity
    abel
  rw [he, norm_neg]
  have h := carOccupation_sub_norm_le a b ha hb
  exact (norm_add_le _ _).trans (by linarith)

lemma carParityPrefix_norm_le_one (q : E) (c : ℕ → E) (hq : ‖q‖ ≤ 1)
    (hp : ∀ i, ‖carModeParity q (c i)‖ ≤ 1) (k : ℕ) : ‖carParityPrefix q c k‖ ≤ 1 := by
  induction k with
  | zero => exact hq
  | succ k ih =>
    change ‖carParityPrefix q c k * carModeParity q (c k)‖ ≤ 1
    exact (norm_mul_le _ _).trans (by
      nlinarith [hp k, norm_nonneg (carParityPrefix q c k),
        norm_nonneg (carModeParity q (c k))])

lemma carParityPrefix_sub_norm_le (q : E) (c d : ℕ → E) (hq : ‖q‖ ≤ 1)
    (hc : ∀ i, ‖c i‖ ≤ 1) (hd : ∀ i, ‖d i‖ ≤ 1)
    (hpc : ∀ i, ‖carModeParity q (c i)‖ ≤ 1)
    (hpd : ∀ i, ‖carModeParity q (d i)‖ ≤ 1)
    (δ : ℝ) (hδ : 0 ≤ δ) (hcd : ∀ i, ‖c i - d i‖ ≤ δ) (k : ℕ) :
    ‖carParityPrefix q c k - carParityPrefix q d k‖ ≤ 4 * (k : ℝ) * δ := by
  induction k with
  | zero => simpa only [carParityPrefix, sub_self, norm_zero, Nat.cast_zero, mul_zero, zero_mul]
      using (le_refl (0 : ℝ))
  | succ k ih =>
    have hp := (carModeParity_sub_norm_le q (c k) (d k) (hc k) (hd k)).trans
      (mul_le_mul_of_nonneg_left (hcd k) (by norm_num : (0 : ℝ) ≤ 4))
    have hprefix := carParityPrefix_norm_le_one q d hq hpd k
    have he : carParityPrefix q c (k + 1) - carParityPrefix q d (k + 1) =
        (carParityPrefix q c k - carParityPrefix q d k) * carModeParity q (c k) +
          carParityPrefix q d k * (carModeParity q (c k) - carModeParity q (d k)) := by
      simp only [carParityPrefix]
      noncomm_ring
    rw [he]
    calc
      _ ≤ ‖(carParityPrefix q c k - carParityPrefix q d k) * carModeParity q (c k)‖ +
          ‖carParityPrefix q d k * (carModeParity q (c k) - carModeParity q (d k))‖ := norm_add_le _ _
      _ ≤ ‖carParityPrefix q c k - carParityPrefix q d k‖ * ‖carModeParity q (c k)‖ +
          ‖carParityPrefix q d k‖ * ‖carModeParity q (c k) - carModeParity q (d k)‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ (4 * (k : ℝ) * δ) * 1 + 1 * (4 * δ) := by
        gcongr
        exact hpc k
      _ = _ := by push_cast; ring

lemma carJordanWigner_sub_norm_le (q : E) (c d : ℕ → E) (hq : ‖q‖ ≤ 1)
    (hc : ∀ i, ‖c i‖ ≤ 1) (hd : ∀ i, ‖d i‖ ≤ 1)
    (hpc : ∀ i, ‖carModeParity q (c i)‖ ≤ 1)
    (hpd : ∀ i, ‖carModeParity q (d i)‖ ≤ 1)
    (δ : ℝ) (hδ : 0 ≤ δ) (hcd : ∀ i, ‖c i - d i‖ ≤ δ) (k : ℕ) :
    ‖carJordanWigner q c k - carJordanWigner q d k‖ ≤ (4 * (k : ℝ) + 1) * δ := by
  have hprefix := carParityPrefix_sub_norm_le q c d hq hc hd hpc hpd δ hδ hcd k
  have hdnorm := carParityPrefix_norm_le_one q d hq hpd k
  have he : carJordanWigner q c k - carJordanWigner q d k =
      (carParityPrefix q c k - carParityPrefix q d k) * c k +
        carParityPrefix q d k * (c k - d k) := by
    unfold carJordanWigner
    noncomm_ring
  rw [he]
  calc
    _ ≤ ‖(carParityPrefix q c k - carParityPrefix q d k) * c k‖ +
        ‖carParityPrefix q d k * (c k - d k)‖ := norm_add_le _ _
    _ ≤ ‖carParityPrefix q c k - carParityPrefix q d k‖ * ‖c k‖ +
        ‖carParityPrefix q d k‖ * ‖c k - d k‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ ((4 * (k : ℝ)) * δ) * 1 + 1 * δ := by
      gcongr
      · exact hc k
      · exact hcd k
    _ = _ := by ring

lemma carModeParity_smul (q a : E) (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    carModeParity q (ζ • a) = carModeParity q a := by
  have hc : star ζ * ζ = (1 : ℂ) := by
    simpa [Complex.star_def, hζ] using Complex.conj_mul' ζ
  have hc' : ζ * star ζ = (1 : ℂ) := by rw [mul_comm, hc]
  simp only [carModeParity, star_smul, smul_mul_assoc, mul_smul_comm,
    smul_smul, hc', one_smul]

lemma carParityPrefix_smul (q : E) (c : ℕ → E) (ζ : ℕ → ℂ)
    (hζ : ∀ i, ‖ζ i‖ = 1) (k : ℕ) :
    carParityPrefix q (fun i => ζ i • c i) k = carParityPrefix q c k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change carParityPrefix q (fun i => ζ i • c i) k * carModeParity q (ζ k • c k) = _
    rw [ih, carModeParity_smul q (c k) (ζ k) (hζ k)]
    rfl

lemma carJordanWigner_smul (q : E) (c : ℕ → E) (ζ : ℕ → ℂ)
    (hζ : ∀ i, ‖ζ i‖ = 1) (k : ℕ) :
    carJordanWigner q (fun i => ζ i • c i) k = ζ k • carJordanWigner q c k := by
  unfold carJordanWigner
  rw [carParityPrefix_smul q c ζ hζ, mul_smul_comm]

variable {n : ℕ}

lemma evenRowShift_sub (r : Fin 2 × Fin n → E) (x y : E) :
    evenRowShift r (x - y) = evenRowShift r x - evenRowShift r y := by
  simp only [evenRowShift, mul_sub, sub_mul, Finset.sum_sub_distrib]

lemma evenRowShift_carModeParity (q : E) (r : Fin 2 × Fin n → E)
    (hqstar : star q = q) (hqq : q * q = q)
    (hrow : ∀ i j, star (r i) * r j = if i = j then q else 0)
    (hsum : (∑ i, r i * star (r i)) = q) (x : E) (hqx : q * x = x) :
    evenRowShift r (carModeParity q x) = carModeParity q (evenRowShift r x) := by
  simp only [carModeParity, evenRowShift_sub, evenRowShift_add,
    evenRowShift_unit q r hqstar hqq hrow hsum]
  rw [← evenRowShift_mul q r hrow _ _ hqx, ← evenRowShift_star]

lemma evenRowShift_carParityPrefix (q : E) (r : Fin 2 × Fin n → E)
    (hqstar : star q = q) (hqq : q * q = q)
    (hrow : ∀ i j, star (r i) * r j = if i = j then q else 0)
    (hsum : (∑ i, r i * star (r i)) = q) (c : ℕ → E)
    (hl : ∀ i, q * c i = c i) (hr : ∀ i, c i * q = c i)
    (ha : ∀ i j, c i * c j + c j * c i = 0)
    (hg : ∀ i j, star (c i) * c j + c j * star (c i) = if i = j then q else 0)
    (k : ℕ) :
    evenRowShift r (carParityPrefix q c k) = carParityPrefix q (fun i => evenRowShift r (c i)) k := by
  induction k with
  | zero => exact evenRowShift_unit q r hqstar hqq hrow hsum
  | succ k ih =>
    change evenRowShift r (carParityPrefix q c k * carModeParity q (c k)) = _
    rw [← evenRowShift_mul q r hrow _ _
      (carFamily_parity_properties q c hqstar hqq hl hr ha hg k).2.2.1,
      ih, evenRowShift_carModeParity q r hqstar hqq hrow hsum _ (hl k)]
    rfl

lemma evenRowShift_carJordanWigner (q : E) (r : Fin 2 × Fin n → E)
    (hqstar : star q = q) (hqq : q * q = q)
    (hrow : ∀ i j, star (r i) * r j = if i = j then q else 0)
    (hsum : (∑ i, r i * star (r i)) = q) (c : ℕ → E)
    (hl : ∀ i, q * c i = c i) (hr : ∀ i, c i * q = c i)
    (ha : ∀ i j, c i * c j + c j * c i = 0)
    (hg : ∀ i j, star (c i) * c j + c j * star (c i) = if i = j then q else 0)
    (k : ℕ) :
    evenRowShift r (carJordanWigner q c k) = carJordanWigner q (fun i => evenRowShift r (c i)) k := by
  unfold carJordanWigner
  rw [← evenRowShift_mul q r hrow _ _ (hl k),
    evenRowShift_carParityPrefix q r hqstar hqq hrow hsum c hl hr ha hg k]

lemma evenRowShift_normalizedMode (q : E) (r : Fin 2 × Fin n → E)
    (hqstar : star q = q) (hqq : q * q = q)
    (hrow : ∀ i j, star (r i) * r j = if i = j then q else 0)
    (hsum : (∑ i, r i * star (r i)) = q)
    (x : E) (hqx : q * x = x) (hxq : x * q = x) (hxx : x * x = 0)
    (hgram : star x * x + x * star x = q) :
    (q * evenRowShift r x = evenRowShift r x) ∧
    (evenRowShift r x * q = evenRowShift r x) ∧
    (evenRowShift r x * evenRowShift r x = 0) ∧
    (star (evenRowShift r x) * evenRowShift r x +
      evenRowShift r x * star (evenRowShift r x) = q) := by
  obtain ⟨hl, hr⟩ := evenRowShift_support q r hqstar hqq hrow hsum x
  have hqx' : q * star x = star x := by
    simpa only [star_mul, hqstar] using congrArg star hxq
  refine ⟨hl, hr, ?_, ?_⟩
  · rw [evenRowShift_mul q r hrow _ _ hqx, hxx, evenRowShift_zero]
  · rw [evenRowShift_star, evenRowShift_mul q r hrow _ _ hqx,
      evenRowShift_mul q r hrow _ _ hqx', ← evenRowShift_add, hgram,
      evenRowShift_unit q r hqstar hqq hrow hsum]

lemma evenRohlinCoordinate_shift_error (q : E) (r : Fin 2 × Fin n → E)
    (hqstar : star q = q) (hqq : q * q = q)
    (hrow : ∀ i j, star (r i) * r j = if i = j then q else 0)
    (hsum : (∑ i, r i * star (r i)) = q) (L : ℕ) (hL : 0 < L) (i : ℕ) :
    ‖evenRowShift r (evenRohlinCoordinate q r L i) -
      carDyadicPhase i • evenRohlinCoordinate q r L i‖ ≤
        (4 * (i : ℝ) + 1) * Real.sqrt (18 / (L : ℝ)) := by
  let c : ℕ → E := evenBlockFamily r L carDyadicPhase
  let d : ℕ → E := fun j => evenRowShift r (c j)
  let e : ℕ → E := fun j => carDyadicPhase j • c j
  let δ : ℝ := Real.sqrt (18 / (L : ℝ))
  obtain ⟨hl, hr, ha, hg⟩ := evenBlockFamily_CAR q r hqstar hqq hrow hsum
    L hL carDyadicPhase carDyadicPhase_norm
  have hqnorm : ‖q‖ ≤ 1 := IsStarProjection.norm_le q ⟨hqq, hqstar⟩
  have hczero (j : ℕ) : c j * c j = 0 := carFamily_square_zero c ha j
  have hcgram (j : ℕ) : star (c j) * c j + c j * star (c j) = q := by
    simpa only [ite_true] using hg j j
  have hcnorm (j : ℕ) : ‖c j‖ ≤ 1 :=
    carNormalizedMode_norm_le_one q (c j) (hl j) (hczero j) (hcgram j)
  have hcpnorm (j : ℕ) : ‖carModeParity q (c j)‖ ≤ 1 := by
    have hp := carModeParity_properties q (c j) hqstar hqq (hl j) (hr j) (hczero j) (hcgram j)
    exact carSelfAdjointSquare_norm_le_one q _ hqnorm hp.1 hp.2.1
  have hdprops (j : ℕ) := evenRowShift_normalizedMode q r hqstar hqq hrow hsum
    (c j) (hl j) (hr j) (hczero j) (hcgram j)
  have hdnorm (j : ℕ) : ‖d j‖ ≤ 1 :=
    carNormalizedMode_norm_le_one q (d j) (hdprops j).1 (hdprops j).2.2.1 (hdprops j).2.2.2
  have hdpnorm (j : ℕ) : ‖carModeParity q (d j)‖ ≤ 1 := by
    have hp := carModeParity_properties q (d j) hqstar hqq
      (hdprops j).1 (hdprops j).2.1 (hdprops j).2.2.1 (hdprops j).2.2.2
    exact carSelfAdjointSquare_norm_le_one q _ hqnorm hp.1 hp.2.1
  have henorm (j : ℕ) : ‖e j‖ ≤ 1 := by
    change ‖carDyadicPhase j • c j‖ ≤ 1
    rw [norm_smul, carDyadicPhase_norm, one_mul]
    exact hcnorm j
  have hepnorm (j : ℕ) : ‖carModeParity q (e j)‖ ≤ 1 := by
    change ‖carModeParity q (carDyadicPhase j • c j)‖ ≤ 1
    rw [carModeParity_smul q _ _ (carDyadicPhase_norm j)]
    exact hcpnorm j
  have hde (j : ℕ) : ‖d j - e j‖ ≤ δ := by
    have h := evenRohlinBlock_shift_error q r hqstar hqq hrow hsum L hL j
    change ‖d j - e j‖ ^ 2 ≤ 18 / (L : ℝ) at h
    have hsq := Real.sq_sqrt (show 0 ≤ 18 / (L : ℝ) by positivity)
    change δ ^ 2 = 18 / (L : ℝ) at hsq
    nlinarith [norm_nonneg (d j - e j), Real.sqrt_nonneg (18 / (L : ℝ))]
  have h := carJordanWigner_sub_norm_le q d e hqnorm hdnorm henorm hdpnorm hepnorm
    δ (Real.sqrt_nonneg _) hde i
  dsimp only [d, e] at h
  rw [← evenRowShift_carJordanWigner q r hqstar hqq hrow hsum c hl hr ha hg i,
    carJordanWigner_smul q c carDyadicPhase carDyadicPhase_norm i] at h
  exact h

end WeakPureInfiniteness

end

end OAI
