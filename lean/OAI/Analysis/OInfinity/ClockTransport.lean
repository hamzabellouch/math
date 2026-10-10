import OAI.Analysis.OInfinity.MaskedShift

namespace OAI

/-! # A finite clock for the actual CAR partition

The clock is the finite product of the occupation phase unitaries of the
commuting Jordan–Wigner coordinates. It has exact dyadic order and cycles
the corresponding partition. Its row commutators are controlled by the
proved coordinate shift errors, independently of any cocycle equation.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

/-- The two occupation projections receive phases one and `ζ`. -/
def carClockFactor (a : E) (ζ : ℂ) : E := star a * a + ζ • (a * star a)

private lemma clock_occupation (a : E) (hz : a * a = 0)
    (hg : star a * a + a * star a = 1) :
    (star a * a) * (star a * a) = star a * a ∧
      (a * star a) * (a * star a) = a * star a ∧
      (star a * a) * (a * star a) = 0 ∧
      (a * star a) * (star a * a) = 0 ∧
      a * (star a * a) = a ∧ (a * star a) * a = a := by
  have hza : star a * star a = 0 := by
    simpa only [star_mul, star_zero] using congrArg star hz
  have ha : a * (star a * a) = a := by
    have h := congrArg (fun x : E => a * x) hg
    simpa only [mul_add, ← mul_assoc, hz, zero_mul, add_zero, mul_one] using h
  refine ⟨?_, ?_, ?_, ?_, ha, ?_⟩
  · rw [mul_assoc, ha]
  · calc
      (a * star a) * (a * star a) = (a * (star a * a)) * star a := by noncomm_ring
      _ = a * star a := by rw [ha]
  · calc
      (star a * a) * (a * star a) = star a * (a * a) * star a := by noncomm_ring
      _ = 0 := by rw [hz, mul_zero, zero_mul]
  · calc
      _ = a * (star a * star a) * a := by noncomm_ring
      _ = 0 := by rw [hza, mul_zero, zero_mul]
  · simpa only [mul_assoc] using ha

lemma carClockFactor_mem_unitary (a : E) (hz : a * a = 0)
    (hg : star a * a + a * star a = 1) (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    carClockFactor a ζ ∈ unitary E := by
  obtain ⟨hpp, hqq, hpq, hqp, _, _⟩ := clock_occupation a hz hg
  have hscalar : star ζ * ζ = (1 : ℂ) := by
    simpa [Complex.star_def, hζ] using Complex.conj_mul' ζ
  have hscalar' : ζ * star ζ = (1 : ℂ) := by rw [mul_comm, hscalar]
  constructor <;>
    simp only [carClockFactor, star_add, star_mul, star_smul, star_star,
      add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
      hpp, hqq, hpq, hqp, smul_zero, add_zero, zero_add, hscalar, hscalar', one_smul, hg]

lemma carClockFactor_mul_mode (a : E) (hz : a * a = 0)
    (hg : star a * a + a * star a = 1) (ζ : ℂ) :
    carClockFactor a ζ * a = ζ • a ∧ a * carClockFactor a ζ = a := by
  obtain ⟨_, _, _, _, ha, ha'⟩ := clock_occupation a hz hg
  constructor
  · have hz' : (star a * a) * a = 0 := by rw [mul_assoc, hz, mul_zero]
    rw [carClockFactor, add_mul, smul_mul_assoc, hz', ha', zero_add]
  · have hz' : a * (a * star a) = 0 := by rw [← mul_assoc, hz, zero_mul]
    rw [carClockFactor, mul_add, mul_smul_comm, ha, hz', smul_zero, add_zero]

lemma carClockFactor_commute_mode (a b : E) (hab : Commute a b)
    (hsab : Commute (star a) b) (ζ : ℂ) : Commute (carClockFactor a ζ) b :=
  (hsab.mul_left hab).add_left ((hab.mul_left hsab).smul_left ζ)

lemma carClockFactor_commute (a b : E) (hab : Commute a b)
    (hsab : Commute (star a) b) (ζ μ : ℂ) :
    Commute (carClockFactor a ζ) (carClockFactor b μ) := by
  have h := carClockFactor_commute_mode a b hab hsab ζ
  have hs := carClockFactor_commute_mode a (star b) (by
    simpa only [star_star] using hsab.star_star) hab.star_star ζ
  exact (hs.mul_right h).add_right ((h.mul_right hs).smul_right μ)

lemma carClockFactor_pow (a : E) (hz : a * a = 0)
    (hg : star a * a + a * star a = 1) (ζ : ℂ) (N : ℕ) :
    carClockFactor a ζ ^ N = star a * a + (ζ ^ N) • (a * star a) := by
  obtain ⟨hpp, hqq, hpq, hqp, _, _⟩ := clock_occupation a hz hg
  induction N with
  | zero => simpa only [pow_zero, one_smul] using hg.symm
  | succ N ih =>
      rw [pow_succ, ih]
      simp only [carClockFactor, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
        smul_smul, hpp, hqq, hpq, hqp, smul_zero, add_zero, zero_add, pow_succ]
      rw [mul_comm ζ (ζ ^ N)]

/-- Ordered finite product of the commuting occupation clocks. -/
def carClock (a : ℕ → E) (ζ : ℕ → ℂ) : ℕ → E
  | 0 => 1
  | m + 1 => carClock a ζ m * carClockFactor (a m) (ζ m)

section Coordinates
variable (a : ℕ → E) (ζ : ℕ → ℂ)
  (hz : ∀ i, a i * a i = 0)
  (hg : ∀ i, star (a i) * a i + a i * star (a i) = 1)
  (hc : ∀ i j, Commute (a i) (a j))
  (hsc : ∀ i j, i ≠ j → Commute (star (a i)) (a j))
  (hζ : ∀ i, ‖ζ i‖ = 1)

include hz hg hζ in
lemma carClock_mem_unitary (m : ℕ) : carClock a ζ m ∈ unitary E := by
  induction m with
  | zero => exact (unitary E).one_mem
  | succ m ih =>
      exact (unitary E).mul_mem ih
        (carClockFactor_mem_unitary (a m) (hz m) (hg m) (ζ m) (hζ m))

include hc hsc in
lemma carClock_commute_factor (m j : ℕ) :
    Commute (carClock a ζ m) (carClockFactor (a j) (ζ j)) := by
  induction m with
  | zero => exact Commute.one_left _
  | succ m ih =>
      apply ih.mul_left
      by_cases hm : m = j
      · subst j; exact Commute.refl _
      · exact carClockFactor_commute _ _ (hc m j) (hsc m j hm) _ _

include hz hg hc hsc in
lemma carClock_pow_eq_one (m N : ℕ) (hp : ∀ i, i < m → ζ i ^ N = 1) :
    carClock a ζ m ^ N = 1 := by
  induction m with
  | zero => simp only [carClock, one_pow]
  | succ m ih =>
      rw [carClock, (carClock_commute_factor a ζ hc hsc m m).mul_pow,
        ih (fun i hi => hp i (by omega)), one_mul,
        carClockFactor_pow (a m) (hz m) (hg m), hp m (by omega), one_smul, hg m]

include hc hsc in
lemma carClock_commute_later_mode (m j : ℕ) (hmj : m ≤ j) :
    Commute (carClock a ζ m) (a j) := by
  induction m with
  | zero => exact Commute.one_left _
  | succ m ih =>
      exact (ih (by omega)).mul_left
        (carClockFactor_commute_mode _ _ (hc m j) (hsc m j (by omega)) _)

include hz hg hc hsc in
lemma carClock_mul_mode (m i : ℕ) (him : i < m) :
    carClock a ζ m * a i = ζ i • (a i * carClock a ζ m) := by
  induction m with
  | zero => omega
  | succ m ih =>
      by_cases him' : i = m
      · subst i
        obtain ⟨hl, hr⟩ := carClockFactor_mul_mode (a m) (hz m) (hg m) (ζ m)
        have hprev := carClock_commute_later_mode a ζ hc hsc m m le_rfl
        change (carClock a ζ m * carClockFactor (a m) (ζ m)) * a m = _
        rw [mul_assoc, hl, mul_smul_comm, hprev.eq]
        rw [show a m * carClock a ζ (m + 1) = a m * carClock a ζ m by
          calc
            _ = (a m * carClock a ζ m) * carClockFactor (a m) (ζ m) := by
              rw [carClock, ← mul_assoc]
            _ = carClock a ζ m * (a m * carClockFactor (a m) (ζ m)) := by
              rw [← hprev.eq, mul_assoc]
            _ = a m * carClock a ζ m := by rw [hr, hprev.eq]]
      · have hfac := carClockFactor_commute_mode (a m) (a i) (hc m i)
          (hsc m i (Ne.symm him')) (ζ m)
        change (carClock a ζ m * carClockFactor (a m) (ζ m)) * a i = _
        rw [mul_assoc, hfac.eq, ← mul_assoc, ih (by omega), smul_mul_assoc]
        simp only [carClock, mul_assoc]

include hz hg hc hsc hζ in
lemma carClock_conjugate_mode (m i : ℕ) (him : i < m) :
    carClock a ζ m * a i * star (carClock a ζ m) = ζ i • a i := by
  rw [carClock_mul_mode a ζ hz hg hc hsc m i him, smul_mul_assoc,
    mul_assoc, (carClock_mem_unitary a ζ hz hg hζ m).2, mul_one]

end Coordinates

private lemma clock_unitary_norm (u : E) (hu : u ∈ unitary E) : ‖u‖ ≤ 1 := by
  have h := congrArg norm hu.1
  rw [CStarRing.norm_star_mul_self] at h
  have h1 : ‖(1 : E)‖ ≤ 1 := IsStarProjection.norm_le 1
    (isStarProjection_iff'.mpr ⟨by simp, by simp⟩)
  nlinarith [norm_nonneg u]

lemma carClock_conjugate_spin (u a : E) (hu : u ∈ unitary E)
    (ζ μ : ℂ) (ha : u * a * star u = μ • a) :
    u * carSpinProjection 1 a ζ * star u = carSpinProjection 1 a (ζ * μ) := by
  have hsa : u * star a * star u = star μ • star a := by
    simpa only [star_mul, star_smul, star_star, mul_assoc] using congrArg star ha
  have he (x y : E) : u * (x + y) * star u =
      u * x * star u + u * y * star u := by noncomm_ring
  simp only [carSpinProjection, carSpinAxis, mul_smul_comm, smul_mul_assoc, he,
    mul_one, hu.2, ha, hsa, smul_smul, star_mul]
  rw [mul_comm (star μ) (star ζ)]

lemma carClock_conjugate_dyadic (a : ℕ → E) (ζ : ℕ → ℂ)
    (hz : ∀ i, a i * a i = 0)
    (hg : ∀ i, star (a i) * a i + a i * star (a i) = 1)
    (hc : ∀ i j, Commute (a i) (a j))
    (hsc : ∀ i j, i ≠ j → Commute (star (a i)) (a j))
    (hζ : ∀ i, ‖ζ i‖ = 1) (m k : ℕ) :
    carClock a ζ m * dyadicSpinProjection 1 a ζ m k * star (carClock a ζ m) =
      dyadicSpinProjection 1 a ζ m (k + 1) := by
  have hu := carClock_mem_unitary a ζ hz hg hζ m
  have hind (l : ℕ) (hlm : l ≤ m) :
      carClock a ζ m * dyadicSpinProjection 1 a ζ l k * star (carClock a ζ m) =
        dyadicSpinProjection 1 a ζ l (k + 1) := by
    induction l with
    | zero => simpa only [dyadicSpinProjection, mul_one] using hu.2
    | succ l ih =>
        change carClock a ζ m * (dyadicSpinProjection 1 a ζ l k *
          carSpinProjection 1 (a l) (ζ l ^ k)) * star (carClock a ζ m) = _
        have he (x y : E) : carClock a ζ m * (x * y) * star (carClock a ζ m) =
            (carClock a ζ m * x * star (carClock a ζ m)) *
              (carClock a ζ m * y * star (carClock a ζ m)) := by
          calc
            _ = carClock a ζ m * x * (star (carClock a ζ m) * carClock a ζ m) *
                y * star (carClock a ζ m) := by rw [hu.1, mul_one]; noncomm_ring
            _ = _ := by noncomm_ring
        rw [he, ih (by omega), carClock_conjugate_spin _ _ hu _ _
          (carClock_conjugate_mode a ζ hz hg hc hsc hζ m l (by omega)), ← pow_succ]
        rfl
  exact hind m le_rfl

lemma carClockFactor_smul (a : E) (ζ μ : ℂ) (hμ : ‖μ‖ = 1) :
    carClockFactor (μ • a) ζ = carClockFactor a ζ := by
  have h : star μ * μ = (1 : ℂ) := by
    simpa [Complex.star_def, hμ] using Complex.conj_mul' μ
  have h' : μ * star μ = (1 : ℂ) := by rw [mul_comm, h]
  simp only [carClockFactor, star_smul, smul_mul_assoc, mul_smul_comm,
    smul_smul, h, h', one_smul]

lemma carClockFactor_sub_norm (a b : E) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    ‖carClockFactor a ζ - carClockFactor b ζ‖ ≤ 4 * ‖a - b‖ := by
  have he : carClockFactor a ζ - carClockFactor b ζ =
      (star a * a - star b * b) + ζ • (a * star a - b * star b) := by
    simp only [carClockFactor, smul_sub]; abel
  have hp := carOccupation_sub_norm_le a b ha hb
  have hq := carOccupation_sub_norm_le (star a) (star b)
    (by simpa only [norm_star] using ha) (by simpa only [norm_star] using hb)
  simp only [star_star, ← star_sub, norm_star] at hq
  rw [he]
  exact (norm_add_le _ _).trans (by rw [norm_smul, hζ, one_mul]; linarith)

lemma carClockFactor_map (α : E →⋆ₙₐ[ℂ] E) (a : E) (ζ : ℂ) :
    α (carClockFactor a ζ) = carClockFactor (α a) ζ := by
  simp only [carClockFactor, map_add, map_mul, map_star, map_smul]

lemma carClock_map_shift_bound (α : E →⋆ₙₐ[ℂ] E) (hα : α 1 = 1)
    (a : ℕ → E) (ζ : ℕ → ℂ)
    (hz : ∀ i, a i * a i = 0)
    (hg : ∀ i, star (a i) * a i + a i * star (a i) = 1)
    (hζ : ∀ i, ‖ζ i‖ = 1) (m : ℕ) :
    ‖α (carClock a ζ m) - carClock a ζ m‖ ≤
      4 * ∑ i ∈ Finset.range m, ‖α (a i) - ζ i • a i‖ := by
  have hfactor (i : ℕ) : ‖α (carClockFactor (a i) (ζ i)) - carClockFactor (a i) (ζ i)‖ ≤
      4 * ‖α (a i) - ζ i • a i‖ := by
    rw [carClockFactor_map, ← carClockFactor_smul (a i) (ζ i) (ζ i) (hζ i)]
    apply carClockFactor_sub_norm
    · exact (NonUnitalStarAlgHom.norm_apply_le α _).trans
        (carNormalizedMode_norm_le_one 1 (a i) (one_mul _) (hz i) (hg i))
    · rw [norm_smul, hζ i, one_mul]
      exact carNormalizedMode_norm_le_one 1 (a i) (one_mul _) (hz i) (hg i)
    · exact hζ i
  induction m with
  | zero => simp only [carClock, hα, sub_self, norm_zero, Finset.range_zero,
      Finset.sum_empty, mul_zero, le_refl]
  | succ m ih =>
      have hnorm := clock_unitary_norm _ (carClock_mem_unitary a ζ hz hg hζ m)
      have hfnorm := clock_unitary_norm _
        (carClockFactor_mem_unitary (a m) (hz m) (hg m) (ζ m) (hζ m))
      have he : α (carClock a ζ (m + 1)) - carClock a ζ (m + 1) =
          (α (carClock a ζ m) - carClock a ζ m) * α (carClockFactor (a m) (ζ m)) +
            carClock a ζ m * (α (carClockFactor (a m) (ζ m)) - carClockFactor (a m) (ζ m)) := by
        simp only [carClock, map_mul]; noncomm_ring
      rw [he]
      calc
        _ ≤ ‖(α (carClock a ζ m) - carClock a ζ m) * α (carClockFactor (a m) (ζ m))‖ +
            ‖carClock a ζ m * (α (carClockFactor (a m) (ζ m)) - carClockFactor (a m) (ζ m))‖ :=
          norm_add_le _ _
        _ ≤ ‖α (carClock a ζ m) - carClock a ζ m‖ *
            ‖α (carClockFactor (a m) (ζ m))‖ +
              ‖carClock a ζ m‖ * ‖α (carClockFactor (a m) (ζ m)) - carClockFactor (a m) (ζ m)‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
        _ ≤ (4 * ∑ i ∈ Finset.range m, ‖α (a i) - ζ i • a i‖) * 1 +
              1 * (4 * ‖α (a m) - ζ m • a m‖) := by
          gcongr
          exact (NonUnitalStarAlgHom.norm_apply_le α _).trans hfnorm
          exact hfactor m
        _ = _ := by rw [Finset.sum_range_succ]; ring

/-- The actual occupation clock for the supplied even row. -/
def evenRohlinClock {n : ℕ} (r : Fin 2 × Fin n → E) (L m : ℕ) : E :=
  carClock (evenRohlinCoordinate 1 r L) carDyadicPhase m

section Actual
variable {n : ℕ} (r : Fin 2 × Fin n → E)
  (hr : ∀ i j, star (r i) * r j = if i = j then 1 else 0)
  (hsum : (∑ i, r i * star (r i)) = 1) (L : ℕ) (hL : 0 < L)

include hr hsum hL in
lemma evenRohlinClock_mem_unitary (m : ℕ) : evenRohlinClock r L m ∈ unitary E := by
  obtain ⟨_, _, hz, hg, _, _⟩ := evenRohlinCoordinate_properties 1 r (star_one _) (one_mul _) hr hsum L hL
  exact carClock_mem_unitary _ _ hz hg carDyadicPhase_norm m

include hr hsum hL in
lemma evenRohlinClock_order (m : ℕ) : evenRohlinClock r L m ^ (2 ^ m) = 1 := by
  obtain ⟨_, _, hz, hg, hc, hsc⟩ := evenRohlinCoordinate_properties 1 r (star_one _) (one_mul _) hr hsum L hL
  exact carClock_pow_eq_one _ _ hz hg hc hsc m (2 ^ m)
    (fun i hi => dyadic_phase_period carDyadicPhase carDyadicPhase_half i m hi)

include hr hsum hL in
lemma evenRohlinClock_cycles (m k : ℕ) :
    evenRohlinClock r L m * evenRohlinProjection 1 r L m k * star (evenRohlinClock r L m) =
      evenRohlinProjection 1 r L m (k + 1) := by
  obtain ⟨_, _, hz, hg, hc, hsc⟩ := evenRohlinCoordinate_properties 1 r (star_one _) (one_mul _) hr hsum L hL
  exact carClock_conjugate_dyadic _ _ hz hg hc hsc carDyadicPhase_norm m k

include hr hsum hL in
lemma evenRohlinClock_shift_bound (m : ℕ) :
    ‖evenRowShift r (evenRohlinClock r L m) - evenRohlinClock r L m‖ ≤
      4 * (m : ℝ) * (4 * (m : ℝ) + 1) * Real.sqrt (18 / (L : ℝ)) := by
  obtain ⟨_, _, hz, hg, _, _⟩ := evenRohlinCoordinate_properties 1 r (star_one _) (one_mul _) hr hsum L hL
  have hα : finiteCuntzDiagonalHom r hr 1 = 1 := by
    change evenRowShift r 1 = 1
    exact evenRowShift_unit 1 r (star_one _) (one_mul _) hr hsum
  have he := carClock_map_shift_bound (finiteCuntzDiagonalHom r hr) hα
    (evenRohlinCoordinate 1 r L) carDyadicPhase hz hg carDyadicPhase_norm m
  change ‖evenRowShift r (evenRohlinClock r L m) - evenRohlinClock r L m‖ ≤ _ at he
  refine he.trans ?_
  have hterm (i : ℕ) (hi : i ∈ Finset.range m) :
      ‖evenRowShift r (evenRohlinCoordinate 1 r L i) -
        carDyadicPhase i • evenRohlinCoordinate 1 r L i‖ ≤
          (4 * (m : ℝ) + 1) * Real.sqrt (18 / (L : ℝ)) := by
    refine (evenRohlinCoordinate_shift_error 1 r (star_one _) (one_mul _) hr hsum L hL i).trans ?_
    have hi' : (i : ℝ) ≤ m := by exact_mod_cast (Nat.le_of_lt (Finset.mem_range.mp hi))
    gcongr
  calc
    _ ≤ 4 * ∑ _i ∈ Finset.range m,
        ((4 * (m : ℝ) + 1) * Real.sqrt (18 / (L : ℝ))) := by gcongr with i hi; exact hterm i hi
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

include hr hsum hL in
lemma evenRohlinClock_generator_commutator (m : ℕ) (i : Fin 2 × Fin n) :
    ‖evenRohlinClock r L m * r i - r i * evenRohlinClock r L m‖ ≤
      4 * (m : ℝ) * (4 * (m : ℝ) + 1) * Real.sqrt (18 / (L : ℝ)) := by
  have he : evenRohlinClock r L m * r i - r i * evenRohlinClock r L m =
      (evenRohlinClock r L m - evenRowShift r (evenRohlinClock r L m)) * r i := by
    rw [sub_mul]
    rw [show evenRowShift r (evenRohlinClock r L m) * r i =
      r i * evenRohlinClock r L m from
        finiteRowShift_mul_row 1 r hr _ (mul_one _) i]
  have hi : ‖r i‖ ≤ 1 := by
    have h := congrArg norm (hr i i)
    simp only [ite_true, CStarRing.norm_star_mul_self] at h
    have h1 : ‖(1 : E)‖ ≤ 1 := IsStarProjection.norm_le 1
      (isStarProjection_iff'.mpr ⟨by simp, by simp⟩)
    nlinarith [norm_nonneg (r i)]
  rw [he]
  exact (norm_mul_le _ _).trans ((mul_le_of_le_one_right (norm_nonneg _) hi).trans
    (by rw [norm_sub_rev]; exact evenRohlinClock_shift_bound r hr hsum L hL m))

end Actual
end WeakPureInfiniteness

end

end OAI
