import OAI.NumberTheory.PrimeGaps.DivisorBounds

namespace OAI

namespace LargePrimeGaps

open Filter

noncomputable def weightedMarkedError (n X H Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q,
    if Squarefree q then (((2 ^ n) ^ q.primeFactors.card : ℕ) : ℝ) *
      (markedError X H q : ℝ) else 0

theorem dyadic_theta_error_le_markedError_one (X H : ℕ) :
    |(∑ m ∈ Finset.Ioc X (2 * X), theta m) - (X : ℝ)| ≤
      (markedError X H 1 : ℝ) := by
  simpa only [residueStarts, Nat.mod_one, Finset.filter_true, Nat.add_zero, Nat.totient_one,
      Nat.cast_one, div_one] using
    (markedClassError_le (X := X) (H := H) (q := 1) (a := 0) (c := 0)
      (Nat.zero_le H) (by norm_num) (by simp))

theorem dyadic_theta_error_le_weightedMarkedError (n X H : ℕ) {Q : ℕ}
    (hQ : 1 ≤ Q) :
    |(∑ m ∈ Finset.Ioc X (2 * X), theta m) - (X : ℝ)| ≤
      weightedMarkedError n X H Q := by
  apply (dyadic_theta_error_le_markedError_one X H).trans
  have h1 : (1 : ℕ) ∈ Finset.Icc 1 Q := by simp [hQ]
  have h := Finset.single_le_sum (s := Finset.Icc 1 Q)
    (f := fun q => if Squarefree q then (((2 ^ n) ^ q.primeFactors.card : ℕ) : ℝ) *
      (markedError X H q : ℝ) else 0) (fun q _ => by split_ifs <;> positivity) h1
  simpa only [weightedMarkedError, squarefree_one, ite_true, Nat.primeFactors_one,
    Finset.card_empty, pow_zero, Nat.cast_one, one_mul] using h

open Set Filter MeasureTheory

open scoped Topology ContDiff

noncomputable def reciprocalBump (R : ℝ) (hR : 2 ≤ R) :
    ContDiffBump ((R + 1) / 2) where
  rIn := (R - 1) / 2
  rOut := R / 2
  rIn_pos := by linarith
  rIn_lt_rOut := by linarith

noncomputable def reciprocalProfile (R : ℝ) (hR : 2 ≤ R) (u : ℝ) : ℝ :=
  reciprocalBump R hR u / u

theorem reciprocalBump_eq_zero_left {R : ℝ} (hR : 2 ≤ R) {u : ℝ}
    (hu : u ≤ 1 / 2) : reciprocalBump R hR u = 0 := by
  apply ContDiffBump.zero_of_le_dist
  change R / 2 ≤ dist u ((R + 1) / 2)
  rw [Real.dist_eq, abs_of_nonpos (by linarith : u - (R + 1) / 2 ≤ 0)]
  linarith

theorem reciprocalBump_eq_zero_right {R : ℝ} (hR : 2 ≤ R) {u : ℝ}
    (hu : 2 * R ≤ u) : reciprocalBump R hR u = 0 := by
  apply ContDiffBump.zero_of_le_dist
  change R / 2 ≤ dist u ((R + 1) / 2)
  rw [Real.dist_eq, abs_of_nonneg (by linarith : 0 ≤ u - (R + 1) / 2)]
  linarith

theorem reciprocalProfile_zero_left {R : ℝ} (hR : 2 ≤ R) {u : ℝ}
    (hu : u ≤ 1 / 2) : reciprocalProfile R hR u = 0 := by
  simp [reciprocalProfile, reciprocalBump_eq_zero_left hR hu]

theorem reciprocalProfile_zero_right {R : ℝ} (hR : 2 ≤ R) {u : ℝ}
    (hu : 2 * R ≤ u) : reciprocalProfile R hR u = 0 := by
  simp [reciprocalProfile, reciprocalBump_eq_zero_right hR hu]

theorem reciprocalProfile_eq_inv {R : ℝ} (hR : 2 ≤ R) {u : ℝ}
    (hu : u ∈ Icc 1 R) : reciprocalProfile R hR u = u⁻¹ := by
  have hb : reciprocalBump R hR u = 1 := by
    apply ContDiffBump.one_of_mem_closedBall
    change dist u ((R + 1) / 2) ≤ (R - 1) / 2
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith [hu.1, hu.2]
  simp [reciprocalProfile, hb]

theorem reciprocalProfile_nonneg {R : ℝ} (hR : 2 ≤ R) (u : ℝ) :
    0 ≤ reciprocalProfile R hR u := by
  by_cases hu : u ≤ 1 / 2
  · rw [reciprocalProfile_zero_left hR hu]
  · exact div_nonneg (ContDiffBump.nonneg _) (by linarith)

theorem reciprocalProfile_smooth {R : ℝ} (hR : 2 ≤ R) :
    ContDiff ℝ ∞ (reciprocalProfile R hR) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  by_cases hu : u = 0
  · subst u
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds (show (0 : ℝ) < 1 / 2 by norm_num)] with x hx
    exact reciprocalProfile_zero_left hR hx.le
  · exact (ContDiffBump.contDiffAt _).div contDiffAt_id hu

theorem reciprocalProfile_compact {R : ℝ} (hR : 2 ≤ R) :
    HasCompactSupport (reciprocalProfile R hR) := by
  unfold reciprocalProfile
  simp only [div_eq_mul_inv]
  exact ((reciprocalBump R hR).hasCompactSupport.mul_right (f' := fun u : ℝ => u⁻¹))

theorem reciprocalProfile_tsupport {R : ℝ} (hR : 2 ≤ R) :
    tsupport (reciprocalProfile R hR) ⊆ Icc (1/2) (2*R) := by
  apply closure_minimal _ isClosed_Icc
  intro u hu
  constructor
  · by_contra hx
    exact hu (reciprocalProfile_zero_left hR (le_of_not_ge hx))
  · by_contra hx
    exact hu (reciprocalProfile_zero_right hR (le_of_not_ge hx))

theorem reciprocalProfile_integrable {R : ℝ} (hR : 2 ≤ R) :
    Integrable (reciprocalProfile R hR) :=
  (reciprocalProfile_smooth hR).continuous.integrable_of_hasCompactSupport
    (reciprocalProfile_compact hR)

theorem reciprocalProfile_sq_integrable {R : ℝ} (hR : 2 ≤ R) :
    Integrable (fun u => reciprocalProfile R hR u ^ 2) := by
  apply ((reciprocalProfile_smooth hR).continuous.pow 2).integrable_of_hasCompactSupport
  simpa only [pow_two] using (reciprocalProfile_compact hR).mul_right

theorem reciprocalProfile_moment_integrable {R : ℝ} (hR : 2 ≤ R) :
    Integrable (fun u => u * reciprocalProfile R hR u ^ 2) := by
  apply (continuous_id.mul ((reciprocalProfile_smooth hR).continuous.pow 2)).integrable_of_hasCompactSupport
  apply HasCompactSupport.mul_left
  simpa only [pow_two] using (reciprocalProfile_compact hR).mul_right

theorem reciprocalProfile_mass_lower {R : ℝ} (hR : 2 ≤ R) :
    Real.log R ≤ ∫ u, reciprocalProfile R hR u := by
  have h1 : (1 : ℝ) ≤ R := by linarith
  have heq : (∫ u in (1 : ℝ)..R, reciprocalProfile R hR u) = Real.log R := by
    rw [intervalIntegral.integral_congr (g := fun u : ℝ => u⁻¹) (by
      intro u hu
      rw [uIcc_of_le h1] at hu
      exact reciprocalProfile_eq_inv hR hu)]
    simpa using integral_inv_of_pos (by norm_num : (0 : ℝ) < 1) (by linarith : 0 < R)
  rw [← heq, intervalIntegral.integral_of_le h1]
  exact setIntegral_le_integral (reciprocalProfile_integrable hR)
    (Filter.Eventually.of_forall (reciprocalProfile_nonneg hR))

theorem reciprocalProfile_sq_mass_pos {R : ℝ} (hR : 2 ≤ R) :
    0 < ∫ u, reciprocalProfile R hR u ^ 2 := by
  apply integral_pos_of_integrable_nonneg_nonzero
    ((reciprocalProfile_smooth hR).continuous.pow 2) (reciprocalProfile_sq_integrable hR)
      (fun u => sq_nonneg _) (x := 1)
  have h := reciprocalProfile_eq_inv hR (show (1 : ℝ) ∈ Icc 1 R by constructor <;> linarith)
  simp [h]

theorem reciprocalProfile_moment_upper {R : ℝ} (hR : 2 ≤ R) :
    (∫ u, u * reciprocalProfile R hR u ^ 2) ≤ Real.log (4 * R) := by
  have heq : (∫ u in (1/2 : ℝ)..(2*R), u * reciprocalProfile R hR u ^ 2) =
      ∫ u, u * reciprocalProfile R hR u ^ 2 := by
    apply intervalIntegral.integral_eq_integral_of_support_subset
    intro u hu
    constructor
    · by_contra hx
      have hz := reciprocalProfile_zero_left hR (le_of_not_gt hx)
      exact hu (by simp [hz])
    · by_contra hx
      have hz := reciprocalProfile_zero_right hR (le_of_not_ge hx)
      exact hu (by simp [hz])
  rw [← heq]
  calc
    _ ≤ ∫ u in (1/2 : ℝ)..(2*R), u⁻¹ := by
      apply intervalIntegral.integral_mono_on (by linarith)
        (reciprocalProfile_moment_integrable hR).intervalIntegrable
      · apply intervalIntegral.intervalIntegrable_inv (f := fun u : ℝ => u)
        · intro u hu
          rw [uIcc_of_le (by linarith : (1/2 : ℝ) ≤ 2*R)] at hu
          linarith [hu.1]
        · exact continuous_id.continuousOn
      · intro u hu
        have hup : 0 < u := by linarith [hu.1]
        have hb0 : 0 ≤ reciprocalBump R hR u := ContDiffBump.nonneg _
        have hb1 : reciprocalBump R hR u ≤ 1 := ContDiffBump.le_one _
        calc
          u * reciprocalProfile R hR u ^ 2 = reciprocalBump R hR u ^ 2 / u := by
            dsimp [reciprocalProfile]
            field_simp
          _ ≤ 1 / u := div_le_div_of_nonneg_right (by nlinarith) hup.le
          _ = _ := one_div u
    _ = _ := by
      rw [integral_inv_of_pos (by norm_num : (0 : ℝ) < 1/2) (by linarith : 0 < 2*R)]
      congr 1
      ring

theorem exists_normalized_reciprocal_profile {lambda R : ℝ}
    (hlambda : 0 < lambda) (hR : 2 ≤ R) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      tsupport g ⊆ Ioi 0 ∧ (∀ u, 0 ≤ g u) ∧
      (∫ u, g u ^ 2) = 1 ∧ (∫ u, g u) = Real.sqrt lambda ∧
      (∫ u, u * g u ^ 2) = lambda * (∫ u, u * reciprocalProfile R hR u ^ 2) /
        (∫ u, reciprocalProfile R hR u) ^ 2 := by
  let A : ℝ := ∫ u, reciprocalProfile R hR u
  let Q : ℝ := ∫ u, reciprocalProfile R hR u ^ 2
  let B : ℝ := ∫ u, u * reciprocalProfile R hR u ^ 2
  have hA : 0 < A := lt_of_lt_of_le (Real.log_pos (by linarith : 1 < R))
    (reciprocalProfile_mass_lower hR)
  have hQ : 0 < Q := reciprocalProfile_sq_mass_pos hR
  have hroot : 0 < Real.sqrt lambda := Real.sqrt_pos.2 hlambda
  have hroot2 := Real.sq_sqrt hlambda.le
  let a : ℝ := A / (Real.sqrt lambda * Q)
  let b : ℝ := A ^ 2 / (lambda * Q)
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  let g : ℝ → ℝ := fun u => a * reciprocalProfile R hR (b * u)
  have hsmooth : ContDiff ℝ ∞ g :=
    contDiff_const.mul ((reciprocalProfile_smooth hR).comp (contDiff_const.mul contDiff_id))
  have hcompact : HasCompactSupport g := by
    exact ((reciprocalProfile_compact hR).comp_smul hb.ne').mul_left
  have hsupp : tsupport g ⊆ Ioi 0 := by
    have hs : tsupport g ⊆ Ici ((1/2) / b) := by
      apply closure_minimal _ isClosed_Ici
      intro u hu
      by_contra hn
      have hub : b * u ≤ 1/2 := by
        have := (lt_div_iff₀ hb).mp (lt_of_not_ge hn)
        nlinarith
      exact hu (by dsimp [g]; rw [reciprocalProfile_zero_left hR hub, mul_zero])
    intro u hu
    exact lt_of_lt_of_le (by positivity : (0 : ℝ) < (1/2)/b) (hs hu)
  have hmass1 : (∫ u, g u) = a * b⁻¹ * A := by
    dsimp only [g]
    rw [integral_const_mul, Measure.integral_comp_mul_left]
    rw [abs_of_pos (inv_pos.mpr hb)]
    simp only [smul_eq_mul, A]
    ring
  have hmass2 : (∫ u, g u ^ 2) = a ^ 2 * b⁻¹ * Q := by
    simp only [g, mul_pow]
    rw [integral_const_mul]
    change a ^ 2 * (∫ u, (fun x => reciprocalProfile R hR x ^ 2) (b * u)) = _
    rw [Measure.integral_comp_mul_left (fun x => reciprocalProfile R hR x ^ 2) b,
      abs_of_pos (inv_pos.mpr hb)]
    simp only [smul_eq_mul, Q]
    ring
  have hmom : (∫ u, u * g u ^ 2) = (a ^ 2 / b) * b⁻¹ * B := by
    calc
      _ = ∫ u, (a ^ 2 / b) * ((b * u) * reciprocalProfile R hR (b * u) ^ 2) := by
        apply integral_congr_ae
        filter_upwards [] with u
        dsimp only [g]
        field_simp
      _ = _ := by
        rw [integral_const_mul]
        change (a ^ 2 / b) * (∫ u, (fun x => x * reciprocalProfile R hR x ^ 2) (b * u)) = _
        rw [Measure.integral_comp_mul_left (fun x => x * reciprocalProfile R hR x ^ 2) b,
          abs_of_pos (inv_pos.mpr hb)]
        simp only [smul_eq_mul, B]
        ring
  refine ⟨g, hsmooth, hcompact, hsupp, (fun u => mul_nonneg ha.le (reciprocalProfile_nonneg hR _)), ?_, ?_, ?_⟩
  · rw [hmass2]
    dsimp only [a, b]
    field_simp
    nlinarith [hroot2]
  · rw [hmass1]
    dsimp only [a, b]
    field_simp
    nlinarith [hroot2]
  · rw [hmom]
    change (a ^ 2 / b) * b⁻¹ * B = lambda * B / A ^ 2
    dsimp only [a, b]
    field_simp
    rw [hroot2]

theorem exists_small_first_moment_profile {lambda beta : ℝ}
    (hlambda : 0 < lambda) (hbeta : 0 < beta) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      tsupport g ⊆ Ioi 0 ∧ (∀ u, 0 ≤ g u) ∧
      (∫ u, g u ^ 2) = 1 ∧ (∫ u, g u) = Real.sqrt lambda ∧
      (∫ u, u * g u ^ 2) < beta := by
  let t : ℝ := max (Real.log 4) (2 * lambda / beta) + 1
  have htlog : Real.log 4 < t := by dsimp [t]; linarith [le_max_left (Real.log 4) (2*lambda/beta)]
  have htlarge : 2 * lambda / beta < t := by dsimp [t]; linarith [le_max_right (Real.log 4) (2*lambda/beta)]
  have htpos : 0 < t := lt_trans (Real.log_pos (by norm_num : (1 : ℝ) < 4)) htlog
  let R : ℝ := Real.exp t
  have hR : 2 ≤ R := by
    have : 4 < R := by
      dsimp [R]
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 4)]
      exact Real.exp_lt_exp.mpr htlog
    linarith
  obtain ⟨g, hgs, hgc, hgp, hgn, hg2, hg1, hgB⟩ :=
    exists_normalized_reciprocal_profile hlambda hR
  refine ⟨g, hgs, hgc, hgp, hgn, hg2, hg1, ?_⟩
  rw [hgB]
  have hA : t ≤ ∫ u, reciprocalProfile R hR u := by
    simpa only [R, Real.log_exp] using reciprocalProfile_mass_lower hR
  have hB : (∫ u, u * reciprocalProfile R hR u ^ 2) ≤ Real.log 4 + t := by
    convert reciprocalProfile_moment_upper hR using 1
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (by exact (Real.exp_pos t).ne' : R ≠ 0)]
    simp only [R, Real.log_exp]
  apply (div_lt_iff₀ (sq_pos_of_pos (htpos.trans_le hA))).mpr
  have hva : 2 * lambda < t * beta := (div_lt_iff₀ hbeta).mp htlarge
  have hsq : t ^ 2 ≤ (∫ u, reciprocalProfile R hR u) ^ 2 := by nlinarith
  have hBt : (∫ u, u * reciprocalProfile R hR u ^ 2) < 2 * t := by linarith
  nlinarith

noncomputable def scaledProfileDensity (g : ℝ → ℝ) (k : ℝ) (u : ℝ) : ℝ :=
  k * g (k * u) ^ 2

noncomputable def productProfile (g : ℝ → ℝ) (k : ℝ) (j : ℕ) (t : Fin j → ℝ) : ℝ :=
  ∏ i, Real.sqrt k * g (k * t i)

noncomputable def productDensity (p : ℝ → ℝ) (j : ℕ) (t : Fin j → ℝ) : ℝ :=
  ∏ i, p (t i)

def coordinateSum {j : ℕ} (t : Fin j → ℝ) : ℝ := ∑ i, t i

theorem productProfile_sq (g : ℝ → ℝ) {k : ℝ} (hk : 0 ≤ k)
    (j : ℕ) (t : Fin j → ℝ) :
    productProfile g k j t ^ 2 = productDensity (scaledProfileDensity g k) j t := by
  simp only [productProfile, productDensity, ← Finset.prod_pow, mul_pow,
    Real.sq_sqrt hk, scaledProfileDensity]

theorem scaledProfileDensity_integral {g : ℝ → ℝ} {k : ℝ} (hk : 0 < k)
    (hg : (∫ u, g u ^ 2) = 1) : (∫ u, scaledProfileDensity g k u) = 1 := by
  unfold scaledProfileDensity
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun u => g u ^ 2) k,
    abs_of_pos (inv_pos.mpr hk), smul_eq_mul, hg]
  field_simp

theorem scaledProfileDensity_moment (g : ℝ → ℝ) {k : ℝ} (hk : 0 < k) :
    (∫ u, u * scaledProfileDensity g k u) = (∫ u, u * g u ^ 2) / k := by
  calc
    _ = ∫ u, (k * u) * g (k * u) ^ 2 := by
      apply integral_congr_ae
      filter_upwards [] with u
      dsimp [scaledProfileDensity]
      ring
    _ = _ := by
      rw [Measure.integral_comp_mul_left (fun u => u * g u ^ 2) k,
        abs_of_pos (inv_pos.mpr hk), smul_eq_mul]
      ring

theorem productDensity_integral {p : ℝ → ℝ} (hp : (∫ u, p u) = 1) (j : ℕ) :
    (∫ t : Fin j → ℝ, productDensity p j t) = 1 := by
  simp only [productDensity, integral_fintype_prod_volume_eq_pow, hp, one_pow]

theorem productDensity_nonneg {p : ℝ → ℝ} (hp : ∀ u, 0 ≤ p u)
    (j : ℕ) (t : Fin j → ℝ) : 0 ≤ productDensity p j t :=
  Finset.prod_nonneg fun i _ => hp (t i)

theorem coordinate_mul_productDensity {p : ℝ → ℝ} {j : ℕ} (i : Fin j) (t : Fin j → ℝ) :
    t i * productDensity p j t =
      ∏ l, (if l = i then t l else 1) * p (t l) := by
  rw [Finset.prod_mul_distrib]
  simp [productDensity]

theorem coordinate_productDensity_integrable {p : ℝ → ℝ} {j : ℕ}
    (hp : Integrable p) (hp1 : Integrable (fun u => u * p u)) (i : Fin j) :
    Integrable (fun t : Fin j → ℝ => t i * productDensity p j t) := by
  simp only [coordinate_mul_productDensity]
  change Integrable (fun t : Fin j → ℝ =>
    ∏ l, (fun u : ℝ => (if l = i then u else 1) * p u) (t l))
      (Measure.pi fun _ : Fin j => (volume : Measure ℝ))
  apply Integrable.fintype_prod (f := fun l u => (if l = i then u else 1) * p u)
    (μ := fun _ : Fin j => (volume : Measure ℝ))
  intro l
  by_cases hl : l = i
  · simpa only [ite_eq_left hl] using hp1
  · simpa only [ite_eq_right hl, one_mul] using hp

theorem coordinate_productDensity_integral {p : ℝ → ℝ} {j : ℕ}
    (hp : (∫ u, p u) = 1) (i : Fin j) :
    (∫ t : Fin j → ℝ, t i * productDensity p j t) = ∫ u, u * p u := by
  simp only [coordinate_mul_productDensity]
  change (∫ t : Fin j → ℝ,
    ∏ l, (fun u : ℝ => (if l = i then u else 1) * p u) (t l)) = _
  rw [integral_fintype_prod_volume_eq_prod
    (fun l u => (if l = i then u else 1) * p u)]
  have hf : (fun l : Fin j => ∫ u : ℝ, (if l = i then u else 1) * p u) =
      fun l => if l = i then ∫ u, u * p u else 1 := by
    funext l
    split_ifs with hl
    · rfl
    · simpa only [one_mul] using hp
  rw [hf]
  simp

theorem coordinateSum_productDensity_integrable {p : ℝ → ℝ}
    (hp : Integrable p) (hp1 : Integrable (fun u => u * p u)) (j : ℕ) :
    Integrable (fun t : Fin j → ℝ => coordinateSum t * productDensity p j t) := by
  simp only [coordinateSum, Finset.sum_mul]
  exact integrable_finsetSum _ (fun i _ => coordinate_productDensity_integrable hp hp1 i)

theorem coordinateSum_productDensity_integral {p : ℝ → ℝ} (hp : (∫ u, p u) = 1)
    (hp0 : Integrable p) (hp1 : Integrable (fun u => u * p u)) (j : ℕ) :
    (∫ t : Fin j → ℝ, coordinateSum t * productDensity p j t) =
      (j : ℝ) * ∫ u, u * p u := by
  simp only [coordinateSum, Finset.sum_mul]
  rw [integral_finsetSum _ (fun i _ => coordinate_productDensity_integrable hp0 hp1 i)]
  simp only [coordinate_productDensity_integral hp, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

theorem productDensity_ne_zero_coordinates {p : ℝ → ℝ} {j : ℕ}
    (hs : Function.support p ⊆ Ioi 0) {t : Fin j → ℝ}
    (ht : productDensity p j t ≠ 0) (i : Fin j) : 0 < t i := by
  apply hs
  exact (Finset.prod_ne_zero_iff.mp ht) i (Finset.mem_univ i)

theorem productDensity_ne_zero_sum_nonneg {p : ℝ → ℝ} {j : ℕ}
    (hs : Function.support p ⊆ Ioi 0) {t : Fin j → ℝ}
    (ht : productDensity p j t ≠ 0) : 0 ≤ coordinateSum t := by
  exact Finset.sum_nonneg fun i _ => (productDensity_ne_zero_coordinates hs ht i).le

theorem productDensity_compact {p : ℝ → ℝ} (hp : HasCompactSupport p) (j : ℕ) :
    HasCompactSupport (productDensity p j) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_univ_pi fun _ => hp)
  intro t ht i _
  exact subset_closure (show t i ∈ Function.support p from
    (Finset.prod_ne_zero_iff.mp ht) i (Finset.mem_univ i))

theorem productDensity_continuous {p : ℝ → ℝ} (hp : Continuous p) (j : ℕ) :
    Continuous (productDensity p j) := by
  unfold productDensity
  fun_prop

theorem productDensity_integrable {p : ℝ → ℝ} (hp : Continuous p)
    (hpc : HasCompactSupport p) (j : ℕ) : Integrable (productDensity p j) :=
  (productDensity_continuous hp j).integrable_of_hasCompactSupport (productDensity_compact hpc j)

theorem poly_productDensity_integrable {p : ℝ → ℝ} {j : ℕ} (hp : Continuous p)
    (hpc : HasCompactSupport p) {P : (Fin j → ℝ) → ℝ} (hP : Continuous P) :
    Integrable (fun t => P t * productDensity p j t) :=
  (hP.mul (productDensity_continuous hp j)).integrable_of_hasCompactSupport
    ((productDensity_compact hpc j).mul_left)

theorem one_coordinate_productDensity {p f : ℝ → ℝ} {j : ℕ}
    (i : Fin j) (t : Fin j → ℝ) :
    f (t i) * productDensity p j t =
      ∏ l, (if l = i then f (t l) else 1) * p (t l) := by
  rw [Finset.prod_mul_distrib]
  simp [productDensity]

theorem two_coordinate_productDensity {p f : ℝ → ℝ} {j : ℕ}
    (i l : Fin j) (hil : i ≠ l) (t : Fin j → ℝ) :
    (f (t i) * f (t l)) * productDensity p j t =
      ∏ a, (if a = i then f (t a) else if a = l then f (t a) else 1) * p (t a) := by
  have hf : (fun a : Fin j => if a = i then f (t a) else if a = l then f (t a) else 1) =
      fun a => (if a = i then f (t a) else 1) * (if a = l then f (t a) else 1) := by
    funext a
    by_cases hai : a = i
    · subst a
      simp [hil]
    · simp [hai]
  rw [Finset.prod_mul_distrib, hf, Finset.prod_mul_distrib]
  simp [productDensity]

theorem one_coordinate_productDensity_integral {p f : ℝ → ℝ} {j : ℕ}
    (hp : (∫ u, p u) = 1) (i : Fin j) :
    (∫ t : Fin j → ℝ, f (t i) * productDensity p j t) = ∫ u, f u * p u := by
  simp only [one_coordinate_productDensity]
  rw [integral_fintype_prod_volume_eq_prod
    (fun l u => (if l = i then f u else 1) * p u)]
  have hf : (fun l : Fin j => ∫ u : ℝ, (if l = i then f u else 1) * p u) =
      fun l => if l = i then ∫ u, f u * p u else 1 := by
    funext l
    split_ifs with hl
    · rfl
    · simpa only [one_mul] using hp
  rw [hf]
  simp

theorem two_coordinate_productDensity_integral {p f : ℝ → ℝ} {j : ℕ}
    (hp : (∫ u, p u) = 1) (i l : Fin j) (hil : i ≠ l) :
    (∫ t : Fin j → ℝ, (f (t i) * f (t l)) * productDensity p j t) =
      (∫ u, f u * p u)^2 := by
  simp only [two_coordinate_productDensity i l hil]
  rw [integral_fintype_prod_volume_eq_prod
    (fun a u => (if a = i then f u else if a = l then f u else 1) * p u)]
  have hf : (fun a : Fin j => ∫ u : ℝ,
      (if a = i then f u else if a = l then f u else 1) * p u) =
      fun a => (if a = i then ∫ u, f u * p u else 1) *
        (if a = l then ∫ u, f u * p u else 1) := by
    funext a
    by_cases hai : a = i
    · subst a
      simp [hil]
    · by_cases hal : a = l
      · subst a
        simp [hil.symm]
      · simp [hai, hal, hp]
  rw [hf, Finset.prod_mul_distrib]
  simp [pow_two]

end LargePrimeGaps

end OAI
