import OAI.GroupTheory.ArtinCAT0.StableLength

namespace OAI

namespace ArtinCAT0

section BusemannCharacter

open Filter Topology

variable {G X : Type*} [Group G] [MetricSpace X] [MulAction G X]

/-- Busemann function based on the positive orbit of a minimizing point. -/
noncomputable def orbitBusemann (x : X) (g : G) (D : ℝ) (z : X) : ℝ :=
  ⨅ n : ℕ, dist z ((g ^ n) • x) - (n : ℝ) * D

lemma orbitBusemann_tendsto (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x : X) (g : G) (D : ℝ) (haxis : ∀ n : ℕ, dist x ((g ^ n) • x) = n * D)
    (z : X) :
    Tendsto (fun n : ℕ => dist z ((g ^ n) • x) - (n : ℝ) * D)
      atTop (𝓝 (orbitBusemann x g D z)) := by
  have hD : dist x (g • x) = D := by simpa using haxis 1
  apply tendsto_atTop_ciInf
  · apply antitone_nat_of_succ_le
    intro n
    have ht := dist_triangle z ((g ^ n) • x) ((g ^ (n + 1)) • x)
    rw [powerStepDistance hi, hD] at ht
    push_cast
    linarith
  · refine ⟨-dist z x, ?_⟩
    rintro _ ⟨n, rfl⟩
    have ht := dist_triangle x z ((g ^ n) • x)
    rw [haxis n, dist_comm x z] at ht
    linarith

lemma orbitBusemann_lipschitz (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x : X) (g : G) (D : ℝ) (haxis : ∀ n : ℕ, dist x ((g ^ n) • x) = n * D)
    (z w : X) : |orbitBusemann x g D z - orbitBusemann x g D w| ≤ dist z w := by
  apply le_of_tendsto' (((orbitBusemann_tendsto hi x g D haxis z).sub
    (orbitBusemann_tendsto hi x g D haxis w)).abs)
  intro n
  simpa only [sub_sub_sub_cancel_right] using abs_dist_sub_le z w ((g ^ n) • x)

lemma fourSquares_limit {A B C E : ℕ → ℝ} {a b c e D : ℝ}
    (hA : Tendsto (fun n : ℕ => A n - n * D) atTop (𝓝 a))
    (hB : Tendsto (fun n : ℕ => B n - n * D) atTop (𝓝 b))
    (hC : Tendsto (fun n : ℕ => C n - n * D) atTop (𝓝 c))
    (hE : Tendsto (fun n : ℕ => E n - n * D) atTop (𝓝 e)) :
    Tendsto (fun n : ℕ => (A n ^ 2 + B n ^ 2 - C n ^ 2 - E n ^ 2) / (n : ℝ))
      atTop (𝓝 (2 * D * (a + b - c - e))) := by
  have hs := ((((hA.pow 2).add (hB.pow 2)).sub (hC.pow 2)).sub (hE.pow 2)).div_atTop
    tendsto_natCast_atTop_atTop
  have hl := ((((hA.add hB).sub hC).sub hE).const_mul (2 * D)).add hs
  simp only [add_zero] at hl
  refine Tendsto.congr' ?_ hl
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn)
  field_simp
  ring

lemma quadrilateral_difference (hX : CAT0 X) (z w p q : X) :
    |dist z p ^ 2 + dist w q ^ 2 - dist w p ^ 2 - dist z q ^ 2| ≤
      dist z w ^ 2 + dist p q ^ 2 := by
  have h₁ := quadrilateral hX z w p q
  have h₂ := quadrilateral hX w z p q
  rw [dist_comm q z] at h₁
  rw [dist_comm q w, dist_comm w z] at h₂
  rw [abs_le]
  constructor <;> linarith

lemma orbitBusemann_centralizer_difference (hX : CAT0 X)
    (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x : X) (g : G) (D : ℝ) (hD : 0 < D)
    (haxis : ∀ n : ℕ, dist x ((g ^ n) • x) = n * D)
    {h : G} (hc : Commute g h) (z w : X) :
    orbitBusemann x g D (h • z) - orbitBusemann x g D (h • w) =
      orbitBusemann x g D z - orbitBusemann x g D w := by
  let p : ℕ → X := fun n => (g ^ n) • x
  let q : ℕ → X := fun n => h⁻¹ • p n
  have hq (v : X) (n : ℕ) : dist v (q n) = dist (h • v) (p n) := by
    rw [← (hi h).dist_eq]
    dsimp [q]
    rw [smul_inv_smul]
  have hpq (n : ℕ) : dist (p n) (q n) = dist x (h⁻¹ • x) := by
    dsimp [p, q]
    rw [← mul_smul, ← (hc.pow_left n).inv_right.eq, mul_smul, (hi (g ^ n)).dist_eq]
  have hl := fourSquares_limit (orbitBusemann_tendsto hi x g D haxis z)
    (orbitBusemann_tendsto hi x g D haxis (h • w))
    (orbitBusemann_tendsto hi x g D haxis w)
    (orbitBusemann_tendsto hi x g D haxis (h • z))
  have hu : ∀ n : ℕ,
      |(dist z (p n)^2 + dist (h • w) (p n)^2 - dist w (p n)^2 - dist (h • z) (p n)^2) / (n : ℝ)|
        ≤ (dist z w ^ 2 + dist x (h⁻¹ • x)^2) / (n : ℝ) := by
    intro n
    have hquad := quadrilateral_difference hX z w (p n) (q n)
    rw [hq, hq, hpq] at hquad
    rw [abs_div, show |(n : ℝ)| = (n : ℝ) from abs_of_nonneg (Nat.cast_nonneg n)]
    exact div_le_div_of_nonneg_right hquad (Nat.cast_nonneg n)
  have hz := le_of_tendsto_of_tendsto' hl.abs
    (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop) hu
  have hzero : 2 * D * (orbitBusemann x g D z + orbitBusemann x g D (h • w) -
      orbitBusemann x g D w - orbitBusemann x g D (h • z)) = 0 := by
    exact abs_nonpos_iff.mp hz
  have he := (mul_eq_zero.mp hzero).resolve_left (mul_ne_zero (by norm_num) hD.ne')
  linarith

noncomputable def orbitCharacter (x : X) (g : G) (D : ℝ) (h : G) : ℝ :=
  orbitBusemann x g D x - orbitBusemann x g D (h • x)

lemma orbitCharacter_one (x : X) (g : G) (D : ℝ) : orbitCharacter x g D 1 = 0 := by
  simp [orbitCharacter]

lemma orbitCharacter_mul (hX : CAT0 X)
    (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x : X) (g : G) (D : ℝ) (hD : 0 < D)
    (haxis : ∀ n : ℕ, dist x ((g ^ n) • x) = n * D)
    {h k : G} (hc : Commute g h) :
    orbitCharacter x g D (h * k) = orbitCharacter x g D h + orbitCharacter x g D k := by
  have he := orbitBusemann_centralizer_difference hX hi x g D hD haxis hc (k • x) x
  dsimp [orbitCharacter]
  rw [mul_smul]
  linarith

lemma orbitCharacter_pow (hX : CAT0 X)
    (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x : X) (g : G) (D : ℝ) (hD : 0 < D)
    (haxis : ∀ n : ℕ, dist x ((g ^ n) • x) = n * D)
    {h : G} (hc : Commute g h) (n : ℕ) :
    orbitCharacter x g D (h ^ n) = n * orbitCharacter x g D h := by
  induction n with
  | zero => simp [orbitCharacter_one]
  | succ n ih =>
    rw [pow_succ, orbitCharacter_mul hX hi x g D hD haxis (hc.pow_right n), ih]
    push_cast
    ring

lemma orbitCharacter_inv (hX : CAT0 X)
    (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x : X) (g : G) (D : ℝ) (hD : 0 < D)
    (haxis : ∀ n : ℕ, dist x ((g ^ n) • x) = n * D)
    {h : G} (hc : Commute g h) :
    orbitCharacter x g D h⁻¹ = -orbitCharacter x g D h := by
  have he := orbitCharacter_mul hX hi x g D hD haxis (k := h⁻¹) hc
  rw [mul_inv_cancel, orbitCharacter_one] at he
  linarith

lemma orbitCharacter_zpow (hX : CAT0 X)
    (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x : X) (g : G) (D : ℝ) (hD : 0 < D)
    (haxis : ∀ n : ℕ, dist x ((g ^ n) • x) = n * D)
    {h : G} (hc : Commute g h) (n : ℤ) :
    orbitCharacter x g D (h ^ n) = n * orbitCharacter x g D h := by
  cases n with
  | ofNat n => simpa using orbitCharacter_pow hX hi x g D hD haxis hc n
  | negSucc n =>
    rw [zpow_negSucc, orbitCharacter_inv hX hi x g D hD haxis (hc.pow_right (n+1)),
      orbitCharacter_pow hX hi x g D hD haxis hc]
    push_cast
    ring

lemma orbitBusemann_self (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x : X) (g : G) (D : ℝ) (haxis : ∀ n : ℕ, dist x ((g ^ n) • x) = n * D) :
    orbitBusemann x g D x = 0 := by
  have he := orbitBusemann_tendsto hi x g D haxis x
  simp only [haxis, sub_self] at he
  exact tendsto_nhds_unique he tendsto_const_nhds

lemma orbitCharacter_self (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x : X) (g : G) (D : ℝ) (haxis : ∀ n : ℕ, dist x ((g ^ n) • x) = n * D) :
    orbitCharacter x g D g = D := by
  have he := (orbitBusemann_tendsto hi x g D haxis (g • x)).comp (tendsto_add_atTop_nat 1)
  have hd (n : ℕ) : dist (g • x) ((g ^ (n+1)) • x) = n * D := by
    rw [pow_succ', mul_smul, (hi g).dist_eq, haxis]
  have he' : orbitBusemann x g D (g • x) = -D := by
    apply tendsto_nhds_unique he
    convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => -D) atTop (𝓝 (-D))) using 1
    ext n
    dsimp only [Function.comp_apply]
    rw [hd, Nat.cast_add_one]
    ring
  simp [orbitCharacter, orbitBusemann_self hi x g D haxis, he']

lemma orbitCharacter_abs_le (hX : CAT0 X)
    (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x : X) (g : G) (D : ℝ) (hD : 0 < D)
    (haxis : ∀ n : ℕ, dist x ((g ^ n) • x) = n * D)
    {h : G} (hc : Commute g h) : |orbitCharacter x g D h| ≤ stableLengthAt x h := by
  apply ge_of_tendsto (stableLength_tendsto hi x h)
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have he := orbitBusemann_lipschitz hi x g D haxis x ((h ^ n) • x)
  change |orbitCharacter x g D (h ^ n)| ≤ _ at he
  rw [orbitCharacter_pow hX hi x g D hD haxis hc, abs_mul,
    show |(n : ℝ)| = (n : ℝ) from abs_of_nonneg (Nat.cast_nonneg n)] at he
  exact (le_div_iff₀ (Nat.cast_pos.mpr hn)).mpr (by simpa only [mul_comm] using he)

lemma lengthPairing_eq_orbitCharacter (hX : CAT0 X)
    (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x : X) (g : G) (D : ℝ) (hD : 0 < D)
    (haxis : ∀ n : ℕ, dist x ((g ^ n) • x) = n * D)
    (hL : stableLengthAt x g = D) {h : G} (hc : Commute g h) :
    lengthPairing x g h = D * orbitCharacter x g D h := by
  have he : 2 * (D * orbitCharacter x g D h - lengthPairing x g h) = 0 :=
    zero_of_int_mul_le (b := stableLengthAt x h ^ 2 - orbitCharacter x g D h ^ 2) (fun n => by
      have hb := orbitCharacter_abs_le hX hi x g D hD haxis
        ((Commute.refl g).zpow_right n |>.mul_right hc)
      rw [orbitCharacter_mul hX hi x g D hD haxis ((Commute.refl g).zpow_right n),
        orbitCharacter_zpow hX hi x g D hD haxis (Commute.refl g),
        orbitCharacter_self hi x g D haxis] at hb
      have hs : ((n : ℝ) * D + orbitCharacter x g D h)^2 ≤
          stableLengthAt x ((g ^ n) * h)^2 := by
        nlinarith [sq_abs ((n : ℝ) * D + orbitCharacter x g D h),
          stableLength_nonneg hi x ((g ^ n) * h), abs_nonneg ((n : ℝ) * D + orbitCharacter x g D h)]
      rw [stableLength_zpow_product_sq hX hi x hc, hL] at hs
      nlinarith)
  linarith

lemma lengthPairing_centralizer [ProperSpace X] [Nonempty X]
    (hG : GeometricAction G X) (x : X) {g h k : G}
    (hgh : Commute g h) (hgk : Commute g k) :
    lengthPairing x g (h * k) = lengthPairing x g h + lengthPairing x g k := by
  by_cases hz : stableLengthAt x g = 0
  · rw [lengthPairing_zero_of_length_zero hG.1 hG.2.1 x (hgh.mul_right hgk) hz,
      lengthPairing_zero_of_length_zero hG.1 hG.2.1 x hgh hz,
      lengthPairing_zero_of_length_zero hG.1 hG.2.1 x hgk hz]
    ring
  obtain ⟨p, hp⟩ := exists_displacement_minimizer hG g
  have hLp := stableLength_minimizer hG.1 hG.2.1 g hp
  have hD : 0 < dist p (g • p) := by
    have ht := stableLength_nonneg hG.2.1 x g
    rw [stableLength_basepoint hG.2.1 x p g, hLp] at hz ht
    exact lt_of_le_of_ne ht (Ne.symm hz)
  have haxis := minimizer_displacement_pow hG.1 hG.2.1 g hp
  rw [lengthPairing_basepoint hG.2.1 x p,
    lengthPairing_basepoint hG.2.1 x p g h, lengthPairing_basepoint hG.2.1 x p g k]
  rw [lengthPairing_eq_orbitCharacter hG.1 hG.2.1 p g _ hD haxis hLp (hgh.mul_right hgk),
    lengthPairing_eq_orbitCharacter hG.1 hG.2.1 p g _ hD haxis hLp hgh,
    lengthPairing_eq_orbitCharacter hG.1 hG.2.1 p g _ hD haxis hLp hgk,
    orbitCharacter_mul hG.1 hG.2.1 p g _ hD haxis hgh, mul_add]

end BusemannCharacter

end ArtinCAT0

end OAI
