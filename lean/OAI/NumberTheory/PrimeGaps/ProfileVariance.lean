import OAI.NumberTheory.PrimeGaps.Profiles

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

theorem centered_profile_integral {p : ℝ → ℝ} (hp : Continuous p)
    (hpc : HasCompactSupport p) (hpi : (∫ u, p u) = 1) :
    (∫ u, (u - ∫ v, v * p v) * p u) = 0 := by
  simp only [sub_mul]
  have hp0 : Integrable p := hp.integrable_of_hasCompactSupport hpc
  have hp1 : Integrable (fun u => u * p u) :=
    (continuous_id.mul hp).integrable_of_hasCompactSupport hpc.mul_left
  rw [integral_sub hp1 (hp0.const_mul _), integral_const_mul, hpi]
  ring

theorem coordinateSum_variance {p : ℝ → ℝ} (hp : Continuous p)
    (hpc : HasCompactSupport p) (hpi : (∫ u, p u) = 1) (j : ℕ) :
    (∫ t : Fin j → ℝ, (coordinateSum t - (j : ℝ) * ∫ u, u * p u)^2 *
      productDensity p j t) = (j : ℝ) * ∫ u, (u - ∫ v, v * p v)^2 * p u := by
  let m : ℝ := ∫ u, u * p u
  have hexpand (t : Fin j → ℝ) :
      (coordinateSum t - (j : ℝ) * m)^2 * productDensity p j t =
      ∑ i, ∑ l, ((t i - m) * (t l - m)) * productDensity p j t := by
    have hs : coordinateSum t - (j : ℝ) * m = ∑ i : Fin j, (t i - m) := by
      simp [coordinateSum, Finset.sum_sub_distrib]
    rw [hs, pow_two, Finset.sum_mul]
    simp only [Finset.mul_sum, Finset.sum_mul]
  change (∫ t : Fin j → ℝ, (coordinateSum t - (j : ℝ) * m)^2 *
    productDensity p j t) = (j : ℝ) * ∫ u, (u - m)^2 * p u
  simp only [hexpand]
  have hint (i l : Fin j) : Integrable (fun t : Fin j → ℝ =>
      ((t i - m) * (t l - m)) * productDensity p j t) :=
    poly_productDensity_integrable hp hpc (by fun_prop)
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun l _ => hint i l))]
  simp only [integral_finsetSum _ (fun l _ => hint _ l)]
  have hterm (i l : Fin j) :
      (∫ t : Fin j → ℝ, ((t i - m) * (t l - m)) * productDensity p j t) =
      if l = i then ∫ u, (u - m)^2 * p u else 0 := by
    split_ifs with hli
    · subst l
      simpa only [← pow_two] using
        (one_coordinate_productDensity_integral (f := fun u => (u-m)^2) hpi i)
    · rw [two_coordinate_productDensity_integral (f := fun u => u-m) hpi i l (Ne.symm hli),
        centered_profile_integral hp hpc hpi]
      norm_num
  simp only [hterm]
  simp [m]

theorem scaledProfileDensity_continuous {g : ℝ → ℝ} (hg : Continuous g) (k : ℝ) :
    Continuous (scaledProfileDensity g k) := by
  unfold scaledProfileDensity
  fun_prop

theorem scaledProfileDensity_compact {g : ℝ → ℝ} (hg : HasCompactSupport g)
    {k : ℝ} (hk : k ≠ 0) : HasCompactSupport (scaledProfileDensity g k) := by
  have hh : HasCompactSupport (fun u => g (k*u)^2) := by
    have hh := (hg.comp_smul hk).mul_right (f' := fun u => g (k*u))
    change HasCompactSupport (fun u => g (k*u) * g (k*u)) at hh
    simpa only [pow_two] using hh
  exact hh.mul_left

theorem scaledProfileDensity_variance (g : ℝ → ℝ) {k : ℝ} (hk : 0 < k) :
    (∫ u, (u - (∫ v, v * g v^2)/k)^2 * scaledProfileDensity g k u) =
      (∫ u, (u - ∫ v, v * g v^2)^2 * g u^2) / k^2 := by
  let m : ℝ := ∫ u, u * g u^2
  calc
    _ = k⁻¹ * ∫ u, (k*u - m)^2 * g (k*u)^2 := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with u
      dsimp only [scaledProfileDensity]
      change (u - m / k)^2 * (k * g (k*u)^2) = _
      field_simp
    _ = _ := by
      rw [Measure.integral_comp_mul_left (fun u => (u-m)^2 * g u^2) k,
        abs_of_pos (inv_pos.mpr hk), smul_eq_mul]
      dsimp only [m]
      ring

theorem concentrated_cutoff_mass {p chi : ℝ → ℝ} (hp : Continuous p)
    (hpc : HasCompactSupport p) (hpn : ∀ u, 0 ≤ p u) (hpi : (∫ u, p u) = 1)
    (hchi : Continuous chi) (hchi0 : ∀ s, 0 ≤ chi s) (hchi1 : ∀ s, chi s ≤ 1)
    {beta d : ℝ} (hd : 0 < d) (hflat : ∀ s ≤ beta, chi s = 1)
    (j : ℕ) (hmean : (j : ℝ) * (∫ u, u*p u) + d ≤ beta) :
    1 - ((j : ℝ) * ∫ u, (u - ∫ v, v*p v)^2 * p u) / d^2 ≤
      ∫ t : Fin j → ℝ, productDensity p j t * chi (coordinateSum t)^2 := by
  let m : ℝ := (j : ℝ) * (∫ u, u*p u)
  have hD := productDensity_integrable hp hpc j
  have hC : Integrable (fun t : Fin j → ℝ =>
      productDensity p j t * chi (coordinateSum t)^2) := by
    simpa only [mul_comm] using
      (poly_productDensity_integrable hp hpc
        (P := fun t : Fin j → ℝ => chi (coordinateSum t)^2) (by
          unfold coordinateSum
          fun_prop))
  have hV : Integrable (fun t : Fin j → ℝ =>
      (coordinateSum t - m)^2 * productDensity p j t) :=
    poly_productDensity_integrable hp hpc (by unfold coordinateSum; fun_prop)
  have hle (t : Fin j → ℝ) :
      productDensity p j t - productDensity p j t * chi (coordinateSum t)^2 ≤
        ((coordinateSum t - m)^2 * productDensity p j t) / d^2 := by
    have hDn := productDensity_nonneg hpn j t
    have hc0 := hchi0 (coordinateSum t)
    have hc1 := hchi1 (coordinateSum t)
    by_cases ht : coordinateSum t ≤ beta
    · rw [hflat _ ht]
      simpa only [one_pow, mul_one, sub_self] using
        (div_nonneg (mul_nonneg (sq_nonneg _) hDn) (sq_nonneg d))
    · have hdm : d ≤ coordinateSum t - m := by dsimp only [m]; linarith
      have hd2 : 0 < d^2 := sq_pos_of_pos hd
      apply (le_div_iff₀ hd2).mpr
      have hc2 : 0 ≤ chi (coordinateSum t)^2 := sq_nonneg _
      have hv2 : d^2 ≤ (coordinateSum t - m)^2 := by nlinarith
      calc
        _ ≤ productDensity p j t * d^2 :=
          mul_le_mul_of_nonneg_right (sub_le_self _ (mul_nonneg hDn hc2)) hd2.le
        _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hv2 hDn]
  have hint := integral_mono (hD.sub hC) (hV.div_const (d^2)) hle
  dsimp only [Pi.sub_apply] at hint
  rw [integral_sub hD hC, productDensity_integral hpi, integral_div] at hint
  change 1 - _ ≤ (∫ t : Fin j → ℝ,
    (coordinateSum t - (j:ℝ)*(∫ u, u*p u))^2 * productDensity p j t) / d^2 at hint
  rw [coordinateSum_variance hp hpc hpi] at hint
  linarith

theorem cutoff_mass_le_one {p chi : ℝ → ℝ} (hp : Continuous p)
    (hpc : HasCompactSupport p) (hpn : ∀ u, 0 ≤ p u) (hpi : (∫ u, p u) = 1)
    (hchi : Continuous chi) (hchi0 : ∀ s, 0 ≤ chi s) (hchi1 : ∀ s, chi s ≤ 1) (j : ℕ) :
    (∫ t : Fin j → ℝ, productDensity p j t * chi (coordinateSum t)^2) ≤ 1 := by
  rw [← productDensity_integral hpi j]
  apply integral_mono
  · simpa only [mul_comm] using
      (poly_productDensity_integrable hp hpc
        (P := fun t : Fin j → ℝ => chi (coordinateSum t)^2) (by
          unfold coordinateSum
          fun_prop))
  · exact productDensity_integrable hp hpc j
  · intro t
    have hc0 := hchi0 (coordinateSum t)
    have hc1 := hchi1 (coordinateSum t)
    have hc2 : chi (coordinateSum t)^2 ≤ 1 := by nlinarith
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hc2 (productDensity_nonneg hpn j t)

noncomputable def simplexCutoff (beta gamma : ℝ) (s : ℝ) : ℝ :=
  1 - Real.smoothTransition ((s-beta)/(gamma-beta))

theorem simplexCutoff_smooth (beta gamma : ℝ) : ContDiff ℝ ∞ (simplexCutoff beta gamma) := by
  unfold simplexCutoff
  exact contDiff_const.sub (Real.smoothTransition.contDiff.comp
    ((contDiff_id.sub contDiff_const).div_const _))

theorem simplexCutoff_nonneg (beta gamma s : ℝ) : 0 ≤ simplexCutoff beta gamma s :=
  sub_nonneg.mpr (Real.smoothTransition.le_one _)

theorem simplexCutoff_le_one (beta gamma s : ℝ) : simplexCutoff beta gamma s ≤ 1 :=
  sub_le_self _ (Real.smoothTransition.nonneg _)

theorem simplexCutoff_eq_one {beta gamma s : ℝ} (hbg : beta < gamma) (hs : s ≤ beta) :
    simplexCutoff beta gamma s = 1 := by
  unfold simplexCutoff
  rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr hs) (sub_pos.mpr hbg).le), sub_zero]

theorem simplexCutoff_eq_zero {beta gamma s : ℝ} (hbg : beta < gamma) (hs : gamma ≤ s) :
    simplexCutoff beta gamma s = 0 := by
  unfold simplexCutoff
  rw [Real.smoothTransition.one_of_one_le ((le_div_iff₀ (sub_pos.mpr hbg)).mpr (by linarith))]
  ring

noncomputable def cutoffDeletion (g chi : ℝ → ℝ) (k s : ℝ) : ℝ :=
  ∫ u, g u * chi (s+u/k)

theorem cutoffDeletion_continuous {g chi : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hchi : Continuous chi) (k : ℝ) :
    Continuous (cutoffDeletion g chi k) := by
  rw [← continuousOn_univ]
  apply continuousOn_integral_of_compact_support hgc
  · exact (show Continuous (Function.uncurry fun s u : ℝ => g u * chi (s+u/k)) by
      unfold Function.uncurry
      fun_prop).continuousOn
  · intro s u _ hu
    rw [image_eq_zero_of_notMem_tsupport hu, zero_mul]

theorem cutoffDeletion_integrable {g chi : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hchi : Continuous chi) (k s : ℝ) :
    Integrable (fun u => g u * chi (s+u/k)) :=
  (hg.mul (hchi.comp (by fun_prop))).integrable_of_hasCompactSupport hgc.mul_right

theorem cutoffDeletion_nonneg {g chi : ℝ → ℝ} (hg : ∀ u, 0 ≤ g u)
    (hchi : ∀ s, 0 ≤ chi s) (k s : ℝ) : 0 ≤ cutoffDeletion g chi k s :=
  integral_nonneg fun u => mul_nonneg (hg u) (hchi _)

theorem cutoffDeletion_le_mass {g chi : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hchi : Continuous chi)
    (hgn : ∀ u, 0 ≤ g u) (hchi1 : ∀ s, chi s ≤ 1) (k s : ℝ) :
    cutoffDeletion g chi k s ≤ ∫ u, g u := by
  apply integral_mono (cutoffDeletion_integrable hg hgc hchi k s)
    (hg.integrable_of_hasCompactSupport hgc)
  intro u
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (hchi1 _) (hgn u)

theorem cutoffDeletion_eq_mass {g chi : ℝ → ℝ} {k beta B s : ℝ} (hk : 0 < k)
    (hB : ∀ u ∈ Function.support g, u ≤ B)
    (hflat : ∀ x ≤ beta, chi x = 1) (hs : s ≤ beta-B/k) :
    cutoffDeletion g chi k s = ∫ u, g u := by
  apply integral_congr_ae
  filter_upwards [] with u
  by_cases hu : g u = 0
  · simp only [hu, zero_mul]
  · rw [hflat (s+u/k) ?_, mul_one]
    have hub := hB u hu
    have hud := (div_le_div_iff_of_pos_right hk).mpr hub
    linarith

noncomputable def cancellationBracket (g chi : ℝ → ℝ) (lambda k : ℝ) (j : ℕ) (s : ℝ) : ℝ :=
  chi s - (Real.sqrt (((j:ℝ)+1)/k) / Real.sqrt lambda) * cutoffDeletion g chi k s

theorem cancellationBracket_continuous {g chi : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hchi : Continuous chi) (lambda k : ℝ) (j : ℕ) :
    Continuous (cancellationBracket g chi lambda k j) :=
  hchi.sub ((cutoffDeletion_continuous hg hgc hchi k).const_mul _)

theorem cancellationBracket_abs_le_one {g chi : ℝ → ℝ} {lambda k : ℝ}
    (hlambda : 0 < lambda) (hk : 0 < k) (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgn : ∀ u, 0 ≤ g u) (hgi : (∫ u, g u) = Real.sqrt lambda)
    (hchi : Continuous chi) (hchi0 : ∀ s, 0 ≤ chi s) (hchi1 : ∀ s, chi s ≤ 1)
    (j : ℕ) (hjk : (j:ℝ)+1 ≤ k) (s : ℝ) :
    |cancellationBracket g chi lambda k j s| ≤ 1 := by
  have hlr : 0 < Real.sqrt lambda := Real.sqrt_pos.mpr hlambda
  have h0 := cutoffDeletion_nonneg hgn hchi0 k s
  have h1 := cutoffDeletion_le_mass hg hgc hchi hgn hchi1 k s
  rw [hgi] at h1
  have ha0 : 0 ≤ Real.sqrt (((j:ℝ)+1)/k) / Real.sqrt lambda := by positivity
  have ha1 : Real.sqrt (((j:ℝ)+1)/k) ≤ 1 := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by norm_num, by rw [one_pow]; exact (div_le_one hk).mpr hjk⟩
  have hprod : (Real.sqrt (((j:ℝ)+1)/k) / Real.sqrt lambda) * cutoffDeletion g chi k s ≤ 1 := calc
    _ ≤ (Real.sqrt (((j:ℝ)+1)/k) / Real.sqrt lambda) * Real.sqrt lambda :=
      mul_le_mul_of_nonneg_left h1 ha0
    _ = Real.sqrt (((j:ℝ)+1)/k) := div_mul_cancel₀ _ hlr.ne'
    _ ≤ 1 := ha1
  have hprodn := mul_nonneg ha0 h0
  unfold cancellationBracket
  rw [abs_le]
  constructor <;> linarith [hchi0 s, hchi1 s]

theorem cancellationBracket_flat {g chi : ℝ → ℝ} {lambda k beta B s : ℝ}
    (hlambda : 0 < lambda) (hk : 0 < k)
    (hgi : (∫ u, g u) = Real.sqrt lambda)
    (hB : ∀ u ∈ Function.support g, u ≤ B) (hB0 : 0 ≤ B)
    (hflat : ∀ x ≤ beta, chi x = 1) (hs : s ≤ beta-B/k) (j : ℕ) :
    cancellationBracket g chi lambda k j s = 1 - Real.sqrt (((j:ℝ)+1)/k) := by
  unfold cancellationBracket
  rw [cutoffDeletion_eq_mass hk hB hflat hs, hgi,
    hflat s (by linarith [div_nonneg hB0 hk.le]),
    div_mul_cancel₀ _ (Real.sqrt_pos.mpr hlambda).ne']

theorem concentrated_function_sq {p b : ℝ → ℝ} (hp : Continuous p)
    (hpc : HasCompactSupport p) (hpn : ∀ u, 0 ≤ p u) (hpi : (∫ u, p u) = 1)
    (hb : Continuous b) (hb1 : ∀ s, |b s| ≤ 1)
    {beta d eta : ℝ} (hd : 0 < d) (heta : 0 ≤ eta)
    (hflat : ∀ s ≤ beta, b s^2 ≤ eta) (j : ℕ)
    (hmean : (j : ℝ) * (∫ u, u*p u) + d ≤ beta) :
    (∫ t : Fin j → ℝ, productDensity p j t * b (coordinateSum t)^2) ≤
      eta + ((j : ℝ) * ∫ u, (u - ∫ v, v*p v)^2 * p u) / d^2 := by
  let m : ℝ := (j : ℝ) * (∫ u, u*p u)
  have hD := productDensity_integrable hp hpc j
  have hC : Integrable (fun t : Fin j → ℝ =>
      productDensity p j t * b (coordinateSum t)^2) := by
    simpa only [mul_comm] using
      (poly_productDensity_integrable hp hpc
        (P := fun t : Fin j → ℝ => b (coordinateSum t)^2) (by
          unfold coordinateSum
          fun_prop))
  have hV : Integrable (fun t : Fin j → ℝ =>
      (coordinateSum t - m)^2 * productDensity p j t) :=
    poly_productDensity_integrable hp hpc (by unfold coordinateSum; fun_prop)
  have hle (t : Fin j → ℝ) :
      productDensity p j t * b (coordinateSum t)^2 ≤
        eta * productDensity p j t +
        ((coordinateSum t - m)^2 * productDensity p j t) / d^2 := by
    have hDn := productDensity_nonneg hpn j t
    have hvn : 0 ≤ ((coordinateSum t-m)^2 * productDensity p j t) / d^2 := by positivity
    by_cases ht : coordinateSum t ≤ beta
    · have hb2 := hflat _ ht
      nlinarith [mul_le_mul_of_nonneg_left hb2 hDn]
    · have hdm : d ≤ coordinateSum t - m := by dsimp only [m]; linarith
      have hd2 : 0 < d^2 := sq_pos_of_pos hd
      have hv2 : d^2 ≤ (coordinateSum t - m)^2 := by nlinarith
      have hDle : productDensity p j t ≤
          ((coordinateSum t - m)^2 * productDensity p j t) / d^2 := by
        apply (le_div_iff₀ hd2).mpr
        nlinarith [mul_le_mul_of_nonneg_left hv2 hDn]
      have hb2 : b (coordinateSum t)^2 ≤ 1 := by
        have := abs_le.mp (hb1 (coordinateSum t))
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hb2 hDn, mul_nonneg heta hDn]
  have hint := integral_mono hC ((hD.const_mul eta).add (hV.div_const (d^2))) hle
  dsimp only [Pi.add_apply] at hint
  rw [integral_add (hD.const_mul eta) (hV.div_const (d^2)), integral_const_mul,
    productDensity_integral hpi, mul_one, integral_div] at hint
  change _ ≤ eta + (∫ t : Fin j → ℝ,
    (coordinateSum t - (j:ℝ)*(∫ u, u*p u))^2 * productDensity p j t) / d^2 at hint
  rwa [coordinateSum_variance hp hpc hpi] at hint

theorem profile_first_moment_nonneg {g : ℝ → ℝ}
    (hs : Function.support g ⊆ Ioi 0) : 0 ≤ ∫ u, u * g u^2 := by
  apply integral_nonneg
  intro u
  by_cases hu : g u = 0
  · simp only [hu, zero_pow (by decide : 2 ≠ 0), mul_zero, Pi.zero_apply, le_refl]
  · exact mul_nonneg (hs hu).le (sq_nonneg _)

theorem scaled_level_moment_bound {g : ℝ → ℝ} {k : ℝ} (hk : 0 < k)
    (hm : 0 ≤ ∫ u, u*g u^2) (j : ℕ) (hjk : (j:ℝ) ≤ k) :
    (j:ℝ) * (∫ u, u * scaledProfileDensity g k u) ≤ ∫ u, u*g u^2 := by
  rw [scaledProfileDensity_moment g hk]
  have : (j:ℝ) / k ≤ 1 := (div_le_one hk).mpr hjk
  have h := mul_le_mul_of_nonneg_right this hm
  simpa only [div_mul_eq_mul_div, mul_div_assoc, one_mul] using h

theorem scaled_level_variance_bound {g : ℝ → ℝ} {k : ℝ} (hk : 0 < k)
    (j : ℕ) (hjk : (j:ℝ) ≤ k) :
    (j:ℝ) * (∫ u, (u-∫ v, v * scaledProfileDensity g k v)^2 *
      scaledProfileDensity g k u) ≤ (∫ u, (u-∫ v, v*g v^2)^2 * g u^2)/k := by
  rw [scaledProfileDensity_moment g hk, scaledProfileDensity_variance g hk]
  have hv : 0 ≤ ∫ u, (u-∫ v, v*g v^2)^2 * g u^2 :=
    integral_nonneg fun u => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hdiv : (j:ℝ) / k^2 ≤ 1/k := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hk) hk).mpr
    nlinarith
  have h := mul_le_mul_of_nonneg_right hdiv hv
  simpa only [div_mul_eq_mul_div, mul_div_assoc, one_mul] using h

theorem scaled_cutoff_mass_bounds {g chi : ℝ → ℝ} {k beta : ℝ}
    (hk : 0 < k) (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgs : Function.support g ⊆ Ioi 0) (hg2 : (∫ u, g u^2) = 1)
    (hchi : Continuous chi) (hchi0 : ∀ s, 0 ≤ chi s) (hchi1 : ∀ s, chi s ≤ 1)
    (hflat : ∀ s ≤ beta, chi s = 1) (hmu : (∫ u, u*g u^2) < beta)
    (j : ℕ) (hjk : (j:ℝ) ≤ k) :
    let d := beta - ∫ u, u*g u^2
    let v := ∫ u, (u-∫ v, v*g v^2)^2 * g u^2
    1-v/(k*d^2) ≤ (∫ t : Fin j → ℝ,
      productDensity (scaledProfileDensity g k) j t * chi (coordinateSum t)^2) ∧
    (∫ t : Fin j → ℝ,
      productDensity (scaledProfileDensity g k) j t * chi (coordinateSum t)^2) ≤ 1 := by
  dsimp only
  have hp := scaledProfileDensity_continuous hg k
  have hpc := scaledProfileDensity_compact hgc hk.ne'
  have hpn : ∀ u, 0 ≤ scaledProfileDensity g k u := fun u => mul_nonneg hk.le (sq_nonneg _)
  have hpi := scaledProfileDensity_integral hk hg2
  constructor
  · have hb := concentrated_cutoff_mass hp hpc hpn hpi hchi hchi0 hchi1
      (sub_pos.mpr hmu) hflat j (by
        have := scaled_level_moment_bound hk (profile_first_moment_nonneg hgs) j hjk
        linarith)
    have hv := scaled_level_variance_bound (g := g) hk j hjk
    have hd2 : 0 < (beta - ∫ u, u*g u^2)^2 := sq_pos_of_pos (sub_pos.mpr hmu)
    have hdiv := div_le_div_of_nonneg_right hv hd2.le
    have heq : (∫ u, (u-∫ v, v*g v^2)^2 * g u^2)/k/(beta-∫ u, u*g u^2)^2 =
      (∫ u, (u-∫ v, v*g v^2)^2 * g u^2)/(k*(beta-∫ u, u*g u^2)^2) := by rw [div_div]
    rw [heq] at hdiv
    linarith
  · exact cutoff_mass_le_one hp hpc hpn hpi hchi hchi0 hchi1 j

theorem one_sub_sqrt_level_sq {k r : ℝ} (hk : 0 < k) (hr : 0 ≤ r)
    (j : ℕ) (hupper : (j:ℝ)+1 ≤ k) (hlower : k-r ≤ (j:ℝ)+1) :
    (1-Real.sqrt (((j:ℝ)+1)/k))^2 ≤ (r/k)^2 := by
  have hx : 0 ≤ ((j:ℝ)+1)/k := by positivity
  have hx1 : ((j:ℝ)+1)/k ≤ 1 := (div_le_one hk).mpr hupper
  have hs : Real.sqrt (((j:ℝ)+1)/k)^2 = ((j:ℝ)+1)/k := Real.sq_sqrt hx
  have hs0 := Real.sqrt_nonneg (((j:ℝ)+1)/k)
  have hs1 : Real.sqrt (((j:ℝ)+1)/k) ≤ 1 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by simpa using hx1⟩
  have hxs : ((j:ℝ)+1)/k ≤ Real.sqrt (((j:ℝ)+1)/k) := by nlinarith
  have hl : 1-r/k ≤ ((j:ℝ)+1)/k := by
    have := (div_le_div_iff_of_pos_right hk).mpr hlower
    rw [sub_div, div_self hk.ne'] at this
    exact this
  have hrk : 0 ≤ r/k := div_nonneg hr hk.le
  nlinarith

theorem scaled_cancellation_integral_bound {g chi : ℝ → ℝ}
    {lambda k r beta B : ℝ} (hlambda : 0 < lambda) (hk : 0 < k) (hr : 0 ≤ r)
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgs : Function.support g ⊆ Ioi 0) (hgn : ∀ u, 0 ≤ g u)
    (hg2 : (∫ u, g u^2) = 1) (hg1 : (∫ u, g u) = Real.sqrt lambda)
    (hB : ∀ u ∈ Function.support g, u ≤ B) (hB0 : 0 ≤ B)
    (hchi : Continuous chi) (hchi0 : ∀ s, 0 ≤ chi s) (hchi1 : ∀ s, chi s ≤ 1)
    (hflat : ∀ s ≤ beta, chi s = 1) (hmu : (∫ u, u*g u^2) < beta)
    (hBk : B/k ≤ (beta - ∫ u, u*g u^2)/2)
    (j : ℕ) (hupper : (j:ℝ)+1 ≤ k) (hlower : k-r ≤ (j:ℝ)+1) :
    let d := beta - ∫ u, u*g u^2
    let v := ∫ u, (u-∫ v, v*g v^2)^2 * g u^2
    (∫ t : Fin j → ℝ, productDensity (scaledProfileDensity g k) j t *
      cancellationBracket g chi lambda k j (coordinateSum t)^2) ≤
      (r/k)^2 + 4*v/(k*d^2) := by
  dsimp only
  let d : ℝ := beta - ∫ u, u*g u^2
  have hd : 0 < d := sub_pos.mpr hmu
  have hp := scaledProfileDensity_continuous hg k
  have hpc := scaledProfileDensity_compact hgc hk.ne'
  have hpn : ∀ u, 0 ≤ scaledProfileDensity g k u := fun u => mul_nonneg hk.le (sq_nonneg _)
  have hpi := scaledProfileDensity_integral hk hg2
  have hb := concentrated_function_sq hp hpc hpn hpi
    (cancellationBracket_continuous hg hgc hchi lambda k j)
    (cancellationBracket_abs_le_one hlambda hk hg hgc hgn hg1 hchi hchi0 hchi1 j hupper)
    (beta := beta-B/k) (d := d/2) (div_pos hd (by norm_num)) (sq_nonneg (r/k))
    (fun s hs => by
      rw [cancellationBracket_flat hlambda hk hg1 hB hB0 hflat hs j]
      exact one_sub_sqrt_level_sq hk hr j hupper hlower) j (by
      have := scaled_level_moment_bound hk (profile_first_moment_nonneg hgs) j (by linarith)
      dsimp only [d]
      linarith)
  have hv := scaled_level_variance_bound (g := g) hk j (by linarith)
  have hdiv := div_le_div_of_nonneg_right hv (sq_nonneg (d/2))
  have heq (v : ℝ) : v/k/(d/2)^2 = 4*v/(k*d^2) := by
    field_simp
    norm_num
  rw [heq] at hdiv
  exact hb.trans (add_le_add (le_refl _) hdiv)

noncomputable def alpha (lambda : ℝ) (j : ℕ) : ℝ := lambda^j / j.factorial

theorem alpha_pos {lambda : ℝ} (hlambda : 0 < lambda) (j : ℕ) : 0 < alpha lambda j :=
  div_pos (pow_pos hlambda j) (by exact_mod_cast Nat.factorial_pos j)

theorem alpha_succ (lambda : ℝ) (j : ℕ) :
    alpha lambda (j+1) = alpha lambda j * lambda / ((j:ℝ)+1) := by
  unfold alpha
  rw [pow_succ, Nat.factorial_succ]
  push_cast
  rw [div_mul_eq_mul_div, div_div, mul_comm (j.factorial:ℝ)]

theorem sqrt_alpha_succ_ratio {lambda k : ℝ} (hlambda : 0 < lambda) (hk : 0 < k) (j : ℕ) :
    Real.sqrt (alpha lambda j) * (Real.sqrt k / k) /
      Real.sqrt (alpha lambda (j+1)) = Real.sqrt (((j:ℝ)+1)/k) / Real.sqrt lambda := by
  have ha := alpha_pos hlambda j
  have ha1 := alpha_pos hlambda (j+1)
  have hlr := Real.sqrt_pos.mpr hlambda
  have hkr := Real.sqrt_pos.mpr hk
  have har := Real.sqrt_pos.mpr ha
  have ha1r := Real.sqrt_pos.mpr ha1
  have hj : 0 < (j:ℝ)+1 := by positivity
  have hs : (Real.sqrt (((j:ℝ)+1)/k))^2 = ((j:ℝ)+1)/k :=
    Real.sq_sqrt (div_nonneg hj.le hk.le)
  have heq : (Real.sqrt (alpha lambda j) * (Real.sqrt k / k) /
      Real.sqrt (alpha lambda (j+1)))^2 =
      (Real.sqrt (((j:ℝ)+1)/k) / Real.sqrt lambda)^2 := by
    rw [div_pow, mul_pow, div_pow, Real.sq_sqrt ha.le, Real.sq_sqrt hk.le,
      Real.sq_sqrt ha1.le, div_pow, hs, Real.sq_sqrt hlambda.le, alpha_succ]
    field_simp [ha.ne', hk.ne', hlambda.ne', hj.ne']
  have hleft : 0 ≤ Real.sqrt (alpha lambda j) * (Real.sqrt k / k) /
      Real.sqrt (alpha lambda (j+1)) := by positivity
  have hright : 0 ≤ Real.sqrt (((j:ℝ)+1)/k) / Real.sqrt lambda := by positivity
  nlinarith

theorem productProfile_snoc (g : ℝ → ℝ) (k : ℝ) (j : ℕ) (t : Fin j → ℝ) (u : ℝ) :
    productProfile g k (j+1) (Fin.snoc t u) = productProfile g k j t * Real.sqrt k * g (k*u) := by
  unfold productProfile
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  ring

theorem coordinateSum_snoc (j : ℕ) (t : Fin j → ℝ) (u : ℝ) :
    coordinateSum (Fin.snoc t u) = coordinateSum t + u := by
  unfold coordinateSum
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

noncomputable def levelFunction (g chi : ℝ → ℝ) (lambda k r : ℝ)
    (j : ℕ) (t : Fin j → ℝ) : ℝ :=
  ((-1:ℝ)^j / (Real.sqrt r * Real.sqrt (alpha lambda j))) *
    productProfile g k j t * chi (coordinateSum t)

noncomputable def deleteCoordinate {j : ℕ} (f : (Fin (j+1) → ℝ) → ℝ)
    (t : Fin j → ℝ) : ℝ := ∫ u : ℝ, f (Fin.snoc t u)

theorem levelFunction_delete {g chi : ℝ → ℝ} {lambda k r : ℝ}
    (hk : 0 < k) (j : ℕ) (t : Fin j → ℝ) :
    deleteCoordinate (levelFunction g chi lambda k r (j+1)) t =
      ((-1:ℝ)^(j+1) / (Real.sqrt r * Real.sqrt (alpha lambda (j+1)))) *
      productProfile g k j t * (Real.sqrt k / k) * cutoffDeletion g chi k (coordinateSum t) := by
  unfold deleteCoordinate levelFunction
  simp only [productProfile_snoc, coordinateSum_snoc]
  let A := ((-1:ℝ)^(j+1) / (Real.sqrt r * Real.sqrt (alpha lambda (j+1)))) *
    productProfile g k j t * Real.sqrt k
  have heq : (fun u => ((-1:ℝ)^(j+1) / (Real.sqrt r * Real.sqrt (alpha lambda (j+1)))) *
      (productProfile g k j t * Real.sqrt k * g (k*u)) * chi (coordinateSum t+u)) =
      fun u => A * (g (k*u) * chi (coordinateSum t+(k*u)/k)) := by
    funext u
    dsimp only [A]
    rw [mul_div_cancel_left₀ _ hk.ne']
    ring
  rw [heq, integral_const_mul]
  rw [Measure.integral_comp_mul_left (fun u => g u * chi (coordinateSum t+u/k)) k,
    abs_of_pos (inv_pos.mpr hk), smul_eq_mul]
  unfold cutoffDeletion
  dsimp only [A]
  ring

end LargePrimeGaps

end OAI
