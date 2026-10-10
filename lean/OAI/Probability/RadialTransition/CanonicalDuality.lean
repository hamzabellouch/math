import OAI.Probability.RadialTransition.DensityMixtures

namespace OAI

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

theorem canonical_le_grand_dual {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {B t β d : ℝ} (hstable : StableWith φ B) (ht : 0 < t) (hβ : 0 ≤ β) (hd : 0 ≤ d)
    (hc : ∀ r : ℝ≥0, 2 ≤ (r : ℝ) → φ r ≤ 0)
    (hlim : Tendsto (fun z : ℝ × ℕ => finiteCanonical φ t z.1 z.2 β)
      (thermodynamicFilter d) (nhds (canonicalThermo φ t β d))) (h : ℝ) :
    h * d - canonicalThermo φ t β d ≤ grandPressure φ t β h := by
  have hH := hlim.comp (floor_tendsto_thermodynamicFilter hd)
  have hlo := ((floor_density_tendsto hd).const_mul h).sub hH
  have hhi := (grandPressure_spec hφ hb hstable ht hβ hc h).1
  apply le_of_tendsto_of_tendsto hlo hhi
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  let n : ℕ := ⌊d * L ^ 3⌋₊
  have hterm := (grandPartition_summable hφ hb hstable hL.le hβ t h).le_tsum n
    (fun N _ => mul_nonneg (Real.exp_pos _).le (partition_nonneg L N β))
  have hh := Real.log_le_log (mul_pos (Real.exp_pos _) (partition_pos hφ hb hL n β)) hterm
  rw [Real.log_mul (Real.exp_ne_zero _) (partition_pos hφ hb hL n β).ne', Real.log_exp] at hh
  have hden : 0 < t * L ^ 3 := by positivity
  change h * ((n : ℝ) / L ^ 3) - finiteCanonical φ t L n β ≤ finiteGrandPressure φ t L β h
  dsimp only [finiteGrandPressure, finiteCanonical]
  apply (le_div_iff₀ hden).mpr
  have he : (h * ((n : ℝ) / L ^ 3) - -Real.log (partition φ L n β) / (t * L ^ 3)) *
      (t * L ^ 3) = t * h * n + Real.log (partition φ L n β) := by field_simp; ring
  rw [he]
  exact hh

theorem grandPartition_tail_le_one {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {B t L β h D : ℝ} (hstable : StableWith φ B) (ht : 0 < t) (hL : 0 ≤ L)
    (hβ : 0 ≤ β) (hD : Real.exp (β * B + t * h + 1) ≤ D) :
    (∑' n : {n : ℕ // ⌊D * L ^ 3⌋₊ < n},
      Real.exp (t * h * (n : ℕ)) * partition φ L n β) ≤ 1 := by
  have hD0 : 0 < D := (Real.exp_pos _).trans_le hD
  let m := ⌊D * L ^ 3⌋₊
  let h' := h + t⁻¹
  have hs := grandPartition_summable hφ hb hstable hL hβ t h'
  have hfac : Summable (fun n : ℕ => Real.exp (-D * L ^ 3) *
      (Real.exp (t * h' * n) * partition φ L n β)) := hs.mul_left _
  have hsub := (grandPartition_summable hφ hb hstable hL hβ t h).subtype (fun n => m < n)
  have hh (n : {n : ℕ // m < n}) :
      Real.exp (t * h * (n : ℕ)) * partition φ L n β ≤
      Real.exp (-D * L ^ 3) * (Real.exp (t * h' * (n : ℕ)) * partition φ L n β) := by
    have hn : D * L ^ 3 < (n : ℕ) := (Nat.floor_lt (by positivity)).mp n.property
    have hfield : t * h' = t * h + 1 := by dsimp [h']; field_simp
    rw [← mul_assoc, ← Real.exp_add, hfield]
    apply mul_le_mul_of_nonneg_right _ (partition_nonneg L n β)
    apply Real.exp_le_exp.mpr
    nlinarith
  have hsum := hsub.tsum_le_tsum hh (hfac.subtype (fun n => m < n))
  have hsuble := Summable.tsum_subtype_le _ {n : ℕ | m < n}
    (fun n => mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (Real.exp_pos _).le (partition_nonneg L n β))) hfac
  have hh' := hsum.trans hsuble
  rw [tsum_mul_left] at hh'
  have hbound := mul_le_mul_of_nonneg_left
    (grandPartition_bounds hφ hb hstable hL hβ t h').2 (Real.exp_pos (-D * L ^ 3)).le
  have heq : β * B + t * h' = β * B + t * h + 1 := by dsimp [h']; field_simp; ring
  rw [heq, ← Real.exp_add] at hbound
  apply hh'.trans (hbound.trans _)
  apply Real.exp_le_one_iff.mpr
  nlinarith [pow_nonneg hL (3 : ℕ)]

theorem finiteGrandPressure_max_term {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {B t L β h D : ℝ} (hstable : StableWith φ B) (ht : 0 < t) (hL : 1 ≤ L)
    (hβ : 0 ≤ β) (hD : Real.exp (β * B + t * h + 1) ≤ D) :
    ∃ n : ℕ, (n : ℝ) / L ^ 3 ∈ Icc 0 D ∧
      finiteGrandPressure φ t L β h ≤
        h * ((n : ℝ) / L ^ 3) - finiteCanonical φ t L n β +
          Real.log ((D + 2) * L ^ 3) / (t * L ^ 3) := by
  classical
  have hL0 : 0 < L := by linarith
  have hD0 : 0 < D := (Real.exp_pos _).trans_le hD
  let m := ⌊D * L ^ 3⌋₊
  let F (n : ℕ) := Real.exp (t * h * n) * partition φ L n β
  have hs : Summable F := grandPartition_summable hφ hb hstable hL0.le hβ t h
  obtain ⟨n, hn, hnmax⟩ := (Finset.range (m+1)).exists_max_image F (by simp)
  have hnle : n ≤ m := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hn
  have hnD : (n : ℝ) ≤ D * L ^ 3 :=
    (by exact_mod_cast hnle : (n : ℝ) ≤ m).trans (Nat.floor_le (by positivity))
  have hge1 : 1 ≤ F n := by
    have hh := hnmax 0 (by simp)
    simpa [F, partition_zero] using hh
  have htail : (∑' k : {k : ℕ // k ∉ Finset.range (m+1)}, F k) ≤ 1 := by
    let e : {k : ℕ // k ∉ Finset.range (m+1)} ≃ {k : ℕ // m < k} :=
      Equiv.subtypeEquivProp (by funext k; apply propext; simp)
    have he := e.tsum_eq (fun k => F k)
    change (∑' k : {k : ℕ // k ∉ Finset.range (m+1)}, F k) =
      (∑' k : {k : ℕ // m < k}, F k) at he
    rw [he]
    exact grandPartition_tail_le_one hφ hb hstable ht hL0.le hβ hD
  have hgrand : grandPartition φ t L β h ≤ ((m : ℝ) + 2) * F n := by
    rw [grandPartition, ← hs.sum_add_tsum_compl (s := Finset.range (m+1))]
    have hsum := Finset.sum_le_card_nsmul (Finset.range (m+1)) F (F n) hnmax
    simp only [Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at hsum
    change (∑ k ∈ Finset.range (m+1), F k) + (∑' k : {k : ℕ // k ∉ Finset.range (m+1)}, F k) ≤ _
    nlinarith
  have hV : 1 ≤ L ^ 3 := one_le_pow₀ hL
  have hmD : (m : ℝ) + 2 ≤ (D + 2) * L ^ 3 := by
    have hm := Nat.floor_le (show 0 ≤ D * L ^ 3 by positivity)
    dsimp only [m]
    nlinarith
  have hgrand' := hgrand.trans (mul_le_mul_of_nonneg_right hmD (by linarith : 0 ≤ F n))
  have hlog := Real.log_le_log (show 0 < grandPartition φ t L β h by
    linarith [(grandPartition_bounds hφ hb hstable hL0.le hβ t h).1]) hgrand'
  have hFp : 0 < F n := by linarith
  rw [Real.log_mul (by positivity) hFp.ne'] at hlog
  have hFlog : Real.log (F n) = t * h * n + Real.log (partition φ L n β) := by
    simp only [F, Real.log_mul (Real.exp_ne_zero _) (partition_pos hφ hb hL0 n β).ne', Real.log_exp]
  rw [hFlog] at hlog
  refine ⟨n, ⟨by positivity, (div_le_iff₀ (by positivity : 0 < L ^ 3)).mpr hnD⟩, ?_⟩
  have hden : 0 < t * L ^ 3 := by positivity
  change Real.log (grandPartition φ t L β h) / (t * L ^ 3) ≤ _
  apply (div_le_iff₀ hden).mpr
  have he : (h * ((n : ℝ) / L ^ 3) - finiteCanonical φ t L n β +
      Real.log ((D + 2) * L ^ 3) / (t * L ^ 3)) * (t * L ^ 3) =
      Real.log ((D + 2) * L ^ 3) + (t * h * n + Real.log (partition φ L n β)) := by
    dsimp only [finiteCanonical]
    field_simp
    ring
  rw [he]
  exact hlog

theorem tendsto_log_volume_error {C t : ℝ} (hC : 0 < C) (ht : 0 < t) :
    Tendsto (fun L : ℝ => Real.log (C * L ^ 3) / (t * L ^ 3)) atTop (nhds 0) := by
  have hx : Tendsto (fun L : ℝ => C * L ^ 3) atTop atTop :=
    Tendsto.const_mul_atTop hC (tendsto_pow_atTop (by norm_num : 3 ≠ 0))
  have hh := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hx
  simp only [one_mul, add_zero, pow_one, Function.comp_def] at hh
  have hh' := hh.const_mul (C / t)
  simp only [mul_zero] at hh'
  apply hh'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  field_simp

theorem grandPressure_exists_maximizing_density {φ : Potential}
    (hφ : Continuous φ) (hb : IsBoundedPotential φ) {B t β : ℝ}
    (hstable : StableWith φ B) (ht : 0 < t) (hβ : 0 ≤ β)
    (hc : ∀ r : ℝ≥0, 2 ≤ (r : ℝ) → φ r ≤ 0)
    (hlim : ∀ d : ℝ, 0 ≤ d → Tendsto (fun z : ℝ × ℕ => finiteCanonical φ t z.1 z.2 β)
      (thermodynamicFilter d) (nhds (canonicalThermo φ t β d))) (h : ℝ) :
    ∃ d : ℝ, 0 ≤ d ∧ grandPressure φ t β h = h * d - canonicalThermo φ t β d := by
  let D := Real.exp (β * B + t * h + 1)
  have hD : 0 < D := Real.exp_pos _
  let L (j : ℕ) : ℝ := j + 1
  have hLs (j : ℕ) : 1 ≤ L j := by dsimp [L]; linarith [Nat.cast_nonneg (α := ℝ) j]
  have hL : Tendsto L atTop atTop := by
    exact tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  choose N hNd hNmax using fun j : ℕ =>
    finiteGrandPressure_max_term hφ hb hstable ht (hLs j) hβ (le_refl D)
  obtain ⟨d, hd, σ, hσ, hden⟩ := isCompact_Icc.tendsto_subseq hNd
  have hside : Tendsto (L ∘ σ) atTop atTop := hL.comp hσ.tendsto_atTop
  have hconfig : Tendsto (fun j => (L (σ j), N (σ j))) atTop (thermodynamicFilter d) := by
    apply tendsto_inf.mpr
    exact ⟨tendsto_comap_iff.mpr hside, tendsto_comap_iff.mpr hden⟩
  have hcost := (hlim d hd.1).comp hconfig
  have hp := (grandPressure_spec hφ hb hstable ht hβ hc h).1.comp hside
  have hu := ((hden.const_mul h).sub hcost).add
    ((tendsto_log_volume_error (show 0 < D + 2 by linarith) ht).comp hside)
  simp only [add_zero, Function.comp_def] at hp hu
  have hle := le_of_tendsto_of_tendsto hp hu (Eventually.of_forall (fun j => hNmax (σ j)))
  exact ⟨d, hd.1, le_antisymm hle
    (canonical_le_grand_dual hφ hb hstable ht hβ hd.1 hc (hlim d hd.1) h)⟩

theorem convex_density_support {F : ℝ → ℝ} (hF : ConvexOn ℝ (Ici 0) F)
    {d : ℝ} (hd : 0 < d) : ∃ h : ℝ, ∀ v : ℝ, 0 ≤ v → F d + h * (v - d) ≤ F v := by
  have hint : d ∈ interior (Ici (0 : ℝ)) := by simpa using hd
  let h := derivWithin F (Iio d) d
  refine ⟨h, fun v hv => ?_⟩
  rcases lt_trichotomy v d with hvd | rfl | hdv
  · have hh := hF.slope_le_of_hasDerivWithinAt_Iio hv hd.le hvd
      (hF.hasDerivWithinAt_leftDeriv_of_mem_interior hint)
    rw [slope_def_field] at hh
    have hmul := (div_le_iff₀ (sub_pos.mpr hvd)).mp hh
    dsimp only [h]
    nlinarith
  · simp
  · have hh := (hF.leftDeriv_le_rightDeriv_of_mem_interior hint).trans
      (hF.le_slope_of_hasDerivWithinAt_Ioi hd.le hv hdv
        (hF.hasDerivWithinAt_rightDeriv_of_mem_interior hint))
    rw [slope_def_field] at hh
    have hmul := (le_div_iff₀ (sub_pos.mpr hdv)).mp hh
    dsimp only [h]
    nlinarith

theorem canonical_grand_duality {φ : Potential}
    (hφ : Continuous φ) (hb : IsBoundedPotential φ) {B t β : ℝ}
    (hstable : StableWith φ B) (ht : 0 < t) (hβ : 0 ≤ β)
    (hc : ∀ r : ℝ≥0, 2 ≤ (r : ℝ) → φ r ≤ 0)
    (hlim : ∀ d : ℝ, 0 ≤ d → Tendsto (fun z : ℝ × ℕ => finiteCanonical φ t z.1 z.2 β)
      (thermodynamicFilter d) (nhds (canonicalThermo φ t β d))) :
    (∀ h : ℝ, grandPressure φ t β h = sSup {v : ℝ | ∃ d ≥ 0, v = h * d - canonicalThermo φ t β d}) ∧
    (∀ d : ℝ, 0 < d → ∃ h : ℝ, canonicalThermo φ t β d = h * d - grandPressure φ t β h ∧
      ∀ j : ℝ, j * d - grandPressure φ t β j ≤ canonicalThermo φ t β d) := by
  have hle (h d : ℝ) (hd : 0 ≤ d) :=
    canonical_le_grand_dual hφ hb hstable ht hβ hd hc (hlim d hd) h
  have hconv : ConvexOn ℝ (Ici 0) (canonicalThermo φ t β) :=
    boxCost_limit_convex (H := fun L N => finiteCanonical φ t L N β)
      (fun s L b hs hL hn m => finiteCanonical_replication hφ hb hβ ht hs hL hc b hn m) hlim
  constructor
  · intro h
    obtain ⟨d, hd, he⟩ := grandPressure_exists_maximizing_density hφ hb hstable ht hβ hc hlim h
    apply le_antisymm
    · apply le_csSup
      · exact ⟨grandPressure φ t β h, fun v ⟨r, hr, hv⟩ => hv ▸ hle h r hr⟩
      · exact ⟨d, hd, he⟩
    · apply csSup_le
      · exact ⟨h * 0 - canonicalThermo φ t β 0, 0, le_rfl, rfl⟩
      · rintro v ⟨r, hr, rfl⟩
        exact hle h r hr
  · intro d hd
    obtain ⟨h, hs⟩ := convex_density_support hconv hd
    obtain ⟨v, hv, he⟩ := grandPressure_exists_maximizing_density hφ hb hstable ht hβ hc hlim h
    refine ⟨h, ?_, ?_⟩
    · have := hs v hv
      have := hle h d hd.le
      rw [he] at this ⊢
      linarith
    · intro j
      linarith [hle j d hd.le]

end RadialTransition

end

end OAI
