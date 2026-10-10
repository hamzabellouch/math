import Mathlib

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology

namespace FirstCut

theorem incompatible_pole_bounds {a : ℝ → ℝ → ℝ} {B C c δ : ℝ}
    (hc : 0 < c) (hδ : 0 < δ)
    (hlo : ∀ s, 0 < s → s < δ → -B * s ≤ s ^ 2 * a s (s ^ 4))
    (hup : ∀ s, 0 < s → s < δ →
      a s (s ^ 4) ≤ C - c / (s ^ 2 + s ^ 4)) : False := by
  let P : ℝ → ℝ := fun s => (C * s ^ 2 + B * s) * (1 + s ^ 2)
  have hlim : Tendsto P (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hcont : Continuous P := by dsimp [P]; fun_prop
    convert hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1
    simp [P]
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), c ≤ P s := by
    filter_upwards [Ioo_mem_nhdsGT hδ] with s hs
    have hs0 : 0 < s := hs.1
    have hsq : 0 < s ^ 2 := sq_pos_of_pos hs0
    have hden : 0 < s ^ 2 + s ^ 4 := by positivity
    have hlo' := hlo s hs0 hs.2
    have hup' := (div_le_iff₀ hden).mp (show c / (s ^ 2 + s ^ 4) ≤
        C - a s (s ^ 4) by linarith [hup s hs0 hs.2])
    have hprod := mul_le_mul_of_nonneg_right hlo' (show 0 ≤ 1 + s ^ 2 by positivity)
    dsimp [P]
    nlinarith
  have hc0 : c ≤ 0 := ge_of_tendsto hlim hev
  exact (not_le_of_gt hc) hc0

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem radial_hessian_identity (A : LinearMap.BilinForm ℝ E)
    (hsymm : ∀ v w, A v w = A w v) {p e : E} {s : ℝ}
    (hpe : inner ℝ p e = 0) (hee : inner ℝ e e = 1)
    (hrad : ∀ v, A (p + s • e) v = inner ℝ (p + s • e) v) :
    A p p = inner ℝ p p + s ^ 2 * (A e e - 1) := by
  have h₁ := hrad p
  have h₂ := hrad e
  have hep : inner ℝ e p = 0 := by rw [real_inner_comm, hpe]
  simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left,
    inner_add_left, real_inner_smul_left, hep, hpe, hee, mul_zero, add_zero,
    zero_add, mul_one] at h₁ h₂
  rw [hsymm e p] at h₁
  nlinarith [congrArg (fun t : ℝ => s * t) h₂]

end InnerProduct

theorem concave_linear_lower {f : ℝ → ℝ} {b s K L : ℝ}
    (hb : 0 < b) (hf : ConcaveOn ℝ (Icc 0 b) f)
    (hzero : f 0 = K) (hend : -L ≤ f b) (hs : s ∈ Icc 0 b) :
    K - ((K + L) / b) * s ≤ f s := by
  have hratio : 0 ≤ s / b := div_nonneg hs.1 hb.le
  have hratio1 : s / b ≤ 1 := (div_le_one hb).mpr hs.2
  have hcomb := hf.2 (show (0 : ℝ) ∈ Icc 0 b from ⟨le_rfl, hb.le⟩)
    (show b ∈ Icc 0 b from ⟨hb.le, le_rfl⟩)
    (sub_nonneg.mpr hratio1) hratio (show (1 - s / b) + s / b = 1 by ring)
  have harg : (1 - s / b) • (0 : ℝ) + (s / b) • b = s := by
    simp [smul_eq_mul, ne_of_gt hb]
  rw [harg, hzero] at hcomb
  simp only [smul_eq_mul] at hcomb
  have hmul := mul_le_mul_of_nonneg_left hend hratio
  have hid : K - (K + L) / b * s = (1 - s / b) * K + (s / b) * (-L) := by
    ring
  rw [hid]
  linarith

theorem incompatible_transverse_pole {f : ℝ → ℝ} {L C c δ : ℝ}
    (hc : 0 < c) (hδ : 0 < δ)
    (hlo : ∀ h, 0 < h → h < δ → L ≤ f h)
    (hup : ∀ h, 0 < h → h < δ → f h ≤ C - c / h) : False := by
  have hlim : Tendsto (fun h : ℝ => (C - L) * h) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul
      (tendsto_id.mono_left nhdsWithin_le_nhds) :
        Tendsto (fun h : ℝ => (C - L) * h) (𝓝[>] 0) (𝓝 ((C - L) * 0)))
  have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ), c ≤ (C - L) * h := by
    filter_upwards [Ioo_mem_nhdsGT hδ] with h hh
    have h₁ := hlo h hh.1 hh.2
    have h₂ := (div_le_iff₀ hh.1).mp
      (show c / h ≤ C - f h by linarith [hup h hh.1 hh.2])
    have h₃ := mul_le_mul_of_nonneg_right (show C - f h ≤ C - L by linarith) hh.1.le
    exact h₂.trans h₃
  exact (not_le_of_gt hc) (ge_of_tendsto hlim hev)

section Segment

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def HasTrialPole (A : ℝ → ℝ → LinearMap.BilinForm ℝ E) (ξ : E) : Prop :=
  ∃ C c δ : ℝ, 0 < c ∧ 0 < δ ∧
    ∀ h, 0 < h → h < δ → ∀ s, |s| < δ →
      A h s ξ ξ ≤ C - c / (s ^ 2 + h)

theorem transverse_pairing_zero
    {A : ℝ → ℝ → LinearMap.BilinForm ℝ E} {a b : ℝ} {e k : E}
    (ha : 0 < a) (hb : 0 < b)
    (hconc : ∀ h, 0 < h → h < 1 → ∀ ξ : E, inner ℝ ξ e = 0 →
      ConcaveOn ℝ (Icc (-a) b) (fun s => A h s ξ ξ))
    (hends : ∀ ξ : E, ∃ L δ : ℝ, 0 < δ ∧
      ∀ h, 0 < h → h < δ → -L ≤ A h (-a) ξ ξ ∧ -L ≤ A h b ξ ξ)
    (htrial : ∀ ξ : E, inner ℝ ξ k ≠ 0 → HasTrialPole A ξ)
    {ξ : E} (hξ : inner ℝ ξ e = 0) : inner ℝ ξ k = 0 := by
  by_contra hne
  obtain ⟨C, c, δ₁, hc, hδ₁, hpole⟩ := htrial ξ hne
  obtain ⟨L, δ₂, hδ₂, hends'⟩ := hends ξ
  let δ := min δ₁ (min δ₂ 1)
  have hδ : 0 < δ := lt_min hδ₁ (lt_min hδ₂ zero_lt_one)
  apply incompatible_transverse_pole hc hδ
    (f := fun h => A h 0 ξ ξ) (L := -L) (C := C)
  · intro h hh hhδ
    have hhδ₂ : h < δ₂ := lt_of_lt_of_le hhδ ((min_le_right _ _).trans (min_le_left _ _))
    have hh1 : h < 1 := lt_of_lt_of_le hhδ ((min_le_right _ _).trans (min_le_right _ _))
    have hab : -a ≤ b := by linarith
    have hc' := (hconc h hh hh1 ξ hξ).ge_on_segment
      (show -a ∈ Icc (-a) b from ⟨le_rfl, hab⟩)
      (show b ∈ Icc (-a) b from ⟨hab, le_rfl⟩)
      (show (0 : ℝ) ∈ segment ℝ (-a) b by
        rw [segment_eq_Icc hab]; exact ⟨by linarith, hb.le⟩)
    have hend' := hends' h hh hhδ₂
    exact (le_min hend'.1 hend'.2).trans hc'
  · intro h hh hhδ
    have hhδ₁ : h < δ₁ := lt_of_lt_of_le hhδ (min_le_left _ _)
    simpa using hpole h hh hhδ₁ 0 (by simpa using hδ₁)

theorem parallel_of_transverse_pairing_zero {e k : E}
    (he : inner ℝ e e = 1)
    (h : ∀ ξ : E, inner ℝ ξ e = 0 → inner ℝ ξ k = 0) :
    k = (inner ℝ e k) • e := by
  let q := k - (inner ℝ e k) • e
  have hqe : inner ℝ q e = 0 := by
    dsimp [q]
    rw [inner_sub_left, real_inner_smul_left, he, mul_one, real_inner_comm k e]
    exact sub_self _
  have hqk : inner ℝ q k = 0 := h q hqe
  have hqq : inner ℝ q q = 0 := by
    conv_rhs => rw [← sub_self (0 : ℝ)]
    dsimp [q] at ⊢
    rw [inner_sub_right, inner_smul_right]
    change inner ℝ q k - inner ℝ e k * inner ℝ q e = 0 - 0
    rw [hqk, hqe, mul_zero]
  have hqzero : q = 0 := (inner_self_eq_zero (𝕜 := ℝ)).mp hqq
  exact sub_eq_zero.mp hqzero

theorem no_first_cut_kernel
    {A : ℝ → ℝ → LinearMap.BilinForm ℝ E} {a b : ℝ} {p e k : E}
    (ha : 0 < a) (hb : 0 < b) (he : inner ℝ e e = 1)
    (hkp : inner ℝ k p = 0)
    (hsymm : ∀ h, 0 < h → h < 1 → ∀ s ∈ Icc (-a) b,
      ∀ v w, A h s v w = A h s w v)
    (hrad : ∀ h, 0 < h → h < 1 → ∀ s ∈ Icc (-a) b,
      ∀ v, A h s (p + s • e) v = inner ℝ (p + s • e) v)
    (hconc : ∀ h, 0 < h → h < 1 → ∀ ξ : E, inner ℝ ξ e = 0 →
      ConcaveOn ℝ (Icc (-a) b) (fun s => A h s ξ ξ))
    (hends : ∀ ξ : E, ∃ L δ : ℝ, 0 < δ ∧
      ∀ h, 0 < h → h < δ → -L ≤ A h (-a) ξ ξ ∧ -L ≤ A h b ξ ξ)
    (htrial : ∀ ξ : E, inner ℝ ξ k ≠ 0 → HasTrialPole A ξ) : k = 0 := by
  by_contra hk
  have hpar : k = (inner ℝ e k) • e :=
    parallel_of_transverse_pairing_zero he
      (fun ξ hξ => transverse_pairing_zero ha hb hconc hends htrial hξ)
  have hα : inner ℝ e k ≠ 0 := by
    intro hzero
    rw [hzero, zero_smul] at hpar
    exact hk hpar
  have hpe : inner ℝ p e = 0 := by
    have hkp' := hkp
    rw [hpar, real_inner_smul_left] at hkp'
    rw [real_inner_comm]
    exact (mul_eq_zero.mp hkp').resolve_left hα
  obtain ⟨C, c, δ₁, hc, hδ₁, hpole⟩ := htrial e hα
  obtain ⟨L, δ₂, hδ₂, hends'⟩ := hends p
  let δ := min δ₁ (min δ₂ (min b 1))
  have hδ : 0 < δ := lt_min hδ₁ (lt_min hδ₂ (lt_min hb zero_lt_one))
  have hδ₁' : δ ≤ δ₁ := min_le_left _ _
  have hδ₂' : δ ≤ δ₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hδb : δ ≤ b := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hδ1 : δ ≤ 1 := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  have hs4 : ∀ s : ℝ, 0 < s → s < δ → 0 < s ^ 4 ∧ s ^ 4 ≤ s := by
    intro s hs hsδ
    refine ⟨pow_pos hs 4, ?_⟩
    have hs1 : s ≤ 1 := (hsδ.trans_le hδ1).le
    have hs3 : s ^ 3 ≤ 1 := pow_le_one₀ hs.le hs1
    calc
      s ^ 4 = s ^ 3 * s := by ring
      _ ≤ 1 * s := mul_le_mul_of_nonneg_right hs3 hs.le
      _ = s := one_mul s
  apply incompatible_pole_bounds (a := fun s h => A h s e e)
    (B := (inner ℝ p p + L) / b) (C := C) hc hδ
  · intro s hs hsδ
    obtain ⟨hs4pos, hs4le⟩ := hs4 s hs hsδ
    have hs41 : s ^ 4 < 1 := hs4le.trans_lt (hsδ.trans_le hδ1)
    have hs4δ₂ : s ^ 4 < δ₂ := hs4le.trans_lt (hsδ.trans_le hδ₂')
    have hsmem : s ∈ Icc (-a) b := ⟨by linarith, (hsδ.trans_le hδb).le⟩
    have h0mem : (0 : ℝ) ∈ Icc (-a) b := ⟨by linarith, hb.le⟩
    have hf : ConcaveOn ℝ (Icc 0 b) (fun s' => A (s ^ 4) s' p p) :=
      (hconc (s ^ 4) hs4pos hs41 p hpe).subset
        (by intro t ht; exact ⟨by linarith [ht.1], ht.2⟩) (convex_Icc 0 b)
    have hzero : A (s ^ 4) 0 p p = inner ℝ p p := by
      simpa using hrad (s ^ 4) hs4pos hs41 0 h0mem p
    have hlinear := concave_linear_lower hb hf hzero
      (hends' (s ^ 4) hs4pos hs4δ₂).2
      (show s ∈ Icc 0 b from ⟨hs.le, hsmem.2⟩)
    have hid := radial_hessian_identity (A (s ^ 4) s)
      (hsymm (s ^ 4) hs4pos hs41 s hsmem) hpe he
      (hrad (s ^ 4) hs4pos hs41 s hsmem)
    rw [hid] at hlinear
    nlinarith [sq_nonneg s]
  · intro s hs hsδ
    obtain ⟨hs4pos, hs4le⟩ := hs4 s hs hsδ
    apply hpole (s ^ 4) hs4pos (hs4le.trans_lt (hsδ.trans_le hδ₁')) s
    rw [abs_of_pos hs]
    exact hsδ.trans_le hδ₁'

end Segment

end FirstCut

open Set Filter
open scoped Topology

namespace FirstCut

theorem index_trial_bound {F : Type*} [AddCommGroup F] [Module ℝ F]
    (Q : LinearMap.BilinForm ℝ F) (hsymm : ∀ x y, Q x y = Q y x)
    (V K : F) {H : ℝ} (hpos : 0 < Q K K)
    (hmin : ∀ a : ℝ, H ≤ Q (V + a • K) (V + a • K)) :
    H ≤ Q V V - (Q V K) ^ 2 / Q K K := by
  calc
    H ≤ Q (V + (-(Q V K) / Q K K) • K)
        (V + (-(Q V K) / Q K K) • K) := hmin _
    _ = Q V V - (Q V K) ^ 2 / Q K K := by
      simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
        LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right]
      rw [hsymm K V]
      field_simp [ne_of_gt hpos]
      ring

theorem scalar_trial_bound {H U R P : ℝ} (hP : 0 < P)
    (htest : ∀ a : ℝ, H ≤ U + 2 * a * R + a ^ 2 * P) :
    H ≤ U - R ^ 2 / P := by
  have h := htest (-R / P)
  have hid : U + 2 * (-R / P) * R + (-R / P) ^ 2 * P = U - R ^ 2 / P := by
    field_simp [ne_of_gt hP]
    ring
  simpa only [hid] using h

theorem quadratic_upper_of_local_min {f : ℝ → ℝ}
    (hf : ContDiffAt ℝ 2 f 0) (hmin : IsLocalMin f 0) (hzero : f 0 = 0) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ s, |s| < δ → f s ≤ C * s ^ 2 := by
  have hfd : ContDiffAt ℝ 1 (fderiv ℝ f) 0 := hf.fderiv_right (by norm_num)
  obtain ⟨K, t, ht, hK⟩ := hfd.exists_lipschitzOnWith
  have hdiff : ∀ᶠ x in 𝓝 (0 : ℝ), DifferentiableAt ℝ f x :=
    (hf.eventually (by norm_num)).mono (fun x hx => hx.differentiableAt (by norm_num))
  obtain ⟨δ, hδ, hsubset⟩ := Metric.mem_nhds_iff.mp (inter_mem ht hdiff)
  have h0 : (0 : ℝ) ∈ Metric.ball 0 δ := Metric.mem_ball_self hδ
  have hD0 : fderiv ℝ f 0 = 0 := hmin.fderiv_eq_zero
  refine ⟨(K : ℝ) + 1, δ, by positivity, hδ, ?_⟩
  intro s hs
  have hseg : ∀ u ∈ segment ℝ (0 : ℝ) s, ‖u‖ ≤ ‖s‖ := by
    intro u hu
    simpa using norm_sub_le_of_mem_segment hu
  have hball : ∀ u ∈ segment ℝ (0 : ℝ) s, u ∈ Metric.ball 0 δ := by
    intro u hu
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using
      (hseg u hu).trans_lt hs
  have hbound : ∀ u ∈ segment ℝ (0 : ℝ) s, ‖fderiv ℝ f u‖ ≤ (K : ℝ) * ‖s‖ := by
    intro u hu
    have h := hK.norm_sub_le (hsubset (hball u hu)).1 (hsubset h0).1
    rw [hD0, sub_zero, sub_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hseg u hu) K.coe_nonneg)
  have hm := (convex_segment (0 : ℝ) s).norm_image_sub_le_of_norm_fderiv_le
    (fun u hu => (hsubset (hball u hu)).2) hbound
    (left_mem_segment ℝ (0 : ℝ) s) (right_mem_segment ℝ (0 : ℝ) s)
  rw [hzero, sub_zero, sub_zero] at hm
  have hsquare : ‖s‖ * ‖s‖ = s ^ 2 := by
    simpa only [Real.norm_eq_abs, pow_two] using (sq_abs s)
  have hfinal : ‖f s‖ ≤ (K : ℝ) * s ^ 2 := by
    calc
      ‖f s‖ ≤ (K : ℝ) * ‖s‖ * ‖s‖ := hm
      _ = (K : ℝ) * s ^ 2 := by rw [mul_assoc, hsquare]
  calc
    f s ≤ ‖f s‖ := le_abs_self _
    _ ≤ (K : ℝ) * s ^ 2 := hfinal
    _ ≤ ((K : ℝ) + 1) * s ^ 2 := by nlinarith [sq_nonneg s]

theorem two_parameter_quadratic_upper {P : ℝ × ℝ → ℝ}
    (hP : ContDiffAt ℝ 2 P (0, 0))
    (hmin : ∀ᶠ s in 𝓝 (0 : ℝ), 0 ≤ P (s, 0)) (hzero : P (0, 0) = 0) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ s h : ℝ,
      |s| < δ → 0 ≤ h → h < δ → P (s, h) ≤ C * (s ^ 2 + h) := by
  have hslice : ContDiffAt ℝ 2 (fun s : ℝ => P (s, 0)) 0 :=
    hP.comp (f := fun s : ℝ => (s, (0 : ℝ))) 0
      (contDiffAt_id.prodMk contDiffAt_const)
  have hlocal : IsLocalMin (fun s : ℝ => P (s, 0)) 0 := by
    simpa only [IsLocalMin, IsMinFilter, hzero] using hmin
  obtain ⟨C, δ₁, hC, hδ₁, hquad⟩ := quadratic_upper_of_local_min hslice hlocal hzero
  obtain ⟨K, t, ht, hK⟩ := (hP.of_le (show (1 : WithTop ℕ∞) ≤ 2 by norm_num)).exists_lipschitzOnWith
  obtain ⟨δ₂, hδ₂, ht₂⟩ := Metric.mem_nhds_iff.mp ht
  refine ⟨C + (K : ℝ) + 1, min δ₁ δ₂, by positivity, lt_min hδ₁ hδ₂, ?_⟩
  intro s h hs hh hhδ
  have hs₁ : |s| < δ₁ := hs.trans_le (min_le_left _ _)
  have hs₂ : |s| < δ₂ := hs.trans_le (min_le_right _ _)
  have hh₂ : |h| < δ₂ := by rw [abs_of_nonneg hh]; exact hhδ.trans_le (min_le_right _ _)
  have hmem : (s, h) ∈ t := ht₂ (by
    simpa only [Metric.mem_ball, Prod.dist_eq, dist_zero_right, Real.norm_eq_abs,
      max_lt_iff] using And.intro hs₂ hh₂)
  have hmem0 : (s, 0) ∈ t := ht₂ (by
    simpa only [Metric.mem_ball, Prod.dist_eq, dist_zero_right, Real.norm_eq_abs,
      abs_zero, max_lt_iff] using And.intro hs₂ hδ₂)
  have hdiff := hK.norm_sub_le hmem hmem0
  have hnorm : ‖(s, h) - (s, 0)‖ = h := by
    simp [Prod.norm_def, Real.norm_eq_abs, abs_of_nonneg hh, hh]
  rw [hnorm] at hdiff
  have hdiff' : P (s, h) - P (s, 0) ≤ (K : ℝ) * h :=
    (le_abs_self _).trans hdiff
  have hsquare : 0 ≤ s ^ 2 := sq_nonneg _
  have hquad' := hquad s hs₁
  nlinarith [K.coe_nonneg, mul_nonneg K.coe_nonneg hsquare, mul_nonneg hC.le hh]

theorem pole_of_smooth_index_coefficients
    {P U R H : ℝ × ℝ → ℝ}
    (hP : ContDiffAt ℝ 2 P (0, 0))
    (hmin : ∀ᶠ s in 𝓝 (0 : ℝ), 0 ≤ P (s, 0)) (hzero : P (0, 0) = 0)
    (hU : ContinuousAt U (0, 0)) (hR : ContinuousAt R (0, 0))
    (hRzero : R (0, 0) ≠ 0)
    (hpositive : ∀ᶠ q in 𝓝 (0, 0), 0 < q.2 → 0 < P q)
    (htest : ∀ᶠ q in 𝓝 (0, 0), 0 < q.2 →
      ∀ a : ℝ, H q ≤ U q + 2 * a * R q + a ^ 2 * P q) :
    ∃ C c δ : ℝ, 0 < c ∧ 0 < δ ∧ ∀ h, 0 < h → h < δ → ∀ s, |s| < δ →
      H (s, h) ≤ C - c / (s ^ 2 + h) := by
  obtain ⟨B, δ₁, hB, hδ₁, hbound⟩ := two_parameter_quadratic_upper hP hmin hzero
  have hR2 : 0 < R (0, 0) ^ 2 := sq_pos_of_ne_zero hRzero
  have hUbound : ∀ᶠ q in 𝓝 ((0, 0) : ℝ × ℝ), U q < U (0, 0) + 1 :=
    hU.eventually_lt continuousAt_const (by linarith)
  have hRbound : ∀ᶠ q in 𝓝 ((0, 0) : ℝ × ℝ), R (0, 0) ^ 2 / 2 < R q ^ 2 :=
    continuousAt_const.eventually_lt (hR.pow 2) (by linarith)
  obtain ⟨δ₂, hδ₂, hgood⟩ := Metric.mem_nhds_iff.mp
    (hUbound.and (hRbound.and (hpositive.and htest)))
  refine ⟨U (0, 0) + 1, (R (0, 0) ^ 2 / 2) / B, min δ₁ δ₂,
    div_pos (by positivity) hB, lt_min hδ₁ hδ₂, ?_⟩
  intro h hh hhδ s hs
  have hh₁ : h < δ₁ := hhδ.trans_le (min_le_left _ _)
  have hs₁ : |s| < δ₁ := hs.trans_le (min_le_left _ _)
  have hh₂ : |h| < δ₂ := by rw [abs_of_pos hh]; exact hhδ.trans_le (min_le_right _ _)
  have hs₂ : |s| < δ₂ := hs.trans_le (min_le_right _ _)
  obtain ⟨hUb, hRb, hPb, htrial⟩ := hgood (show (s, h) ∈ Metric.ball (0, 0) δ₂ by
    simpa only [Metric.mem_ball, Prod.dist_eq, dist_zero_right, Real.norm_eq_abs,
      max_lt_iff] using And.intro hs₂ hh₂)
  have hposP := hPb hh
  have hscalar := scalar_trial_bound hposP (htrial hh)
  have hden : 0 < s ^ 2 + h := by positivity
  have hPbound := hbound s h hs₁ hh.le hh₁
  have hquot : (R (0, 0) ^ 2 / 2) / B / (s ^ 2 + h) ≤ R (s, h) ^ 2 / P (s, h) := by
    rw [div_div]
    apply (div_le_div_iff₀ (mul_pos hB hden) hposP).mpr
    calc
      (R (0, 0) ^ 2 / 2) * P (s, h) ≤
          (R (0, 0) ^ 2 / 2) * (B * (s ^ 2 + h)) :=
        mul_le_mul_of_nonneg_left hPbound (by positivity)
      _ ≤ R (s, h) ^ 2 * (B * (s ^ 2 + h)) :=
        mul_le_mul_of_nonneg_right hRb.le (by positivity)
  linarith

end FirstCut

open Set Filter MeasureTheory
open scoped Topology

namespace JacobiIndex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def integrand (R : ℝ → E →L[ℝ] E) (U V : ℝ → E) (t : ℝ) : ℝ :=
  inner ℝ (deriv U t) (deriv V t) - inner ℝ (R t (U t)) (V t)

noncomputable def indexForm (R : ℝ → E →L[ℝ] E) (U V : ℝ → E) : ℝ :=
  ∫ t in (0 : ℝ)..1, integrand R U V t

theorem indexForm_symm {R : ℝ → E →L[ℝ] E}
    (hR : ∀ t u v, inner ℝ (R t u) v = inner ℝ u (R t v)) (U V : ℝ → E) :
    indexForm R U V = indexForm R V U := by
  unfold indexForm
  congr 1
  funext t
  simp only [integrand]
  rw [real_inner_comm (deriv U t) (deriv V t), hR t (U t) (V t),
    real_inner_comm (U t) (R t (V t))]

theorem continuous_integrand {R : ℝ → E →L[ℝ] E} {U V : ℝ → E}
    (hR : Continuous R) (hU : ContDiff ℝ 1 U) (hV : ContDiff ℝ 1 V) :
    Continuous (integrand R U V) :=
  (hU.continuous_deriv_one.inner hV.continuous_deriv_one).sub
    ((hR.clm_apply hU.continuous).inner hV.continuous)

theorem indexForm_jacobi {R : ℝ → E →L[ℝ] E} {U K : ℝ → E}
    (hR : Continuous R)
    (hsymm : ∀ t u v, inner ℝ (R t u) v = inner ℝ u (R t v))
    (hU : ContDiff ℝ 1 U) (hK : ContDiff ℝ 2 K)
    (hjac : ∀ t ∈ Icc (0 : ℝ) 1, deriv (deriv K) t = -(R t (K t))) :
    indexForm R U K = inner ℝ (U 1) (deriv K 1) - inner ℝ (U 0) (deriv K 0) := by
  have hK' : ContDiff ℝ 1 (deriv K) := hK.deriv'
  unfold indexForm
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t => inner ℝ (U t) (deriv K t))
  · intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
    have hd := HasDerivAt.inner ℝ
      ((hU.differentiable (by norm_num)) t).hasDerivAt
      ((hK'.differentiable (by norm_num)) t).hasDerivAt
    have heq : integrand R U K t =
        inner ℝ (U t) (deriv (deriv K) t) + inner ℝ (deriv U t) (deriv K t) := by
      simp only [integrand, hjac t ht', inner_neg_right, ← hsymm]
      ring
    rw [heq]
    exact hd
  · exact (continuous_integrand hR hU (hK.of_le (by norm_num))).intervalIntegrable (μ := volume) 0 1

theorem indexForm_null_pairing {R : ℝ → E →L[ℝ] E} {U K : ℝ → E}
    (hR : Continuous R)
    (hsymm : ∀ t u v, inner ℝ (R t u) v = inner ℝ u (R t v))
    (hU : ContDiff ℝ 1 U) (hK : ContDiff ℝ 2 K)
    (hjac : ∀ t ∈ Icc (0 : ℝ) 1, deriv (deriv K) t = -(R t (K t)))
    (hend : U 1 = 0) :
    indexForm R U K = -inner ℝ (U 0) (deriv K 0) := by
  rw [indexForm_jacobi hR hsymm hU hK hjac, hend, inner_zero_left, zero_sub]

theorem indexForm_null_energy {R : ℝ → E →L[ℝ] E} {K : ℝ → E}
    (hR : Continuous R)
    (hsymm : ∀ t u v, inner ℝ (R t u) v = inner ℝ u (R t v))
    (hK : ContDiff ℝ 2 K)
    (hjac : ∀ t ∈ Icc (0 : ℝ) 1, deriv (deriv K) t = -(R t (K t)))
    (hstart : K 0 = 0) (hend : K 1 = 0) :
    indexForm R K K = 0 := by
  rw [indexForm_null_pairing hR hsymm (hK.of_le (by norm_num)) hK hjac hend,
    hstart, inner_zero_left, neg_zero]

theorem indexForm_trial_expansion {R : ℝ → E →L[ℝ] E} {U K : ℝ → E}
    (hR : Continuous R)
    (hsymm : ∀ t u v, inner ℝ (R t u) v = inner ℝ u (R t v))
    (hU : ContDiff ℝ 1 U) (hK : ContDiff ℝ 1 K) (a : ℝ) :
    indexForm R (U + a • K) (U + a • K) =
      indexForm R U U + 2 * a * indexForm R U K + a ^ 2 * indexForm R K K := by
  have hid : integrand R (U + a • K) (U + a • K) = fun t =>
      integrand R U U t + 2 * a * integrand R U K t + a ^ 2 * integrand R K K t := by
    funext t
    have hUt := (hU.differentiable (by norm_num)) t
    have hKt := (hK.differentiable (by norm_num)) t
    simp only [integrand, deriv_add hUt (hKt.const_smul a), deriv_const_smul a hKt,
      Pi.add_apply, Pi.smul_apply, map_add, map_smul, inner_add_left, inner_add_right,
      real_inner_smul_left, inner_smul_right]
    rw [real_inner_comm (deriv K t) (deriv U t), hsymm t (K t) (U t),
      real_inner_comm (K t) (R t (U t))]
    ring
  unfold indexForm
  rw [hid]
  have hUU := (continuous_integrand hR hU hU).intervalIntegrable (μ := volume) 0 1
  have hUK := (continuous_integrand hR hU hK).intervalIntegrable (μ := volume) 0 1
  have hKK := (continuous_integrand hR hK hK).intervalIntegrable (μ := volume) 0 1
  rw [intervalIntegral.integral_add (hUU.add (hUK.const_mul (2 * a)))
      (hKK.const_mul (a ^ 2)), intervalIntegral.integral_add hUU (hUK.const_mul (2 * a)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

theorem initial_derivative_perp_radial {R : ℝ → E →L[ℝ] E} {K : ℝ → E} {p : E}
    (hR : Continuous R)
    (hsymm : ∀ t u v, inner ℝ (R t u) v = inner ℝ u (R t v))
    (hK : ContDiff ℝ 2 K)
    (hjac : ∀ t ∈ Icc (0 : ℝ) 1, deriv (deriv K) t = -(R t (K t)))
    (hstart : K 0 = 0) (hend : K 1 = 0)
    (hrad : ∀ t ∈ Icc (0 : ℝ) 1, R t p = 0) :
    inner ℝ (deriv K 0) p = 0 := by
  let U : ℝ → E := fun t => (1 - t) • p
  have hU : ContDiff ℝ 2 U := by dsimp [U]; fun_prop
  have hUder : deriv U = fun _ => -p := by
    funext t
    have h := ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).smul_const p
    simpa [U] using h.deriv
  have hUjac : ∀ t ∈ Icc (0 : ℝ) 1, deriv (deriv U) t = -(R t (U t)) := by
    intro t ht
    rw [hUder]
    simp [U, hrad t ht]
  have hcross := indexForm_jacobi hR hsymm (hK.of_le (by norm_num)) hU hUjac
  rw [hstart, hend, inner_zero_left, inner_zero_left, sub_self] at hcross
  rw [indexForm_symm hsymm K U] at hcross
  have hcross' := indexForm_null_pairing hR hsymm (hU.of_le (by norm_num)) hK hjac
    (show U 1 = 0 by simp [U])
  have hUzero : U 0 = p := by simp [U]
  rw [hUzero, real_inner_comm] at hcross'
  linarith

theorem jacobi_minimizes_index {R : ℝ → E →L[ℝ] E} {Y X : ℝ → E}
    (hR : Continuous R)
    (hsymm : ∀ t u v, inner ℝ (R t u) v = inner ℝ u (R t v))
    (hX : ContDiff ℝ 1 X) (hY : ContDiff ℝ 2 Y)
    (hjac : ∀ t ∈ Icc (0 : ℝ) 1, deriv (deriv Y) t = -(R t (Y t)))
    (hstart : X 0 = Y 0) (hend : X 1 = Y 1)
    (hmin : ∀ Z : ℝ → E, ContDiff ℝ 1 Z → Z 0 = 0 → Z 1 = 0 →
      0 ≤ indexForm R Z Z) :
    indexForm R Y Y ≤ indexForm R X X := by
  let Z := X - Y
  have hZ : ContDiff ℝ 1 Z := hX.sub (hY.of_le (by norm_num))
  have hZ0 : Z 0 = 0 := by simp [Z, hstart]
  have hZ1 : Z 1 = 0 := by simp [Z, hend]
  have hcross := indexForm_jacobi hR hsymm hZ hY hjac
  rw [hZ0, hZ1, inner_zero_left, inner_zero_left, sub_self,
    indexForm_symm hsymm Z Y] at hcross
  have hexp := indexForm_trial_expansion hR hsymm (hY.of_le (by norm_num)) hZ (1 : ℝ)
  have hsum : Y + (1 : ℝ) • Z = X := by simp [Z]
  rw [hsum, hcross] at hexp
  have hnonneg := hmin Z hZ hZ0 hZ1
  linarith

end JacobiIndex

open Set Filter MeasureTheory
open scoped Topology

namespace JacobiIndex

universe u

variable {H F : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [FiniteDimensional ℝ H] [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def parameterDerivative (f : H → ℝ → F) (q : H) (t : ℝ) : H →L[ℝ] F :=
  fderiv ℝ (fun q => f q t) q

omit [FiniteDimensional ℝ H] in
theorem contDiff_parameterDerivative {f : H → ℝ → F} {k : ℕ}
    (hf : ContDiff ℝ (k + 1 : ℕ) (Function.uncurry f)) :
    ContDiff ℝ k (Function.uncurry (parameterDerivative f)) := by
  have hg : ContDiff ℝ (k + 1 : ℕ)
      (fun z : (H × ℝ) × H => f z.2 z.1.2) :=
    hf.comp (contDiff_snd.prodMk (contDiff_fst.snd))
  have hh := ContDiff.fderiv (f := fun p : H × ℝ => fun q : H => f q p.2)
    (g := fun p : H × ℝ => p.1) hg (contDiff_fst : ContDiff ℝ k (fun p : H × ℝ => p.1))
    (show (k : WithTop ℕ∞) + 1 ≤ (k + 1 : ℕ) by simp)
  exact hh

theorem continuous_parameterIntegral {f : H → ℝ → F}
    (hf : Continuous (Function.uncurry f)) :
    Continuous (fun q => ∫ t in (0 : ℝ)..1, f q t) := by
  have hcont := continuous_parametric_integral_of_continuous
    (μ := volume) hf (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))
  convert hcont using 1
  funext q
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]

theorem hasFDerivAt_parameterIntegral {f : H → ℝ → F}
    (hf : ContDiff ℝ 1 (Function.uncurry f)) (q₀ : H) :
    HasFDerivAt (fun q => ∫ t in (0 : ℝ)..1, f q t)
      (∫ t in (0 : ℝ)..1, parameterDerivative f q₀ t) q₀ := by
  have hpd : Continuous (Function.uncurry (parameterDerivative f)) :=
    (contDiff_parameterDerivative (k := 0) hf).continuous
  have hcompact : IsCompact (Metric.closedBall q₀ 1 ×ˢ Icc (0 : ℝ) 1) :=
    (isCompact_closedBall q₀ 1).prod isCompact_Icc
  obtain ⟨K, hK⟩ := hcompact.bddAbove_image hpd.norm.continuousOn
  have hbound : ∀ q ∈ Metric.closedBall q₀ 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖parameterDerivative f q t‖ ≤ K := by
    intro q hq t ht
    exact hK (mem_image_of_mem _ (show (q, t) ∈
      Metric.closedBall q₀ 1 ×ˢ Icc (0 : ℝ) 1 from ⟨hq, ht⟩))
  have hfslice : ∀ q, Continuous (f q) := fun q =>
    hf.continuous.comp (continuous_const.prodMk continuous_id)
  have hpdslice : ∀ q, Continuous (parameterDerivative f q) := fun q =>
    hpd.comp (continuous_const.prodMk continuous_id)
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := f) (F' := parameterDerivative f) (x₀ := q₀)
    (s := Metric.ball q₀ 1) (bound := fun _ => K) (Metric.ball_mem_nhds _ zero_lt_one)
  · exact Filter.Eventually.of_forall (fun q => (hfslice q).aestronglyMeasurable)
  · exact (hfslice q₀).intervalIntegrable _ _
  · exact (hpdslice q₀).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro t ht q hq
    apply hbound q (Metric.ball_subset_closedBall hq) t
    exact Ioc_subset_Icc_self (by simpa only [uIoc_of_le zero_le_one] using ht)
  · exact intervalIntegrable_const
  · apply Filter.Eventually.of_forall
    intro t _ q _
    have hslice : DifferentiableAt ℝ (fun q : H => f q t) q :=
      ((hf.differentiable one_ne_zero).differentiableAt).comp q
        (differentiableAt_id.prodMk (differentiableAt_const t))
    exact hslice.hasFDerivAt

theorem contDiff_parameterIntegral {k : ℕ} {f : H → ℝ → F}
    (hf : ContDiff ℝ k (Function.uncurry f)) :
    ContDiff ℝ k (fun q => ∫ t in (0 : ℝ)..1, f q t) := by
  induction k generalizing F with
  | zero =>
      exact contDiff_zero.mpr (continuous_parameterIntegral hf.continuous)
  | succ k ih =>
      simp only [Nat.cast_add, Nat.cast_one]
      rw [contDiff_succ_iff_hasFDerivAt]
      refine ⟨fun q => ∫ t in (0 : ℝ)..1, parameterDerivative f q t, ?_, ?_⟩
      · exact ih (contDiff_parameterDerivative hf)
      · exact hasFDerivAt_parameterIntegral (hf.of_le (by simp))

end JacobiIndex

namespace JacobiIndex

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem contDiff_indexForm {R : (ℝ × ℝ) → ℝ → E →L[ℝ] E} {U K : ℝ → E} {k : ℕ}
    (hR : ContDiff ℝ k (Function.uncurry R))
    (hU : ContDiff ℝ (k + 1 : ℕ) U) (hK : ContDiff ℝ (k + 1 : ℕ) K) :
    ContDiff ℝ k (fun q => indexForm (R q) U K) := by
  have hUd : ContDiff ℝ k (deriv U) := hU.deriv'
  have hKd : ContDiff ℝ k (deriv K) := hK.deriv'
  have hUInt : ContDiff ℝ k (fun z : (ℝ × ℝ) × ℝ => U z.2) :=
    (hU.of_le (by simp)).comp contDiff_snd
  have hKInt : ContDiff ℝ k (fun z : (ℝ × ℝ) × ℝ => K z.2) :=
    (hK.of_le (by simp)).comp contDiff_snd
  apply contDiff_parameterIntegral
  exact ((hUd.comp contDiff_snd).inner ℝ (hKd.comp contDiff_snd)).sub
    ((hR.clm_apply hUInt).inner ℝ hKInt)

theorem trial_pole_from_index
    {A : ℝ → ℝ → LinearMap.BilinForm ℝ E}
    {R : (ℝ × ℝ) → ℝ → E →L[ℝ] E} {K U : ℝ → E} {ξ : E}
    (hR : ContDiff ℝ 2 (Function.uncurry R))
    (hsymm : ∀ q t u v, inner ℝ (R q t u) v = inner ℝ u (R q t v))
    (hK : ContDiff ℝ 3 K) (hU : ContDiff ℝ 3 U)
    (hjac : ∀ t ∈ Icc (0 : ℝ) 1, deriv (deriv K) t = -(R (0, 0) t (K t)))
    (hKstart : K 0 = 0) (hKend : K 1 = 0) (hUstart : U 0 = ξ) (hUend : U 1 = 0)
    (hpair : inner ℝ ξ (deriv K 0) ≠ 0)
    (hmin : ∀ᶠ s in 𝓝 (0 : ℝ), 0 ≤ indexForm (R (s, 0)) K K)
    (hpositive : ∀ᶠ q in 𝓝 ((0, 0) : ℝ × ℝ), 0 < q.2 → 0 < indexForm (R q) K K)
    (htest : ∀ᶠ q in 𝓝 ((0, 0) : ℝ × ℝ), 0 < q.2 →
      ∀ a : ℝ, A q.2 q.1 ξ ξ ≤ indexForm (R q) (U + a • K) (U + a • K)) :
    FirstCut.HasTrialPole A ξ := by
  have hRslice : ∀ q, Continuous (R q) := fun q =>
    hR.continuous.comp (continuous_const.prodMk continuous_id)
  have hK2 : ContDiff ℝ 2 K := hK.of_le (by norm_num)
  have hK1 : ContDiff ℝ 1 K := hK.of_le (by norm_num)
  have hU1 : ContDiff ℝ 1 U := hU.of_le (by norm_num)
  have hzero : indexForm (R (0, 0)) K K = 0 :=
    indexForm_null_energy (hRslice _) (hsymm _) hK2 hjac hKstart hKend
  have hpairzero : indexForm (R (0, 0)) U K ≠ 0 := by
    rw [indexForm_null_pairing (hRslice _) (hsymm _) hU1 hK2 hjac hUend, hUstart]
    exact neg_ne_zero.mpr hpair
  have htest' : ∀ᶠ q in 𝓝 ((0, 0) : ℝ × ℝ), 0 < q.2 → ∀ a : ℝ,
      A q.2 q.1 ξ ξ ≤ indexForm (R q) U U + 2 * a * indexForm (R q) U K +
        a ^ 2 * indexForm (R q) K K := by
    filter_upwards [htest] with q hq hh a
    rw [← indexForm_trial_expansion (hRslice q) (hsymm q) hU1 hK1 a]
    exact hq hh a
  exact FirstCut.pole_of_smooth_index_coefficients
    (H := fun q => A q.2 q.1 ξ ξ)
    (contDiff_indexForm hR hK hK).contDiffAt hmin hzero
    (contDiff_indexForm hR hU hU).continuous.continuousAt
    (contDiff_indexForm hR hU hK).continuous.continuousAt
    hpairzero hpositive htest'

end JacobiIndex

namespace JacobiIndex

open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem jacobi_eq_zero_of_initial_data {R : ℝ → E →L[ℝ] E} {K : ℝ → E}
    (hR : Continuous R) (hK : ContDiff ℝ 2 K)
    (hjac : ∀ t ∈ Icc (0 : ℝ) 1, deriv (deriv K) t = -(R t (K t)))
    (hstart : K 0 = 0) (hstart' : deriv K 0 = 0) :
    ∀ t ∈ Icc (0 : ℝ) 1, K t = 0 := by
  have hK' : ContDiff ℝ 1 (deriv K) := hK.deriv'
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).bddAbove_image
    hR.norm.continuousOn
  have hbound : ∀ t ∈ Icc (0 : ℝ) 1, ‖R t‖ ≤ B :=
    fun t ht => hB (mem_image_of_mem _ ht)
  let F : ℝ → E × E := fun t => (K t, deriv K t)
  let F' : ℝ → E × E := fun t => (deriv K t, -(R t (K t)))
  have hFcont : ContinuousOn F (Icc (0 : ℝ) 1) :=
    (hK.continuous.prodMk hK'.continuous).continuousOn
  have hFder : ∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt F (F' t) (Ici t) t := by
    intro t ht
    have h := ((hK.differentiable (by norm_num)) t).hasDerivAt.prodMk
      ((hK'.differentiable (by norm_num)) t).hasDerivAt
    rw [hjac t ⟨ht.1, ht.2.le⟩] at h
    exact h.hasDerivWithinAt
  have hFzero : F 0 = 0 := by simp [F, hstart, hstart']
  have hFbound : ∀ t ∈ Ico (0 : ℝ) 1, ‖F' t‖ ≤ max 1 B * ‖F t‖ := by
    intro t ht
    dsimp [F, F']
    simp only [norm_neg]
    apply max_le
    · calc
        ‖deriv K t‖ ≤ max ‖K t‖ ‖deriv K t‖ := le_max_right _ _
        _ ≤ max 1 B * max ‖K t‖ ‖deriv K t‖ := by
          exact le_mul_of_one_le_left (by positivity) (le_max_left _ _)
    · calc
        ‖R t (K t)‖ ≤ ‖R t‖ * ‖K t‖ := (R t).le_opNorm _
        _ ≤ max 1 B * max ‖K t‖ ‖deriv K t‖ := by
          apply mul_le_mul ((hbound t ⟨ht.1, ht.2.le⟩).trans (le_max_right _ _))
            (le_max_left _ _) (norm_nonneg _)
          exact (zero_le_one.trans (le_max_left 1 B))
  have hz := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    hFcont hFder hFzero hFbound
  intro t ht
  exact congrArg Prod.fst (hz t ht)

end JacobiIndex

namespace FirstCut

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem no_first_cut_null_field
    {A : ℝ → ℝ → LinearMap.BilinForm ℝ E}
    {R : (ℝ × ℝ) → ℝ → E →L[ℝ] E} {K : ℝ → E}
    {a b : ℝ} {p e : E}
    (ha : 0 < a) (hb : 0 < b) (he : inner ℝ e e = 1)
    (hsymm : ∀ h, 0 < h → h < 1 → ∀ s ∈ Icc (-a) b,
      ∀ v w, A h s v w = A h s w v)
    (hrad : ∀ h, 0 < h → h < 1 → ∀ s ∈ Icc (-a) b,
      ∀ v, A h s (p + s • e) v = inner ℝ (p + s • e) v)
    (hconc : ∀ h, 0 < h → h < 1 → ∀ ξ : E, inner ℝ ξ e = 0 →
      ConcaveOn ℝ (Icc (-a) b) (fun s => A h s ξ ξ))
    (hends : ∀ ξ : E, ∃ L δ : ℝ, 0 < δ ∧
      ∀ h, 0 < h → h < δ → -L ≤ A h (-a) ξ ξ ∧ -L ≤ A h b ξ ξ)
    (hR : ContDiff ℝ 2 (Function.uncurry R))
    (hRsymm : ∀ q t u v, inner ℝ (R q t u) v = inner ℝ u (R q t v))
    (hRrad : ∀ t ∈ Icc (0 : ℝ) 1, R (0, 0) t p = 0)
    (hK : ContDiff ℝ 3 K)
    (hjac : ∀ t ∈ Icc (0 : ℝ) 1, deriv (deriv K) t = -(R (0, 0) t (K t)))
    (hKstart : K 0 = 0) (hKend : K 1 = 0)
    (hmin : ∀ᶠ s in 𝓝 (0 : ℝ), 0 ≤ JacobiIndex.indexForm (R (s, 0)) K K)
    (hpositive : ∀ᶠ q in 𝓝 ((0, 0) : ℝ × ℝ), 0 < q.2 →
      0 < JacobiIndex.indexForm (R q) K K)
    (htest : ∀ ξ : E, ∀ᶠ q in 𝓝 ((0, 0) : ℝ × ℝ), 0 < q.2 → ∀ α : ℝ,
      A q.2 q.1 ξ ξ ≤ JacobiIndex.indexForm (R q)
        ((fun t => (1 - t) • ξ) + α • K) ((fun t => (1 - t) • ξ) + α • K)) :
    ∀ t ∈ Icc (0 : ℝ) 1, K t = 0 := by
  have hR0 : Continuous (R (0, 0)) :=
    hR.continuous.comp (continuous_const.prodMk continuous_id)
  have hK2 : ContDiff ℝ 2 K := hK.of_le (by norm_num)
  have hkp : inner ℝ (deriv K 0) p = 0 :=
    JacobiIndex.initial_derivative_perp_radial hR0 (hRsymm _) hK2 hjac
      hKstart hKend hRrad
  have htrial : ∀ ξ : E, inner ℝ ξ (deriv K 0) ≠ 0 → HasTrialPole A ξ := by
    intro ξ hξ
    exact JacobiIndex.trial_pole_from_index hR hRsymm hK
      (show ContDiff ℝ 3 (fun t : ℝ => (1 - t) • ξ) by fun_prop)
      hjac hKstart hKend (by simp) (by simp) hξ hmin hpositive (htest ξ)
  have hd0 := no_first_cut_kernel ha hb he hkp hsymm hrad hconc hends htrial
  exact JacobiIndex.jacobi_eq_zero_of_initial_data hR0 hK2 hjac hKstart hd0

end FirstCut

end

end WeakMTWGlobalSupport

end OAI
