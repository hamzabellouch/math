import Mathlib

namespace OAI

/-! Core smoothing, controlled linear cutoffs and exponential scales. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.CoreSmoothing

variable {W E B : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [HasContDiffBump W] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace B] [ChartedSpace E B]

def coreBump : ContDiffBump (0 : W) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

def smoothCore (g : B × W → ℝ) (p : B × W) : ℝ :=
  (1 - (coreBump (W := W)) p.2) * g p

omit [TopologicalSpace B] in
lemma smoothCore_eq_zero {g : B × W → ℝ} {p : B × W} (hp : ‖p.2‖ ≤ 1 / 2) :
    smoothCore g p = 0 := by
  have hb : (coreBump (W := W)) p.2 = 1 := (coreBump (W := W)).one_of_mem_closedBall (by
    simpa [coreBump] using hp)
  simp [smoothCore, hb]

omit [TopologicalSpace B] in
lemma smoothCore_eq {g : B × W → ℝ} {p : B × W} (hp : 1 ≤ ‖p.2‖) :
    smoothCore g p = g p := by
  have hb : (coreBump (W := W)) p.2 = 0 := (coreBump (W := W)).zero_of_le_dist (by
    simpa [coreBump] using hp)
  simp [smoothCore, hb]

theorem contMDiff_smoothCore {g : B × W → ℝ}
    (hg : ∀ p : B × W, p.2 ≠ 0 →
      ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, W)) 𝓘(ℝ, ℝ) ∞ g p) :
    ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, W)) 𝓘(ℝ, ℝ) ∞ (smoothCore g) := by
  intro p
  by_cases hp : p.2 = 0
  · apply contMDiffAt_const.congr_of_eventuallyEq
    have hball : ∀ᶠ y : B × W in 𝓝 p, ‖y.2‖ < 1 / 2 :=
      (continuous_snd.norm.continuousAt.eventually_lt continuousAt_const (by rw [hp]; norm_num))
    filter_upwards [hball] with y hy
    exact smoothCore_eq_zero hy.le
  · exact (contMDiffAt_const.sub
      ((coreBump (W := W)).contDiff.contMDiff.comp contMDiff_snd p)).mul (hg p hp)

variable [IsManifold 𝓘(ℝ, E) ∞ B]

omit [HasContDiffBump W] in

lemma contMDiffAt_vertical {g : B × W → ℝ} {p : B × W}
    (hg : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, W)) 𝓘(ℝ, ℝ) ∞ g p) :
    ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, W)) 𝓘(ℝ, W →L[ℝ] ℝ) ∞
      (fun x : B × W => fderiv ℝ (fun w => g (x.1, w)) x.2) p := by
  let F : (B × W) → W → ℝ := fun x w => g (x.1, w)
  have hF : ContMDiffAt ((𝓘(ℝ, E).prod 𝓘(ℝ, W)).prod 𝓘(ℝ, W)) 𝓘(ℝ, ℝ) ∞
      (Function.uncurry F) (p, p.2) :=
    hg.comp (p, p.2) ((contMDiffAt_fst.comp _ contMDiffAt_fst).prodMk contMDiffAt_snd)
  have h := hF.mfderiv (m := ∞) F Prod.snd contMDiffAt_snd (by simp)
  erw [inTangentCoordinates_model_space] at h
  simpa only [F, mfderiv_eq_fderiv] using h

omit [HasContDiffBump W] in

theorem exists_core_bound [CompactSpace B] [Nonempty B] [ProperSpace W]
    {g : B × W → ℝ}
    (hg : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, W)) 𝓘(ℝ, ℝ) ∞ g) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ b w, ‖w‖ ≤ 1 →
      ‖fderiv ℝ (fun a => g (b, a)) w‖ ≤ M := by
  have hd : Continuous (fun p : B × W => ‖fderiv ℝ (fun a => g (p.1, a)) p.2‖) :=
    (show ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, W)) 𝓘(ℝ, W →L[ℝ] ℝ) ∞
        (fun p : B × W => fderiv ℝ (fun a => g (p.1, a)) p.2) from
      fun p => contMDiffAt_vertical (hg p)).continuous.norm
  have hs : IsCompact ((univ : Set B) ×ˢ Metric.closedBall (0 : W) 1) :=
    isCompact_univ.prod (isCompact_closedBall _ _)
  have hne : ((univ : Set B) ×ˢ Metric.closedBall (0 : W) 1).Nonempty :=
    Set.univ_nonempty.prod (Metric.nonempty_closedBall.mpr (by norm_num))
  obtain ⟨p, _, hp⟩ := hs.exists_isMaxOn hne hd.continuousOn
  refine ⟨‖fderiv ℝ (fun a => g (p.1, a)) p.2‖, norm_nonneg _, ?_⟩
  intro b w hw
  exact hp (show (b, w) ∈ (univ : Set B) ×ˢ Metric.closedBall (0 : W) 1 from
    ⟨Set.mem_univ _, by simpa using hw⟩)

end NearbyLagrangian.CoreSmoothing

namespace NearbyLagrangian.Cutoff

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

def cutoffLinear (β : ℝ → ℝ) (T : ℝ) (v w : W) : ℝ :=
  β (‖w‖ / T) * ⟪v, w⟫_ℝ

def family (G : W → ℝ) (β : ℝ → ℝ) (T R : ℝ) (v w : W) : ℝ :=
  G w - R * cutoffLinear β T v w

lemma differentiableAt_cutoffLinear {β : ℝ → ℝ} {T : ℝ} {v w : W}
    (hβ : DifferentiableAt ℝ β (‖w‖ / T)) (hw : w ≠ 0) :
    DifferentiableAt ℝ (cutoffLinear β T v) w := by
  have hn : DifferentiableAt ℝ (fun x : W => ‖x‖) w := differentiableAt_id.norm ℝ hw
  have hd : DifferentiableAt ℝ (fun x : W => ‖x‖ / T) w := by
    simpa only [div_eq_mul_inv] using hn.mul_const T⁻¹
  apply DifferentiableAt.mul
  · exact hβ.comp w hd
  · exact (innerSL ℝ v).differentiableAt

theorem contDiff_cutoffLinear {β : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hβ : ContDiff ℝ ∞ β) (hflat : ∀ s ∈ Icc (0 : ℝ) 1, β s = 1) (v : W) :
    ContDiff ℝ ∞ (cutoffLinear β T v) := by
  rw [contDiff_iff_contDiffAt]
  intro w
  by_cases hw : w = 0
  · subst w
    apply (innerSL ℝ v).contDiff.contDiffAt.congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds (0 : W) hT] with x hx
    have hnorm : ‖x‖ < T := by simpa using hx
    have hs : ‖x‖ / T ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg (norm_nonneg _) hT.le, (div_le_one hT).mpr hnorm.le⟩
    simp only [cutoffLinear, hflat _ hs, one_mul, innerSL_apply_apply]
  · exact ((hβ.contDiffAt.comp w ((contDiffAt_id.norm ℝ hw).div_const T)).mul
      (innerSL ℝ v).contDiff.contDiffAt)

theorem contDiff_cutoffLinear_joint {β : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hβ : ContDiff ℝ ∞ β) (hflat : ∀ s ∈ Icc (0 : ℝ) 1, β s = 1) :
    ContDiff ℝ ∞ (fun p : W × W => cutoffLinear β T p.1 p.2) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  have hi : ContDiffAt ℝ ∞ (fun p : W × W => ⟪p.1, p.2⟫_ℝ) p :=
    contDiffAt_fst.inner ℝ contDiffAt_snd
  by_cases hp : p.2 = 0
  · apply hi.congr_of_eventuallyEq
    have he : ∀ᶠ y : W × W in 𝓝 p, ‖y.2‖ < T :=
      continuous_snd.norm.continuousAt.eventually_lt continuousAt_const (by simpa [hp] using hT)
    filter_upwards [he] with y hy
    have hs : ‖y.2‖ / T ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg (norm_nonneg _) hT.le, (div_le_one hT).mpr hy.le⟩
    simp only [cutoffLinear, hflat _ hs, one_mul]
  · exact (hβ.contDiffAt.comp p ((contDiffAt_snd.norm ℝ hp).div_const T)).mul hi

lemma norm_fderiv_radialCutoff [Nontrivial W] {β : ℝ → ℝ} {T : ℝ} {w : W}
    (hT : 0 < T) (hβ : DifferentiableAt ℝ β (‖w‖ / T)) (hw : w ≠ 0) :
    ‖fderiv ℝ (fun x : W => β (‖x‖ / T)) w‖ = |deriv β (‖w‖ / T)| / T := by
  have hn : DifferentiableAt ℝ (fun x : W => ‖x‖) w := differentiableAt_id.norm ℝ hw
  have hd : HasFDerivAt (fun x : W => ‖x‖ / T)
      (T⁻¹ • fderiv ℝ (fun x : W => ‖x‖) w) w := by
    simpa only [div_eq_mul_inv] using hn.hasFDerivAt.mul_const T⁻¹
  have hb := hβ.hasDerivAt.comp_hasFDerivAt w hd
  have he : fderiv ℝ (fun x : W => β (‖x‖ / T)) w =
      deriv β (‖w‖ / T) • T⁻¹ • fderiv ℝ (fun x : W => ‖x‖) w := hb.fderiv
  rw [he, norm_smul, norm_smul, norm_fderiv_norm hn]
  simp [Real.norm_eq_abs, abs_of_pos hT, div_eq_mul_inv]

theorem norm_fderiv_cutoffLinear_le [Nontrivial W]
    {β : ℝ → ℝ} {T : ℝ} {v w : W} (hT : 0 < T)
    (hβ : DifferentiableAt ℝ β (‖w‖ / T)) (hw : w ≠ 0) (hv : ‖v‖ = 1) :
    ‖fderiv ℝ (cutoffLinear β T v) w‖ ≤
      |β (‖w‖ / T)| + (‖w‖ / T) * |deriv β (‖w‖ / T)| := by
  have hn : DifferentiableAt ℝ (fun x : W => ‖x‖) w := differentiableAt_id.norm ℝ hw
  have hd : DifferentiableAt ℝ (fun x : W => ‖x‖ / T) w := by
    simpa only [div_eq_mul_inv] using hn.mul_const T⁻¹
  have ha := hβ.comp w hd
  have he : fderiv ℝ (cutoffLinear β T v) w =
      β (‖w‖ / T) • innerSL ℝ v +
      ⟪v, w⟫_ℝ • fderiv ℝ (fun x : W => β (‖x‖ / T)) w := by
    exact (ha.hasFDerivAt.mul (innerSL ℝ v).hasFDerivAt).fderiv
  rw [he]
  have hh : |⟪v, w⟫_ℝ| ≤ ‖w‖ := by simpa [hv] using abs_real_inner_le_norm v w
  calc
    _ ≤ ‖β (‖w‖ / T) • innerSL ℝ v‖ +
        ‖⟪v, w⟫_ℝ • fderiv ℝ (fun x : W => β (‖x‖ / T)) w‖ := norm_add_le _ _
    _ = |β (‖w‖ / T)| + |⟪v, w⟫_ℝ| * (|deriv β (‖w‖ / T)| / T) := by
      rw [norm_smul, norm_smul, norm_fderiv_radialCutoff hT hβ hw,
        innerSL_apply_norm, hv]
      simp only [Real.norm_eq_abs, mul_one]
    _ ≤ |β (‖w‖ / T)| + ‖w‖ * (|deriv β (‖w‖ / T)| / T) := by
      gcongr
    _ = _ := by ring

lemma fderiv_family_core {G : W → ℝ} {β : ℝ → ℝ} {T R : ℝ} {v w : W}
    (hT : 0 < T) (hβ : ∀ s ∈ Icc (0 : ℝ) 1, β s = 1)
    (hw : ‖w‖ < T) (hG : DifferentiableAt ℝ G w) :
    fderiv ℝ (family G β T R v) w = fderiv ℝ G w - R • innerSL ℝ v := by
  have he : family G β T R v =ᶠ[𝓝 w] (fun x : W => G x - R * ⟪v, x⟫_ℝ) := by
    filter_upwards [continuous_norm.continuousAt.eventually (eventually_lt_nhds hw)] with x hx
    have hs : ‖x‖ / T ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg (norm_nonneg _) hT.le, (div_le_one hT).mpr hx.le⟩
    simp only [family, cutoffLinear, hβ _ hs, one_mul]
  exact he.fderiv_eq.trans (hG.hasFDerivAt.sub ((innerSL ℝ v).hasFDerivAt.const_mul R)).fderiv

lemma fderiv_eq_of_eq_outside {G g : W → ℝ} {w : W}
    (heq : ∀ w, 1 ≤ ‖w‖ → G w = g w) (hw : 1 < ‖w‖) :
    fderiv ℝ G w = fderiv ℝ g w := by
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [continuous_norm.continuousAt.eventually (eventually_gt_nhds hw)] with x hx
  exact heq x hx.le

theorem no_inner_critical {G : W → ℝ} {β : ℝ → ℝ} {T R : ℝ} {v w : W}
    (hT : 1 < T) (hR : 0 < R) (hβ : ∀ s ∈ Icc (0 : ℝ) 1, β s = 1)
    (hv : ‖v‖ = 1) (hw : ‖w‖ ≤ 1) (hG : DifferentiableAt ℝ G w)
    (hsmall : ‖fderiv ℝ G w‖ < R) :
    fderiv ℝ (family G β T R v) w ≠ 0 := by
  rw [fderiv_family_core (zero_lt_one.trans hT) hβ (hw.trans_lt hT) hG]
  intro hz
  have he := sub_eq_zero.mp hz
  have hn : ‖fderiv ℝ G w‖ = R := by
    rw [he, norm_smul, innerSL_apply_norm, hv, mul_one, Real.norm_eq_abs, abs_of_pos hR]
  linarith

theorem no_outer_critical [Nontrivial W]
    {G g : W → ℝ} {β : ℝ → ℝ} {T R c D : ℝ} {v w : W}
    (hT : 1 < T) (hR : 0 < R) (hc : 0 < c) (hscale : D * R / c < T)
    (hβ : DifferentiableAt ℝ β (‖w‖ / T))
    (hD : |β (‖w‖ / T)| + (‖w‖ / T) * |deriv β (‖w‖ / T)| ≤ D)
    (hv : ‖v‖ = 1) (hw : T ≤ ‖w‖) (hG : DifferentiableAt ℝ G w)
    (heq : ∀ w, 1 ≤ ‖w‖ → G w = g w)
    (hlower : c * ‖w‖ ≤ ‖fderiv ℝ g w‖) :
    fderiv ℝ (family G β T R v) w ≠ 0 := by
  have hwpos : 0 < ‖w‖ := (zero_lt_one.trans hT).trans_le hw
  have hcut := differentiableAt_cutoffLinear (v := v) hβ (norm_pos_iff.mp hwpos)
  have he : fderiv ℝ (family G β T R v) w =
      fderiv ℝ g w - R • fderiv ℝ (cutoffLinear β T v) w := by
    change fderiv ℝ (fun x => G x - R * cutoffLinear β T v x) w = _
    exact (hG.hasFDerivAt.sub (hcut.hasFDerivAt.const_mul R)).fderiv.trans
      (congrArg (fun d => d - R • fderiv ℝ (cutoffLinear β T v) w)
        (fderiv_eq_of_eq_outside heq (hT.trans_le hw)))
  have hb := (norm_fderiv_cutoffLinear_le (zero_lt_one.trans hT) hβ
    (norm_pos_iff.mp hwpos) hv).trans hD
  rw [he]
  intro hz
  have hn : ‖fderiv ℝ g w‖ ≤ R * D := by
    rw [sub_eq_zero.mp hz, norm_smul, Real.norm_eq_abs, abs_of_pos hR]
    exact mul_le_mul_of_nonneg_left hb hR.le
  have hstrict : D * R < T * c := (div_lt_iff₀ hc).mp hscale
  nlinarith

theorem critical_iff [Nontrivial W]
    {G g : W → ℝ} {β : ℝ → ℝ} {T R c C D : ℝ} {v w : W}
    (hT : 1 < T) (hR : 0 < R) (hc : 0 < c) (hC : C < R)
    (hscale₁ : R / c < T) (hscale₂ : D * R / c < T)
    (hβ : Differentiable ℝ β) (hflat : ∀ s ∈ Icc (0 : ℝ) 1, β s = 1)
    (hD : ∀ s, 0 ≤ s → |β s| + s * |deriv β s| ≤ D)
    (hv : ‖v‖ = 1) (hG : Differentiable ℝ G)
    (heq : ∀ w, 1 ≤ ‖w‖ → G w = g w)
    (hsmall : ∀ w, ‖w‖ ≤ 1 → ‖fderiv ℝ G w‖ < R)
    (hlower : ∀ w, c * ‖w‖ ≤ ‖fderiv ℝ g w‖)
    (hupper : ∀ w, ‖fderiv ℝ g w‖ ≤ C * ‖w‖) :
    fderiv ℝ (family G β T R v) w = 0 ↔ fderiv ℝ g w = R • innerSL ℝ v := by
  have hTpos : 0 < T := zero_lt_one.trans hT
  constructor
  · intro hz
    have hwlower : 1 < ‖w‖ := by
      by_contra! hn
      exact no_inner_critical hT hR hflat hv hn (hG w) (hsmall w hn) hz
    have hwupper : ‖w‖ < T := by
      by_contra! hn
      exact no_outer_critical hT hR hc hscale₂ (hβ _) (hD _
        (div_nonneg (norm_nonneg _) hTpos.le)) hv hn (hG w) heq (hlower w) hz
    rw [fderiv_family_core hTpos hflat hwupper (hG w),
      fderiv_eq_of_eq_outside heq hwlower, sub_eq_zero] at hz
    exact hz
  · intro he
    have hn : ‖fderiv ℝ g w‖ = R := by
      rw [he, norm_smul, innerSL_apply_norm, hv, mul_one, Real.norm_eq_abs, abs_of_pos hR]
    have hwpos : 0 < ‖w‖ := by
      have hh := hupper w
      rw [hn] at hh
      by_contra! hz
      have hz' : ‖w‖ = 0 := le_antisymm hz (norm_nonneg _)
      rw [hz', mul_zero] at hh
      exact (not_le_of_gt hR) hh
    have hCpos : 0 < C := by
      have hh := hupper w
      rw [hn] at hh
      nlinarith
    have hwlower : 1 < ‖w‖ := by
      have hh := hupper w
      rw [hn] at hh
      nlinarith
    have hwupper : ‖w‖ < T := by
      have hh := hlower w
      rw [hn] at hh
      have hstrict := (div_lt_iff₀ hc).mp hscale₁
      nlinarith
    rw [fderiv_family_core hTpos hflat hwupper (hG w),
      fderiv_eq_of_eq_outside heq hwlower, he, sub_self]

theorem family_eq_outside {G g : W → ℝ} {β : ℝ → ℝ} {T R : ℝ} {v w : W}
    (hT : 1 < T) (hβ : ∀ s, 2 ≤ s → β s = 0)
    (heq : ∀ w, 1 ≤ ‖w‖ → G w = g w) (hw : 2 * T ≤ ‖w‖) :
    family G β T R v w = g w := by
  have ht : 0 < T := zero_lt_one.trans hT
  have hs : 2 ≤ ‖w‖ / T := (le_div_iff₀ ht).mpr hw
  have hw₁ : 1 ≤ ‖w‖ := by linarith
  simp only [family, cutoffLinear, hβ _ hs, zero_mul, mul_zero, sub_zero, heq _ hw₁]

def betaBump : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩

def beta : ℝ → ℝ := betaBump

lemma contDiff_beta : ContDiff ℝ ∞ beta := betaBump.contDiff

lemma beta_mem_Icc (s : ℝ) : beta s ∈ Icc (0 : ℝ) 1 :=
  ⟨betaBump.nonneg, betaBump.le_one⟩

lemma beta_eq_one {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : beta s = 1 := by
  apply betaBump.one_of_mem_closedBall
  simpa [betaBump, abs_of_nonneg hs.1] using hs.2

lemma beta_eq_zero {s : ℝ} (hs : 2 ≤ s) : beta s = 0 := by
  apply betaBump.zero_of_le_dist
  simpa [betaBump, abs_of_nonneg (show 0 ≤ s by linarith)] using hs

def cutoffControl (β : ℝ → ℝ) : ℝ :=
  sSup (Set.range (fun s : Ici (0 : ℝ) => |β s| + (s : ℝ) * |deriv β s|))

lemma beta_control_bddAbove :
    BddAbove (Set.range (fun s : Ici (0 : ℝ) => |beta s| + (s : ℝ) * |deriv beta s|)) := by
  have hc : Continuous (fun s : ℝ => s * deriv beta s) :=
    continuous_id.mul (contDiff_beta.continuous_deriv (by simp))
  have hs : HasCompactSupport (fun s : ℝ => s * deriv beta s) :=
    betaBump.hasCompactSupport.deriv.mul_left
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
  refine ⟨1 + C, ?_⟩
  rintro _ ⟨s, rfl⟩
  have hb : |beta s| ≤ 1 := by
    rw [abs_of_nonneg (beta_mem_Icc s).1]
    exact (beta_mem_Icc s).2
  have hd : (s : ℝ) * |deriv beta s| ≤ C := by
    simpa [Real.norm_eq_abs, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (s : ℝ) from s.property)] using hC s
  linarith

lemma beta_le_control {s : ℝ} (hs : 0 ≤ s) :
    |beta s| + s * |deriv beta s| ≤ cutoffControl beta :=
  le_csSup beta_control_bddAbove ⟨⟨s, hs⟩, rfl⟩

lemma one_le_beta_control : 1 ≤ cutoffControl beta := by
  have h := beta_le_control (s := 0) le_rfl
  simpa [beta_eq_one (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num)] using h

end NearbyLagrangian.Cutoff

namespace NearbyLagrangian.Scales

variable {B : Type*}

def exponentialScale (θ : B → ℝ) (K Λ : ℝ) (b : B) : ℝ :=
  Λ * Real.exp (K * θ b)

lemma exponentialScale_pos {θ : B → ℝ} {K Λ : ℝ} (hΛ : 0 < Λ) (b : B) :
    0 < exponentialScale θ K Λ b := mul_pos hΛ (Real.exp_pos _)

theorem exists_source_scales [TopologicalSpace B] [CompactSpace B] [Nonempty B]
    {θ : B → ℝ} (hθ : Continuous θ) {c C C₁ M δ D : ℝ}
    (hc : 0 < c) (hC : 0 ≤ C) (hC₁ : 0 ≤ C₁) (_hM : 0 ≤ M) (hδ : 0 < δ) :
    ∃ K Λ T : ℝ, ∃ bmin bmax : B,
      0 < K ∧ 0 < Λ ∧ C₁ / c < K * δ ∧
      max C M < exponentialScale θ K Λ bmin ∧
      (∀ b, exponentialScale θ K Λ bmin ≤ exponentialScale θ K Λ b ∧
        exponentialScale θ K Λ b ≤ exponentialScale θ K Λ bmax) ∧
      max 1 (max (exponentialScale θ K Λ bmax / c)
        (D * exponentialScale θ K Λ bmax / c)) < T := by
  let K := (C₁ / c + 1) / δ
  have hKp : 0 < K := div_pos (by positivity) hδ
  have hK : C₁ / c < K * δ := by
    dsimp [K]
    rw [div_mul_cancel₀ _ hδ.ne']
    linarith
  have hη : Continuous (fun b => Real.exp (K * θ b)) :=
    (continuous_const.mul hθ).rexp
  obtain ⟨bmin, _, hmin⟩ := isCompact_univ.exists_isMinOn
    (Set.univ_nonempty : (Set.univ : Set B).Nonempty) hη.continuousOn
  obtain ⟨bmax, _, hmax⟩ := isCompact_univ.exists_isMaxOn
    (Set.univ_nonempty : (Set.univ : Set B).Nonempty) hη.continuousOn
  let Λ := (max C M + 1) / Real.exp (K * θ bmin)
  have hΛ : 0 < Λ := div_pos (by positivity) (Real.exp_pos _)
  have hval : exponentialScale θ K Λ bmin = max C M + 1 := by
    exact div_mul_cancel₀ _ (Real.exp_ne_zero _)
  let T := max 1 (max (exponentialScale θ K Λ bmax / c)
    (D * exponentialScale θ K Λ bmax / c)) + 1
  refine ⟨K, Λ, T, bmin, bmax, hKp, hΛ, hK, ?_, ?_, ?_⟩
  · rw [hval]
    linarith
  · intro b
    exact ⟨mul_le_mul_of_nonneg_left (hmin (Set.mem_univ b)) hΛ.le,
      mul_le_mul_of_nonneg_left (hmax (Set.mem_univ b)) hΛ.le⟩
  · dsimp [T]
    linarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace B] [ChartedSpace E B]

theorem contMDiff_exponentialScale {θ : B → ℝ} (K Λ : ℝ)
    (hθ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ θ) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (exponentialScale θ K Λ) := by
  exact contMDiff_const.mul (Real.contDiff_exp.comp_contMDiff (contMDiff_const.mul hθ))

theorem mfderiv_exponentialScale {θ : B → ℝ} (K Λ : ℝ) {b : B}
    (hθ : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) θ b) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (exponentialScale θ K Λ) b =
      (K * exponentialScale θ K Λ b) • mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) θ b := by
  let g : ℝ → ℝ := fun s => Λ * Real.exp (K * s)
  have hg : HasDerivAt g (Λ * (Real.exp (K * θ b) * K)) (θ b) :=
    by simpa [g] using ((Real.hasDerivAt_exp (K * θ b)).comp (θ b)
      ((hasDerivAt_id (θ b)).const_mul K)).const_mul Λ
  have hd := mfderiv_comp b hg.differentiableAt.mdifferentiableAt hθ
  change mfderiv _ _ (g ∘ θ) b = _
  rw [hd]
  have he (a : ℝ) : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) g (θ b) a =
      (Λ * (Real.exp (K * θ b) * K)) * a := by
    rw [mfderiv_eq_fderiv]
    erw [hg.hasFDerivAt.fderiv]
    change a * (Λ * (Real.exp (K * θ b) * K)) = _
    ring
  ext v
  let a : ℝ := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) θ b v
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) g (θ b) a =
      (K * exponentialScale θ K Λ b) * a
  rw [he]
  change (Λ * (Real.exp (K * θ b) * K)) * a = (K * (Λ * Real.exp (K * θ b))) * a
  exact (by ring : (Λ * (Real.exp (K * θ b) * K)) * a =
    (K * (Λ * Real.exp (K * θ b))) * a)

end NearbyLagrangian.Scales

end

end OAI
