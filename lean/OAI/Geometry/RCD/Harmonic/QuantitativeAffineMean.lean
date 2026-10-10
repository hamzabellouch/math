import OAI.Geometry.RCD.Harmonic.VanishingVariationAffineLimit

namespace OAI

/-! # Quantitative affine means without assuming a common value limit -/

open Set Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates

theorem interior_chord_error_tendsto_zero
    (F G : ℕ → ℝ → ℝ)
    (hF : ∀ k t, t ∈ Ioo (0:ℝ) 1 → DifferentiableAt ℝ (F k) t)
    (hint : ∀ k a b, 0 < a → a ≤ b → b < 1 →
      (∫ t in a..b, G k t) = deriv (F k) b-deriv (F k) a)
    (hG : ∀ a b, 0 < a → a ≤ b → b < 1 →
      TendstoUniformlyOn G (fun _ => 0) atTop (Icc a b))
    {a b x : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) (hx : x ∈ Icc a b) :
    Tendsto (fun k => F k x-F k a-((F k b-F k a)/(b-a))*(x-a)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro e he
  let δ := e/((b-a)^2+1)
  have hδ : 0 < δ := div_pos he (by positivity)
  have hδe : δ*(b-a)^2 < e := by
    have hh : δ*((b-a)^2+1)=e := div_mul_cancel₀ e (by positivity)
    nlinarith
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp (hG a b ha hab.le hb)) δ hδ] with k hk
  have hbound := chord_error_le_of_derivative_oscillation hab hδ.le hx
    (fun t ht => hF k t ⟨ha.trans_le ht.1,ht.2.trans_lt hb⟩)
    (fun u hu v hv => integrated_derivative_oscillation (g := G k) hδ.le
      (fun t ht => by simpa only [dist_zero_left,Real.norm_eq_abs] using (hk t ht).le)
      (fun u v hau huv hvb => hint k u v (ha.trans_le hau) huv (hvb.trans_lt hb)) hu hv)
  simpa only [dist_zero_right,Real.norm_eq_abs] using hbound.trans_lt hδe

theorem abs_le_of_chord_error {f : ℝ → ℝ} {a b x B D : ℝ}
    (hab : a < b) (hx : x ∈ Icc a b)
    (ha : |f a| ≤ B) (hb : |f b| ≤ B)
    (he : |f x-f a-((f b-f a)/(b-a))*(x-a)| ≤ D) : |f x| ≤ D+B := by
  let t := (x-a)/(b-a)
  have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hx.1) (sub_pos.mpr hab).le
  have ht1 : t ≤ 1 := (div_le_one (sub_pos.mpr hab)).mpr (by linarith [hx.2])
  have hid : f x=(f x-f a-((f b-f a)/(b-a))*(x-a))+(1-t)*f a+t*f b := by
    dsimp only [t]
    field_simp [(sub_pos.mpr hab).ne']
    ring
  rw [hid]
  calc
    _ ≤ |f x-f a-((f b-f a)/(b-a))*(x-a)|+|(1-t)*f a|+|t*f b| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ D+(1-t)*B+t*B := by
      rw [abs_mul,abs_of_nonneg (sub_nonneg.mpr ht1),abs_mul,abs_of_nonneg ht0]
      gcongr
    _ = D+B := by ring

theorem endpoint_chord_error_of_interior_errors
    (F : ℕ → ℝ → ℝ) (M : ℝ≥0)
    (hLip : ∀ k, LipschitzOnWith M (F k) (Icc (0:ℝ) 1))
    (hchord : ∀ {a b x : ℝ}, 0 < a → a < b → b < 1 → x ∈ Icc a b →
      Tendsto (fun k => F k x-F k a-((F k b-F k a)/(b-a))*(x-a)) atTop (𝓝 0))
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    Tendsto (fun k => F k t-((1-t)*F k 0+t*F k 1)) atTop (𝓝 0) := by
  by_cases ht0 : t=0
  · simpa only [ht0,sub_zero,mul_zero,zero_mul,one_mul,add_zero,sub_self] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
  by_cases ht1 : t=1
  · simpa only [ht1,sub_self,zero_mul,one_mul,zero_add] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
  have ht0' : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have ht1' : t < 1 := lt_of_le_of_ne ht.2 ht1
  let P k x := F k x-((1-x)*F k 0+x*F k 1)
  have h01 (k : ℕ) : |F k 1-F k 0| ≤ M := by
    simpa only [Real.dist_eq,sub_zero,abs_one,mul_one] using
      (hLip k).dist_le_mul 1 ⟨zero_le_one,le_rfl⟩ 0 ⟨le_rfl,zero_le_one⟩
  apply Metric.tendsto_nhds.mpr
  intro e he
  let δ := min (t/2) (min ((1-t)/2) (e/(8*((M:ℝ)+1))))
  have hδ : 0 < δ := lt_min (half_pos ht0')
    (lt_min (half_pos (sub_pos.mpr ht1')) (div_pos he (by positivity)))
  have hδt : δ < t := (min_le_left _ _).trans_lt (by linarith)
  have hδb : t < 1-δ := by
    have hh : δ ≤ (1-t)/2 := (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hab : δ < 1-δ := hδt.trans hδb
  have hδ1 : δ < 1 := hδt.trans ht1'
  have hsmallB : 2*(M:ℝ)*δ < e/2 := by
    have hle : δ ≤ e/(8*((M:ℝ)+1)) := (min_le_right _ _).trans (min_le_right _ _)
    have hh := (le_div_iff₀ (by positivity : 0 < 8*((M:ℝ)+1))).mp hle
    nlinarith [M.coe_nonneg]
  have hpA (k : ℕ) : |P k δ| ≤ 2*(M:ℝ)*δ := by
    have hh : |F k δ-F k 0| ≤ (M:ℝ)*δ := by
      simpa only [Real.dist_eq,sub_zero,abs_of_pos hδ] using
        (hLip k).dist_le_mul δ ⟨hδ.le,hδ1.le⟩ 0 ⟨le_rfl,zero_le_one⟩
    have heq : P k δ=(F k δ-F k 0)-δ*(F k 1-F k 0) := by dsimp only [P]; ring
    rw [heq]
    calc
      _ ≤ |F k δ-F k 0|+|δ*(F k 1-F k 0)| := by
        simpa only [sub_zero,zero_sub,abs_neg] using
          abs_sub_le (F k δ-F k 0) 0 (δ*(F k 1-F k 0))
      _ ≤ (M:ℝ)*δ+δ*(M:ℝ) := by
        rw [abs_mul,abs_of_pos hδ]
        exact add_le_add hh (mul_le_mul_of_nonneg_left (h01 k) hδ.le)
      _ = _ := by ring
  have hpB (k : ℕ) : |P k (1-δ)| ≤ 2*(M:ℝ)*δ := by
    have hh : |F k (1-δ)-F k 1| ≤ (M:ℝ)*δ := by
      simpa only [Real.dist_eq,show (1-δ)-1=-δ by ring,abs_neg,abs_of_pos hδ] using
        (hLip k).dist_le_mul (1-δ) ⟨by linarith,by linarith⟩ 1 ⟨zero_le_one,le_rfl⟩
    have heq : P k (1-δ)=(F k (1-δ)-F k 1)+δ*(F k 1-F k 0) := by dsimp only [P]; ring
    rw [heq]
    calc
      _ ≤ |F k (1-δ)-F k 1|+|δ*(F k 1-F k 0)| := abs_add_le _ _
      _ ≤ (M:ℝ)*δ+δ*(M:ℝ) := by
        rw [abs_mul,abs_of_pos hδ]
        exact add_le_add hh (mul_le_mul_of_nonneg_left (h01 k) hδ.le)
      _ = _ := by ring
  have hch := hchord hδ hab
    (by linarith : 1-δ < 1) ⟨hδt.le,hδb.le⟩
  have hchP : Tendsto (fun k => P k t-P k δ-
      ((P k (1-δ)-P k δ)/((1-δ)-δ))*(t-δ)) atTop (𝓝 0) := by
    apply hch.congr'
    filter_upwards [] with k
    dsimp only [P]
    field_simp [(sub_pos.mpr hab).ne']
    ring
  filter_upwards [Metric.tendsto_nhds.mp hchP (e/2) (half_pos he)] with k hk
  have hh := abs_le_of_chord_error hab ⟨hδt.le,hδb.le⟩ (hpA k) (hpB k)
    (show |P k t-P k δ-((P k (1-δ)-P k δ)/((1-δ)-δ))*(t-δ)| ≤ e/2 by
      simpa only [dist_zero_right,Real.norm_eq_abs] using hk.le)
  have hf : |P k t| < e := hh.trans_lt (by linarith)
  simpa only [dist_zero_right,Real.norm_eq_abs] using hf


theorem endpoint_chord_error_tendsto_zero
    (F G : ℕ → ℝ → ℝ) (M : ℝ≥0)
    (hLip : ∀ k, LipschitzOnWith M (F k) (Icc (0:ℝ) 1))
    (hF : ∀ k t, t ∈ Ioo (0:ℝ) 1 → DifferentiableAt ℝ (F k) t)
    (hint : ∀ k a b, 0 < a → a ≤ b → b < 1 →
      (∫ t in a..b, G k t) = deriv (F k) b-deriv (F k) a)
    (hG : ∀ a b, 0 < a → a ≤ b → b < 1 →
      TendstoUniformlyOn G (fun _ => 0) atTop (Icc a b))
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    Tendsto (fun k => F k t-((1-t)*F k 0+t*F k 1)) atTop (𝓝 0) :=
  endpoint_chord_error_of_interior_errors F M hLip
    (fun ha hab hb hx => interior_chord_error_tendsto_zero F G hF hint hG ha hab hb hx) ht

theorem interior_chord_errors_transfer (F H : ℕ → ℝ → ℝ)
    (hval : ∀ t ∈ Ioo (0:ℝ) 1, Tendsto (fun k => F k t-H k t) atTop (𝓝 0))
    (hchord : ∀ {a b x : ℝ}, 0 < a → a < b → b < 1 → x ∈ Icc a b →
      Tendsto (fun k => H k x-H k a-((H k b-H k a)/(b-a))*(x-a)) atTop (𝓝 0))
    {a b x : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) (hx : x ∈ Icc a b) :
    Tendsto (fun k => F k x-F k a-((F k b-F k a)/(b-a))*(x-a)) atTop (𝓝 0) := by
  have ha' : a ∈ Ioo (0:ℝ) 1 := ⟨ha,hab.trans hb⟩
  have hb' : b ∈ Ioo (0:ℝ) 1 := ⟨ha.trans hab,hb⟩
  have hx' : x ∈ Ioo (0:ℝ) 1 := ⟨ha.trans_le hx.1,hx.2.trans_lt hb⟩
  have hdiff := (((hval x hx').sub (hval a ha')).sub
    ((((hval b hb').sub (hval a ha')).div_const (b-a)).mul_const (x-a)))
  have hh := (hchord ha hab hb hx).add hdiff
  convert hh using 1
  · funext k
    ring
  · simp

end RegularPointCoordinates

end

end OAI
