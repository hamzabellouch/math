import OAI.Probability.SLE.Loewner.SmoothRawTipLimit
import OAI.Probability.SLE.Loewner.ReverseLongContraction

namespace OAI

/-! A bounded derivative gives a finite radial tip limit at every time.
The proof first gains a positive height on a short terminal interval,
then uses ordinary interior stability for the remaining reverse time. -/
noncomputable section
open Set Filter Metric Complex
open scoped Topology NNReal

namespace SLEExactGauge.Target

theorem inverseFlow_vertical_distance_of_smooth_driver
    (b : Driver) (T : ℝ≥0) (b' : ℝ → ℝ)
    (hd : ∀ t ∈ Icc 0 (T : ℝ), HasDerivWithinAt (fun s => b s.toNNReal)
      (b' t) (Icc 0 (T : ℝ)) t)
    {L a : ℝ} (hL : 0 ≤ L) (ha : 0 < a) (haT : a ≤ T)
    (hb : ∀ t ∈ Icc 0 (T : ℝ), |b' t| ≤ L) (hsmall : L^2*a ≤ 1)
    {y v : ℝ} (hy : 0 < y) (hv : 0 < v) :
    dist (inverseFlow 1 b T ((b T : ℂ)+(y : ℂ)*I))
      (inverseFlow 1 b T ((b T : ℂ)+(v : ℂ)*I)) ≤
        |y-v| * Real.exp ((4*(Real.sqrt a)⁻¹^2)*((T : ℝ)-a)) := by
  obtain ⟨q,hq0,hqy,hqd,heq⟩ := exists_raw_reverse_trajectory b T
    ((b T : ℂ)+(y : ℂ)*I) (by simpa [upperHalfPlane] using hy)
  obtain ⟨r,hr0,hry,hrd,her⟩ := exists_raw_reverse_trajectory b T
    ((b T : ℂ)+(v : ℂ)*I) (by simpa [upperHalfPlane] using hv)
  let u (s : ℝ) := driverValue b ((T : ℝ)-s)
  have hreflect (s : ℝ) (hs : s ∈ Icc 0 (T : ℝ)) :
      (T : ℝ)-s ∈ Icc 0 (T : ℝ) :=
    ⟨sub_nonneg.mpr hs.2,sub_le_self _ hs.1⟩
  have hu (s : ℝ) (hs : s ∈ Icc 0 (T : ℝ)) : HasDerivWithinAt u
      (-b' ((T : ℝ)-s)) (Icc 0 (T : ℝ)) s := by
    have hi : HasDerivWithinAt (fun t : ℝ => (T : ℝ)-t) (-1) (Icc 0 (T : ℝ)) s := by
      simpa using ((hasDerivAt_id s).const_sub (T : ℝ)).hasDerivWithinAt
    convert! (hd _ (hreflect s hs)).comp s hi hreflect using 1
    simp only [mul_neg,mul_one]
  have hh := smooth_reverse_long_distance ha haT hL q r u
    (fun s => -b' ((T : ℝ)-s))
    (fun s hs => (hqd s hs.1).mono Icc_subset_Ici_self)
    (fun s hs => (hrd s hs.1).mono Icc_subset_Ici_self) hu
    (fun s hs => by simpa using hb _ (hreflect s hs))
    (fun s hs => hy.trans_le (by simpa using hqy s hs.1))
    (fun s hs => hv.trans_le (by simpa using hry s hs.1))
    (by simp [hq0,u,driverValue]) (by simp [hr0,u,driverValue]) hsmall
  rw [heq,her]
  convert hh using 1
  rw [hq0,hr0,dist_eq_norm]
  have he : ((b T : ℂ)+(y : ℂ)*I)-((b T : ℂ)+(v : ℂ)*I)=((y-v : ℝ) : ℂ)*I := by
    push_cast
    ring
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one]

theorem inverseFlow_tip_limit_of_smooth_window
    (b : Driver) (T : ℝ≥0) (b' : ℝ → ℝ)
    (hd : ∀ t ∈ Icc 0 (T : ℝ), HasDerivWithinAt (fun s => b s.toNNReal)
      (b' t) (Icc 0 (T : ℝ)) t)
    {L a : ℝ} (hL : 0 ≤ L) (ha : 0 < a) (haT : a ≤ T)
    (hb : ∀ t ∈ Icc 0 (T : ℝ), |b' t| ≤ L) (hsmall : L^2*a ≤ 1) :
    ∃ z : ℂ, Tendsto (fun y : ℝ => inverseFlow 1 b T ((b T : ℂ)+(y : ℂ)*I))
      (𝓝[>] 0) (𝓝 z) := by
  let C : ℝ≥0 := ⟨Real.exp ((4*(Real.sqrt a)⁻¹^2)*((T : ℝ)-a)),(Real.exp_pos _).le⟩
  refine exists_right_limit_of_complex_lipschitz
    (fun y : ℝ => inverseFlow 1 b T ((b T : ℂ)+(y : ℂ)*I)) C ?_
  intro y hy v hv
  exact (inverseFlow_vertical_distance_of_smooth_driver b T b' hd hL ha haT hb hsmall hy hv).trans_eq
    (mul_comm _ _)

lemma exists_smooth_window (T : ℝ) (hT : 0 < T) (L : ℝ) :
    ∃ a : ℝ, 0 < a ∧ a ≤ T ∧ L^2*a ≤ 1 := by
  let a : ℝ := min T (1/(L^2+1))
  have ha : 0 < a := lt_min hT (by positivity)
  refine ⟨a,ha,min_le_left _ _,?_⟩
  have hden : 0 < L^2+1 := by positivity
  have h : a*(L^2+1) ≤ 1 := (le_div_iff₀ hden).mp (min_le_right T (1/(L^2+1)))
  nlinarith [ha.le]

theorem inverseFlow_tip_limit_of_smooth_driver
    (b : Driver) (T : ℝ≥0) (b' : ℝ → ℝ)
    (hd : ∀ t ∈ Icc 0 (T : ℝ), HasDerivWithinAt (fun s => b s.toNNReal)
      (b' t) (Icc 0 (T : ℝ)) t)
    {L : ℝ} (hL : 0 ≤ L) (hb : ∀ t ∈ Icc 0 (T : ℝ), |b' t| ≤ L) :
    ∃ z : ℂ, Tendsto (fun y : ℝ => inverseFlow 1 b T ((b T : ℂ)+(y : ℂ)*I))
      (𝓝[>] 0) (𝓝 z) := by
  by_cases hT : T=0
  · subst T
    exact inverseFlow_tip_limit_of_short_smooth_driver b 0 b' hd hL hb (by simp)
  obtain ⟨a,ha,haT,hsmall⟩ := exists_smooth_window T
    (by exact_mod_cast (pos_iff_ne_zero.mpr hT)) L
  exact inverseFlow_tip_limit_of_smooth_window b T b' hd hL ha haT hb hsmall

end SLEExactGauge.Target

end

end OAI
