import OAI.Probability.SLE.Geometry.CurveJoin
import OAI.Probability.SLE.Gauge.SerpentineExperimentGeometry

namespace OAI

/-! A proper polygonal continuation from the high right-hand tail of
the serpentine through the marked point and then to infinity on its left. -/

noncomputable section
open Set Filter Metric
open scoped Topology NNReal

namespace SLEExactGauge.Serpentine

def hookTop (_w : ℂ) (R H t : ℝ) : ℂ := ((R - t : ℝ) : ℂ) + (H : ℂ) * Complex.I

def hookDown (w : ℂ) (R H t : ℝ) : ℂ :=
  (w.re : ℂ) + ((H - (t - (R - w.re)) : ℝ) : ℂ) * Complex.I

def hookLeft (w : ℂ) (R H t : ℝ) : ℂ :=
  ((w.re - (t - ((R - w.re) + (H - w.im))) : ℝ) : ℂ) + (w.im : ℂ) * Complex.I

def hookUp (w : ℂ) (R H a t : ℝ) : ℂ :=
  ((w.re - a : ℝ) : ℂ) + ((w.im + t - ((R - w.re) + (H - w.im) + a) : ℝ) : ℂ) * Complex.I

def markedHook (w : ℂ) (R H a : ℝ) : ℝ → ℂ :=
  curveJoin (R - w.re) (hookTop w R H)
    (curveJoin ((R - w.re) + (H - w.im)) (hookDown w R H)
      (curveJoin ((R - w.re) + (H - w.im) + a) (hookLeft w R H) (hookUp w R H a)))

lemma markedHook_zero (w : ℂ) {R H a : ℝ} (hR : w.re < R) :
    markedHook w R H a 0 = (R : ℂ) + (H : ℂ) * Complex.I := by
  simp only [markedHook, curveJoin_of_le (show (0 : ℝ) ≤ R - w.re by linarith), hookTop,
    sub_zero]

lemma markedHook_continuous (w : ℂ) (R : ℝ) {H a : ℝ} (hH : w.im < H) (ha : 0 < a) :
    Continuous (markedHook w R H a) := by
  have htop : Continuous (hookTop w R H) := by unfold hookTop; fun_prop
  have hdown : Continuous (hookDown w R H) := by unfold hookDown; fun_prop
  have hleft : Continuous (hookLeft w R H) := by unfold hookLeft; fun_prop
  have hup : Continuous (hookUp w R H a) := by unfold hookUp; fun_prop
  have h1 : hookTop w R H (R - w.re) = hookDown w R H (R - w.re) := by
    unfold hookTop hookDown
    push_cast
    ring
  have h2 : hookDown w R H ((R - w.re) + (H - w.im)) =
      hookLeft w R H ((R - w.re) + (H - w.im)) := by
    unfold hookDown hookLeft
    push_cast
    ring
  have h3 : hookLeft w R H ((R - w.re) + (H - w.im) + a) =
      hookUp w R H a ((R - w.re) + (H - w.im) + a) := by
    unfold hookLeft hookUp
    push_cast
    ring
  unfold markedHook
  apply curveJoin_continuous _ _ _ htop
  · exact curveJoin_continuous _ _ _ hdown (curveJoin_continuous _ _ _ hleft hup h3) (by
      rw [curveJoin_of_le (show (R - w.re) + (H - w.im) ≤ (R - w.re) + (H - w.im) + a by linarith)]
      exact h2)
  · rw [curveJoin_of_le (show R - w.re ≤ (R - w.re) + (H - w.im) by linarith)]
    exact h1

lemma markedHook_pieces (w : ℂ) {R H a t : ℝ} (_hR : w.re < R) (_hH : w.im < H)
    (_ha : 0 < a) (ht : 0 ≤ t) :
    (t ∈ Icc 0 (R - w.re) ∧ markedHook w R H a t = hookTop w R H t) ∨
    (t ∈ Icc (R - w.re) ((R - w.re) + (H - w.im)) ∧
      markedHook w R H a t = hookDown w R H t) ∨
    (t ∈ Icc ((R - w.re) + (H - w.im)) ((R - w.re) + (H - w.im) + a) ∧
      markedHook w R H a t = hookLeft w R H t) ∨
    ((R - w.re) + (H - w.im) + a ≤ t ∧ markedHook w R H a t = hookUp w R H a t) := by
  by_cases h1 : t ≤ R - w.re
  · exact Or.inl ⟨⟨ht, h1⟩, by unfold markedHook; rw [curveJoin_of_le h1]⟩
  · right
    by_cases h2 : t ≤ (R - w.re) + (H - w.im)
    · exact Or.inl ⟨⟨by linarith, h2⟩, by simp only [markedHook,
        curveJoin_of_gt (lt_of_not_ge h1), curveJoin_of_le h2]⟩
    · right
      by_cases h3 : t ≤ (R - w.re) + (H - w.im) + a
      · exact Or.inl ⟨⟨by linarith, h3⟩, by simp only [markedHook,
          curveJoin_of_gt (lt_of_not_ge h1), curveJoin_of_gt (lt_of_not_ge h2), curveJoin_of_le h3]⟩
      · exact Or.inr ⟨by linarith, by simp only [markedHook,
          curveJoin_of_gt (lt_of_not_ge h1), curveJoin_of_gt (lt_of_not_ge h2),
          curveJoin_of_gt (lt_of_not_ge h3)]⟩

lemma markedHook_injective (w : ℂ) {R H a : ℝ} (hR : w.re < R) (hH : w.im < H)
    (ha : 0 < a) : InjOn (markedHook w R H a) (Ici 0) := by
  intro s hs t ht he
  rcases markedHook_pieces w hR hH ha hs with ⟨hs, hse⟩ | ⟨hs, hse⟩ | ⟨hs, hse⟩ | ⟨hs, hse⟩ <;>
    rcases markedHook_pieces w hR hH ha ht with ⟨ht, hte⟩ | ⟨ht, hte⟩ | ⟨ht, hte⟩ | ⟨ht, hte⟩
  all_goals
    rw [hse, hte] at he
    have hre := congrArg Complex.re he
    have him := congrArg Complex.im he
    simp only [hookTop, hookDown, hookLeft, hookUp, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, zero_add] at hre him
    try simp only [mem_Icc] at hs ht
    linarith [hs, ht]

lemma markedHook_passes_marked (w : ℂ) {R H a : ℝ} (hH : w.im < H) :
    markedHook w R H a ((R - w.re) + (H - w.im)) = w := by
  have h1 : R - w.re < (R - w.re) + (H - w.im) := by linarith
  simp only [markedHook, curveJoin_of_gt h1, curveJoin_of_le le_rfl, hookDown]
  convert Complex.re_add_im w using 1
  push_cast
  ring

lemma markedHook_tail_region (w : ℂ) {R H a t : ℝ} (hR : w.re < R) (hH : w.im < H)
    (ha : 0 < a) (ht : 0 ≤ t) :
    (markedHook w R H a t).im = H ∨
      ((markedHook w R H a t).re ≤ w.re ∧ w.im ≤ (markedHook w R H a t).im) := by
  rcases markedHook_pieces w hR hH ha ht with ⟨_, he⟩ | ⟨ht, he⟩ | ⟨ht, he⟩ | ⟨ht, he⟩
  · left
    rw [he]
    simp [hookTop]
  all_goals
    right
    rw [he]
    simp only [hookDown, hookLeft, hookUp, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, zero_add]
    try simp only [mem_Icc] at ht
    constructor <;> linarith [ht]

lemma markedHook_disjoint_prefix (w : ℂ) {R H a : ℝ} (hR : w.re < R) (hH : w.im < H)
    (ha : 0 < a) (z : ℂ) (hzH : z.im < H) (hz : z.im < w.im ∨ w.re < z.re)
    {t : ℝ} (ht : 0 ≤ t) : z ≠ markedHook w R H a t := by
  intro he
  rw [he] at hzH hz
  rcases markedHook_tail_region w hR hH ha ht with hh | hh
  · linarith
  · rcases hz with hz | hz <;> linarith [hh.1, hh.2]

lemma markedHook_tail (w : ℂ) {R H a t : ℝ} (hH : w.im < H) (ha : 0 < a)
    (ht : (R - w.re) + (H - w.im) + a < t) :
    markedHook w R H a t = hookUp w R H a t := by
  simp only [markedHook,
    curveJoin_of_gt (show R - w.re < t by linarith),
    curveJoin_of_gt (show (R - w.re) + (H - w.im) < t by linarith), curveJoin_of_gt ht]

lemma markedHook_unbounded (w : ℂ) {R H a : ℝ} (hR : w.re < R) (hH : w.im < H)
    (ha : 0 < a) : ¬ Bornology.IsBounded (range (fun t : ℝ≥0 => markedHook w R H a t)) := by
  intro hb
  obtain ⟨B, hB, hbound⟩ := hb.exists_pos_norm_lt
  let t : ℝ≥0 := ⟨(R - w.re) + (H - w.im) + a + B + |w.im| + 1, by positivity⟩
  have htval : (t : ℝ) = (R - w.re) + (H - w.im) + a + B + |w.im| + 1 := rfl
  have ht : (R - w.re) + (H - w.im) + a < (t : ℝ) := by
    rw [htval]
    linarith [abs_nonneg w.im]
  have hn := hbound (markedHook w R H a t) (mem_range_self t)
  have hi := Complex.im_le_norm (markedHook w R H a t)
  rw [markedHook_tail w hH ha ht] at hi hn
  simp only [hookUp, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add] at hi
  rw [htval] at hi hn
  dsimp only [hookUp] at hn
  linarith [neg_le_abs w.im]

theorem markedHook_survives
    (γ : ℝ≥0 → ℂ) (T : ℝ≥0) (w : ℂ) (hw : 0 < w.im)
    {R H a : ℝ} (hR : w.re < R) (hH : w.im < H) (ha : 0 < a)
    (hpast : ∀ z ∈ γ '' Icc 0 T, z.im < H ∧ (z.im < w.im ∨ w.re < z.re)) :
    range (fun t : ℝ≥0 => markedHook w R H a t) ⊆ survivingDomain γ T := by
  apply survives_of_unbounded_free_curve γ T _
    ((markedHook_continuous w R hH ha).comp NNReal.continuous_coe) ?_
    (markedHook_unbounded w hR hH ha)
  rintro z ⟨t, rfl⟩
  have hregion := markedHook_tail_region w hR hH ha t.coe_nonneg
  refine ⟨?_, ?_⟩
  · change 0 < (markedHook w R H a t).im
    rcases hregion with he | hh <;> linarith
  · intro hp
    exact markedHook_disjoint_prefix w hR hH ha _ (hpast _ hp).1 (hpast _ hp).2 t.coe_nonneg rfl

def appendMarkedHook (α : ℝ → ℂ) (T : ℝ) (w : ℂ) (R H a : ℝ) : ℝ → ℂ :=
  curveJoin T α (fun t => markedHook w R H a (t - T))

lemma appendMarkedHook_continuous (α : ℝ → ℂ) (hα : Continuous α) (T : ℝ)
    (w : ℂ) {R H a : ℝ} (hR : w.re < R) (hH : w.im < H) (ha : 0 < a)
    (hαT : α T = (R : ℂ) + (H : ℂ) * Complex.I) :
    Continuous (appendMarkedHook α T w R H a) := by
  apply curveJoin_continuous _ _ _ hα
  · exact (markedHook_continuous w R hH ha).comp (continuous_id.sub continuous_const)
  · simpa only [sub_self, markedHook_zero w hR] using hαT

lemma appendMarkedHook_injective (α : ℝ → ℂ) {T : ℝ} (_hT : 0 ≤ T)
    (hαinj : InjOn α (Icc 0 T)) (w : ℂ) {R H a : ℝ}
    (hR : w.re < R) (hH : w.im < H) (ha : 0 < a)
    (hαT : α T = (R : ℂ) + (H : ℂ) * Complex.I)
    (hregion : ∀ t ∈ Ico 0 T, (α t).im < H ∧ ((α t).im < w.im ∨ w.re < (α t).re)) :
    InjOn (appendMarkedHook α T w R H a) (Ici 0) := by
  intro s hs t ht he
  have hzero : (0 : ℝ) ∈ Ici (0 : ℝ) := show (0 : ℝ) ≤ 0 from le_rfl
  by_cases hsT : s ≤ T
  · by_cases htT : t ≤ T
    · apply hαinj ⟨hs, hsT⟩ ⟨ht, htT⟩
      simpa only [appendMarkedHook, curveJoin_of_le hsT, curveJoin_of_le htT] using he
    · have htT' : T < t := lt_of_not_ge htT
      simp only [appendMarkedHook, curveJoin_of_le hsT, curveJoin_of_gt htT'] at he
      rcases eq_or_lt_of_le hsT with hsEq | hsT'
      · rw [hsEq, hαT, ← markedHook_zero w (a := a) hR] at he
        have hx := markedHook_injective w hR hH ha hzero
          (show t - T ∈ Ici (0 : ℝ) by change 0 ≤ t - T; linarith) he
        linarith
      · exact (markedHook_disjoint_prefix w hR hH ha (α s)
          (hregion s ⟨hs, hsT'⟩).1 (hregion s ⟨hs, hsT'⟩).2 (by linarith) he).elim
  · have hsT' : T < s := lt_of_not_ge hsT
    by_cases htT : t ≤ T
    · simp only [appendMarkedHook, curveJoin_of_gt hsT', curveJoin_of_le htT] at he
      rcases eq_or_lt_of_le htT with htEq | htT'
      · rw [htEq, hαT, ← markedHook_zero w (a := a) hR] at he
        have hx := markedHook_injective w hR hH ha
          (show s - T ∈ Ici (0 : ℝ) by change 0 ≤ s - T; linarith) hzero he
        linarith
      · exact (markedHook_disjoint_prefix w hR hH ha (α t)
          (hregion t ⟨ht, htT'⟩).1 (hregion t ⟨ht, htT'⟩).2 (by linarith) he.symm).elim
    · have htT' : T < t := lt_of_not_ge htT
      simp only [appendMarkedHook, curveJoin_of_gt hsT', curveJoin_of_gt htT'] at he
      have hx := markedHook_injective w hR hH ha
        (show s - T ∈ Ici 0 by change 0 ≤ s - T; linarith)
        (show t - T ∈ Ici 0 by change 0 ≤ t - T; linarith) he
      linarith

lemma appendMarkedHook_passes_marked (α : ℝ → ℂ) (T : ℝ) (w : ℂ) {R H a : ℝ}
    (hR : w.re < R) (hH : w.im < H) :
    appendMarkedHook α T w R H a (T + ((R - w.re) + (H - w.im))) = w := by
  have hT : T < T + ((R - w.re) + (H - w.im)) := by linarith
  simp only [appendMarkedHook, curveJoin_of_gt hT, add_sub_cancel_left]
  exact markedHook_passes_marked w hH

end SLEExactGauge.Serpentine

end

end OAI
