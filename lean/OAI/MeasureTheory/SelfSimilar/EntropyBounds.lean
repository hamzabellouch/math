import OAI.MeasureTheory.SelfSimilar.MeasureEntropy

namespace OAI

universe uι

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace System
variable {ι : Type uι} [Fintype ι] [Nonempty ι]
open MeasureEntropy

theorem stopped_lower (S : System ι) (F : ℝ → ℝ) {a v B : ℝ}
    (ha : 0 < a) (hai : ∀ i, a ≤ |S.ratio i|) (hv : 0 < v)
    (hstep : ∀ s, 0 < s → (∑ i, S.weight i*F (s/|S.ratio i|)) ≤ F s)
    (hbase : ∀ z, v ≤ z → z ≤ v/a → B ≤ F z) :
    ∀ s, 0 < s → s < v → B ≤ F s := by
  classical
  obtain ⟨c,_T,hc,hc1,_hT,hr,_ht⟩ := S.exists_uniform_bounds
  have hi : ∀ n s, 0 < s → v*c^n ≤ s → s ≤ v/a → B ≤ F s := by
    intro n
    induction n with
    | zero =>
      intro s _hs hvs hsa
      exact hbase s (by simpa using hvs) hsa
    | succ n ih =>
      intro s hs hvs hsa
      by_cases hvz : v ≤ s
      · exact hbase s hvz hsa
      have hsv : s < v := lt_of_not_ge hvz
      apply le_trans _ (hstep s hs)
      calc
        B = ∑i, S.weight i*B := by rw [← Finset.sum_mul, S.weight_sum, one_mul]
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro i _
          apply mul_le_mul_of_nonneg_left _ (S.weight_nonneg i)
          apply ih _ (div_pos hs (S.ratio_pos i))
          · apply (le_div_iff₀ (S.ratio_pos i)).mpr
            calc
              v*c^n*|S.ratio i| ≤ v*c^n*c :=
                mul_le_mul_of_nonneg_left (hr i) (by positivity)
              _ ≤ s := by simpa only [pow_succ, mul_assoc] using hvs
          · exact (div_le_div_of_nonneg_left hv.le ha (hai i)).trans'
              (div_le_div_of_nonneg_right hsv.le (S.ratio_pos i).le)
  intro s hs hsv
  have hz : Filter.Tendsto (fun n : ℕ => v*c^n) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc.le hc1).const_mul v
  obtain ⟨n,hn⟩ := (hz.eventually (gt_mem_nhds hs)).exists
  have ha1 : a ≤ 1 := (hai (Classical.arbitrary ι)).trans
    (S.ratio_lt_one (Classical.arbitrary ι)).le
  exact hi n s hs hn.le (hsv.le.trans ((le_div_iff₀ ha).mpr (by nlinarith)))

theorem window_selfSimilar (S : System ι) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : S.SelfSimilar μ) {s : ℝ} (hs : 0 < s) {K : ℕ} (hK : 0 < K) :
    (∑i, S.weight i*(averaged μ (s/|S.ratio i|)-
      averaged μ ((K : ℝ)*(s/|S.ratio i|)))) ≤
      averaged μ s-averaged μ ((K : ℝ)*s) := by
  classical
  obtain ⟨B,hB,hBμ⟩ := S.selfSimilar_compact μ hμ
  have hc : CompactlyCarried μ := ⟨B,hB.le,hBμ⟩
  let : ∀ i, IsProbabilityMeasure (μ.map (S.affine i)) := fun i =>
    (Measure.isProbabilityMeasure_map_iff (S.affine_continuous i).measurable.aemeasurable).2 inferInstance
  have hh := averaged_nested_mixture μ hc (fun i => μ.map (S.affine i))
    (fun i => hc.map_affine (S.ratio i) (S.offset i)) S.weight S.weight_nonneg hμ hs hK
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i _
  change _ = S.weight i*(averaged (μ.map (fun x => S.ratio i*x+S.offset i)) s-
    averaged (μ.map (fun x => S.ratio i*x+S.offset i)) ((K : ℝ)*s))
  rw [averaged_affine μ hc hs (abs_pos.mp (S.ratio_pos i)),
    averaged_affine μ hc (mul_pos (by exact_mod_cast hK) hs) (abs_pos.mp (S.ratio_pos i))]
  congr 2
  ring_nf

theorem stopped_window_transfer (S : System ι) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : S.SelfSimilar μ) {a v : ℝ} (ha : 0 < a)
    (hai : ∀ i, a ≤ |S.ratio i|) (hv : 0 < v) {K : ℕ} (hK : 0 < K)
    {s : ℝ} (hs : 0 < s) (hsv : s < v) :
    averaged μ v-averaged μ ((K : ℝ)*v)-(Real.log (1/a+2)+Real.log 2) ≤
      averaged μ s-averaged μ ((K : ℝ)*s) := by
  obtain ⟨B,hB,hBμ⟩ := S.selfSimilar_compact μ hμ
  have hc : CompactlyCarried μ := ⟨B,hB.le,hBμ⟩
  apply S.stopped_lower (fun z => averaged μ z-averaged μ ((K : ℝ)*z)) ha hai hv
    (fun z hz => S.window_selfSimilar μ hμ hz hK) _ s hs hsv
  intro z hvz hza
  have hz : 0 < z := hv.trans_le hvz
  have hk : (0 : ℝ) < K := by exact_mod_cast hK
  have h1 := averaged_le_averaged_add_log_ratio μ hc hv hz
  have h2 := averaged_le_averaged_add_log_two μ hc (mul_pos hk hz) (mul_pos hk hv)
    (mul_le_mul_of_nonneg_left hvz hk.le)
  have hlog : Real.log (z/v+2) ≤ Real.log (1/a+2) := by
    apply Real.log_le_log (by positivity)
    suffices z/v ≤ 1/a by linarith
    apply (div_le_iff₀ hv).mpr
    simpa [div_eq_mul_inv, mul_comm] using hza
  linarith

end System

namespace MeasureEntropy

theorem geometric_gain_lower (F : ℝ → ℝ) {v K B : ℝ} (hv : 0 < v) (hK : 1 < K)
    (hg : ∀ s, 0 < s → s < v → B ≤ F s-F (K*s)) (m : ℕ) :
    F v+(m : ℝ)*B ≤ F (v*(1/K)^m) := by
  have hk : 0 < K := zero_lt_one.trans hK
  have hr : 0 < 1/K := div_pos zero_lt_one hk
  have hr1 : 1/K < 1 := (div_lt_one hk).mpr hK
  induction m with
  | zero => simp
  | succ m ih =>
    have hs : 0 < v*(1/K)^(m+1) := mul_pos hv (pow_pos hr _)
    have hsv : v*(1/K)^(m+1) < v := by
      nlinarith [pow_lt_one₀ hr.le hr1 (by omega : m+1 ≠ 0)]
    have he : K*(v*(1/K)^(m+1))=v*(1/K)^m := by
      rw [pow_succ]
      field_simp
    have hh := hg _ hs hsv
    rw [he] at hh
    push_cast
    nlinarith

theorem geometric_gain_bound (F : ℝ → ℝ) {v K B d C : ℝ} (hv : 0 < v) (hK : 1 < K)
    (hu : ∀ s, 0 < s → s < 1 → F s ≤ d*Real.log (1/s)+C)
    (hg : ∀ s, 0 < s → s < v → B ≤ F s-F (K*s)) : B ≤ d*Real.log K := by
  have hk : 0 < K := zero_lt_one.trans hK
  have hr : 0 < 1/K := div_pos zero_lt_one hk
  have hr1 : 1/K < 1 := (div_lt_one hk).mpr hK
  have ht : Filter.Tendsto (fun n : ℕ => v*(1/K)^(n+1)) Filter.atTop (nhds 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hr.le hr1).comp (Filter.tendsto_add_atTop_nat 1)
    simpa using h.const_mul v
  have he : ∀ᶠ n : ℕ in Filter.atTop,
      F v/((n : ℝ)+1)+B ≤ d*Real.log K + (C-d*Real.log v)/((n : ℝ)+1) := by
    filter_upwards [ht.eventually (gt_mem_nhds zero_lt_one)] with n hn
    have hg' := geometric_gain_lower F hv hK hg (n+1)
    have hu' := hu _ (mul_pos hv (pow_pos hr _)) hn
    have hlog : Real.log (1/(v*(1/K)^(n+1)))= ((n : ℝ)+1)*Real.log K-Real.log v := by
      rw [Real.log_div (by norm_num) (ne_of_gt (mul_pos hv (pow_pos hr _))), Real.log_one,
        Real.log_mul hv.ne' (pow_pos hr _).ne', Real.log_pow, Real.log_div (by norm_num) hk.ne',
        Real.log_one]
      push_cast
      ring
    rw [hlog] at hu'
    have hh : F v+((n : ℝ)+1)*B ≤ d*(((n : ℝ)+1)*Real.log K-Real.log v)+C := by
      exact_mod_cast hg'.trans hu'
    have hnpos : 0 < (n : ℝ)+1 := by positivity
    have hh' := (div_le_div_iff_of_pos_right hnpos).mpr hh
    have hl' : (F v+((n : ℝ)+1)*B)/((n : ℝ)+1) = F v/((n : ℝ)+1)+B := by
      field_simp
    have hr' : (d*(((n : ℝ)+1)*Real.log K-Real.log v)+C)/((n : ℝ)+1) =
        d*Real.log K+(C-d*Real.log v)/((n : ℝ)+1) := by
      field_simp
      ring
    rwa [hl',hr'] at hh'
  have hz : Filter.Tendsto (fun n : ℕ => 1/((n : ℝ)+1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hl : Filter.Tendsto (fun n : ℕ => F v/((n : ℝ)+1)+B) Filter.atTop (nhds B) := by
    simpa only [mul_one_div, mul_zero, zero_add] using (hz.const_mul (F v)).add_const B
  have hu' : Filter.Tendsto (fun n : ℕ => d*Real.log K+(C-d*Real.log v)/((n : ℝ)+1))
      Filter.atTop (nhds (d*Real.log K)) := by
    simpa only [mul_one_div, mul_zero, add_zero] using (hz.const_mul (C-d*Real.log v)).const_add (d*Real.log K)
  exact le_of_tendsto_of_tendsto hl hu' he

end MeasureEntropy

namespace System
variable {ι : Type uι} [Fintype ι] [Nonempty ι]
open MeasureEntropy

theorem uniform_nonsaturation_of_entropy_bound (S : System ι) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hμ : S.SelfSimilar μ) {d C : ℝ} (hd : d < 1)
    (hu : ∀ s, 0 < s → s < 1 → averaged μ s ≤ d*Real.log (1/s)+C) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ v : ℝ, 0 < v → δ ≤ deficit μ v := by
  classical
  obtain ⟨B,hB,hBμ⟩ := S.selfSimilar_compact μ hμ
  have hc : CompactlyCarried μ := ⟨B,hB.le,hBμ⟩
  obtain ⟨i,_,hi⟩ := Finset.exists_min_image Finset.univ (fun i => |S.ratio i|) Finset.univ_nonempty
  let a := |S.ratio i|
  have ha : 0 < a := S.ratio_pos i
  have hai : ∀ i, a ≤ |S.ratio i| := fun i => hi i (Finset.mem_univ i)
  let L := Real.log (1/a+2)+Real.log 2
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨j,hj⟩ := exists_nat_gt (max 1 ((L+1)/((1-d)*Real.log 2)))
  have hjpos : 0 < j := by have := (le_max_left _ _).trans_lt hj; exact_mod_cast (lt_trans zero_lt_one this)
  have hgap : L+1 < (1-d)*(j*Real.log 2) := by
    have hh := (div_lt_iff₀ (mul_pos (sub_pos.mpr hd) hl)).mp ((le_max_right _ _).trans_lt hj)
    nlinarith
  by_contra! h
  choose v hv hvd using fun n : ℕ => h (1/((n : ℝ)+1)) (by positivity)
  have hzero : Filter.Tendsto (fun n => deficit μ (v n)) Filter.atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat
      (fun n => (deficit_bounds μ hc (hv n)).1) (fun n => (hvd n).le)
  have hw := wide_window_saturation μ hc v hv hzero j
  obtain ⟨n,hn⟩ := (hw.eventually (lt_mem_nhds (by linarith :
    (j : ℝ)*Real.log 2-1 < j*Real.log 2))).exists
  have hk : 1 < (2 : ℝ)^j := one_lt_pow₀ (by norm_num) (by omega)
  have ht : ∀ s, 0 < s → s < v n →
      averaged μ (v n)-averaged μ ((2 : ℝ)^j*v n)-L ≤
        averaged μ s-averaged μ ((2 : ℝ)^j*s) := by
    intro s hs hsn
    simpa only [L, Nat.cast_pow, Nat.cast_ofNat] using
      S.stopped_window_transfer μ hμ ha hai (hv n) (K := 2^j) (by positivity) hs hsn
  have hh := geometric_gain_bound (averaged μ) (hv n) hk hu ht
  rw [Real.log_pow] at hh
  nlinarith

end System

end EntropyRateDimension
end

end OAI
