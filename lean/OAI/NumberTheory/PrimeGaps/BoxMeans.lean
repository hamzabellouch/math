import OAI.NumberTheory.PrimeGaps.SingularTails

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

noncomputable def distinctBox {s h : ℕ} (a : Fin s → ℤ) : Finset (Fin s → Fin h) :=
  Finset.univ.filter fun n => Function.Injective (boxTuple a n)

noncomputable def truncatedBoxMean {s h : ℕ} (a : Fin s → ℤ) (q : ℕ) : ℝ :=
  (∑ n : Fin s → Fin h, siftedTuple (boxTuple a n) q)/(h:ℝ)^s

noncomputable def distinctTruncatedBoxMean {s h : ℕ} (a : Fin s → ℤ) (q : ℕ) : ℝ :=
  (∑ n ∈ distinctBox (h:=h) a, siftedTuple (boxTuple a n) q)/(h:ℝ)^s

noncomputable def singularBoxMean {s h : ℕ} (a : Fin s → ℤ) : ℝ :=
  (∑ n ∈ distinctBox (h:=h) a, singularSeries (Finset.univ.image (boxTuple a n)))/(h:ℝ)^s

theorem siftedTuple_boxTuple {s h q : ℕ} [NeZero q] (a : Fin s → ℤ) (n : Fin s → Fin h) :
    siftedTuple (boxTuple a n) q = normalizedSiftedCount (residueTuple (q:=q) a n) := by
  rw [siftedTuple_eq]
  congr 1
  funext i
  simp only [boxTuple, residueTuple, Int.cast_add, Int.cast_natCast]

theorem truncatedBoxMean_bounds {s h q : ℕ} [NeZero q] (hh : 0<h) (hq : q≤h)
    (a : Fin s → ℤ) :
    (1-(q:ℝ)/h)^s ≤ truncatedBoxMean (h:=h) a q ∧
    truncatedBoxMean (h:=h) a q ≤ (1+(q:ℝ)/h)^s := by
  have hhR : (0:ℝ)<h := by exact_mod_cast hh
  have hqR : (q:ℝ)≤h := by exact_mod_cast hq
  have hdiv : ((h/q:ℕ):ℝ)*(q:ℝ) ≤ h := by exact_mod_cast Nat.div_mul_le_self h q
  have hfloor : (h:ℝ)-(q:ℝ) ≤ ((h/q:ℕ):ℝ)*(q:ℝ) := by
    have he := Nat.div_add_mod h q
    have hm := Nat.mod_lt h (NeZero.pos q)
    have heR : ((h/q:ℕ):ℝ)*(q:ℝ)+(h%q:ℕ)=h := by
      exact_mod_cast (by simpa only [Nat.mul_comm] using he : h/q*q+h%q=h)
    have hmR : ((h%q:ℕ):ℝ)<q := by exact_mod_cast hm
    linarith
  have hb := residueTuple_sum_bounds (h:=h) a (@normalizedSiftedCount s q _) normalizedSiftedCount_nonneg
  rw [normalizedSiftedCount_sum] at hb
  simp_rw [← siftedTuple_boxTuple] at hb
  unfold truncatedBoxMean
  constructor
  · calc
      _ = ((h:ℝ)-(q:ℝ))^s/(h:ℝ)^s := by rw [← div_pow]; congr 1; field_simp
      _ ≤ (((h/q:ℕ):ℝ)*(q:ℝ))^s/(h:ℝ)^s := div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (sub_nonneg.mpr hqR) hfloor s) (by positivity)
      _ ≤ _ := by rw [mul_pow]; exact div_le_div_of_nonneg_right hb.1 (by positivity)
  · calc
      _ ≤ (((h/q+1:ℕ):ℝ)*(q:ℝ))^s/(h:ℝ)^s := by
        rw [mul_pow]; exact div_le_div_of_nonneg_right hb.2 (by positivity)
      _ ≤ ((h:ℝ)+(q:ℝ))^s/(h:ℝ)^s := div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) (by push_cast; nlinarith) s) (by positivity)
      _ = _ := by rw [← div_pow]; congr 1; field_simp

theorem distinctTruncatedBoxMean_nonneg {s h q : ℕ} [NeZero q] (a : Fin s → ℤ) :
    0 ≤ distinctTruncatedBoxMean (h:=h) a q := by
  apply div_nonneg _ (by positivity)
  apply Finset.sum_nonneg
  intro n _
  rw [siftedTuple_eq]
  exact normalizedSiftedCount_nonneg _

theorem distinctTruncatedBoxMean_le {s h q : ℕ} [NeZero q] (a : Fin s → ℤ) :
    distinctTruncatedBoxMean (h:=h) a q ≤ truncatedBoxMean (h:=h) a q := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro n _ _
  rw [siftedTuple_eq]
  exact normalizedSiftedCount_nonneg _

theorem truncatedBoxMean_sub_distinct_le {s h q : ℕ} [NeZero q] (hh : 0<h)
    (a : Fin s → ℤ) :
    truncatedBoxMean (h:=h) a q - distinctTruncatedBoxMean (h:=h) a q ≤
      (s:ℝ)^2*(q:ℝ)^s/(h:ℝ) := by
  classical
  by_cases hs : s=0
  · subst s
    have hall : distinctBox (h:=h) a = Finset.univ := by
      ext n
      simp [distinctBox, Function.Injective]
    simp [truncatedBoxMean, distinctTruncatedBoxMean, hall]
  have hhR : (0:ℝ)<h := by exact_mod_cast hh
  have hsum := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin s → Fin h))
    (fun n => Function.Injective (boxTuple a n)) (fun n => siftedTuple (boxTuple a n) q)
  have hb : (∑ n ∈ Finset.univ.filter (fun n : Fin s → Fin h => ¬Function.Injective (boxTuple a n)),
      siftedTuple (boxTuple a n) q) ≤ (s:ℝ)^2*(h:ℝ)^(s-1)*(q:ℝ)^s := by
    calc
      _ ≤ ((Finset.univ.filter fun n : Fin s → Fin h => ¬Function.Injective (boxTuple a n)).card:ℝ) *
          (q:ℝ)^s := by
        simpa only [nsmul_eq_mul] using Finset.sum_le_card_nsmul _ _ ((q:ℝ)^s) (fun n _ => by
          rw [siftedTuple_eq]
          exact normalizedSiftedCount_le _)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast boxTuple_nondistinct_count (h:=h) a)
        (by positivity)
  unfold truncatedBoxMean distinctTruncatedBoxMean distinctBox
  rw [← sub_div]
  calc
    _ ≤ ((s:ℝ)^2*(h:ℝ)^(s-1)*(q:ℝ)^s)/(h:ℝ)^s := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith [hsum]
    _ = _ := by
      have hp : (h:ℝ)^s=(h:ℝ)^(s-1)*(h:ℝ) := by
        rw [← pow_succ]; congr 1; omega
      rw [hp]
      field_simp

noncomputable def boxTruncationError (s h q : ℕ) : ℝ :=
  |(1-(q:ℝ)/h)^s-1| + |(1+(q:ℝ)/h)^s-1| + (s:ℝ)^2*(q:ℝ)^s/h

theorem distinctTruncatedBoxMean_error {s h q : ℕ} [NeZero q] (hh : 0<h) (hq : q≤h)
    (a : Fin s → ℤ) :
    |distinctTruncatedBoxMean (h:=h) a q-1| ≤ boxTruncationError s h q := by
  have hb := truncatedBoxMean_bounds hh hq a
  have hd := truncatedBoxMean_sub_distinct_le (q:=q) hh a
  have hle := distinctTruncatedBoxMean_le (q:=q) (h:=h) a
  unfold boxTruncationError
  apply abs_le.mpr
  constructor
  · have hl := neg_abs_le ((1-(q:ℝ)/h)^s-1)
    have hpos := abs_nonneg ((1+(q:ℝ)/h)^s-1)
    linarith
  · have hu := le_abs_self ((1+(q:ℝ)/h)^s-1)
    have hpos := abs_nonneg ((1-(q:ℝ)/h)^s-1)
    have hnn : 0≤(s:ℝ)^2*(q:ℝ)^s/h := by positivity
    linarith

noncomputable def uniformSingularTailBound (s M y : ℕ) : ℝ :=
  2*((s:ℝ)^2*(2:ℝ)^s)/(y:ℝ) +
    4*(s:ℝ)*((s*(s-1):ℕ):ℝ)*Real.log M/((y:ℝ)*Real.log y)

theorem singularTailBound_le_uniform {s M y : ℕ} (a : Fin s → ℤ)
    (ha : Function.Injective a) (hy : 1<y)
    (hd : ∀ i j, (a i-a j).natAbs ≤ M) :
    singularTailBound (Finset.univ.image a) y ≤ uniformSingularTailBound s M y := by
  have hc : (Finset.univ.image a).card=s := by
    rw [Finset.card_image_of_injective _ ha, Finset.card_univ, Fintype.card_fin]
  have hb := differenceProduct_le (Finset.univ.image a) (M:=M) (by
    intro x hx z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hz
    exact hd i j)
  rw [hc] at hb
  have hl : Real.log (differenceProduct (Finset.univ.image a)) ≤
      ((s*(s-1):ℕ):ℝ)*Real.log M := by
    rw [← Real.log_pow]
    apply Real.log_le_log
    · exact_mod_cast differenceProduct_pos (Finset.univ.image a)
    · exact_mod_cast hb
  unfold singularTailBound uniformSingularTailBound
  rw [hc]
  apply add_le_add le_rfl
  calc
    _ ≤ 4*(s:ℝ)*(((s*(s-1):ℕ):ℝ)*Real.log M)/((y:ℝ)*Real.log y) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hl (by positivity))
        (mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast (show 1≤y by omega))))
    _ = _ := by ring

def boxDiameterBound {s h : ℕ} (a : Fin s → ℤ) (M : ℕ) : Prop :=
  ∀ (n : Fin s → Fin h) i j, (boxTuple a n i-boxTuple a n j).natAbs ≤ M

theorem uniformSingularTailBound_nonneg (s : ℕ) {M y : ℕ} (hM : 0<M) (hy : 1<y) :
    0 ≤ uniformSingularTailBound s M y := by
  have hlogM : 0≤Real.log (M:ℝ) := Real.log_nonneg (by exact_mod_cast hM)
  have hlogy : 0≤Real.log (y:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤y by omega))
  unfold uniformSingularTailBound
  positivity

theorem singularBoxMean_sub_truncation {s h M y : ℕ} (a : Fin s → ℤ)
    (hy : 1<y) (hys : 2*s≤y) (hd : boxDiameterBound (h:=h) a M)
    (hB : uniformSingularTailBound s M y≤1) :
    |singularBoxMean (h:=h) a-distinctTruncatedBoxMean (h:=h) a (primorial y)| ≤
      2*uniformSingularTailBound s M y*distinctTruncatedBoxMean (h:=h) a (primorial y) := by
  classical
  let : NeZero (primorial y) := ⟨(primorial_pos y).ne'⟩
  have hpoint (n : Fin s → Fin h) (hn : n∈distinctBox a) :
      |singularSeries (Finset.univ.image (boxTuple a n))-siftedTuple (boxTuple a n) (primorial y)| ≤
      2*uniformSingularTailBound s M y*siftedTuple (boxTuple a n) (primorial y) := by
    have hi := (Finset.mem_filter.mp hn).2
    have hc : (Finset.univ.image (boxTuple a n)).card=s := by
      rw [Finset.card_image_of_injective _ hi, Finset.card_univ, Fintype.card_fin]
    have hut := singularTailBound_le_uniform (boxTuple a n) hi hy (hd n)
    have ht := singularTail_error (Finset.univ.image (boxTuple a n)) hy (by simpa only [hc] using hys)
      (hut.trans hB)
    have hp : 0 ≤ siftedTuple (boxTuple a n) (primorial y) := by
      rw [siftedTuple_eq]
      exact normalizedSiftedCount_nonneg _
    rw [singularSeries_eq_truncation_mul_tail _ hy (by simpa only [hc] using hys),
      ← siftedTuple_primorial_eq _ hi, ← primorial_eq_prod_primesLE]
    calc
      _ = siftedTuple (boxTuple a n) (primorial y)*|singularTail (Finset.univ.image (boxTuple a n)) y-1| := by
        rw [← mul_sub_one, abs_mul, abs_of_nonneg hp]
      _ ≤ siftedTuple (boxTuple a n) (primorial y)*(2*uniformSingularTailBound s M y) :=
        mul_le_mul_of_nonneg_left (ht.trans (mul_le_mul_of_nonneg_left hut (by norm_num))) hp
      _ = _ := by ring
  unfold singularBoxMean distinctTruncatedBoxMean
  rw [← sub_div, abs_div, abs_of_nonneg (by positivity : 0≤(h:ℝ)^s), ← Finset.sum_sub_distrib]
  calc
    _ ≤ (∑ n ∈ distinctBox a, |singularSeries (Finset.univ.image (boxTuple a n))-
        siftedTuple (boxTuple a n) (primorial y)|)/(h:ℝ)^s :=
      div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ (∑ n ∈ distinctBox a, 2*uniformSingularTailBound s M y*
        siftedTuple (boxTuple a n) (primorial y))/(h:ℝ)^s :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum hpoint) (by positivity)
    _ = _ := by rw [← Finset.mul_sum]; ring

theorem singularBoxMean_error {s h M y : ℕ} (a : Fin s → ℤ) (hh : 0<h)
    (hM : 0<M) (hy : 1<y) (hys : 2*s≤y) (hd : boxDiameterBound (h:=h) a M)
    (hB : uniformSingularTailBound s M y≤1) (hq : primorial y≤h) :
    |singularBoxMean (h:=h) a-1| ≤ boxTruncationError s h (primorial y) +
      2*uniformSingularTailBound s M y*(1+(primorial y:ℝ)/h)^s := by
  let : NeZero (primorial y) := ⟨(primorial_pos y).ne'⟩
  have hb := uniformSingularTailBound_nonneg s hM hy
  calc
    _ ≤ |singularBoxMean (h:=h) a-distinctTruncatedBoxMean (h:=h) a (primorial y)| +
        |distinctTruncatedBoxMean (h:=h) a (primorial y)-1| := abs_sub_le _ _ _
    _ ≤ 2*uniformSingularTailBound s M y*distinctTruncatedBoxMean (h:=h) a (primorial y) +
        boxTruncationError s h (primorial y) := add_le_add
      (singularBoxMean_sub_truncation a hy hys hd hB) (distinctTruncatedBoxMean_error hh hq a)
    _ ≤ 2*uniformSingularTailBound s M y*(1+(primorial y:ℝ)/h)^s +
        boxTruncationError s h (primorial y) := add_le_add_left
      (mul_le_mul_of_nonneg_left ((distinctTruncatedBoxMean_le (q:=primorial y) a).trans (truncatedBoxMean_bounds hh hq a).2)
        (show 0 ≤ 2*uniformSingularTailBound s M y from mul_nonneg (by norm_num) hb)) _
    _ = _ := by ring

noncomputable def singularCutoffScale (s : ℕ) : ℝ := 2*((s:ℝ)+1)*Real.log 4

noncomputable def singularCutoff (s h : ℕ) : ℕ := ⌊Real.log h/singularCutoffScale s⌋₊

theorem singularCutoffScale_pos (s : ℕ) : 0<singularCutoffScale s := by
  unfold singularCutoffScale
  positivity

theorem singularCutoff_tendsto (s : ℕ) : Tendsto (singularCutoff s) atTop atTop :=
  tendsto_nat_floor_atTop.comp (Tendsto.atTop_div_const (singularCutoffScale_pos s)
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))

theorem singularCutoff_ratio_tendsto (s : ℕ) :
    Tendsto (fun h : ℕ => (singularCutoff s h:ℝ)/Real.log h) atTop (𝓝 (1/singularCutoffScale s)) := by
  have hh := (tendsto_nat_floor_mul_div_atTop (a:=1/singularCutoffScale s)
    (one_div_nonneg.mpr (singularCutoffScale_pos s).le)).comp
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ)))
  simpa only [singularCutoff, one_div_mul_eq_div, Function.comp_def] using hh

theorem log_div_singularCutoff_tendsto (s : ℕ) :
    Tendsto (fun h : ℕ => Real.log h/(singularCutoff s h:ℝ)) atTop (𝓝 (singularCutoffScale s)) := by
  simpa only [inv_div, one_div, inv_inv] using (singularCutoff_ratio_tendsto s).inv₀
    (one_div_ne_zero (singularCutoffScale_pos s).ne')

theorem primorial_singularCutoff_power_bound (s : ℕ) {h : ℕ} (hh : 0<h) :
    (primorial (singularCutoff s h):ℝ)^(s+1) ≤ (h:ℝ)^(1/2:ℝ) := by
  have hhR : (0:ℝ)<h := by exact_mod_cast hh
  have hlog : 0≤Real.log (h:ℝ) := Real.log_nonneg (by exact_mod_cast hh)
  have hfloor := Nat.floor_le (div_nonneg hlog (singularCutoffScale_pos s).le)
  change (singularCutoff s h:ℝ) ≤ Real.log h/singularCutoffScale s at hfloor
  have hb := (le_div_iff₀ (singularCutoffScale_pos s)).mp hfloor
  have hexp : ((singularCutoff s h:ℝ)*((s:ℝ)+1))*Real.log 4 ≤ Real.log h*(1/2) := by
    unfold singularCutoffScale at hb
    nlinarith
  calc
    _ ≤ ((4:ℝ)^(singularCutoff s h))^(s+1) := pow_le_pow_left₀ (by positivity)
      (by exact_mod_cast primorial_le_four_pow (singularCutoff s h)) _
    _ = Real.exp (((singularCutoff s h:ℝ)*((s:ℝ)+1))*Real.log 4) := by
      rw [← pow_mul, ← Real.exp_log (by norm_num : (0:ℝ)<4), ← Real.exp_nat_mul]
      rw [Real.log_exp]
      push_cast
      congr 1
    _ ≤ _ := by rw [Real.rpow_def_of_pos hhR]; exact Real.exp_le_exp.mpr hexp

theorem primorial_singularCutoff_ratio_tendsto (s r : ℕ) (hr : r ≤ s+1) :
    Tendsto (fun h : ℕ => (primorial (singularCutoff s h):ℝ)^r/(h:ℝ)) atTop (𝓝 0) := by
  have ht : Tendsto (fun h : ℕ => (h:ℝ)^(-(1/2:ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/2)).comp tendsto_natCast_atTop_atTop
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
  · exact Filter.Eventually.of_forall fun h => by positivity
  · filter_upwards [eventually_ge_atTop 1] with h hh
    have hhR : (0:ℝ)<h := by exact_mod_cast hh
    calc
      _ ≤ (primorial (singularCutoff s h):ℝ)^(s+1)/(h:ℝ) :=
        div_le_div_of_nonneg_right (by exact_mod_cast (Nat.pow_le_pow_right
          (primorial_pos (singularCutoff s h)) hr)) hhR.le
      _ ≤ (h:ℝ)^(1/2:ℝ)/(h:ℝ) := div_le_div_of_nonneg_right
        (primorial_singularCutoff_power_bound s (by omega)) hhR.le
      _ = _ := by
        have he := Real.rpow_sub hhR (1/2:ℝ) 1
        norm_num only [Real.rpow_one, show (1/2:ℝ)-1=-(1/2) by norm_num] at he
        exact he.symm

theorem primorial_singularCutoff_div_tendsto (s : ℕ) :
    Tendsto (fun h : ℕ => (primorial (singularCutoff s h):ℝ)/(h:ℝ)) atTop (𝓝 0) := by
  simpa only [pow_one] using primorial_singularCutoff_ratio_tendsto s 1 (by omega)

theorem log_mul_div_singularCutoff_tendsto (s : ℕ) {K : ℕ} (hK : 0<K) :
    Tendsto (fun h : ℕ => Real.log (K*h:ℕ)/(singularCutoff s h:ℝ)) atTop (𝓝 (singularCutoffScale s)) := by
  have hy := tendsto_natCast_atTop_atTop (R:=ℝ) |>.comp (singularCutoff_tendsto s)
  have hz : Tendsto (fun h : ℕ => Real.log (K:ℝ)/(singularCutoff s h:ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero, div_eq_mul_inv, Pi.inv_apply, Function.comp_apply] using hy.inv_tendsto_atTop.const_mul (Real.log (K:ℝ))
  have ht := hz.add (log_div_singularCutoff_tendsto s)
  rw [zero_add] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with h hh
  rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hK.ne') (by exact_mod_cast (show h≠0 by omega)), add_div]

theorem uniformSingularTailBound_tendsto (s : ℕ) {K : ℕ} (hK : 0<K) :
    Tendsto (fun h : ℕ => uniformSingularTailBound s (K*h) (singularCutoff s h)) atTop (𝓝 0) := by
  have hy := tendsto_natCast_atTop_atTop (R:=ℝ) |>.comp (singularCutoff_tendsto s)
  have hl := Real.tendsto_log_atTop.comp hy
  have ht := (hy.inv_tendsto_atTop.const_mul (2*((s:ℝ)^2*(2:ℝ)^s))).add
    (((log_mul_div_singularCutoff_tendsto s hK).mul hl.inv_tendsto_atTop).const_mul
      (4*(s:ℝ)*((s*(s-1):ℕ):ℝ)))
  simp only [mul_zero, add_zero] at ht
  convert ht using 1
  ext h
  unfold uniformSingularTailBound
  simp only [div_eq_mul_inv, mul_inv_rev, Pi.inv_apply, Function.comp_apply]
  ring

theorem boxTruncationError_tendsto (s : ℕ) :
    Tendsto (fun h : ℕ => boxTruncationError s h (primorial (singularCutoff s h))) atTop (𝓝 0) := by
  have hq := primorial_singularCutoff_div_tendsto s
  have hl := ((tendsto_const_nhds (x:=(1:ℝ)).sub hq).pow s).sub (tendsto_const_nhds (x:=(1:ℝ)))
  have hu := ((tendsto_const_nhds (x:=(1:ℝ)).add hq).pow s).sub (tendsto_const_nhds (x:=(1:ℝ)))
  have hd := (primorial_singularCutoff_ratio_tendsto s s (by omega)).const_mul ((s:ℝ)^2)
  have ht := (hl.abs.add hu.abs).add hd
  simp only [sub_zero, one_pow, sub_self, add_zero, abs_zero, mul_zero] at ht
  convert ht using 1
  ext h
  unfold boxTruncationError
  ring

noncomputable def singularBoxError (s K h : ℕ) : ℝ :=
  boxTruncationError s h (primorial (singularCutoff s h)) +
    2*uniformSingularTailBound s (K*h) (singularCutoff s h)*
      (1+(primorial (singularCutoff s h):ℝ)/h)^s

theorem singularBoxError_tendsto (s : ℕ) {K : ℕ} (hK : 0<K) :
    Tendsto (singularBoxError s K) atTop (𝓝 0) := by
  have ht := (boxTruncationError_tendsto s).add
    (((uniformSingularTailBound_tendsto s hK).const_mul 2).mul
      ((tendsto_const_nhds (x:=(1:ℝ))).add (primorial_singularCutoff_div_tendsto s) |>.pow s))
  simp only [mul_zero, zero_mul, add_zero] at ht
  exact ht

theorem singularBoxMean_error_eventually (s : ℕ) {K : ℕ} (hK : 0<K) :
    ∀ᶠ h : ℕ in atTop, ∀ a : Fin s → ℤ, boxDiameterBound (h:=h) a (K*h) →
      |singularBoxMean (h:=h) a-1| ≤ singularBoxError s K h := by
  have hB := (uniformSingularTailBound_tendsto s hK).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  have hq := (primorial_singularCutoff_div_tendsto s).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [eventually_ge_atTop 1, (singularCutoff_tendsto s).eventually_ge_atTop 2,
      (singularCutoff_tendsto s).eventually_ge_atTop (2*s), hB, hq] with h hh hy hys hB hq
  intro a hd
  have hqh : primorial (singularCutoff s h) ≤ h := by
    have hhR : (0:ℝ)<h := by exact_mod_cast hh
    have ht := (div_lt_one hhR).mp hq
    exact_mod_cast ht.le
  exact singularBoxMean_error a (by omega) (Nat.mul_pos hK (by omega)) (by omega) hys hd hB.le hqh

theorem singularBoxMean_uniform (s : ℕ) {K : ℕ} (hK : 0<K) {ε : ℝ} (hε : 0<ε) :
    ∃ h₀ : ℕ, ∀ h≥h₀, ∀ a : Fin s → ℤ, boxDiameterBound (h:=h) a (K*h) →
      |singularBoxMean (h:=h) a-1| < ε := by
  have he := (singularBoxError_tendsto s hK).eventually (gt_mem_nhds hε)
  have hb := (singularBoxMean_error_eventually s hK).and he
  obtain ⟨h₀, hh₀⟩ := Filter.eventually_atTop.mp hb
  exact ⟨h₀, fun h hh a hd => ((hh₀ h hh).1 a hd).trans_lt (hh₀ h hh).2⟩

end LargePrimeGaps

end OAI
