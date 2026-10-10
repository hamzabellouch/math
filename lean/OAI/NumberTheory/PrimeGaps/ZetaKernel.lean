import OAI.NumberTheory.PrimeGaps.BoxMeans

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

theorem mangoldt_log_term_nonneg (s : ℝ) (n : ℕ) :
    0 ≤ ArithmeticFunction.vonMangoldt n / ((n:ℝ)^s*Real.log n) := by
  positivity

theorem mangoldt_log_term_le (s : ℝ) (n : ℕ) :
    ArithmeticFunction.vonMangoldt n / ((n:ℝ)^s*Real.log n) ≤ 1/(n:ℝ)^s := by
  by_cases hn : n≤1
  · interval_cases n <;> simp
    positivity
  have hnR : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
  have hlog : 0<Real.log (n:ℝ) := Real.log_pos hnR
  have hpow : 0<(n:ℝ)^s := Real.rpow_pos_of_pos (by linarith) _
  calc
    _ ≤ Real.log (n:ℝ)/((n:ℝ)^s*Real.log n) :=
      div_le_div_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log (mul_pos hpow hlog).le
    _ = _ := by field_simp

theorem prime_power_sum_le_log_zeta (X : ℕ) {s : ℝ} (hs : 1<s) :
    (∑ p ∈ Nat.primesLE X, 1/(p:ℝ)^s) ≤ Real.log (riemannZeta (s:ℂ)).re := by
  have hsum : Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt n / ((n:ℝ)^s*Real.log n)) :=
    (Real.summable_one_div_nat_rpow.mpr hs).of_nonneg_of_le
      (mangoldt_log_term_nonneg s) (mangoldt_log_term_le s)
  rw [log_riemannZeta_eq hs]
  calc
    _ = ∑ p ∈ Nat.primesLE X, ArithmeticFunction.vonMangoldt p / ((p:ℝ)^s*Real.log p) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hpP := (Nat.mem_primesLE.mp hp).2
      have hl : Real.log (p:ℝ)≠0 := (Real.log_pos (by exact_mod_cast hpP.one_lt)).ne'
      rw [ArithmeticFunction.vonMangoldt_apply_prime hpP]
      field_simp
    _ ≤ _ := Summable.sum_le_tsum _ (fun n _ => mangoldt_log_term_nonneg s n) hsum

theorem prime_reciprocal_rankin (X : ℕ) (hX : 2≤X) :
    (∑ p ∈ Nat.primesLE X, (1:ℝ)/p) ≤
      Real.exp 1*Real.log (riemannZeta ((1+1/Real.log X:ℝ):ℂ)).re := by
  have hlog : 0<Real.log (X:ℝ) := Real.log_pos (by exact_mod_cast hX)
  have hs : 1<(1:ℝ)+1/Real.log X := lt_add_of_pos_right 1 (one_div_pos.mpr hlog)
  calc
    _ ≤ ∑ p ∈ Nat.primesLE X, Real.exp 1*(1/(p:ℝ)^(1+1/Real.log X)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpP := (Nat.mem_primesLE.mp hp).2
      have hpX := (Nat.mem_primesLE.mp hp).1
      have hp0 : (0:ℝ)<p := by exact_mod_cast hpP.pos
      have hpY : Real.log (p:ℝ)≤Real.log (X:ℝ) := Real.log_le_log hp0 (by exact_mod_cast hpX)
      have he : (p:ℝ)^(1/Real.log X:ℝ) ≤ Real.exp 1 := by
        rw [Real.rpow_def_of_pos hp0]
        apply Real.exp_le_exp.mpr
        simpa only [mul_one_div] using (div_le_one hlog).mpr hpY
      calc
        _ = (p:ℝ)^(1/Real.log X:ℝ)/(p:ℝ)^(1+1/Real.log X:ℝ) := by
          rw [Real.rpow_add hp0, Real.rpow_one]
          field_simp
        _ ≤ Real.exp 1/(p:ℝ)^(1+1/Real.log X:ℝ) := div_le_div_of_nonneg_right he (by positivity)
        _ = _ := by ring
    _ = Real.exp 1*(∑ p ∈ Nat.primesLE X, 1/(p:ℝ)^(1+1/Real.log X:ℝ)) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (prime_power_sum_le_log_zeta X hs) (Real.exp_pos _).le

theorem eventually_prime_reciprocal_bound :
    ∀ᶠ X : ℕ in atTop, (∑ p ∈ Nat.primesLE X, (1:ℝ)/p) ≤
      Real.exp 1*(1+Real.log (Real.log X)) := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hx : Tendsto (fun X : ℕ => (1:ℝ)+1/Real.log X) atTop (𝓝[>] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,?_⟩
    · simpa only [one_div, add_zero, Pi.inv_apply, Function.comp_def] using tendsto_const_nhds.add hlog.inv_tendsto_atTop
    · filter_upwards [eventually_ge_atTop 2] with X hX
      exact lt_add_of_pos_right 1 (one_div_pos.mpr (Real.log_pos (by exact_mod_cast hX)))
  have hζ : Tendsto (fun s : ℝ => Real.log (riemannZeta (s:ℂ)).re + Real.log (s-1))
      (𝓝[>] 1) (𝓝 0) :=
    log_riemannZeta_add_log_sub_isLittleO_ofReal.tendsto_zero_of_tendsto tendsto_const_nhds
  have hb := (hζ.comp hx).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [hb, eventually_ge_atTop 2] with X hζX hX
  have he : Real.log (riemannZeta ((1+1/Real.log X:ℝ):ℂ)).re ≤ 1+Real.log (Real.log X) := by
    dsimp only [Function.comp_apply] at hζX
    rw [add_sub_cancel_left, one_div, Real.log_inv] at hζX
    simp only [one_div] at *
    linarith
  exact (prime_reciprocal_rankin X hX).trans (mul_le_mul_of_nonneg_left he (Real.exp_pos _).le)

open Asymptotics

theorem zeta_pole_linear_error :
    ∃ c>0, ∃ ε>0, ∀ z : ℂ, z≠0 → ‖z‖<ε →
      ‖z*riemannZeta (1+z)-1‖ ≤ c*‖z‖ := by
  obtain ⟨c,hc,hbound⟩ := (differentiable_riemannZeta₁ 1).isBigO_sub.exists_pos
  have hb := hbound.bound
  rw [Metric.eventually_nhds_iff] at hb
  obtain ⟨ε,hε,hεb⟩ := hb
  refine ⟨c,hc,ε,hε,fun z hz hze => ?_⟩
  have hs : (1:ℂ)+z≠1 := by simpa using hz
  have ht := @hεb (1+z) (by simpa only [dist_eq_norm, add_sub_cancel_left] using hze)
  have he : z*riemannZeta (1+z) = riemannZeta₁ (1+z) := by
    rw [riemannZeta_eq_inv_sub_mul hs, add_sub_cancel_left, ← mul_assoc, mul_inv_cancel₀ hz, one_mul]
  simpa only [riemannZeta₁_one, add_sub_cancel_left, he] using ht

theorem zeta_pole_two_sided :
    ∃ c>0, ∃ ε>0, ∀ z : ℂ, z≠0 → ‖z‖<ε →
      ‖z*riemannZeta (1+z)-1‖ ≤ c*‖z‖ ∧
      1/2 ≤ ‖z*riemannZeta (1+z)‖ ∧ ‖z*riemannZeta (1+z)‖ ≤ 3/2 := by
  obtain ⟨c,hc,ε,hε,hb⟩ := zeta_pole_linear_error
  refine ⟨c,hc,min ε (1/(2*c)), lt_min hε (by positivity), fun z hz hze => ?_⟩
  have he := hb z hz (hze.trans_le (min_le_left _ _))
  have hzbound : c*‖z‖<1/2 := by
    have hh := hze.trans_le (min_le_right _ _)
    have hm := (lt_div_iff₀ (show 0<2*c by positivity)).mp hh
    nlinarith
  refine ⟨he,?_,?_⟩
  · have ht := norm_sub_norm_le (1:ℂ) (z*riemannZeta (1+z))
    rw [norm_one, norm_sub_rev] at ht
    linarith
  · have ht := norm_sub_norm_le (z*riemannZeta (1+z)) (1:ℂ)
    rw [norm_one] at ht
    linarith

theorem norm_prod_sub_prod_le {ι : Type*} (s : Finset ι) (f g : ι → ℂ)
    (B e : ι → ℝ) (hB : ∀ i∈s, 1≤B i)
    (hf : ∀ i∈s, ‖f i‖≤B i) (hg : ∀ i∈s, ‖g i‖≤B i)
    (he : ∀ i∈s, ‖f i-g i‖≤e i) :
    ‖(∏ i∈s, f i)-(∏ i∈s, g i)‖ ≤ (∏ i∈s, B i)*(∑ i∈s, e i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hBas : ∀ i∈s, 1≤B i := fun i hi => hB i (Finset.mem_insert_of_mem hi)
    have hfs : ∀ i∈s, ‖f i‖≤B i := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hgs : ∀ i∈s, ‖g i‖≤B i := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hes : ∀ i∈s, ‖f i-g i‖≤e i := fun i hi => he i (Finset.mem_insert_of_mem hi)
    have hBa := hB a (Finset.mem_insert_self _ _)
    have hga := hg a (Finset.mem_insert_self _ _)
    have hea := he a (Finset.mem_insert_self _ _)
    have hea0 : 0≤e a := (norm_nonneg _).trans hea
    have hprod0 : 0≤∏ i∈s, B i := Finset.prod_nonneg (fun i hi => (hBas i hi).trans' zero_le_one)
    have hsum0 : 0≤∑ i∈s, e i := Finset.sum_nonneg fun i hi => (norm_nonneg _).trans (hes i hi)
    have hprod : ‖∏ i∈s, f i‖≤∏ i∈s, B i := by
      rw [norm_prod]
      exact Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) hfs
    have hi := ih hBas hfs hgs hes
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    calc
      _ = ‖(f a-g a)*(∏ i∈s, f i)+g a*((∏ i∈s, f i)-(∏ i∈s, g i))‖ := by congr 1; ring
      _ ≤ ‖f a-g a‖*‖∏ i∈s, f i‖+‖g a‖*‖(∏ i∈s, f i)-(∏ i∈s, g i)‖ := by
        simpa only [norm_mul] using norm_add_le ((f a-g a)*(∏ i∈s, f i)) (g a*((∏ i∈s, f i)-(∏ i∈s, g i)))
      _ ≤ e a*(∏ i∈s, B i)+B a*((∏ i∈s, B i)*(∑ i∈s, e i)) := by
        gcongr
      _ ≤ (B a*(∏ i∈s, B i))*(e a+∑ i∈s, e i) := by
        nlinarith [mul_nonneg hea0 hprod0, mul_nonneg (sub_nonneg.mpr hBa) (mul_nonneg hea0 hprod0)]

theorem norm_prod_sub_one_le {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    {B e : ℝ} (hB : 1≤B) (hf : ∀ i∈s, ‖f i‖≤B) (he : ∀ i∈s, ‖f i-1‖≤e) :
    ‖(∏ i∈s, f i)-1‖ ≤ B^s.card*(s.card*e) := by
  simpa only [Finset.prod_const, Finset.sum_const, nsmul_eq_mul, Finset.prod_const_one, one_pow]
    using norm_prod_sub_prod_le s f (fun _ => 1) (fun _ => B) (fun _ => e)
      (fun _ _ => hB) hf (by simpa using fun _ _ => hB) he

noncomputable def nonemptySubsets {ι : Type*} (s : Finset ι) : Finset (Finset ι) := by
  classical
  exact s.powerset.erase ∅

theorem mem_nonemptySubsets {ι : Type*} {s S : Finset ι} :
    S∈nonemptySubsets s ↔ S.Nonempty ∧ S⊆s := by
  classical
  simp [nonemptySubsets, Finset.nonempty_iff_ne_empty]

theorem sum_nonemptySubsets_sign {ι : Type*} {s : Finset ι} (hs : s.Nonempty) :
    (∑ S∈nonemptySubsets s, (-1:ℤ)^S.card) = -1 := by
  classical
  have h := Finset.sum_erase_add s.powerset (fun S => (-1:ℤ)^S.card) (Finset.empty_mem_powerset s)
  rw [Finset.sum_powerset_neg_one_pow_card_of_nonempty hs] at h
  simpa only [Finset.card_empty, pow_zero, add_eq_zero_iff_eq_neg, nonemptySubsets] using h

theorem prod_const_zpow {ι : Type*} (s : Finset ι) (f : ι → ℤ) {c : ℂ} (hc : c≠0) :
    (∏ i∈s, c^(f i)) = c^(∑ i∈s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp only [Finset.prod_insert ha, Finset.sum_insert ha, zpow_add₀ hc, ih]

noncomputable def fiberKernel {ι : Type*} (s : Finset ι) (w : ι → ℂ) : ℂ :=
  ∏ S∈nonemptySubsets s, (∑ i∈S, w i)^(-((-1:ℤ)^S.card))

noncomputable def fiberZeta {ι : Type*} (s : Finset ι) (z : ι → ℂ) : ℂ :=
  ∏ S∈nonemptySubsets s, riemannZeta (1+∑ i∈S, z i)^((-1:ℤ)^S.card)

noncomputable def normalizedFiberZeta {ι : Type*} (s : Finset ι) (z : ι → ℂ) : ℂ :=
  ∏ S∈nonemptySubsets s, ((∑ i∈S, z i)*riemannZeta (1+∑ i∈S, z i))^((-1:ℤ)^S.card)

theorem fiberKernel_homogeneous {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    (w : ι → ℂ) {c : ℂ} (hc : c≠0) :
    fiberKernel s (fun i => c*w i) = c*fiberKernel s w := by
  classical
  unfold fiberKernel
  simp_rw [← Finset.mul_sum, mul_zpow]
  rw [Finset.prod_mul_distrib, prod_const_zpow _ _ hc, Finset.sum_neg_distrib,
    sum_nonemptySubsets_sign hs, neg_neg, zpow_one]

theorem fiberZeta_factorization {ι : Type*} (s : Finset ι) (z : ι → ℂ)
    (hz : ∀ S∈nonemptySubsets s, ∑ i∈S, z i≠0) :
    fiberZeta s z = fiberKernel s z*normalizedFiberZeta s z := by
  classical
  unfold fiberZeta fiberKernel normalizedFiberZeta
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro S hS
  rw [mul_zpow, ← mul_assoc]
  have h : (∑ i∈S, z i)^(-((-1:ℤ)^S.card))*(∑ i∈S, z i)^((-1:ℤ)^S.card) = 1 := by
    rw [← zpow_add₀ (hz S hS), neg_add_cancel, zpow_zero]
  rw [h, one_mul]

theorem norm_inv_sub_one_le {a : ℂ} (ha : 1/2≤‖a‖) : ‖a⁻¹-1‖≤2*‖a-1‖ := by
  have ha0 : a≠0 := norm_pos_iff.mp (by linarith)
  have he : a⁻¹-1 = -(a-1)/a := by field_simp; ring
  rw [he, norm_div, norm_neg]
  apply (div_le_iff₀ (by linarith : 0<‖a‖)).mpr
  nlinarith [norm_nonneg (a-1)]

theorem normalizedFiberZeta_error {ι : Type*} (s : Finset ι) (z : ι → ℂ)
    {c ε : ℝ} (hc : 0<c) (hε : 0≤ε)
    (hz : ∀ S∈nonemptySubsets s,
      ‖(∑ i∈S, z i)*riemannZeta (1+∑ i∈S, z i)-1‖≤c*ε ∧
      1/2≤‖(∑ i∈S, z i)*riemannZeta (1+∑ i∈S, z i)‖ ∧
      ‖(∑ i∈S, z i)*riemannZeta (1+∑ i∈S, z i)‖≤3/2) :
    ‖normalizedFiberZeta s z-1‖ ≤ 2^(nonemptySubsets s).card*((nonemptySubsets s).card*(2*c*ε)) := by
  apply norm_prod_sub_one_le _ _ (by norm_num : (1:ℝ)≤2)
  · intro S hS
    rcases neg_one_pow_eq_or ℤ S.card with h | h
    · rw [h, zpow_one]
      linarith [(hz S hS).2.2]
    · rw [h, zpow_neg_one, norm_inv]
      exact (inv_le_comm₀ (by linarith [(hz S hS).2.1] : 0<‖(∑ i∈S, z i)*riemannZeta (1+∑ i∈S, z i)‖) (by norm_num)).mpr (by simpa only [one_div] using (hz S hS).2.1)
  · intro S hS
    rcases neg_one_pow_eq_or ℤ S.card with h | h
    · rw [h, zpow_one]
      nlinarith [(hz S hS).1]
    · rw [h, zpow_neg_one]
      exact (norm_inv_sub_one_le (hz S hS).2.1).trans (by nlinarith [(hz S hS).1])

noncomputable def frequencyW (u : ℝ) : ℂ := 1+Complex.I*(u:ℂ)

@[simp] theorem frequencyW_re (u : ℝ) : (frequencyW u).re=1 := by simp [frequencyW]

theorem frequencyW_norm (u : ℝ) : ‖frequencyW u‖≤1+|u| := by
  simpa [frequencyW] using norm_add_le (1:ℂ) (Complex.I*(u:ℂ))

theorem frequencySum_re {ι : Type*} (S : Finset ι) (u : ι → ℝ) :
    (∑ i∈S, frequencyW (u i)).re=(S.card:ℝ) := by simp

theorem frequencySum_norm_lower {ι : Type*} {S : Finset ι} (hS : S.Nonempty) (u : ι → ℝ) :
    1≤‖∑ i∈S, frequencyW (u i)‖ := by
  have hc : (1:ℝ)≤S.card := by exact_mod_cast hS.card_pos
  have hr := Complex.re_le_norm (∑ i∈S, frequencyW (u i))
  rw [frequencySum_re] at hr
  exact hc.trans hr

theorem frequencySum_ne_zero {ι : Type*} {S : Finset ι} (hS : S.Nonempty) (u : ι → ℝ) :
    ∑ i∈S, frequencyW (u i)≠0 :=
  norm_pos_iff.mp ((by norm_num : (0:ℝ)<1).trans_le (frequencySum_norm_lower hS u))

theorem frequencySum_norm_upper {ι : Type*} (S : Finset ι) (u : ι → ℝ)
    {U : ℝ} (hu : ∀ i∈S, |u i|≤U) :
    ‖∑ i∈S, frequencyW (u i)‖ ≤ S.card*(1+U) := by
  calc
    _ ≤ ∑ i∈S, ‖frequencyW (u i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i∈S, (1+U) := Finset.sum_le_sum fun i hi => (frequencyW_norm _).trans (by linarith [hu i hi])
    _ = _ := by simp; ring

theorem fiberKernel_norm_polynomial {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    (u : ι → ℝ) {U : ℝ} (hU : 0≤U) (hu : ∀ i∈s, |u i|≤U) :
    ‖fiberKernel s (fun i => frequencyW (u i))‖ ≤
      ((s.card:ℝ)*(1+U))^(nonemptySubsets s).card := by
  have hc : (1:ℝ)≤ s.card := by exact_mod_cast hs.card_pos
  have hB : 1≤(s.card:ℝ)*(1+U) := by nlinarith
  unfold fiberKernel
  rw [norm_prod]
  calc
    _ ≤ ∏ _S∈nonemptySubsets s, ((s.card:ℝ)*(1+U)) := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro S hS
      obtain ⟨hSne,hSs⟩ := mem_nonemptySubsets.mp hS
      have hSC : (S.card:ℝ)≤ s.card := by exact_mod_cast Finset.card_le_card hSs
      rcases neg_one_pow_eq_or ℤ S.card with h | h
      · rw [h, zpow_neg_one, norm_inv]
        exact (inv_le_one_of_one_le₀ (frequencySum_norm_lower hSne u)).trans hB
      · rw [h, neg_neg, zpow_one]
        exact (frequencySum_norm_upper S u (fun i hi => hu i (hSs hi))).trans
          (mul_le_mul_of_nonneg_right hSC (by positivity))
    _ = _ := by simp

theorem fiberZeta_contour_error :
    ∃ c>0, ∃ δ>0, ∀ {ι : Type*} (s : Finset ι), s.Nonempty →
      ∀ (u : ι → ℝ) {L U : ℝ}, 0<L → 0≤U → (∀ i∈s, |u i|≤U) →
      (s.card:ℝ)*(1+U)/L<δ →
      ‖fiberZeta s (fun i => frequencyW (u i)/(L:ℂ))-
        (L:ℂ)⁻¹*fiberKernel s (fun i => frequencyW (u i))‖ ≤
      L⁻¹*‖fiberKernel s (fun i => frequencyW (u i))‖ *
        (2^(nonemptySubsets s).card*((nonemptySubsets s).card*(2*c*((s.card:ℝ)*(1+U)/L)))) := by
  obtain ⟨c,hc,δ,hδ,hpole⟩ := zeta_pole_two_sided
  refine ⟨c,hc,δ,hδ,?_⟩
  intro ι s hs u L U hL hU hu hsmall
  have hLc : (L:ℂ)≠0 := by exact_mod_cast hL.ne'
  have hsum (S : Finset ι) : (∑ i∈S, frequencyW (u i)/(L:ℂ)) =
      (∑ i∈S, frequencyW (u i))/(L:ℂ) := (Finset.sum_div _ _ _).symm
  have hnz : ∀ S∈nonemptySubsets s, (∑ i∈S, frequencyW (u i)/(L:ℂ))≠0 := by
    intro S hS
    rw [hsum]
    exact div_ne_zero (frequencySum_ne_zero (mem_nonemptySubsets.mp hS).1 u) hLc
  have hnorm : ∀ S∈nonemptySubsets s, ‖∑ i∈S, frequencyW (u i)/(L:ℂ)‖≤(s.card:ℝ)*(1+U)/L := by
    intro S hS
    have hSs := (mem_nonemptySubsets.mp hS).2
    rw [hsum, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
    apply div_le_div_of_nonneg_right _ hL.le
    exact (frequencySum_norm_upper S u (fun i hi => hu i (hSs hi))).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hSs) (by positivity))
  have hp : ∀ S∈nonemptySubsets s,
      ‖(∑ i∈S, frequencyW (u i)/(L:ℂ))*riemannZeta (1+∑ i∈S, frequencyW (u i)/(L:ℂ))-1‖≤c*((s.card:ℝ)*(1+U)/L) ∧
      1/2≤‖(∑ i∈S, frequencyW (u i)/(L:ℂ))*riemannZeta (1+∑ i∈S, frequencyW (u i)/(L:ℂ))‖ ∧
      ‖(∑ i∈S, frequencyW (u i)/(L:ℂ))*riemannZeta (1+∑ i∈S, frequencyW (u i)/(L:ℂ))‖≤3/2 := by
    intro S hS
    have hh := hpole _ (hnz S hS) ((hnorm S hS).trans_lt hsmall)
    exact ⟨hh.1.trans (mul_le_mul_of_nonneg_left (hnorm S hS) hc.le), hh.2⟩
  have herr := normalizedFiberZeta_error s (fun i => frequencyW (u i)/(L:ℂ)) hc (by positivity) hp
  have hker : fiberKernel s (fun i => frequencyW (u i)/(L:ℂ)) =
      (L:ℂ)⁻¹*fiberKernel s (fun i => frequencyW (u i)) := by
    simpa only [div_eq_mul_inv, mul_comm] using
      fiberKernel_homogeneous hs (fun i => frequencyW (u i)) (inv_ne_zero hLc)
  rw [fiberZeta_factorization _ _ hnz, hker, ← mul_sub_one, norm_mul, norm_mul,
    norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
  exact mul_le_mul_of_nonneg_left herr (by positivity)

end LargePrimeGaps

end OAI
