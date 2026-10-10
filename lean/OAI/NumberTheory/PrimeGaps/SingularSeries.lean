import OAI.NumberTheory.PrimeGaps.MangoldtBounds

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

def residueCount (H : Finset ℤ) (p : ℕ) : ℕ :=
  (H.image fun a => a % (p:ℤ)).card

noncomputable def singularLocal (H : Finset ℤ) (p : ℕ) : ℝ :=
  (1 - (residueCount H p : ℝ)/(p:ℝ)) / (1 - 1/(p:ℝ))^H.card

noncomputable def singularSeries (H : Finset ℤ) : ℝ :=
  ∏' p : Nat.Primes, singularLocal H p

noncomputable def singularTruncation (H : Finset ℤ) (y : ℕ) : ℝ :=
  ∏ p ∈ Nat.primesLE y, singularLocal H p

theorem residueCount_le_card (H : Finset ℤ) (p : ℕ) : residueCount H p ≤ H.card :=
  Finset.card_image_le

theorem residueCount_le_modulus (H : Finset ℤ) {p : ℕ} (hp : 0 < p) :
    residueCount H p ≤ p := by
  have hpZ : (0:ℤ) < p := by exact_mod_cast hp
  have hsub : H.image (fun a => a % (p:ℤ)) ⊆ Finset.Ico (0:ℤ) (p:ℤ) := by
    intro r hr
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hr
    exact Finset.mem_Ico.mpr ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ hpZ⟩
  have hc := Finset.card_le_card hsub
  simpa only [residueCount, Int.card_Ico, sub_zero, Int.toNat_natCast] using hc

theorem singularLocal_nonneg (H : Finset ℤ) {p : ℕ} (hp : Nat.Prime p) :
    0 ≤ singularLocal H p := by
  unfold singularLocal
  apply div_nonneg
  · have hn : (residueCount H p : ℝ) ≤ p := by exact_mod_cast residueCount_le_modulus H hp.pos
    have hp0 : (0:ℝ)<p := by exact_mod_cast hp.pos
    exact sub_nonneg.mpr ((div_le_one hp0).mpr hn)
  · have hp1 : (1:ℝ)≤p := by exact_mod_cast hp.one_le
    exact pow_nonneg (by linarith [one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hp1]) _

theorem singularLocal_empty (p : ℕ) : singularLocal ∅ p = 1 := by
  simp [singularLocal, residueCount]

theorem singularLocal_singleton (a : ℤ) {p : ℕ} (hp : Nat.Prime p) :
    singularLocal {a} p = 1 := by
  have hp1 : (1:ℝ)<p := by exact_mod_cast hp.one_lt
  have hne : (1:ℝ)-1/p ≠ 0 := by
    have hh := (div_lt_one (by linarith : (0:ℝ)<p)).mpr hp1
    linarith
  simp only [singularLocal, residueCount, Finset.image_singleton, Finset.card_singleton,
    Nat.cast_one, pow_one]
  exact div_self hne

theorem bernoulli_second_order (s : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ (1-u)^s - (1-(s:ℝ)*u) ∧
    (1-u)^s - (1-(s:ℝ)*u) ≤ (s:ℝ)^2*u^2 := by
  induction s with
  | zero => simp
  | succ s ih =>
    have hid : (1-u)^(s+1) - (1-((s+1:ℕ):ℝ)*u) =
        (1-u)*((1-u)^s-(1-(s:ℝ)*u))+(s:ℝ)*u^2 := by
      rw [pow_succ, Nat.cast_add, Nat.cast_one]
      ring
    rw [hid]
    constructor
    · exact add_nonneg (mul_nonneg (by linarith) ih.1) (by positivity)
    · have hh := mul_le_mul_of_nonneg_left ih.2 (by linarith : 0≤1-u)
      have hpos : 0 ≤ (s:ℝ)^2*u^2 := by positivity
      have hsm : (1-u)*((s:ℝ)^2*u^2) ≤ (s:ℝ)^2*u^2 := by nlinarith
      push_cast
      nlinarith [sq_nonneg u, Nat.cast_nonneg (α:=ℝ) s]

theorem generic_local_error (s : ℕ) {p : ℕ} (hp : 2 ≤ p) :
    |(1-(s:ℝ)/(p:ℝ))/(1-1/(p:ℝ))^s - 1| ≤
      ((s:ℝ)^2 * (2:ℝ)^s) / (p:ℝ)^2 := by
  have hpR : (2:ℝ)≤p := by exact_mod_cast hp
  have hp0 : (0:ℝ)<p := by linarith
  have hu0 : 0 ≤ (1:ℝ)/p := by positivity
  have hu1 : (1:ℝ)/p ≤ 1/2 := (one_div_le_one_div_of_le (by norm_num) hpR)
  have hs := bernoulli_second_order s hu0 (by linarith)
  have hm : (s:ℝ)*(1/(p:ℝ))=(s:ℝ)/(p:ℝ) := by ring
  rw [hm] at hs
  have hd0 : 0 < (1-(1:ℝ)/p)^s := pow_pos (by linarith) _
  have hdp : (1/2:ℝ)^s ≤ (1-1/(p:ℝ))^s :=
    pow_le_pow_left₀ (by norm_num) (by linarith) s
  have hnum : (1-(s:ℝ)/(p:ℝ))/(1-1/(p:ℝ))^s ≤ 1 := by
    apply (div_le_one hd0).mpr
    nlinarith [hs.1]
  rw [abs_of_nonpos (by linarith : (1-(s:ℝ)/(p:ℝ))/(1-1/(p:ℝ))^s-1≤0)]
  calc
    _ = ((1-1/(p:ℝ))^s - (1-(s:ℝ)/(p:ℝ))) / (1-1/(p:ℝ))^s := by simp only [sub_div, div_self hd0.ne']; ring
    _ ≤ ((s:ℝ)^2 * (1/(p:ℝ))^2) / (1-1/(p:ℝ))^s := by
      apply div_le_div_of_nonneg_right _ hd0.le
      exact hs.2
    _ ≤ ((s:ℝ)^2 * (1/(p:ℝ))^2) / (1/2:ℝ)^s :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hdp
    _ = _ := by simp only [div_pow, one_pow]; field_simp

theorem residueCount_eq_card_of_large (H : Finset ℤ) {p : ℕ}
    (hp : 2 * H.sup Int.natAbs < p) : residueCount H p = H.card := by
  apply Finset.card_image_of_injOn
  intro a ha b hb hab
  have hd : (p:ℤ) ∣ a-b := Int.dvd_of_emod_eq_zero
    (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hab)
  have hdN : p ∣ (a-b).natAbs := by
    simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hd
  have hlt : (a-b).natAbs < p := by
    have h1 := Finset.le_sup (f:=Int.natAbs) ha
    have h2 := Finset.le_sup (f:=Int.natAbs) hb
    have h3 := Int.natAbs_sub_le a b
    omega
  exact sub_eq_zero.mp (Int.natAbs_eq_zero.mp (Nat.eq_zero_of_dvd_of_lt hdN hlt))

theorem singularLocal_generic_error (H : Finset ℤ) {p : ℕ} (hp : 2 ≤ p)
    (hlarge : 2 * H.sup Int.natAbs < p) :
    |singularLocal H p - 1| ≤ ((H.card:ℝ)^2 * (2:ℝ)^H.card) / (p:ℝ)^2 := by
  simpa only [singularLocal, residueCount_eq_card_of_large H hlarge] using
    generic_local_error H.card hp

theorem singularLocal_summable_error (H : Finset ℤ) :
    Summable (fun p : ℕ => if p.Prime then singularLocal H p - 1 else 0) := by
  have hh : Summable (fun p : ℕ => ((H.card:ℝ)^2 * (2:ℝ)^H.card) / (p:ℝ)^2) := by
    simpa only [mul_one_div] using
      ((Real.summable_one_div_nat_pow.mpr (by norm_num : 1<2)).mul_left
        ((H.card:ℝ)^2 * (2:ℝ)^H.card))
  apply hh.of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop (max 2 (2*H.sup Int.natAbs+1))] with p hp
  split_ifs with hprime
  · rw [Real.norm_eq_abs]
    exact singularLocal_generic_error H (by omega) (by omega)
  · simp only [norm_zero]
    positivity

theorem singularSeries_multipliable (H : Finset ℤ) :
    Multipliable (fun p : Nat.Primes => singularLocal H p) := by
  apply (Nat.Primes.multipliable_iff_multipliable_ite (singularLocal H)).mpr
  have hh := Real.multipliable_one_add_of_summable (singularLocal_summable_error H)
  apply hh.congr
  intro p
  split_ifs <;> ring

theorem singularSeries_nonneg (H : Finset ℤ) : 0 ≤ singularSeries H :=
  tprod_nonneg fun p => singularLocal_nonneg H p.property

theorem singularSeries_empty : singularSeries ∅ = 1 := by
  simp [singularSeries, singularLocal_empty]

theorem singularSeries_singleton (a : ℤ) : singularSeries {a} = 1 := by
  have hh : (fun p : Nat.Primes => singularLocal {a} p) = fun _ => (1:ℝ) :=
    funext fun p => singularLocal_singleton a p.property
  rw [singularSeries, hh, tprod_one]

noncomputable def tupleLocal {s p : ℕ} (a : Fin s → Fin p) : ℝ :=
  (1 - ((Finset.univ.image a).card:ℝ)/(p:ℝ)) / (1 - 1/(p:ℝ))^s

theorem missing_residue_card {s p : ℕ} (a : Fin s → Fin p) :
    ((Finset.univ.filter fun x => ∀ i, a i ≠ x).card:ℝ) =
      (p:ℝ) - (Finset.univ.image a).card := by
  have he : (Finset.univ.filter fun x => ∀ i, a i ≠ x) =
      Finset.univ \ Finset.univ.image a := by
    ext x
    simp
  rw [he, Finset.card_sdiff_of_subset (Finset.subset_univ _), Nat.cast_sub]
  · simp
  · simpa using Finset.card_le_card (Finset.subset_univ (Finset.univ.image a))

theorem avoiding_tuple_count (s p : ℕ) (x : Fin p) :
    (Finset.univ.filter fun a : Fin s → Fin p => ∀ i, a i ≠ x).card = (p-1)^s := by
  have he : (Finset.univ.filter fun a : Fin s → Fin p => ∀ i, a i ≠ x) =
      Fintype.piFinset (fun _ : Fin s => Finset.univ.erase x) := by
    ext a
    simp [Fintype.mem_piFinset, ne_comm]
  rw [he]
  simp

theorem missing_residue_sum (s : ℕ) {p : ℕ} (hp : 1 ≤ p) :
    (∑ a : Fin s → Fin p, ((Finset.univ.filter fun x => ∀ i, a i ≠ x).card:ℝ)) =
      (p:ℝ) * ((p:ℝ)-1)^s := by
  have hcount (a : Fin s → Fin p) :
      ((Finset.univ.filter fun x => ∀ i, a i ≠ x).card:ℝ) =
        ∑ x : Fin p, if ∀ i, a i ≠ x then (1:ℝ) else 0 := by
    simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  simp_rw [hcount]
  rw [Finset.sum_comm]
  have hx (x : Fin p) : (∑ a : Fin s → Fin p, if ∀ i, a i ≠ x then (1:ℝ) else 0) =
      ((p:ℝ)-1)^s := by
    simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one,
      avoiding_tuple_count, Nat.cast_pow, Nat.cast_sub hp, Nat.cast_one]
  simp_rw [hx]
  simp

theorem tupleLocal_sum (s : ℕ) {p : ℕ} (hp : 2 ≤ p) :
    (∑ a : Fin s → Fin p, tupleLocal a) = (p:ℝ)^s := by
  have hp0 : (0:ℝ)<p := by exact_mod_cast (show 0<p by omega)
  have hp1 : (1:ℝ)<p := by exact_mod_cast (show 1<p by omega)
  have hd : (1:ℝ)-1/p ≠ 0 := by
    have := (div_lt_one hp0).mpr hp1
    linarith
  have he (a : Fin s → Fin p) : tupleLocal a =
      ((Finset.univ.filter fun x => ∀ i, a i ≠ x).card:ℝ) / p / (1-1/(p:ℝ))^s := by
    rw [missing_residue_card]
    unfold tupleLocal
    simp only [sub_div, div_self hp0.ne']
  simp_rw [he]
  rw [← Finset.sum_div, ← Finset.sum_div, missing_residue_sum s (by omega)]
  have hdform : (1:ℝ)-1/p = ((p:ℝ)-1)/p := by field_simp
  rw [hdform, div_pow]
  field_simp [sub_ne_zero.mpr hp1.ne']

def differenceProduct (H : Finset ℤ) : ℕ :=
  ∏ a ∈ H, ∏ b ∈ H.erase a, (a-b).natAbs

theorem differenceProduct_pos (H : Finset ℤ) : 0 < differenceProduct H := by
  classical
  apply Finset.prod_pos
  intro a _
  apply Finset.prod_pos
  intro b hb
  have hba : b ≠ a := (Finset.mem_erase.mp hb).1
  exact Int.natAbs_pos.mpr (sub_ne_zero.mpr hba.symm)

theorem prime_dvd_differenceProduct_of_collision {H : Finset ℤ} {p : ℕ}
    {a b : ℤ} (ha : a ∈ H) (hb : b ∈ H) (hab : a ≠ b)
    (hmod : a % (p:ℤ) = b % (p:ℤ)) : p ∣ differenceProduct H := by
  have hd : (p:ℤ) ∣ a-b := Int.dvd_of_emod_eq_zero
    (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hmod)
  have hdN : p ∣ (a-b).natAbs := by
    simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hd
  exact hdN.trans ((Finset.dvd_prod_of_mem (fun b => (a-b).natAbs)
    (Finset.mem_erase.mpr ⟨hab.symm, hb⟩)).trans
    (Finset.dvd_prod_of_mem (fun a => ∏ b ∈ H.erase a, (a-b).natAbs) ha))

theorem residueCount_eq_card_of_not_dvd (H : Finset ℤ) {p : ℕ}
    (hp : ¬p ∣ differenceProduct H) : residueCount H p = H.card := by
  apply Finset.card_image_of_injOn
  intro a ha b hb hab
  by_contra hne
  exact hp (prime_dvd_differenceProduct_of_collision ha hb hne hab)

theorem differenceProduct_le (H : Finset ℤ) {M : ℕ}
    (hM : ∀ a ∈ H, ∀ b ∈ H, (a-b).natAbs ≤ M) :
    differenceProduct H ≤ M^(H.card*(H.card-1)) := by
  classical
  calc
    _ ≤ ∏ a ∈ H, M^(H.card-1) := by
      apply Finset.prod_le_prod
      intro a ha
      calc
        _ ≤ ∏ _b ∈ H.erase a, M := Finset.prod_le_prod fun b hb =>
          hM a ha b (Finset.mem_erase.mp hb).2
        _ = _ := by simp [Finset.card_erase_of_mem ha]
    _ = _ := by simp [← pow_mul, Nat.mul_comm]

theorem abs_log_le_two_abs_sub_one {x : ℝ} (hx : 1/2 ≤ x) :
    |Real.log x| ≤ 2*|x-1| := by
  have hx0 : 0<x := by linarith
  by_cases hx1 : 1 ≤ x
  · rw [abs_of_nonneg (Real.log_nonneg hx1), abs_of_nonneg (by linarith)]
    linarith [Real.log_le_sub_one_of_pos hx0]
  · have hx1' : x ≤ 1 := le_of_not_ge hx1
    rw [abs_of_nonpos (Real.log_nonpos hx0.le hx1'), abs_of_nonpos (by linarith)]
    have hh := Real.log_le_sub_one_of_pos (inv_pos.mpr hx0)
    rw [Real.log_inv] at hh
    have hi : x⁻¹-1 ≤ 2*(1-x) := by
      have hh : (1:ℝ) / x ≤ 2*(1-x)+1 := (div_le_iff₀ hx0).mpr (by nlinarith)
      simpa only [one_div] using (sub_le_iff_le_add).mpr hh
    linarith

theorem abs_log_one_sub_le {u : ℝ} (hu0 : 0≤u) (hu1 : u≤1/2) :
    |Real.log (1-u)| ≤ 2*u := by
  have hh := abs_log_le_two_abs_sub_one (x:=1-u) (by linarith)
  simpa only [sub_sub_cancel_left, abs_neg, abs_of_nonneg hu0] using hh

theorem singularLocal_ge_half (H : Finset ℤ) {p : ℕ} (hp : 2 ≤ p)
    (hps : 2 * H.card ≤ p) : 1/2 ≤ singularLocal H p := by
  have hp0 : (0:ℝ)<p := by exact_mod_cast (show 0<p by omega)
  have hs : (2:ℝ)*H.card ≤ p := by exact_mod_cast hps
  have hn : (residueCount H p:ℝ) ≤ H.card := by exact_mod_cast residueCount_le_card H p
  have hpR : (2:ℝ)≤p := by exact_mod_cast hp
  have hd0 : 0 ≤ 1-(1:ℝ)/p := by
    have hh := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) hpR
    linarith
  have hd1 : 1-(1:ℝ)/p ≤ 1 := sub_le_self _ (by positivity)
  have hpow : (1-(1:ℝ)/p)^H.card ≤ 1 := pow_le_one₀ hd0 hd1
  have hn0 : 1/2 ≤ 1-(residueCount H p:ℝ)/p := by
    have hh : (residueCount H p:ℝ)/p ≤ 1/2 := (div_le_iff₀ hp0).mpr (by linarith)
    linarith
  unfold singularLocal
  have hdpos : 0 < 1-(1:ℝ)/p := by
    have hh := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) hpR
    linarith
  exact hn0.trans (le_div_self (by linarith) (pow_pos hdpos _) hpow)

theorem singularLocal_log_generic (H : Finset ℤ) {p : ℕ} (hp : 2 ≤ p)
    (hps : 2*H.card ≤ p) (hdiv : ¬p ∣ differenceProduct H) :
    |Real.log (singularLocal H p)| ≤
      2*((H.card:ℝ)^2*(2:ℝ)^H.card)/(p:ℝ)^2 := by
  have h1 := abs_log_le_two_abs_sub_one (singularLocal_ge_half H hp hps)
  have h2 : |singularLocal H p-1| ≤ ((H.card:ℝ)^2*(2:ℝ)^H.card)/(p:ℝ)^2 := by
    simpa only [singularLocal, residueCount_eq_card_of_not_dvd H hdiv] using
      generic_local_error H.card hp
  calc
    _ ≤ 2*|singularLocal H p-1| := h1
    _ ≤ 2*(((H.card:ℝ)^2*(2:ℝ)^H.card)/(p:ℝ)^2) := by gcongr
    _ = _ := by ring

theorem singularLocal_log_bound (H : Finset ℤ) {p : ℕ} (hp : 2 ≤ p)
    (hps : 2*H.card ≤ p) :
    |Real.log (singularLocal H p)| ≤ 4*(H.card:ℝ)/(p:ℝ) := by
  have hp0 : (0:ℝ)<p := by exact_mod_cast (show 0<p by omega)
  have hpR : (2:ℝ)≤p := by exact_mod_cast hp
  have hs : (2:ℝ)*H.card ≤ p := by exact_mod_cast hps
  have hn : (residueCount H p:ℝ) ≤ H.card := by exact_mod_cast residueCount_le_card H p
  have hn0 : 0 ≤ (residueCount H p:ℝ)/p := by positivity
  have hn1 : (residueCount H p:ℝ)/p ≤ 1/2 := (div_le_iff₀ hp0).mpr (by linarith)
  have hq1 : (1:ℝ)/p ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) hpR
  have hlog1 := abs_log_one_sub_le hn0 hn1
  have hlog2 := abs_log_one_sub_le (by positivity : 0≤(1:ℝ)/p) hq1
  rw [singularLocal, Real.log_div (by linarith : (1-(residueCount H p:ℝ)/p) ≠ 0)
    (pow_ne_zero _ (by linarith : (1-(1:ℝ)/p) ≠ 0)), Real.log_pow]
  calc
    _ ≤ |Real.log (1-(residueCount H p:ℝ)/p)| +
          |(H.card:ℝ)*Real.log (1-(1:ℝ)/p)| := abs_sub _ _
    _ = |Real.log (1-(residueCount H p:ℝ)/p)| +
          (H.card:ℝ)*|Real.log (1-(1:ℝ)/p)| := by rw [abs_mul, abs_of_nonneg (show (0:ℝ) ≤ H.card from Nat.cast_nonneg _)]
    _ ≤ 2*((residueCount H p:ℝ)/p) + (H.card:ℝ)*(2*((1:ℝ)/p)) := by gcongr
    _ ≤ _ := by
      have hh := div_le_div_of_nonneg_right hn hp0.le
      calc
        _ ≤ 2*((H.card:ℝ)/p) + (H.card:ℝ)*(2*((1:ℝ)/p)) := by gcongr
        _ = _ := by ring

theorem sum_reciprocal_sq_le {S : Finset ℕ} {y : ℕ} (hy : 0 < y)
    (hS : ∀ n ∈ S, y < n) : (∑ n ∈ S, (1:ℝ)/(n:ℝ)^2) ≤ 1/(y:ℝ) := by
  classical
  by_cases hempty : S = ∅
  · subst S
    simp
  let N := S.sup id
  have hsub : S ⊆ Finset.Ico y (N+1) := by
    intro n hn
    exact Finset.mem_Ico.mpr ⟨(hS n hn).le, Nat.lt_succ_iff.mpr (Finset.le_sup (f:=id) hn)⟩
  have hN : y ≤ N+1 := by
    obtain ⟨n, hn⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    exact (Finset.mem_Ico.mp (hsub hn)).1.trans (Finset.mem_Ico.mp (hsub hn)).2.le
  have htel : (∑ n ∈ Finset.Ico y (N+1), ((1:ℝ)/(n:ℝ)-1/((n:ℝ)+1))) =
      1/(y:ℝ)-1/(N+1:ℕ) := by
    rw [Finset.sum_Ico_eq_sub _ hN]
    have hh (k : ℕ) : (∑ n ∈ Finset.range k, ((1:ℝ)/(n:ℝ)-1/((n:ℝ)+1))) =
        (1:ℝ)/(0:ℕ)-1/(k:ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        Finset.sum_range_sub' (fun n : ℕ => (1:ℝ)/(n:ℝ)) k
    rw [hh, hh]
    ring
  have hstep (n : ℕ) (hn : y < n) :
      (1:ℝ)/(n:ℝ)^2 ≤ (1:ℝ)/((n:ℝ)-1)-1/(n:ℝ) := by
    have hn1 : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
    have hid : (1:ℝ)/((n:ℝ)-1)-1/(n:ℝ) = 1/((n:ℝ)*((n:ℝ)-1)) := by
      field_simp [show (n:ℝ) ≠ 0 by linarith, show (n:ℝ)-1 ≠ 0 by linarith]
      ring
    rw [hid]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith

  let T := S.image (fun n => n-1)
  have hi : Set.InjOn (fun n : ℕ => n-1) ↑S := by
    intro n hn m hm he
    have := hS n hn
    have := hS m hm
    change n-1=m-1 at he
    omega
  have he : (∑ n ∈ S, ((1:ℝ)/((n:ℝ)-1)-1/(n:ℝ))) =
      ∑ n ∈ T, ((1:ℝ)/(n:ℝ)-1/((n:ℝ)+1)) := by
    rw [Finset.sum_image hi]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Nat.cast_sub (by have := hS n hn; omega), Nat.cast_one]
    congr 2
    ring
  calc
    _ ≤ ∑ n ∈ S, ((1:ℝ)/((n:ℝ)-1)-1/(n:ℝ)) :=
      Finset.sum_le_sum fun n hn => hstep n (hS n hn)
    _ = _ := he
    _ ≤ ∑ n ∈ Finset.Ico y (N+1), ((1:ℝ)/(n:ℝ)-1/((n:ℝ)+1)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro m hm
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
        have := hS n hn
        have hsup : n ≤ N := Finset.le_sup (f:=id) hn
        simp only [Finset.mem_Ico]
        change y ≤ n-1 ∧ n-1<N+1
        omega
      · intro n hn _
        have hn0 : (0:ℝ)<n := by exact_mod_cast (hy.trans_le (Finset.mem_Ico.mp hn).1)
        exact sub_nonneg.mpr (one_div_le_one_div_of_le hn0 (by linarith))
    _ = 1/(y:ℝ)-1/(N+1:ℕ) := htel
    _ ≤ _ := sub_le_self _ (by positivity)

theorem prime_divisor_reciprocal_sum_le {D y : ℕ} (hD : 0 < D) (hy : 1 < y)
    (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p ∧ y < p ∧ p ∣ D) :
    (∑ p ∈ S, (1:ℝ)/(p:ℝ)) ≤ Real.log D / ((y:ℝ)*Real.log y) := by
  have hy0 : (0:ℝ)<y := by exact_mod_cast (show 0<y by omega)
  have hy1 : (1:ℝ)<y := by exact_mod_cast hy
  have hlogy : 0 < Real.log (y:ℝ) := Real.log_pos hy1
  have hsub : S ⊆ D.primeFactors := fun p hp =>
    Nat.mem_primeFactors.mpr ⟨(hS p hp).1, (hS p hp).2.2, hD.ne'⟩
  have hprod : (∏ p ∈ S, p) ≤ D := Nat.le_of_dvd hD
    ((Finset.prod_dvd_prod_of_subset S D.primeFactors id hsub).trans (Nat.prod_primeFactors_dvd D))
  have hprodpos : (0:ℝ) < ∏ p ∈ S, (p:ℝ) := Finset.prod_pos fun p hp => by
    exact_mod_cast (hS p hp).1.pos
  have hlogs : (∑ p ∈ S, Real.log (p:ℝ)) ≤ Real.log D := by
    rw [← Real.log_prod (s:=S) (f:=fun p : ℕ => (p:ℝ))
      (fun p hp => (ne_of_gt (by exact_mod_cast (hS p hp).1.pos : (0:ℝ)<p)))]
    exact Real.log_le_log hprodpos (by
      simpa only [Nat.cast_prod] using (show ((∏ p ∈ S, p : ℕ):ℝ) ≤ (D:ℝ) by exact_mod_cast hprod))
  calc
    _ ≤ ∑ p ∈ S, Real.log (p:ℝ) / ((y:ℝ)*Real.log y) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpy : (y:ℝ)≤p := by exact_mod_cast (hS p hp).2.1.le
      have hlogp := Real.log_le_log hy0 hpy
      calc
        _ ≤ 1/(y:ℝ) := one_div_le_one_div_of_le hy0 hpy
        _ = Real.log (y:ℝ)/((y:ℝ)*Real.log y) := by field_simp
        _ ≤ _ := div_le_div_of_nonneg_right hlogp (by positivity)
    _ = (∑ p ∈ S, Real.log (p:ℝ))/((y:ℝ)*Real.log y) := (Finset.sum_div _ _ _).symm
    _ ≤ _ := div_le_div_of_nonneg_right hlogs (by positivity)

noncomputable def singularTailBound (H : Finset ℤ) (y : ℕ) : ℝ :=
  2*((H.card:ℝ)^2*(2:ℝ)^H.card)/(y:ℝ) +
    4*(H.card:ℝ)*Real.log (differenceProduct H)/((y:ℝ)*Real.log y)

theorem singularLocal_log_sum_bound (H : Finset ℤ) {y : ℕ} (hy : 1<y)
    (hys : 2*H.card ≤ y) (S : Finset ℕ)
    (hS : ∀ p ∈ S, Nat.Prime p ∧ y < p) :
    (∑ p ∈ S, |Real.log (singularLocal H p)|) ≤ singularTailBound H y := by
  classical
  let K : ℝ := 2*((H.card:ℝ)^2*(2:ℝ)^H.card)
  have hK : 0≤K := by dsimp [K]; positivity
  have hsum : (∑ p ∈ S, |Real.log (singularLocal H p)|) ≤
      (∑ p ∈ S, K*(1/(p:ℝ)^2)) +
      ∑ p ∈ S.filter (fun p => p ∣ differenceProduct H), 4*(H.card:ℝ)*(1/(p:ℝ)) := by
    rw [Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro p hp
    by_cases hd : p ∣ differenceProduct H
    · simp only [hd, ite_true]
      have hh := singularLocal_log_bound H (hS p hp).1.two_le (hys.trans (hS p hp).2.le)
      calc
        _ ≤ 4*(H.card:ℝ)/(p:ℝ) := hh
        _ ≤ K*(1/(p:ℝ)^2) + 4*(H.card:ℝ)*(1/(p:ℝ)) := by
          have h0 : 0≤K*(1/(p:ℝ)^2) := by positivity
          simpa only [mul_one_div] using
            (le_add_of_nonneg_left h0 : 4*(H.card:ℝ)*(1/(p:ℝ)) ≤
              K*(1/(p:ℝ)^2) + 4*(H.card:ℝ)*(1/(p:ℝ)))
    · simp only [hd, ite_false, add_zero]
      simpa only [K, mul_one_div] using
        singularLocal_log_generic H (hS p hp).1.two_le (hys.trans (hS p hp).2.le) hd
  have hinv := sum_reciprocal_sq_le (show 0<y by omega) (fun p hp => (hS p hp).2)
  have hdiv := prime_divisor_reciprocal_sum_le (differenceProduct_pos H) hy
    (S.filter (fun p => p ∣ differenceProduct H)) (by
      intro p hp
      obtain ⟨hpS, hd⟩ := Finset.mem_filter.mp hp
      exact ⟨(hS p hpS).1, (hS p hpS).2, hd⟩)
  calc
    _ ≤ _ := hsum
    _ = K*(∑ p ∈ S, 1/(p:ℝ)^2) +
        4*(H.card:ℝ)*(∑ p ∈ S.filter (fun p => p ∣ differenceProduct H), 1/(p:ℝ)) := by
      rw [Finset.mul_sum, Finset.mul_sum]
    _ ≤ K*(1/(y:ℝ)) + 4*(H.card:ℝ)*(Real.log (differenceProduct H)/((y:ℝ)*Real.log y)) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hinv hK)
        (mul_le_mul_of_nonneg_left hdiv (by positivity))
    _ = _ := by unfold singularTailBound K; ring

end LargePrimeGaps

end OAI
