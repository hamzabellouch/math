import OAI.NumberTheory.PrimeGaps.ZetaKernel

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

theorem norm_prod_linear_remainder {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    {e : ℝ} (he : 0≤e) (hf : ∀ i∈s, ‖f i‖≤2) (hd : ∀ i∈s, ‖f i-1‖≤e) :
    ‖(∏ i∈s, f i)-1-(∑ i∈s, (f i-1))‖ ≤ (s.card:ℝ)^2*2^s.card*e^2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hfs : ∀ i∈s, ‖f i‖≤2 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hds : ∀ i∈s, ‖f i-1‖≤e := fun i hi => hd i (Finset.mem_insert_of_mem hi)
    have hfa := hf a (Finset.mem_insert_self _ _)
    have hda := hd a (Finset.mem_insert_self _ _)
    have hi := ih hfs hds
    have hsum : ‖∑ i∈s, (f i-1)‖≤ s.card*e := by
      exact (norm_sum_le _ _).trans (by simpa using Finset.sum_le_sum hds)
    have hcard : 0≤(s.card:ℝ) := Nat.cast_nonneg _
    have hpow : (1:ℝ)≤2^s.card := one_le_pow₀ (by norm_num)
    simp only [Finset.prod_insert ha, Finset.sum_insert ha, Finset.card_insert_of_notMem ha,
      Nat.cast_add, Nat.cast_one, pow_succ]
    calc
      _ = ‖f a*((∏ i∈s, f i)-1-(∑ i∈s, (f i-1)))+(f a-1)*(∑ i∈s, (f i-1))‖ := by congr 1; ring
      _ ≤ ‖f a‖*‖(∏ i∈s, f i)-1-(∑ i∈s, (f i-1))‖+‖f a-1‖*‖∑ i∈s, (f i-1)‖ := by
        simpa only [norm_mul] using norm_add_le (f a*((∏ i∈s, f i)-1-(∑ i∈s, (f i-1)))) ((f a-1)*(∑ i∈s, (f i-1)))
      _ ≤ 2*((s.card:ℝ)^2*2^s.card*e^2)+e*(s.card*e) := by gcongr
      _ ≤ ((s.card:ℝ)+1)^2*(2^s.card*2)*e^2 := by
        have hcoeff : (s.card:ℝ)≤(4*(s.card:ℝ)+2)*2^s.card := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_right hcoeff (sq_nonneg e)]

theorem norm_one_sub_lower {a : ℂ} {r : ℝ} (ha : ‖a‖≤r) :
    1-r≤‖1-a‖ := by
  have hh := norm_sub_norm_le (1:ℂ) a
  rw [norm_one] at hh
  linarith

theorem norm_one_sub_zpow_le {a : ℂ} {r : ℝ} (hr : r≤1/2) (ha : ‖a‖≤r)
    {σ : ℤ} (hσ : σ=1 ∨ σ= -1) :
    ‖(1-a)^σ‖≤Real.exp (2*r) := by
  have hr0 : 0≤r := (norm_nonneg _).trans ha
  have hl := norm_one_sub_lower ha
  obtain rfl | rfl := hσ
  · rw [zpow_one]
    calc
      _ ≤ 1+‖a‖ := by simpa only [norm_one] using norm_sub_le (1:ℂ) a
      _ ≤ 1+2*r := by linarith
      _ ≤ Real.exp (2*r) := Real.add_one_le_exp _ |>.trans' (by ring_nf; rfl)
  · rw [zpow_neg_one, norm_inv]
    calc
      _ ≤ (1-r)⁻¹ := (inv_le_inv₀ (by linarith) (by linarith)).mpr hl
      _ ≤ 1+2*r := by
        rw [← one_div]
        apply (div_le_iff₀ (by linarith : 0<1-r)).mpr
        nlinarith
      _ ≤ Real.exp (2*r) := by linarith [Real.add_one_le_exp (2*r)]

theorem norm_one_sub_zpow_sub_one {a : ℂ} {r : ℝ} (hr : r≤1/2) (ha : ‖a‖≤r)
    {σ : ℤ} (hσ : σ=1 ∨ σ= -1) :
    ‖(1-a)^σ-1‖≤2*r := by
  have hr0 : 0≤r := (norm_nonneg _).trans ha
  have hl := norm_one_sub_lower ha
  have hn : 1-a≠0 := norm_pos_iff.mp (by linarith)
  obtain rfl | rfl := hσ
  · simpa only [zpow_one, sub_sub_cancel_left, norm_neg] using ha.trans (by linarith : r≤2*r)
  · rw [zpow_neg_one]
    have hid : (1-a)⁻¹-1=a/(1-a) := by field_simp; ring
    rw [hid, norm_div]
    apply (div_le_iff₀ (by linarith : 0<‖1-a‖)).mpr
    nlinarith

theorem norm_one_sub_zpow_linear {a : ℂ} {r : ℝ} (hr : r≤1/2) (ha : ‖a‖≤r)
    {σ : ℤ} (hσ : σ=1 ∨ σ= -1) :
    ‖(1-a)^σ-1+(σ:ℂ)*a‖≤2*r^2 := by
  have hr0 : 0≤r := (norm_nonneg _).trans ha
  have hl := norm_one_sub_lower ha
  have hn : 1-a≠0 := norm_pos_iff.mp (by linarith)
  obtain rfl | rfl := hσ
  · simp; positivity
  · simp only [zpow_neg_one, Int.cast_neg, Int.cast_one, neg_one_mul]
    have hid : (1-a)⁻¹-1+-a=a^2/(1-a) := by field_simp; ring
    rw [hid, norm_div, norm_pow]
    apply (div_le_iff₀ (by linarith : 0<‖1-a‖)).mpr
    nlinarith [sq_nonneg r, norm_nonneg a, sq_nonneg (r-‖a‖)]

noncomputable def genericLocalQuotient {ι : Type*} (s : Finset ι) (σ : ι → ℤ)
    (a : ι → ℂ) (ρ : ℝ) : ℂ :=
  (1+(ρ:ℂ)*(∑ i∈s, (σ i:ℂ)*a i))*(∏ i∈s, (1-a i)^(σ i))

theorem genericLocalQuotient_error {ι : Type*} (s : Finset ι) (σ : ι → ℤ)
    (a : ι → ℂ) {ρ r : ℝ} (hr0 : 0≤r) (hr : r≤1/2)
    (hρ0 : 0≤ρ) (hρ : ρ≤2) (hρ1 : |ρ-1|≤2*r)
    (hσ : ∀ i∈s, σ i=1 ∨ σ i= -1) (ha : ∀ i∈s, ‖a i‖≤r) :
    ‖genericLocalQuotient s σ a ρ-1‖ ≤
      ((1+s.card)*(4*(s.card:ℝ)^2*2^s.card+2*s.card)+2*s.card+2*(s.card:ℝ)^2)*r^2 := by
  classical
  let A : ℂ := ∑ i∈s, (σ i:ℂ)*a i
  let T : ℂ := ∏ i∈s, (1-a i)^(σ i)
  have hsig (i : ι) (hi : i∈s) : ‖(σ i:ℂ)‖=1 := by
    rcases hσ i hi with hh | hh <;> simp [hh]
  have hA : ‖A‖≤ s.card*r := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _i∈s, r := Finset.sum_le_sum fun i hi => by rw [norm_mul, hsig i hi, one_mul]; exact ha i hi
      _ = _ := by simp
  have he : ‖T-1+A‖≤(4*(s.card:ℝ)^2*2^s.card+2*s.card)*r^2 := by
    have hf : ∀ i∈s, ‖(1-a i)^(σ i)‖≤2 := by
      intro i hi
      have hh := norm_one_sub_zpow_sub_one hr (ha i hi) (hσ i hi)
      have hn := norm_sub_norm_le ((1-a i)^(σ i)) (1:ℂ)
      rw [norm_one] at hn
      linarith
    have hprod := norm_prod_linear_remainder s (fun i => (1-a i)^(σ i)) (by positivity : 0≤2*r)
      hf (fun i hi => norm_one_sub_zpow_sub_one hr (ha i hi) (hσ i hi))
    have herr : ‖∑ i∈s, ((1-a i)^(σ i)-1+(σ i:ℂ)*a i)‖≤ s.card*(2*r^2) := by
      exact (norm_sum_le _ _).trans (by simpa using Finset.sum_le_sum (fun i hi => norm_one_sub_zpow_linear hr (ha i hi) (hσ i hi)))
    have hid : T-1+A = (T-1-(∑ i∈s, ((1-a i)^(σ i)-1)))+
        (∑ i∈s, ((1-a i)^(σ i)-1+(σ i:ℂ)*a i)) := by
      rw [Finset.sum_add_distrib]; dsimp [A]; ring
    rw [hid]
    exact (norm_add_le _ _).trans ((add_le_add hprod herr).trans (by ring_nf; rfl))
  have hP : ‖1+(ρ:ℂ)*A‖≤1+s.card := by
    calc
      _ ≤ 1+ρ*‖A‖ := by simpa only [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ0] using norm_add_le (1:ℂ) ((ρ:ℂ)*A)
      _ ≤ 1+2*(s.card*r) := by gcongr
      _ ≤ 1+s.card := by nlinarith [Nat.cast_nonneg (α:=ℝ) s.card]
  have hid : genericLocalQuotient s σ a ρ-1 =
      (1+(ρ:ℂ)*A)*(T-1+A)+((ρ:ℂ)-1)*A-(ρ:ℂ)*A^2 := by dsimp [genericLocalQuotient, A, T]; ring
  rw [hid]
  calc
    _ ≤ ‖1+(ρ:ℂ)*A‖*‖T-1+A‖+‖(ρ:ℂ)-1‖*‖A‖+‖(ρ:ℂ)‖*‖A‖^2 := by
      have h1 := norm_sub_le ((1+(ρ:ℂ)*A)*(T-1+A)+((ρ:ℂ)-1)*A) ((ρ:ℂ)*A^2)
      have h2 := norm_add_le ((1+(ρ:ℂ)*A)*(T-1+A)) (((ρ:ℂ)-1)*A)
      simp only [norm_mul, norm_pow] at h1 h2
      linarith

    _ ≤ (1+s.card)*((4*(s.card:ℝ)^2*2^s.card+2*s.card)*r^2)+(2*r)*(s.card*r)+2*(s.card*r)^2 := by
      have hρn : ‖(ρ:ℂ)‖≤2 := by simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ0] using hρ
      have hρd : ‖(ρ:ℂ)-1‖≤2*r := by exact_mod_cast hρ1
      gcongr
    _ = _ := by ring

theorem norm_exp_sub_one_le_of_re_nonpos {z : ℂ} (hz : z.re≤0) :
    ‖Complex.exp z-1‖ ≤ ‖z‖ := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => Complex.exp ((t:ℂ)*z))
      (Complex.exp ((t:ℂ)*z)*z) t := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const z).cexp
  have hb (t : ℝ) (ht : t∈Set.Ico (0:ℝ) 1) :
      ‖Complex.exp ((t:ℂ)*z)*z‖ ≤ ‖z‖ := by
    rw [norm_mul, Complex.norm_exp]
    have he : Real.exp ((t:ℂ)*z).re ≤ 1 := by
      rw [Real.exp_le_one_iff]
      simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        using mul_nonpos_of_nonneg_of_nonpos ht.1 hz
    exact mul_le_of_le_one_left (norm_nonneg z) he
  simpa only [Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero] using norm_image_sub_le_of_norm_deriv_le_segment_01'
      (fun t _ => (hd t).hasDerivWithinAt) hb

noncomputable def primeMonomial {ι : Type*} (p : ℕ) (z : ι → ℂ) (S : Finset ι) : ℂ :=
  Complex.exp (-(Real.log p : ℂ)*(∑ i∈S, z i))

theorem primeMonomial_norm_le {ι : Type*} {p : ℕ} (hp : 1≤p)
    (z : ι → ℂ) (S : Finset ι) (hz : ∀ i∈S, 0≤(z i).re) :
    ‖primeMonomial p z S‖ ≤ 1 := by
  rw [primeMonomial, Complex.norm_exp, Real.exp_le_one_iff]
  have hlog : 0≤Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast hp)
  have hs : 0≤∑ i∈S, (z i).re := Finset.sum_nonneg hz
  simpa only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
    Complex.ofReal_im, neg_zero, zero_mul, sub_zero, Complex.re_sum]
    using mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hlog) hs

theorem primeMonomial_sub_one {ι : Type*} {p : ℕ} (hp : 1≤p)
    (z : ι → ℂ) (S : Finset ι) (hz : ∀ i∈S, 0≤(z i).re) :
    ‖primeMonomial p z S-1‖ ≤ Real.log p*(∑ i∈S, ‖z i‖) := by
  have hlog : 0≤Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast hp)
  have hexp : (-(Real.log p : ℂ)*(∑ i∈S, z i)).re≤0 := by
    have hs : 0≤∑ i∈S, (z i).re := Finset.sum_nonneg hz
    simpa only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
      Complex.ofReal_im, neg_zero, zero_mul, sub_zero, Complex.re_sum]
      using mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hlog) hs
  calc
    _ ≤ ‖-(Real.log p : ℂ)*(∑ i∈S, z i)‖ := norm_exp_sub_one_le_of_re_nonpos hexp
    _ = Real.log p*‖∑ i∈S, z i‖ := by rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
    _ ≤ _ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) hlog

@[simp] theorem primeMonomial_zero {ι : Type*} (p : ℕ) (S : Finset ι) :
    primeMonomial p (fun _ => (0:ℂ)) S = 1 := by simp [primeMonomial]

noncomputable def eulerP {ι : Type*} (p δ : ℕ) (A : Finset (Finset ι)) (z : ι → ℂ) : ℂ :=
  1+((p:ℂ)-δ)⁻¹*(∑ S∈A, (-1:ℂ)^S.card*primeMonomial p z S)

noncomputable def eulerH {ι : Type*} (p δ : ℕ) (A B : Finset (Finset ι)) (z : ι → ℂ) : ℂ :=
  eulerP p δ A z * ∏ S∈B, (1-(p:ℂ)⁻¹*primeMonomial p z S)^((-1:ℤ)^S.card)

theorem sign_zpow_cases (n : ℕ) : (-1:ℤ)^n=1 ∨ (-1:ℤ)^n= -1 := by
  rcases Nat.even_or_odd n with h | h
  · exact Or.inl h.neg_one_pow
  · exact Or.inr h.neg_one_pow

theorem primeMonomial_scaled_norm {ι : Type*} {p : ℕ} (hp : 1≤p)
    (z : ι → ℂ) (S : Finset ι) (hz : ∀ i∈S, 0≤(z i).re) :
    ‖(p:ℂ)⁻¹*primeMonomial p z S‖ ≤ (p:ℝ)⁻¹ := by
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  exact mul_le_of_le_one_right (by positivity) (primeMonomial_norm_le hp z S hz)

theorem delta_bounds {p δ : ℕ} (hp : 2≤p) (hδ : δ≤1) :
    0<(p:ℝ)-δ ∧ ((p:ℝ)-δ)⁻¹≤2*(p:ℝ)⁻¹ ∧
      0≤(p:ℝ)/((p:ℝ)-δ) ∧ (p:ℝ)/((p:ℝ)-δ)≤2 ∧
        |(p:ℝ)/((p:ℝ)-δ)-1|≤2*(p:ℝ)⁻¹ := by
  have hpR : (2:ℝ)≤p := by exact_mod_cast hp
  have hdR : (δ:ℝ)≤1 := by exact_mod_cast hδ
  have hd0 : (0:ℝ)≤δ := by positivity
  have hp0 : (0:ℝ)<p := by linarith
  have hpd : (0:ℝ)<p-δ := by linarith
  refine ⟨hpd,?_,by positivity,?_,?_⟩
  · rw [inv_eq_one_div, ← div_eq_mul_inv]
    apply (div_le_div_iff₀ hpd hp0).mpr
    linarith
  · exact (div_le_iff₀ hpd).mpr (by linarith)
  · have hid : (p:ℝ)/(p-δ)-1 = δ/(p-δ) := by field_simp; ring
    rw [hid, abs_of_nonneg (by positivity)]
    change (δ:ℝ)/((p:ℝ)-δ)≤2/(p:ℝ)
    apply (div_le_div_iff₀ hpd hp0).mpr
    nlinarith

theorem eulerH_generic_eq {ι : Type*} {p δ : ℕ} (hp : 2≤p) (hδ : δ≤1)
    (A : Finset (Finset ι)) (z : ι → ℂ) :
    eulerH p δ A A z = genericLocalQuotient A
      (fun S => (-1:ℤ)^S.card) (fun S => (p:ℂ)⁻¹*primeMonomial p z S)
      ((p:ℝ)/((p:ℝ)-δ)) := by
  have hp0 : (p:ℂ)≠0 := by exact_mod_cast (by omega : p≠0)
  have hpd : (p:ℂ)-(δ:ℂ)≠0 := by exact_mod_cast (delta_bounds hp hδ).1.ne'
  unfold eulerH eulerP genericLocalQuotient
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro S _
  field_simp

theorem eulerH_generic_error {ι : Type*} {p δ : ℕ} (hp : 2≤p) (hδ : δ≤1)
    (A : Finset (Finset ι)) (z : ι → ℂ) (hz : ∀ S∈A, ∀ i∈S, 0≤(z i).re) :
    ‖eulerH p δ A A z-1‖ ≤
      ((1+A.card)*(4*(A.card:ℝ)^2*2^A.card+2*A.card)+2*A.card+2*(A.card:ℝ)^2)/(p:ℝ)^2 := by
  rw [eulerH_generic_eq hp hδ]
  have hd := delta_bounds hp hδ
  have hr : (p:ℝ)⁻¹≤1/2 := by
    rw [inv_eq_one_div]
    apply (div_le_div_iff₀ (by exact_mod_cast (by omega : 0<p)) (by norm_num)).mpr
    have hh : (2:ℝ)≤p := by exact_mod_cast hp
    linarith
  simpa only [inv_pow, div_eq_mul_inv] using
    genericLocalQuotient_error A (fun S => (-1:ℤ)^S.card)
      (fun S => (p:ℂ)⁻¹*primeMonomial p z S) (by positivity) hr hd.2.2.1 hd.2.2.2.1 hd.2.2.2.2
      (fun S _ => sign_zpow_cases S.card)
      (fun S hS => primeMonomial_scaled_norm (by omega) z S (hz S hS))

theorem norm_one_sub_zpow_sub {a b : ℂ} (ha : ‖a‖≤1/2) (hb : ‖b‖≤1/2)
    {σ : ℤ} (hσ : σ=1 ∨ σ= -1) :
    ‖(1-a)^σ-(1-b)^σ‖≤4*‖a-b‖ := by
  have hla := norm_one_sub_lower ha
  have hlb := norm_one_sub_lower hb
  have hna : 1-a≠0 := norm_pos_iff.mp (by linarith)
  have hnb : 1-b≠0 := norm_pos_iff.mp (by linarith)
  obtain rfl | rfl := hσ
  · simp only [zpow_one]
    have hid : (1-a)-(1-b)= -(a-b) := by ring
    rw [hid, norm_neg]
    nlinarith [norm_nonneg (a-b)]
  · simp only [zpow_neg_one]
    have hid : (1-a)⁻¹-(1-b)⁻¹=(a-b)/((1-a)*(1-b)) := by field_simp; ring
    rw [hid, norm_div, norm_mul]
    have hp : 1/4≤‖1-a‖*‖1-b‖ := by nlinarith
    apply (div_le_iff₀ (by positivity : 0<‖1-a‖*‖1-b‖)).mpr
    nlinarith [norm_nonneg (a-b)]

theorem prime_inv_le_half {p : ℕ} (hp : 2≤p) : (p:ℝ)⁻¹≤1/2 := by
  rw [inv_eq_one_div]
  apply (div_le_div_iff₀ (by exact_mod_cast (by omega : 0<p)) (by norm_num)).mpr
  have hh : (2:ℝ)≤p := by exact_mod_cast hp
  linarith

theorem norm_eulerP_le {ι : Type*} {p δ : ℕ} (hp : 2≤p) (hδ : δ≤1)
    (A : Finset (Finset ι)) (z : ι → ℂ) (hz : ∀ S∈A, ∀ i∈S, 0≤(z i).re) :
    ‖eulerP p δ A z‖ ≤ Real.exp (2*A.card*(p:ℝ)⁻¹) := by
  have hsum : ‖∑ S∈A, (-1:ℂ)^S.card*primeMonomial p z S‖≤A.card := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _S∈A, (1:ℝ) := Finset.sum_le_sum fun S hS => by
        simpa only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
          using primeMonomial_norm_le (by omega) z S (hz S hS)
      _ = _ := by simp
  have hd := delta_bounds hp hδ
  have hn : ‖((p:ℂ)-δ)⁻¹‖≤2*(p:ℝ)⁻¹ := by
    rw [norm_inv, ← Complex.ofReal_natCast p, ← Complex.ofReal_natCast δ,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd.1]
    exact hd.2.1
  calc
    _ ≤ 1+‖((p:ℂ)-δ)⁻¹‖*‖∑ S∈A, (-1:ℂ)^S.card*primeMonomial p z S‖ := by
      simpa only [eulerP, norm_one, norm_mul] using norm_add_le (1:ℂ)
        (((p:ℂ)-δ)⁻¹*(∑ S∈A, (-1:ℂ)^S.card*primeMonomial p z S))
    _ ≤ 1+(2*(p:ℝ)⁻¹)*A.card := by gcongr
    _ = 2*A.card*(p:ℝ)⁻¹+1 := by ring
    _ ≤ _ := Real.add_one_le_exp _

theorem norm_eulerT_le {ι : Type*} {p : ℕ} (hp : 2≤p)
    (B : Finset (Finset ι)) (z : ι → ℂ) (hz : ∀ S∈B, ∀ i∈S, 0≤(z i).re) :
    ‖∏ S∈B, (1-(p:ℂ)⁻¹*primeMonomial p z S)^((-1:ℤ)^S.card)‖ ≤
      Real.exp (2*B.card*(p:ℝ)⁻¹) := by
  have hb (S : Finset ι) (hS : S∈B) :
      ‖(1-(p:ℂ)⁻¹*primeMonomial p z S)^((-1:ℤ)^S.card)‖≤Real.exp (2*(p:ℝ)⁻¹) := by
    have hh := norm_one_sub_zpow_sub_one (prime_inv_le_half hp)
      (primeMonomial_scaled_norm (by omega) z S (hz S hS)) (sign_zpow_cases S.card)
    have hn := norm_sub_norm_le ((1-(p:ℂ)⁻¹*primeMonomial p z S)^((-1:ℤ)^S.card)) (1:ℂ)
    rw [norm_one] at hn
    exact (show _ ≤ 2*(p:ℝ)⁻¹+1 by linarith).trans (Real.add_one_le_exp _)
  calc
    _ ≤ ∏ _S∈B, Real.exp (2*(p:ℝ)⁻¹) := by
      rw [norm_prod]
      exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) hb
    _ = Real.exp (2*B.card*(p:ℝ)⁻¹) := by
      rw [← Real.exp_sum]
      congr 1
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

theorem norm_eulerH_le {ι : Type*} {p δ : ℕ} (hp : 2≤p) (hδ : δ≤1)
    (A B : Finset (Finset ι)) (z : ι → ℂ) (hz : ∀ i, 0≤(z i).re) :
    ‖eulerH p δ A B z‖ ≤ Real.exp (2*(A.card+B.card)*(p:ℝ)⁻¹) := by
  rw [eulerH, norm_mul]
  calc
    _ ≤ Real.exp (2*A.card*(p:ℝ)⁻¹)*Real.exp (2*B.card*(p:ℝ)⁻¹) :=
      mul_le_mul (norm_eulerP_le hp hδ A z (fun _ _ i _ => hz i))
        (norm_eulerT_le hp B z (fun _ _ i _ => hz i)) (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem norm_eulerP_sub_zero_le {ι : Type*} [Fintype ι] {p δ : ℕ}
    (hp : 2≤p) (hδ : δ≤1) (A : Finset (Finset ι))
    (z : ι → ℂ) (hz : ∀ i, 0≤(z i).re) :
    ‖eulerP p δ A z-eulerP p δ A (fun _ => 0)‖ ≤
      2*A.card*(p:ℝ)⁻¹*Real.log p*(∑ i, ‖z i‖) := by
  classical
  have hlog : 0≤Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1≤p))
  have hs (S : Finset ι) : ∑ i∈S, ‖z i‖≤∑ i, ‖z i‖ :=
    Finset.sum_le_univ_sum_of_nonneg (fun _ => norm_nonneg _)
  have he (S : Finset ι) : ‖primeMonomial p z S-1‖≤Real.log p*(∑ i, ‖z i‖) :=
    (primeMonomial_sub_one (by omega) z S (fun i _ => hz i)).trans (mul_le_mul_of_nonneg_left (hs S) hlog)
  have hd := delta_bounds hp hδ
  have hn : ‖((p:ℂ)-δ)⁻¹‖≤2*(p:ℝ)⁻¹ := by
    rw [norm_inv, ← Complex.ofReal_natCast p, ← Complex.ofReal_natCast δ,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd.1]
    exact hd.2.1
  have hid : eulerP p δ A z-eulerP p δ A (fun _ => 0) =
      ((p:ℂ)-δ)⁻¹*∑ S∈A, (-1:ℂ)^S.card*(primeMonomial p z S-1) := by
    simp only [eulerP, primeMonomial_zero, mul_one, Finset.sum_sub_distrib, mul_sub]
    ring
  rw [hid, norm_mul]
  have hsum : ‖∑ S∈A, (-1:ℂ)^S.card*(primeMonomial p z S-1)‖≤
      A.card*(Real.log p*(∑ i, ‖z i‖)) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _S∈A, Real.log p*(∑ i, ‖z i‖) := Finset.sum_le_sum fun S _ => by
        simpa only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul] using he S
      _ = _ := by simp
  calc
    _ ≤ (2*(p:ℝ)⁻¹)*(A.card*(Real.log p*(∑ i, ‖z i‖))) := by gcongr
    _ = _ := by ring

theorem norm_eulerT_sub_zero_le {ι : Type*} [Fintype ι] {p : ℕ}
    (hp : 2≤p) (B : Finset (Finset ι)) (z : ι → ℂ) (hz : ∀ i, 0≤(z i).re) :
    ‖(∏ S∈B, (1-(p:ℂ)⁻¹*primeMonomial p z S)^((-1:ℤ)^S.card)) -
      (∏ S∈B, (1-(p:ℂ)⁻¹)^((-1:ℤ)^S.card))‖ ≤
      Real.exp (2*B.card*(p:ℝ)⁻¹)*(4*B.card*(p:ℝ)⁻¹*Real.log p*(∑ i, ‖z i‖)) := by
  classical
  have hlog : 0≤Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1≤p))
  have hs (S : Finset ι) : ∑ i∈S, ‖z i‖≤∑ i, ‖z i‖ :=
    Finset.sum_le_univ_sum_of_nonneg (fun _ => norm_nonneg _)
  have he (S : Finset ι) : ‖primeMonomial p z S-1‖≤Real.log p*(∑ i, ‖z i‖) :=
    (primeMonomial_sub_one (by omega) z S (fun i _ => hz i)).trans (mul_le_mul_of_nonneg_left (hs S) hlog)
  have hbn (w : ι → ℂ) (hw : ∀ i, 0≤(w i).re) (S : Finset ι) :
      ‖(1-(p:ℂ)⁻¹*primeMonomial p w S)^((-1:ℤ)^S.card)‖≤Real.exp (2*(p:ℝ)⁻¹) := by
    have hh := norm_one_sub_zpow_sub_one (prime_inv_le_half hp)
      (primeMonomial_scaled_norm (by omega) w S (fun i _ => hw i)) (sign_zpow_cases S.card)
    have hn := norm_sub_norm_le ((1-(p:ℂ)⁻¹*primeMonomial p w S)^((-1:ℤ)^S.card)) (1:ℂ)
    rw [norm_one] at hn
    exact (show _ ≤ 2*(p:ℝ)⁻¹+1 by linarith).trans (Real.add_one_le_exp _)
  have hg (S : Finset ι) : ‖(1-(p:ℂ)⁻¹)^((-1:ℤ)^S.card)‖≤Real.exp (2*(p:ℝ)⁻¹) := by
    simpa only [primeMonomial_zero, mul_one] using hbn (fun _ => 0) (by simp) S
  have hd (S : Finset ι) :
      ‖(1-(p:ℂ)⁻¹*primeMonomial p z S)^((-1:ℤ)^S.card)-(1-(p:ℂ)⁻¹)^((-1:ℤ)^S.card)‖≤
        4*(p:ℝ)⁻¹*Real.log p*(∑ i, ‖z i‖) := by
    have ha := (primeMonomial_scaled_norm (by omega : 1≤p) z S (fun i _ => hz i)).trans (prime_inv_le_half hp)
    have hb : ‖(p:ℂ)⁻¹‖≤1/2 := by simpa only [norm_inv, Complex.norm_natCast] using prime_inv_le_half hp
    calc
      _ ≤ 4*‖(p:ℂ)⁻¹*primeMonomial p z S-(p:ℂ)⁻¹‖ := norm_one_sub_zpow_sub ha hb (sign_zpow_cases S.card)
      _ = 4*(p:ℝ)⁻¹*‖primeMonomial p z S-1‖ := by
        rw [← mul_sub_one, norm_mul, norm_inv, Complex.norm_natCast, mul_assoc]
      _ ≤ 4*(p:ℝ)⁻¹*(Real.log p*(∑ i, ‖z i‖)) := mul_le_mul_of_nonneg_left (he S) (by positivity)
      _ = _ := by ring
  have hh := norm_prod_sub_prod_le B
    (fun S => (1-(p:ℂ)⁻¹*primeMonomial p z S)^((-1:ℤ)^S.card))
    (fun S => (1-(p:ℂ)⁻¹)^((-1:ℤ)^S.card))
    (fun _ => Real.exp (2*(p:ℝ)⁻¹)) (fun _ => 4*(p:ℝ)⁻¹*Real.log p*(∑ i, ‖z i‖))
    (fun _ _ => Real.one_le_exp (by positivity)) (fun S _ => hbn z hz S)
    (fun S _ => hg S) (fun S _ => hd S)
  have ht : ∏ _S∈B, Real.exp (2*(p:ℝ)⁻¹)=Real.exp (2*B.card*(p:ℝ)⁻¹) := by
    rw [← Real.exp_sum]
    congr 1
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  rw [ht] at hh
  convert hh using 1
  simp only [Finset.sum_const, nsmul_eq_mul]
  ring

theorem norm_eulerH_sub_zero_le {ι : Type*} [Fintype ι] {p δ : ℕ}
    (hp : 2≤p) (hδ : δ≤1) (A B : Finset (Finset ι))
    (z : ι → ℂ) (hz : ∀ i, 0≤(z i).re) :
    ‖eulerH p δ A B z-eulerH p δ A B (fun _ => 0)‖ ≤
      Real.exp (2*(A.card+B.card)*(p:ℝ)⁻¹)*
        ((2*A.card+4*B.card)*(p:ℝ)⁻¹*Real.log p*(∑ i, ‖z i‖)) := by
  let T := fun w : ι → ℂ => ∏ S∈B, (1-(p:ℂ)⁻¹*primeMonomial p w S)^((-1:ℤ)^S.card)
  have hT := norm_eulerT_le hp B z (fun _ _ i _ => hz i)
  have hdT : ‖T z-T (fun _ => 0)‖≤
      Real.exp (2*B.card*(p:ℝ)⁻¹)*(4*B.card*(p:ℝ)⁻¹*Real.log p*(∑ i, ‖z i‖)) := by
    simpa only [T, primeMonomial_zero, mul_one] using norm_eulerT_sub_zero_le hp B z hz
  have hp0 := norm_eulerP_le hp hδ A (fun _ => 0) (by simp)
  have hPd := norm_eulerP_sub_zero_le hp hδ A z hz
  have hlog : 0≤Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1≤p))
  have hAe : 1≤Real.exp (2*A.card*(p:ℝ)⁻¹) := Real.one_le_exp (by positivity)
  have hid : eulerH p δ A B z-eulerH p δ A B (fun _ => 0) =
      (eulerP p δ A z-eulerP p δ A (fun _ => 0))*T z +
        eulerP p δ A (fun _ => 0)*(T z-T (fun _ => 0)) := by dsimp [eulerH, T]; ring
  rw [hid]
  calc
    _ ≤ ‖eulerP p δ A z-eulerP p δ A (fun _ => 0)‖*‖T z‖ +
        ‖eulerP p δ A (fun _ => 0)‖*‖T z-T (fun _ => 0)‖ := by
      simpa only [norm_mul] using norm_add_le
        ((eulerP p δ A z-eulerP p δ A (fun _ => 0))*T z)
        (eulerP p δ A (fun _ => 0)*(T z-T (fun _ => 0)))
    _ ≤ (2*A.card*(p:ℝ)⁻¹*Real.log p*(∑ i, ‖z i‖))*Real.exp (2*B.card*(p:ℝ)⁻¹)+
        Real.exp (2*A.card*(p:ℝ)⁻¹)*(Real.exp (2*B.card*(p:ℝ)⁻¹)*
          (4*B.card*(p:ℝ)⁻¹*Real.log p*(∑ i, ‖z i‖))) := by gcongr
    _ ≤ Real.exp (2*A.card*(p:ℝ)⁻¹)*
        ((2*A.card*(p:ℝ)⁻¹*Real.log p*(∑ i, ‖z i‖))*Real.exp (2*B.card*(p:ℝ)⁻¹))+
        Real.exp (2*A.card*(p:ℝ)⁻¹)*(Real.exp (2*B.card*(p:ℝ)⁻¹)*
          (4*B.card*(p:ℝ)⁻¹*Real.log p*(∑ i, ‖z i‖))) := by
      have hnn : 0 ≤ (2*(A.card:ℝ)*(p:ℝ)⁻¹*Real.log p*(∑ i, ‖z i‖))*Real.exp (2*B.card*(p:ℝ)⁻¹) := by positivity
      exact add_le_add (le_mul_of_one_le_left hnn hAe) le_rfl
    _ = _ := by
      rw [show 2*((A.card:ℝ)+B.card)*(p:ℝ)⁻¹=2*A.card*(p:ℝ)⁻¹+2*B.card*(p:ℝ)⁻¹ by ring,
        Real.exp_add]
      ring

end LargePrimeGaps

end OAI
