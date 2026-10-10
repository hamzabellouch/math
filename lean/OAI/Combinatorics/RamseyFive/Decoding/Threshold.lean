import Mathlib

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.HighParameters
open scoped BigOperators

noncomputable def threshold (q n a : ℝ) : ℕ := ⌊n*a/(64*q)⌋₊
noncomputable def cap (q a : ℝ) : ℕ := ⌈1024*q^2/a⌉₊
noncomputable def multiplicity (q n a : ℝ) : ℕ := ⌈134217728*q^6/(n^2*a^3)⌉₊
noncomputable def degree (q n a χ : ℝ) : ℕ := ⌈34359738368*q^6/(n^2*a^4)*Real.exp χ⌉₊

lemma threshold_bounds {q n a : ℝ} (hq : 1≤q) (hn : 0<n) (ha : 0<a) (ha2 : a≤2)
    (hhigh : 2097152*q^2≤n*a^2) :
    n*a/(128*q) ≤ (threshold q n a:ℝ) ∧
    (threshold q n a:ℝ) ≤ n*a/(64*q) := by
  have hq0 : 0<q := zero_lt_one.trans_le hq
  have hna : 1048576*q^2≤n*a := by
    have haa : a^2≤2*a := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left haa hn.le]
  have hx : 2≤n*a/(64*q) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (q-1)]
  have hf := Nat.lt_floor_add_one (n*a/(64*q))
  have hfloor : n*a/(128*q)≤(threshold q n a:ℝ) := by
    dsimp [threshold]
    have he : n*a/(128*q)=(n*a/(64*q))/2 := by ring
    rw [he]
    linarith
  exact ⟨hfloor,Nat.floor_le (by positivity)⟩

lemma cap_bounds {q a : ℝ} (hq : 1≤q) (ha : 0<a) (ha2 : a≤2) :
    1024*q^2/a ≤ (cap q a:ℝ) ∧ (cap q a:ℝ) ≤ 2048*q^2/a := by
  have hq0 : 0<q := zero_lt_one.trans_le hq
  have hb : 1≤1024*q^2/a := by
    apply (le_div_iff₀ ha).mpr
    nlinarith [sq_nonneg (q-1)]
  refine ⟨Nat.le_ceil _,?_⟩
  have hc := Nat.ceil_lt_add_one (show 0≤1024*q^2/a by positivity)
  have he : 2048*q^2/a=2*(1024*q^2/a) := by ring
  rw [he]
  dsimp [cap,multiplicity]
  linarith

lemma multiplicity_bounds {q n a : ℝ} (hq : 1≤q) (hn : 0<n) (ha : 0<a)
    (ha2 : a≤2) (hnq : n^2≤100*q^5) :
    134217728*q^6/(n^2*a^3) ≤ (multiplicity q n a:ℝ) ∧
    (multiplicity q n a:ℝ) ≤ 268435456*q^6/(n^2*a^3) := by
  have hq0 : 0<q := zero_lt_one.trans_le hq
  have ha3 : a^3≤8 := by nlinarith [pow_le_pow_left₀ ha.le ha2 3]
  have hden : n^2*a^3 ≤ 800*q^5 := by
    calc _ ≤ (100*q^5)*8 := mul_le_mul hnq ha3 (by positivity) (by positivity)
         _ = _ := by ring
  have hb : 1≤134217728*q^6/(n^2*a^3) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have : q^5≤q^6 := by simpa only [pow_succ,mul_one] using mul_le_mul_of_nonneg_left hq (pow_nonneg hq0.le 5)
    nlinarith [pow_pos hq0 5]
  refine ⟨Nat.le_ceil _,?_⟩
  have hc := Nat.ceil_lt_add_one (show 0≤134217728*q^6/(n^2*a^3) by positivity)
  have he : 268435456*q^6/(n^2*a^3)=2*(134217728*q^6/(n^2*a^3)) := by ring
  rw [he]
  dsimp [cap,multiplicity]
  linarith

theorem high_budget_conditions {q n a : ℝ} (hq : 1≤q) (hn : 0<n) (ha : 0<a)
    (ha2 : a≤2) (hnq : n^2≤100*q^5) (hhigh : 2097152*q^2≤n*a^2) :
    0<threshold q n a ∧
    2*(q+1)≤(threshold q n a:ℝ) ∧
    2*n≤(multiplicity q n a:ℝ)*(threshold q n a:ℝ) ∧
    2*(cap q a:ℝ)/q≤(threshold q n a:ℝ) ∧
    4*q^2*(cap q a:ℝ)≤(multiplicity q n a:ℝ)*(threshold q n a:ℝ)^2 ∧
    64*n≤(threshold q n a:ℝ)^2 := by
  have hq0 : 0<q := zero_lt_one.trans_le hq
  obtain ⟨hM,hM'⟩ := threshold_bounds hq hn ha ha2 hhigh
  obtain ⟨hcap,hcap'⟩ := cap_bounds hq ha ha2
  obtain ⟨hu,hu'⟩ := multiplicity_bounds hq hn ha ha2 hnq
  have hM0 : (0:ℝ)<threshold q n a := (by positivity : 0<n*a/(128*q)).trans_le hM
  have hm2 : (n*a/(128*q))^2≤(threshold q n a:ℝ)^2 := pow_le_pow_left₀ (by positivity) hM 2
  have hna : 1048576*q^2≤n*a := by
    nlinarith [mul_le_mul_of_nonneg_left (show a^2≤2*a by nlinarith) hn.le]
  refine ⟨by exact_mod_cast hM0,?_,?_,?_,?_,?_⟩
  · apply le_trans _ hM
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (q-1)]
  · calc
      _ ≤ (134217728*q^6/(n^2*a^3))*(n*a/(128*q)) := by
        have he : (134217728*q^6/(n^2*a^3))*(n*a/(128*q)) =
            1048576*q^5/(n*a^2) := by field_simp; ring
        rw [he]
        apply (le_div_iff₀ (by positivity)).mpr
        have hna2 : n^2*a^2≤400*q^5 := by
          calc _ ≤ (100*q^5)*4 := mul_le_mul hnq
                 (show a^2≤4 by nlinarith) (by positivity) (by positivity)
               _ = _ := by ring
        nlinarith [pow_pos hq0 5]
      _ ≤ _ := mul_le_mul hu hM (by positivity) (by positivity)
  · calc
      _ ≤ 2*(2048*q^2/a)/q := div_le_div_of_nonneg_right (by nlinarith) hq0.le
      _ ≤ n*a/(128*q) := by
        have he : 2*(2048*q^2/a)/q=4096*q/a := by field_simp; ring
        rw [he]
        apply (div_le_div_iff₀ ha (by positivity)).mpr
        nlinarith
      _ ≤ _ := hM
  · calc
      _ ≤ 4*q^2*(2048*q^2/a) := mul_le_mul_of_nonneg_left hcap' (by positivity)
      _ = (134217728*q^6/(n^2*a^3))*(n*a/(128*q))^2 := by
        field_simp
        ring
      _ ≤ _ := mul_le_mul hu hm2 (by positivity) (by positivity)
  · apply le_trans _ hm2
    rw [div_pow]
    apply (le_div_iff₀ (show 0<(128*q)^2 by positivity)).mpr
    rw [mul_pow]
    nlinarith [mul_le_mul_of_nonneg_left hhigh hn.le]

lemma head_length_condition {q n a j : ℝ} (hq : 1≤q) (hn : 0<n) (ha : 0<a)
    (ha2 : a≤2) (hhigh : 2097152*q^2≤n*a^2) (hj : 0≤j)
    (hjn : j*(cap q a:ℝ)≤n) : j*(q+1)≤(threshold q n a:ℝ) := by
  have hq0 : 0<q := zero_lt_one.trans_le hq
  have hM := (threshold_bounds hq hn ha ha2 hhigh).1
  have hc := (cap_bounds hq ha ha2).1
  have hjn' : j*(1024*q^2/a)≤n := (mul_le_mul_of_nonneg_left hc hj).trans hjn
  calc
    _ ≤ j*(2*q) := mul_le_mul_of_nonneg_left (by linarith) hj
    _ = (j*(1024*q^2/a))*(a/(512*q)) := by field_simp; ring
    _ ≤ n*(a/(512*q)) := mul_le_mul_of_nonneg_right hjn' (by positivity)
    _ ≤ n*a/(128*q) := by
      have he : n*(a/(512*q))=(n*a/(128*q))/4 := by ring
      rw [he]
      have : 0≤n*a/(128*q) := by positivity
      linarith
    _ ≤ _ := hM

lemma degree_multiplicity_condition {q n a χ : ℝ} (hq : 1≤q) (hn : 0<n)
    (ha : 0<a) (ha2 : a≤2) (hnq : n^2≤100*q^5) (hχ : 0≤χ) :
    8*(2*multiplicity q n a+1)≤degree q n a χ := by
  have hq0 : 0<q := zero_lt_one.trans_le hq
  obtain ⟨hu,hu'⟩ := multiplicity_bounds hq hn ha ha2 hnq
  let u₀ := 134217728*q^6/(n^2*a^3)
  have hu₀ : 0<u₀ := by dsimp [u₀]; positivity
  have huN : (0:ℝ)<(multiplicity q n a:ℝ) := hu₀.trans_le hu
  have hu1 : (1:ℝ)≤ multiplicity q n a := by exact_mod_cast (show 1≤ multiplicity q n a by exact_mod_cast huN)
  have hu'₀ : (multiplicity q n a:ℝ)≤2*u₀ := by dsimp [u₀]; convert hu' using 1; ring
  have hd := Nat.le_ceil (34359738368*q^6/(n^2*a^4)*Real.exp χ)
  have hexp : 1≤Real.exp χ := Real.one_le_exp_iff.mpr hχ
  have hd' : 128*u₀≤(degree q n a χ:ℝ) := by
    apply le_trans _ hd
    have he : 34359738368*q^6/(n^2*a^4)*Real.exp χ=256*u₀*Real.exp χ/a := by
      dsimp [u₀]
      field_simp
      ring
    rw [he]
    apply (le_div_iff₀ ha).mpr
    nlinarith [mul_le_mul_of_nonneg_left hexp hu₀.le]
  have hh : (8:ℝ)*(2*(multiplicity q n a:ℝ)+1)≤(degree q n a χ:ℝ) := by linarith
  exact_mod_cast hh

lemma high_real_substitution {q g a : ℝ} (hq : 0<q) (hg : 100000000≤g)
    (ha : Real.exp (-g/10)≤a) : 2097152*q^2≤(q^2*Real.exp g)*a^2 := by
  have ha0 : 0<a := (Real.exp_pos _).trans_le ha
  have ha2 := pow_le_pow_left₀ (Real.exp_pos (-g/10)).le ha 2
  have he : Real.exp g*Real.exp (-g/10)^2=Real.exp (4*g/5) := by
    rw [pow_two,←Real.exp_add,←Real.exp_add]
    congr 1
    ring
  have hh : 2097152≤Real.exp (4*g/5) := by
    have h := Real.add_one_le_exp (4*g/5)
    linarith
  calc
    _ = q^2*2097152 := mul_comm _ _
    _ ≤ q^2*Real.exp (4*g/5) := mul_le_mul_of_nonneg_left hh (sq_nonneg q)
    _ = (q^2*Real.exp g)*Real.exp (-g/10)^2 := by rw [mul_assoc,he]
    _ ≤ _ := mul_le_mul_of_nonneg_left ha2 (by positivity)

theorem tail_exception_bound {q n a χ e : ℝ} (hq : 1≤q) (hn : 0<n)
    (ha : 0<a) (ha2 : a≤2) (hnq : n^2≤100*q^5)
    (hhigh : 2097152*q^2≤n*a^2) (he : 0≤e)
    (hbudget : e*(degree q n a χ:ℝ)^2*(threshold q n a:ℝ)^2 ≤
      4096*n^2*(2*(multiplicity q n a:ℝ)+1)^2) :
    e≤36864*q^2*Real.exp (-(2*χ)) := by
  have hq0 : 0<q := zero_lt_one.trans_le hq
  let u₀ := 134217728*q^6/(n^2*a^3)
  let M₀ := n*a/(128*q)
  let D₀ := 256*u₀*Real.exp χ/a
  have hu₀ : 0<u₀ := by dsimp [u₀]; positivity
  have hM₀ : 0<M₀ := by dsimp [M₀]; positivity
  have hD₀ : 0<D₀ := by dsimp [D₀]; positivity
  obtain ⟨hu,hu'⟩ := multiplicity_bounds hq hn ha ha2 hnq
  have hu'₀ : (multiplicity q n a:ℝ)≤2*u₀ := by
    dsimp [u₀]
    convert hu' using 1
    ring
  have huN : (0:ℝ)<(multiplicity q n a:ℝ) := hu₀.trans_le hu
  have hu1 : (1:ℝ)≤ multiplicity q n a := by
    exact_mod_cast (show 1≤ multiplicity q n a by exact_mod_cast huN)
  have hM : M₀≤(threshold q n a:ℝ) := (threshold_bounds hq hn ha ha2 hhigh).1
  have hD : D₀≤(degree q n a χ:ℝ) := by
    apply le_trans _ (Nat.le_ceil _)
    dsimp [D₀,u₀,degree]
    apply le_of_eq
    field_simp
    ring
  have h2u : 2*(multiplicity q n a:ℝ)+1≤6*u₀ := by linarith
  have hnum : 4096*n^2*(2*(multiplicity q n a:ℝ)+1)^2≤4096*n^2*(6*u₀)^2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h2u 2) (by positivity)
  have hden : D₀^2*M₀^2≤(degree q n a χ:ℝ)^2*(threshold q n a:ℝ)^2 :=
    mul_le_mul (pow_le_pow_left₀ hD₀.le hD 2) (pow_le_pow_left₀ hM₀.le hM 2)
      (by positivity) (by positivity)
  have hh : e*(D₀^2*M₀^2)≤4096*n^2*(6*u₀)^2 := by
    calc
      _ ≤ e*((degree q n a χ:ℝ)^2*(threshold q n a:ℝ)^2) :=
        mul_le_mul_of_nonneg_left hden he
      _ ≤ _ := by nlinarith [hbudget.trans hnum]
  calc
    e ≤ (4096*n^2*(6*u₀)^2)/(D₀^2*M₀^2) :=
      (le_div_iff₀ (by positivity)).mpr hh
    _ = _ := by
      dsimp [D₀,M₀]
      rw [Real.exp_neg,show 2*χ=χ+χ by ring,Real.exp_add]
      field_simp
      ring

lemma head_mean_condition {q n a r : ℝ} (hq : 1≤q) (hn : 0<n) (ha : 0<a)
    (ha2 : a≤2) (hhigh : 2097152*q^2≤n*a^2) (hr : r≤1/q) :
    2*r*(n*a/1024)≤(threshold q n a:ℝ) := by
  have hq0 : 0<q := zero_lt_one.trans_le hq
  have hM := (threshold_bounds hq hn ha ha2 hhigh).1
  calc
    _ ≤ 2*(1/q)*(n*a/1024) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = (n*a/(128*q))/4 := by ring
    _ ≤ n*a/(128*q) := by
      have : 0≤n*a/(128*q) := by positivity
      linarith
    _ ≤ _ := hM

lemma tail_mean_condition {q n a r : ℝ} (hq : 1≤q) (hn : 0<n) (ha : 0<a)
    (ha2 : a≤2) (hnq : n^2≤100*q^5) (hhigh : 2097152*q^2≤n*a^2) (hr : r≤1/q) :
    2*r*(cap q a:ℝ)≤(threshold q n a:ℝ) := by
  have hh := (high_budget_conditions hq hn ha ha2 hnq hhigh).2.2.2.1
  have hcap : (0:ℝ)≤cap q a := Nat.cast_nonneg _
  calc
    _ ≤ 2*(1/q)*(cap q a:ℝ) := mul_le_mul_of_nonneg_right (by linarith) hcap
    _ = 2*(cap q a:ℝ)/q := by ring
    _ ≤ _ := hh

lemma large_exception_bound {q n a e : ℝ} (hq : 1≤q) (hn : 0<n)
    (ha : 0<a)
    (hbudget : e*(n*a/1024)^2≤(q^2+q+1)*n^2) : e≤3145728*q^2/a^2 := by
  have hq0 : 0<q := zero_lt_one.trans_le hq
  have hqQ : q^2+q+1≤3*q^2 := by nlinarith [sq_nonneg (q-1)]
  have hh : e*(n*a/1024)^2≤3*q^2*n^2 :=
    hbudget.trans (mul_le_mul_of_nonneg_right hqQ (sq_nonneg n))
  calc
    e ≤ (3*q^2*n^2)/(n*a/1024)^2 := (le_div_iff₀ (by positivity)).mpr hh
    _ = _ := by field_simp; ring

lemma head_exception_bound {q n a χ j e : ℝ} (hq : 1≤q) (hn : 0<n)
    (ha : 0<a) (ha2 : a≤2) (hhigh : 2097152*q^2≤n*a^2) (he : 0≤e) (hj : 0≤j)
    (hjn : j*(cap q a:ℝ)≤n)
    (hbudget : e*(degree q n a χ:ℝ)*(threshold q n a:ℝ)^2≤4*q^2*(q+1)*j*n) :
    e≤(n^2*a^3/q^3)*Real.exp (-χ) := by
  have hq0 : 0<q := zero_lt_one.trans_le hq
  let D₀ := 34359738368*q^6/(n^2*a^4)*Real.exp χ
  let M₀ := n*a/(128*q)
  have hD₀ : 0<D₀ := by dsimp [D₀]; positivity
  have hM₀ : 0<M₀ := by dsimp [M₀]; positivity
  have hD : D₀≤(degree q n a χ:ℝ) := Nat.le_ceil _
  have hM : M₀≤(threshold q n a:ℝ) := (threshold_bounds hq hn ha ha2 hhigh).1
  have hcap := (cap_bounds hq ha ha2).1
  have hj' : j≤n*a/(1024*q^2) := by
    have hh : j*(1024*q^2/a)≤n := (mul_le_mul_of_nonneg_left hcap hj).trans hjn
    have hh' := (le_div_iff₀ (show 0<1024*q^2/a by positivity)).mpr hh
    calc
      j ≤ n / (1024*q^2/a) := hh'
      _ = _ := div_div_eq_mul_div _ _ _
  have hnum : 4*q^2*(q+1)*j*n≤n^2*a*q/128 := by
    calc
      _ ≤ 4*q^2*(2*q)*j*n := by gcongr; linarith
      _ ≤ 4*q^2*(2*q)*(n*a/(1024*q^2))*n := by gcongr
      _ = _ := by field_simp; ring
  have hden : D₀*M₀^2≤(degree q n a χ:ℝ)*(threshold q n a:ℝ)^2 :=
    mul_le_mul hD (pow_le_pow_left₀ hM₀.le hM 2) (by positivity) (by positivity)
  have hh : e*(D₀*M₀^2)≤n^2*a*q/128 := by
    calc
      _ ≤ e*((degree q n a χ:ℝ)*(threshold q n a:ℝ)^2) := mul_le_mul_of_nonneg_left hden he
      _ ≤ _ := by nlinarith [hbudget.trans hnum]
  calc
    e ≤ (n^2*a*q/128)/(D₀*M₀^2) := (le_div_iff₀ (by positivity)).mpr hh
    _ = ((n^2*a^3/q^3)*Real.exp (-χ))/268435456 := by
      dsimp [D₀,M₀]
      rw [Real.exp_neg]
      field_simp
      ring
    _ ≤ _ := by
      have : 0≤(n^2*a^3/q^3)*Real.exp (-χ) := by positivity
      linarith

end SharpRamseyFive.HighParameters

end OAI
