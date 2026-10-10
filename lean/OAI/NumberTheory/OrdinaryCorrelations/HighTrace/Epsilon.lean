import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter

namespace OrdinaryCorrelations.SourcePrimeBands

def epsilon : ℝ := 1 / 10000
def eta : ℝ := epsilon / 100

def corePrimes (B : ℝ) : Finset ℕ :=
  (Finset.Icc 2 ⌊Real.exp B⌋₊).filter
    (fun p => p.Prime ∧ B ^ (1 - eta) < Real.log (p : ℝ))

def centerPrimes (B : ℝ) : Finset ℕ :=
  (Finset.Icc 2 ⌊Real.exp (B ^ (1 - eta))⌋₊).filter
    (fun p => p.Prime ∧ B ^ (1 - epsilon) < Real.log (p : ℝ))

def coreMass (B : ℝ) : ℝ := ∑ p ∈ corePrimes B, (p : ℝ)⁻¹
def centerMass (B : ℝ) : ℝ := ∑ p ∈ centerPrimes B, (p : ℝ)⁻¹

def primeHarmonic (x : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 2 ⌊x⌋₊).filter Nat.Prime, (p : ℝ)⁻¹

open Classical Finset Real MeasureTheory

namespace Support

def reciprocalHom : ℕ →* ℝ where
  toFun n := (n:ℝ)⁻¹
  map_one' := by simp
  map_mul' m n := by simp [mul_inv_rev,mul_comm]

lemma reciprocal_prime_norm {p : ℕ} (hp : p.Prime) : ‖reciprocalHom p‖ < 1 := by
  have hpR : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  change ‖(p:ℝ)⁻¹‖ < 1
  rw [norm_inv,Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg p)]
  exact (inv_lt_one₀ (by linarith)).mpr hpR

lemma harmonic_le_finite_euler (N : ℕ) :
    (harmonic N:ℝ) ≤ ∏ p ∈ (N+1).primesBelow, (1-(p:ℝ)⁻¹)⁻¹ := by
  let s := (N+1).primesBelow
  have ht := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := reciprocalHom) (fun hp => reciprocal_prime_norm hp) s).2
  have hfil : s.filter Nat.Prime = s := Finset.filter_true_of_mem (fun p hp => Nat.prime_of_mem_primesBelow hp)
  simp only [hfil] at ht
  have hs (n : ↥(Finset.Icc 1 N)) : n.val ∈ Nat.factoredNumbers s := by
    apply Nat.mem_factoredNumbers'.mpr
    intro p hp hpn
    apply Nat.mem_primesBelow.mpr
    refine ⟨?_,hp⟩
    have hn := Finset.mem_Icc.mp n.property
    exact Nat.lt_succ_of_le ((Nat.le_of_dvd (by omega) hpn).trans hn.2)
  let e : ↥(Finset.Icc 1 N) ↪ Nat.factoredNumbers s :=
    ⟨fun n => ⟨n.val, hs n⟩, fun x y h => Subtype.ext (congrArg (fun n : Nat.factoredNumbers s => n.val) h)⟩
  have hb := ht.summable.sum_le_tsum (Finset.univ.map e)
    (fun n _ => show 0 ≤ reciprocalHom n.val by change 0 ≤ (n.val:ℝ)⁻¹; positivity)
  rw [ht.tsum_eq] at hb
  simp only [Finset.sum_map] at hb
  change (∑ n : ↥(Finset.Icc 1 N), (n.val:ℝ)⁻¹) ≤
    ∏ p ∈ (N+1).primesBelow, (1-(p:ℝ)⁻¹)⁻¹ at hb
  rw [Finset.sum_coe_sort (Icc 1 N) (fun n : ℕ => (n:ℝ)⁻¹)] at hb
  simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast] using hb

end Support

open Classical Finset Real MeasureTheory

lemma prime_set_eq (N : ℕ) :
    (Icc 2 N).filter Nat.Prime = (N+1).primesBelow := by
  ext p
  simp only [mem_filter, mem_Icc, Nat.mem_primesBelow]
  constructor
  · rintro ⟨⟨hp2, hpN⟩, hp⟩
    exact ⟨Nat.lt_succ_of_le hpN, hp⟩
  · rintro ⟨hpN, hp⟩
    exact ⟨⟨hp.two_le, Nat.le_of_lt_succ hpN⟩, hp⟩

lemma prime_set_zero_eq (N : ℕ) :
    (Icc 0 N).filter Nat.Prime = (Icc 2 N).filter Nat.Prime := by
  ext p
  simp only [mem_filter, mem_Icc]
  exact ⟨fun h => ⟨⟨h.2.two_le, h.1.2⟩, h.2⟩,
    fun h => ⟨⟨Nat.zero_le _, h.1.2⟩, h.2⟩⟩

lemma logPrimeReciprocal_abel {x : ℝ} (hx : 2 ≤ x) :
    (∑ p ∈ (Icc 2 ⌊x⌋₊).filter Nat.Prime, Real.log p / p) =
      Chebyshev.theta x / x +
        ∫ t in 2..x, Chebyshev.theta t / t^2 := by
  let a : ℕ → ℝ := fun n => if n.Prime then Real.log n else 0
  have hd (t : ℝ) (ht : t ∈ Set.Icc 2 x) :
      HasDerivAt (fun u : ℝ => u⁻¹) (-(t^2)⁻¹) t := by
    exact hasDerivAt_inv (by linarith [ht.1])
  have hi : IntegrableOn (deriv (fun u : ℝ => u⁻¹)) (Set.Icc 2 x) := by
    have hc : ContinuousOn (fun t : ℝ => -(t^2)⁻¹) (Set.Icc 2 x) := by
      apply ContinuousOn.neg
      apply ContinuousOn.inv₀ (continuousOn_id.pow 2)
      intro t ht
      exact pow_ne_zero _ (show t ≠ 0 by linarith [ht.1])
    exact hc.integrableOn_Icc.congr_fun (fun t ht => (hd t ht).deriv.symm) measurableSet_Icc
  have h := sum_mul_eq_sub_integral_mul₁ a (f := fun t : ℝ => t⁻¹)
    (by simp [a]) (by simp [a]) x (fun t ht => (hd t ht).differentiableAt) hi
  have hs : (∑ k ∈ Icc 0 ⌊x⌋₊, (↑k)⁻¹ * a k) =
      ∑ p ∈ (Icc 2 ⌊x⌋₊).filter Nat.Prime, Real.log p / p := by
    rw [← prime_set_zero_eq, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    simp only [a]
    split_ifs <;> simp [div_eq_mul_inv, mul_comm]
  rw [hs, ← intervalIntegral.integral_of_le hx] at h
  have ht (t : ℝ) : (∑ k ∈ Icc 0 ⌊t⌋₊, a k) = Chebyshev.theta t := by
    simp only [a, Chebyshev.theta_eq_sum_Icc, sum_filter]
  simp only [ht] at h
  have he : (∫ t in 2..x, deriv (fun u : ℝ => u⁻¹) t * Chebyshev.theta t) =
      -(∫ t in 2..x, Chebyshev.theta t / t^2) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    dsimp only
    rw [(hd t ht).deriv]
    simp [div_eq_mul_inv, mul_comm]
  rw [he] at h
  simpa [div_eq_mul_inv, mul_comm] using h

lemma logPrimeReciprocal_le {x : ℝ} (hx : 2 ≤ x) :
    (∑ p ∈ (Icc 2 ⌊x⌋₊).filter Nat.Prime, Real.log p / p) ≤
      Real.log 4 * (1 + Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hc : ContinuousOn (fun t : ℝ => (t^2)⁻¹) (Set.Icc 2 x) := by
    apply ContinuousOn.inv₀ (continuousOn_id.pow 2)
    intro t ht
    exact pow_ne_zero _ (show t ≠ 0 by linarith [ht.1])
  have hit : IntegrableOn (fun t => Chebyshev.theta t / t^2) (Set.Icc 2 x) := by
    have h := integrableOn_mul_sum_Icc
      (fun n : ℕ => if n.Prime then Real.log n else 0) (m := 0)
      (by norm_num : (0:ℝ) ≤ 2) hc.integrableOn_Icc
    simpa only [Chebyshev.theta_eq_sum_Icc, sum_filter, div_eq_mul_inv, mul_comm] using h
  have hi : IntervalIntegrable (fun t => Chebyshev.theta t / t^2) volume 2 x := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hx, ← integrableOn_Icc_iff_integrableOn_Ioc]
    exact hit
  have hi' : IntervalIntegrable (fun t : ℝ => Real.log 4 * t⁻¹) volume 2 x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hx]
    apply ContinuousOn.const_mul
    apply continuousOn_id.inv₀
    intro t ht
    change t ≠ 0
    linarith [ht.1]
  rw [logPrimeReciprocal_abel hx]
  have hm : (∫ t in 2..x, Chebyshev.theta t / t^2) ≤
      Real.log 4 * (Real.log x - Real.log 2) := by
    calc
      _ ≤ ∫ t in 2..x, Real.log 4 * t⁻¹ := by
        apply intervalIntegral.integral_mono_on hx hi hi'
        intro t ht
        have ht0 : 0 < t := by linarith [ht.1]
        calc
          _ ≤ (Real.log 4 * t) / t^2 :=
            div_le_div_of_nonneg_right (Chebyshev.theta_le_log4_mul_x ht0.le) (sq_nonneg _)
          _ = _ := by field_simp
      _ = _ := by
        rw [intervalIntegral.integral_const_mul, integral_inv_of_pos (by norm_num) hx0,
          Real.log_div hx0.ne' (by norm_num)]
  have ht : Chebyshev.theta x / x ≤ Real.log 4 := by
    exact (div_le_iff₀ hx0).mpr (Chebyshev.theta_le_log4_mul_x hx0.le)
  have h2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
  have h4 := Real.log_pos (by norm_num : (1:ℝ) < 4)
  nlinarith

def rpowHom (s : ℝ) : ℕ →* ℝ where
  toFun n := (n : ℝ)^(-s)
  map_one' := by simp
  map_mul' m n := by simp [Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]

lemma zeta_rpow_le {s : ℝ} (hs : 1 < s) :
    (∑' n : ℕ, (n : ℝ)^(-s)) ≤ 1 + (s-1)⁻¹ := by
  have hsum : Summable (fun n : ℕ => (n : ℝ)^(-s)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have ha : AntitoneOn (fun t : ℝ => t^(-s)) (Set.Ici 1) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one hx) hxy (by linarith)
  have h := AntitoneOn.tsum_comp_add_le_integral (f := fun t : ℝ => t^(-s)) 1
    (by simpa using ha)
    (by simpa using integrableOn_Ioi_rpow_of_lt (a := -s) (by linarith) (by norm_num : (0:ℝ) < 1))
    (fun t ht => Real.rpow_nonneg (le_trans (by norm_num : (0:ℝ) ≤ (1:ℕ)) ht.le) _)
  simp only [Nat.cast_one] at h
  rw [integral_Ioi_rpow_of_lt (a := -s) (by linarith) (by norm_num : (0:ℝ) < 1)] at h
  have he := hsum.sum_add_tsum_nat_add 2
  norm_num [show -s ≠ 0 by linarith, Finset.sum_range_succ] at he
  have hd : - (1:ℝ)^(-s+1) / (-s+1) = (s-1)⁻¹ := by
    rw [one_rpow, show -s+1 = -(s-1) by ring, div_neg, neg_div, neg_neg, one_div]
  rw [hd] at h
  have h' : (∑' i : ℕ, ((i:ℝ)+2)^(-s)) ≤ (s-1)⁻¹ := by
    simpa only [Nat.add_assoc, Nat.reduceAdd, Nat.cast_add, Nat.cast_ofNat] using h
  rw [← he]
  exact add_le_add (le_refl _) h'

lemma prime_rpow_sum_log_bound {s : ℝ} (hs : 1 < s) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    ∑ p ∈ P, (p : ℝ)^(-s) ≤ Real.log (1 + (s-1)⁻¹) := by
  have hp (p : ℕ) (hp : p.Prime) : ‖rpowHom s p‖ < 1 := by
    change ‖(p : ℝ)^(-s)‖ < 1
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
  have he := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := rpowHom s) (fun h => hp _ h) P).2
  have hfil : P.filter Nat.Prime = P := Finset.filter_true_of_mem hP
  simp only [hfil] at he
  have hsum : Summable (fun n : ℕ => (n : ℝ)^(-s)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hprod : (∏ p ∈ P, (1-(p : ℝ)^(-s))⁻¹) ≤ 1+(s-1)⁻¹ := by
    calc
      _ = ∑' n : Nat.factoredNumbers P, (n.val : ℝ)^(-s) := he.tsum_eq.symm
      _ ≤ ∑' n : ℕ, (n : ℝ)^(-s) :=
        Summable.tsum_subtype_le _ _ (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _) hsum
      _ ≤ _ := zeta_rpow_le hs
  have hp1 (p : ℕ) (h : p ∈ P) : 0 < 1 - (p : ℝ)^(-s) := by
    have hlt := Real.rpow_lt_one_of_one_lt_of_neg
      (show (1:ℝ) < p by exact_mod_cast (hP p h).one_lt) (show -s < 0 by linarith)
    linarith
  calc
    _ ≤ ∑ p ∈ P, Real.log ((1-(p : ℝ)^(-s))⁻¹) := by
      apply Finset.sum_le_sum
      intro p hpP
      rw [Real.log_inv]
      have := Real.log_le_sub_one_of_pos (hp1 p hpP)
      linarith
    _ = Real.log (∏ p ∈ P, (1-(p : ℝ)^(-s))⁻¹) :=
      (Real.log_prod fun p h => inv_ne_zero (hp1 p h).ne').symm
    _ ≤ _ := Real.log_le_log (Finset.prod_pos fun p h => inv_pos.mpr (hp1 p h)) hprod

lemma rpow_reciprocal_error {u : ℝ} (hu : 0 < u) (t : ℝ) :
    u⁻¹ - u^(-(1+t)) ≤ t * (Real.log u / u) := by
  have he : u^(-(1+t)) = u⁻¹ * Real.exp (-(t * Real.log u)) := by
    calc
      _ = u^(-1:ℝ) * u^(-t) := by rw [← Real.rpow_add hu]; congr 1; ring
      _ = _ := by
        rw [Real.rpow_neg_one, Real.rpow_def_of_pos hu]
        congr 2
        ring
  rw [he]
  have h := mul_le_mul_of_nonneg_left (Real.one_sub_le_exp_neg (t * Real.log u))
    (inv_nonneg.mpr hu.le)
  simp only [div_eq_mul_inv]
  nlinarith

lemma primeHarmonic_upper {x : ℝ} (hx : 2 ≤ x) :
    primeHarmonic x ≤ Real.log (Real.log x) +
      (Real.log (1+(Real.log 2)⁻¹) + Real.log 4 * (1+(Real.log 2)⁻¹)) := by
  have hx0 : 0 < x := by linarith
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  let P := (Icc 2 ⌊x⌋₊).filter Nat.Prime
  have hp (p : ℕ) (h : p ∈ P) : p.Prime := (mem_filter.mp h).2
  have he : primeHarmonic x ≤
      (∑ p ∈ P, (p : ℝ)^(-(1+(Real.log x)⁻¹))) +
        (Real.log x)⁻¹ * (∑ p ∈ P, Real.log p / p) := by
    change (∑ p ∈ P, (p : ℝ)⁻¹) ≤ _
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro p h
    have h := rpow_reciprocal_error
      (show 0 < (p:ℝ) by exact_mod_cast (hp p h).pos) ((Real.log x)⁻¹)
    linarith
  have hs : 1 < 1+(Real.log x)⁻¹ := by linarith [inv_pos.mpr hl]
  have hb := prime_rpow_sum_log_bound hs P hp
  have hparam : 1+(Real.log x)⁻¹-1 = (Real.log x)⁻¹ := by ring
  rw [hparam, inv_inv] at hb
  have hw := mul_le_mul_of_nonneg_left (logPrimeReciprocal_le hx) (inv_nonneg.mpr hl.le)
  have hbase : primeHarmonic x ≤ Real.log (1+Real.log x) +
      Real.log 4 * (1+(Real.log x)⁻¹) := by
    calc
      _ ≤ Real.log (1+Real.log x) + (Real.log x)⁻¹ *
          (Real.log 4 * (1+Real.log x)) := by
        exact he.trans (add_le_add hb hw)
      _ = _ := by field_simp; ring
  have hid : 1+Real.log x = Real.log x * (1+(Real.log x)⁻¹) := by
    field_simp
    ring
  rw [hid, Real.log_mul hl.ne' (by positivity : 1+(Real.log x)⁻¹ ≠ 0)] at hbase
  have hi : (Real.log x)⁻¹ ≤ (Real.log 2)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le h2 (Real.log_le_log (by norm_num) hx)
  have hc : Real.log (1+(Real.log x)⁻¹) ≤ Real.log (1+(Real.log 2)⁻¹) := by
    apply Real.log_le_log (by positivity)
    linarith
  have hm := mul_le_mul_of_nonneg_left (show 1+(Real.log x)⁻¹ ≤ 1+(Real.log 2)⁻¹ by linarith) h4
  linarith

lemma log_inv_one_sub_le {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1/2) :
    Real.log ((1-u)⁻¹) ≤ u + 2*u^2 := by
  have hpos : 0 < 1-u := by linarith
  have hi : (1-u)⁻¹ ≤ 1+u+2*u^2 := by
    rw [← one_div]
    apply (div_le_iff₀ hpos).mpr
    have h := mul_nonneg (pow_nonneg hu0 2) (show 0 ≤ 1-2*u by linarith)
    nlinarith
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  linarith

lemma prime_reciprocal_square_le (N : ℕ) :
    (∑ p ∈ (N+1).primesBelow, ((p:ℝ)⁻¹)^2) ≤ 1 := by
  calc
    _ = ∑ p ∈ (N+1).primesBelow, ((p:ℝ)^2)⁻¹ := by simp only [inv_pow]
    _ ≤ ∑ p ∈ Ioo 1 (N+1), ((p:ℝ)^2)⁻¹ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        have h := Nat.mem_primesBelow.mp hp
        exact mem_Ioo.mpr ⟨h.2.one_lt,h.1⟩
      · intro p hp hnot
        positivity
    _ ≤ 1 := by simpa only [Nat.cast_one, one_add_one_eq_two, div_self (by norm_num : (2:ℝ) ≠ 0)] using (sum_Ioo_inv_sq_le (α := ℝ) 1 (N+1))

lemma primeHarmonic_lower {x : ℝ} (hx : 2 ≤ x) :
    Real.log (Real.log x) ≤ primeHarmonic x + 2 := by
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  have hxN : x ≤ (⌊x⌋₊+1 : ℕ) := by
    simpa only [Nat.cast_add,Nat.cast_one] using (Nat.lt_floor_add_one x).le
  have hh : Real.log x ≤ (harmonic ⌊x⌋₊ : ℝ) := by
    exact (Real.log_le_log (by linarith) hxN).trans (by simpa using log_add_one_le_harmonic ⌊x⌋₊)
  have hhpos : 0 < (harmonic ⌊x⌋₊ : ℝ) := lt_of_lt_of_le hl hh
  calc
    _ ≤ Real.log (harmonic ⌊x⌋₊ : ℝ) := Real.log_le_log hl hh
    _ ≤ Real.log (∏ p ∈ (⌊x⌋₊+1).primesBelow, (1-(p:ℝ)⁻¹)⁻¹) :=
      Real.log_le_log hhpos (Support.harmonic_le_finite_euler _)
    _ = ∑ p ∈ (⌊x⌋₊+1).primesBelow, Real.log ((1-(p:ℝ)⁻¹)⁻¹) := by
      apply Real.log_prod
      intro p hp
      apply inv_ne_zero
      have hp1 : (1:ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).one_lt
      have hi := (inv_lt_one₀ (show (0:ℝ) < p by linarith)).mpr hp1
      linarith
    _ ≤ ∑ p ∈ (⌊x⌋₊+1).primesBelow, ((p:ℝ)⁻¹ + 2*((p:ℝ)⁻¹)^2) := by
      apply Finset.sum_le_sum
      intro p hp
      apply log_inv_one_sub_le (by positivity)
      simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 2)
        (show (2:ℝ) ≤ p by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).two_le)
    _ = primeHarmonic x + 2 * (∑ p ∈ (⌊x⌋₊+1).primesBelow, ((p:ℝ)⁻¹)^2) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [primeHarmonic,prime_set_eq]
    _ ≤ _ := by linarith [prime_reciprocal_square_le ⌊x⌋₊]

theorem primeHarmonic_loglog_bounded :
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
      |primeHarmonic x - Real.log (Real.log x)| ≤ C := by
  let K := Real.log (1+(Real.log 2)⁻¹) + Real.log 4 * (1+(Real.log 2)⁻¹)
  refine ⟨max 2 K, fun x hx => ?_⟩
  rw [abs_le]
  constructor
  · have := primeHarmonic_lower hx
    have := le_max_left (2:ℝ) K
    linarith
  · have := primeHarmonic_upper hx
    have := le_max_right (2:ℝ) K
    dsimp only [K] at *
    linarith

lemma primeHarmonic_exp_rpow_ratio {a : ℝ} (ha : 0 < a) :
    Tendsto (fun B : ℝ => primeHarmonic (Real.exp (B^a)) / Real.log B)
      atTop (nhds a) := by
  obtain ⟨C, hC⟩ := primeHarmonic_loglog_bounded
  have ht : Tendsto (fun B : ℝ => Real.exp (B^a)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_rpow_atTop ha)
  apply tendsto_sub_nhds_zero_iff.mp
  apply squeeze_zero_norm' (a := fun B : ℝ => C / Real.log B)
  · filter_upwards [eventually_ge_atTop (2:ℝ), ht.eventually_ge_atTop 2] with B hB hE
    have hB0 : 0 < B := by linarith
    have hl : 0 < Real.log B := Real.log_pos (by linarith)
    have h := hC (Real.exp (B^a)) hE
    rw [Real.log_exp, Real.log_rpow hB0] at h
    have he : primeHarmonic (Real.exp (B^a)) / Real.log B - a =
        (primeHarmonic (Real.exp (B^a)) - a * Real.log B) / Real.log B := by
      field_simp
    rw [he, Real.norm_eq_abs, abs_div, abs_of_pos hl]
    exact div_le_div_of_nonneg_right h hl.le
  · exact tendsto_const_nhds.div_atTop Real.tendsto_log_atTop

lemma primeHarmonic_exp_sub {u v : ℝ} (huv : u ≤ v) :
    (∑ p ∈ (Icc 2 ⌊Real.exp v⌋₊).filter
      (fun p : ℕ => p.Prime ∧ u < Real.log (p : ℝ)), (p:ℝ)⁻¹) =
      primeHarmonic (Real.exp v) - primeHarmonic (Real.exp u) := by
  let P (t : ℝ) := (Icc 2 ⌊Real.exp t⌋₊).filter Nat.Prime
  have hm (t : ℝ) (p : ℕ) (hp : 2 ≤ p) :
      p ∈ P t ↔ p.Prime ∧ Real.log (p:ℝ) ≤ t := by
    simp only [P, mem_filter, mem_Icc, hp, true_and,
      Nat.le_floor_iff (Real.exp_pos t).le]
    rw [← Real.log_le_iff_le_exp (show 0 < (p:ℝ) by exact_mod_cast (show 0 < p by omega))]
    exact and_comm
  have hsub : P u ⊆ P v := by
    intro p hp
    have hp2 := (mem_Icc.mp (mem_filter.mp hp).1).1
    have hm' := (hm u p hp2).mp hp
    exact (hm v p hp2).mpr ⟨hm'.1,hm'.2.trans huv⟩
  have he : (Icc 2 ⌊Real.exp v⌋₊).filter
      (fun p : ℕ => p.Prime ∧ u < Real.log (p:ℝ)) = P v \ P u := by
    ext p
    simp only [mem_filter, mem_Icc, Finset.mem_sdiff, P]
    constructor
    · rintro ⟨⟨hp2,hpv⟩,hp,hpu⟩
      refine ⟨⟨⟨hp2,hpv⟩,hp⟩,?_⟩
      intro h
      have ht := (hm u p hp2).mp (by simpa only [P, mem_filter, mem_Icc] using h)
      exact hpu.not_ge ht.2
    · rintro ⟨⟨⟨hp2,hpv⟩,hp⟩,hpu⟩
      refine ⟨⟨hp2,hpv⟩,hp,?_⟩
      by_contra h
      apply hpu
      simpa only [P, mem_filter, mem_Icc] using (hm u p hp2).mpr ⟨hp, le_of_not_gt h⟩
  rw [he]
  have h := Finset.sum_sdiff (f := fun p : ℕ => (p:ℝ)⁻¹) hsub
  change _ = (∑ p ∈ P v, (p:ℝ)⁻¹) - ∑ p ∈ P u, (p:ℝ)⁻¹
  linarith

lemma coreMass_eq {B : ℝ} (hB : 1 ≤ B) :
    coreMass B = primeHarmonic (Real.exp B) -
      primeHarmonic (Real.exp (B^(1-eta))) := by
  have h : B^(1-eta) ≤ B := by
    calc
      B^(1-eta) ≤ B^(1:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hB (by norm_num [eta,epsilon])
      _ = B := Real.rpow_one B
  exact primeHarmonic_exp_sub h

lemma centerMass_eq {B : ℝ} (hB : 1 ≤ B) :
    centerMass B = primeHarmonic (Real.exp (B^(1-eta))) -
      primeHarmonic (Real.exp (B^(1-epsilon))) := by
  have h : B^(1-epsilon) ≤ B^(1-eta) :=
    Real.rpow_le_rpow_of_exponent_le hB (by norm_num [eta,epsilon])
  exact primeHarmonic_exp_sub h

theorem source_prime_bands :
    Tendsto (fun B : ℝ => coreMass B / Real.log B) atTop (nhds eta) ∧
    Tendsto (fun B : ℝ => centerMass B / Real.log B)
      atTop (nhds (epsilon - eta)) := by
  have h1 : Tendsto (fun B : ℝ => primeHarmonic (Real.exp B) / Real.log B)
      atTop (nhds 1) := by
    simpa only [Real.rpow_one] using primeHarmonic_exp_rpow_ratio (by norm_num : (0:ℝ) < 1)
  have ha := primeHarmonic_exp_rpow_ratio (show 0 < 1-eta by norm_num [eta,epsilon])
  have hb := primeHarmonic_exp_rpow_ratio (show 0 < 1-epsilon by norm_num [epsilon])
  constructor
  · have h := h1.sub ha
    rw [show 1-(1-eta) = eta by ring] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (1:ℝ)] with B hB
    rw [coreMass_eq hB, sub_div]
  · have h := ha.sub hb
    rw [show (1-eta)-(1-epsilon) = epsilon-eta by ring] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (1:ℝ)] with B hB
    rw [centerMass_eq hB, sub_div]

end OrdinaryCorrelations.SourcePrimeBands

end

end OAI
