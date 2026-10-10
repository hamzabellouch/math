import Mathlib
import OAI.Analysis.LaughlinFock.SphereScaling

namespace OAI

/-! Finite Coupling. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators
open Filter Topology

 

def highestWeight (n m z p : ℕ) : ℕ :=
  z.choose p * (n-p).descFactorial (z-p) * (m-z+p).descFactorial p

def highestTotal (n m z : ℕ) : ℕ :=
  ∑ p ∈ Finset.range (z+1), highestWeight n m z p

 
def highestCoefficient (n m z p : ℕ) : ℝ :=
  (-1)^(z-p) * Real.sqrt ((highestWeight n m z p : ℝ) / highestTotal n m z)

theorem highestWeight_zero (n m z p : ℕ) (hp : z < p) :
    highestWeight n m z p = 0 := by
  simp [highestWeight, Nat.choose_eq_zero_of_lt hp]

theorem highestCoefficient_zero (n m z p : ℕ) (hp : z < p) :
    highestCoefficient n m z p = 0 := by
  simp [highestCoefficient, highestWeight_zero n m z p hp]

theorem highestTotal_pos {n m z : ℕ} (hz : z ≤ n) : 0 < highestTotal n m z := by
  unfold highestTotal
  apply Finset.sum_pos'
  · exact fun _ _ => Nat.zero_le _
  · refine ⟨0, by simp, ?_⟩
    simpa [highestWeight] using Nat.descFactorial_pos.mpr hz

theorem highestCoefficient_sq (n m z p : ℕ) :
    highestCoefficient n m z p ^ 2 = (highestWeight n m z p : ℝ) / highestTotal n m z := by
  rw [highestCoefficient, mul_pow, ← pow_mul, mul_comm (z-p) 2, pow_mul]
  norm_num only [neg_sq, one_pow, one_mul]
  exact Real.sq_sqrt (by positivity)

 

theorem highestCoefficient_norm {n m z : ℕ} (hz : z ≤ n) :
    ∑ p ∈ Finset.range (z+1), highestCoefficient n m z p ^ 2 = 1 := by
  simp_rw [highestCoefficient_sq]
  rw [← Finset.sum_div]
  have ht : (∑ p ∈ Finset.range (z+1), (highestWeight n m z p : ℝ)) =
      (highestTotal n m z : ℝ) := by simp [highestTotal]
  rw [ht, div_self (by exact_mod_cast (highestTotal_pos (m := m) hz).ne')]

 
theorem highestWeight_adjacent {n m z p : ℕ} (hz : z ≤ n) (hp : p < z) :
    highestWeight n m z (p+1) * ((p+1)*(n-p)) =
      highestWeight n m z p * ((z-p)*(m-z+p+1)) := by
  have hnp : n-p = (n-(p+1))+1 := by omega
  have hzp : z-p = (z-(p+1))+1 := by omega
  have hnfall : (n-p).descFactorial (z-p) =
      (n-p) * (n-(p+1)).descFactorial (z-(p+1)) := by
    rw [hnp, hzp, Nat.succ_descFactorial_succ]
  have hmfall : (m-z+(p+1)).descFactorial (p+1) =
      (m-z+p+1) * (m-z+p).descFactorial p := by
    rw [show m-z+(p+1) = (m-z+p)+1 by omega, Nat.succ_descFactorial_succ]
  unfold highestWeight
  rw [hnfall, hmfall]
  have hch := Nat.choose_succ_right_eq z p
  calc
    _ = (z.choose (p+1) * (p+1)) * (n-p) *
        (n-(p+1)).descFactorial (z-(p+1)) *
        ((m-z+p+1) * (m-z+p).descFactorial p) := by ring
    _ = _ := by rw [hch]; ring

 

theorem highestCoefficient_raising {n m z p : ℕ} (hz : z ≤ n) (hp : p < z) :
    highestCoefficient n m z (p+1) * Real.sqrt ((p+1 : ℕ) * (n-p : ℕ) : ℝ) +
      highestCoefficient n m z p * Real.sqrt ((z-p : ℕ) * (m-z+p+1 : ℕ) : ℝ) = 0 := by
  have he : (highestWeight n m z (p+1) : ℝ) / highestTotal n m z *
      ((p+1 : ℕ) * (n-p : ℕ) : ℝ) =
      (highestWeight n m z p : ℝ) / highestTotal n m z *
      ((z-p : ℕ) * (m-z+p+1 : ℕ) : ℝ) := by
    have h := congrArg (fun a : ℕ => (a : ℝ)) (highestWeight_adjacent (m := m) hz hp)
    push_cast at h
    simpa only [div_mul_eq_mul_div, Nat.cast_add, Nat.cast_one] using congrArg (fun a : ℝ => a / highestTotal n m z) h
  have hs :
      Real.sqrt ((highestWeight n m z (p+1) : ℝ) / highestTotal n m z) *
        Real.sqrt ((p+1 : ℕ) * (n-p : ℕ) : ℝ) =
      Real.sqrt ((highestWeight n m z p : ℝ) / highestTotal n m z) *
        Real.sqrt ((z-p : ℕ) * (m-z+p+1 : ℕ) : ℝ) := by
    calc
      _ = Real.sqrt ((highestWeight n m z (p+1) : ℝ) / highestTotal n m z *
          ((p+1 : ℕ) * (n-p : ℕ) : ℝ)) := (Real.sqrt_mul (by positivity) _).symm
      _ = _ := congrArg Real.sqrt he
      _ = _ := Real.sqrt_mul (by positivity) _
  have hpar : (-1 : ℝ)^(z-p) = -((-1 : ℝ)^(z-(p+1))) := by
    rw [show z-p = z-(p+1)+1 by omega, pow_succ]
    ring
  unfold highestCoefficient
  rw [hpar]
  calc
    _ = (-1 : ℝ)^(z-(p+1)) *
        (Real.sqrt ((highestWeight n m z (p+1) : ℝ) / highestTotal n m z) *
            Real.sqrt ((p+1 : ℕ) * (n-p : ℕ) : ℝ) -
         Real.sqrt ((highestWeight n m z p : ℝ) / highestTotal n m z) *
            Real.sqrt ((z-p : ℕ) * (m-z+p+1 : ℕ) : ℝ)) := by ring
    _ = 0 := by rw [hs, sub_self, mul_zero]

 
theorem spin_complement_ratio_tendsto (n m : ℕ → ℕ) (r : ℝ)
    (hn : Tendsto n atTop atTop)
    (h : Tendsto (fun Q => (m Q : ℝ) / (n Q + m Q)) atTop (𝓝 r)) :
    Tendsto (fun Q => (n Q : ℝ) / (n Q + m Q)) atTop (𝓝 (1-r)) := by
  apply ((tendsto_const_nhds (x := (1 : ℝ))).sub h).congr'
  filter_upwards [hn.eventually (eventually_ge_atTop 1)] with Q hQ
  have hnQ : (n Q : ℝ) > 0 := by exact_mod_cast hQ
  field_simp
  ring

 

theorem highestWeight_factorization {n m z p : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hmz : z ≤ m) (hp : p ≤ z) :
    (highestWeight n m z p : ℝ) / ((n : ℝ)+m)^z =
      (z.choose p : ℝ) * scaledDescFactorial n p (z-p) *
        scaledDescFactorial m (z-p) p *
        ((n : ℝ)/(n+m))^(z-p) * ((m : ℝ)/(n+m))^p := by
  have hs : m-z+p = m-(z-p) := by omega
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hN : (n : ℝ)+m ≠ 0 := ne_of_gt (by positivity)
  have hpw : ((n : ℝ)+m)^z = ((n : ℝ)+m)^(z-p) * ((n : ℝ)+m)^p := by
    rw [← pow_add, Nat.sub_add_cancel hp]
  simp only [highestWeight, Nat.cast_mul, hs, scaledDescFactorial, div_pow]
  rw [hpw]
  field_simp

 

theorem highestWeight_scaled_tendsto (n m : ℕ → ℕ) (r : ℝ)
    (hn : Tendsto n atTop atTop) (hm : Tendsto m atTop atTop)
    (hr : Tendsto (fun Q => (m Q : ℝ) / (n Q + m Q)) atTop (𝓝 r))
    (z p : ℕ) (hp : p ≤ z) :
    Tendsto (fun Q => (highestWeight (n Q) (m Q) z p : ℝ) /
      ((n Q : ℝ)+m Q)^z) atTop (𝓝 ((z.choose p : ℝ) * (1-r)^(z-p) * r^p)) := by
  have hc := spin_complement_ratio_tendsto n m r hn hr
  have h := (((((tendsto_const_nhds (x := (z.choose p : ℝ))).mul
    ((scaledDescFactorial_tendsto p (z-p)).comp hn)).mul
    ((scaledDescFactorial_tendsto (z-p) p).comp hm)).mul (hc.pow (z-p))).mul (hr.pow p))
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards [hn.eventually (eventually_ge_atTop 1),
    hm.eventually (eventually_ge_atTop (z+1))] with Q hnQ hmQ
  exact (highestWeight_factorization (by omega) (by omega) (by omega) hp).symm

 

theorem highestTotal_scaled_tendsto (n m : ℕ → ℕ) (r : ℝ)
    (hn : Tendsto n atTop atTop) (hm : Tendsto m atTop atTop)
    (hr : Tendsto (fun Q => (m Q : ℝ) / (n Q + m Q)) atTop (𝓝 r)) (z : ℕ) :
    Tendsto (fun Q => (highestTotal (n Q) (m Q) z : ℝ) /
      ((n Q : ℝ)+m Q)^z) atTop (𝓝 1) := by
  have h := tendsto_finsetSum (Finset.range (z+1))
    (fun p hp => highestWeight_scaled_tendsto n m r hn hm hr z p (by
      have := Finset.mem_range.mp hp; omega))
  have hsum : ∑ p ∈ Finset.range (z+1),
      (z.choose p : ℝ) * (1-r)^(z-p) * r^p = 1 := by
    calc
      _ = (r + (1-r))^z := by
        rw [add_pow]
        apply Finset.sum_congr rfl
        intro p _
        ring
      _ = 1 := by simp
  simpa only [hsum, ← Finset.sum_div, highestTotal, Nat.cast_sum] using h

 

theorem highestCoefficient_tendsto (n m : ℕ → ℕ) (r : ℝ)
    (hn : Tendsto n atTop atTop) (hm : Tendsto m atTop atTop)
    (hr : Tendsto (fun Q => (m Q : ℝ) / (n Q + m Q)) atTop (𝓝 r))
    (z p : ℕ) (hp : p ≤ z) :
    Tendsto (fun Q => highestCoefficient (n Q) (m Q) z p) atTop
      (𝓝 ((-1 : ℝ)^(z-p) * Real.sqrt ((z.choose p : ℝ) * (1-r)^(z-p) * r^p))) := by
  have hratio := (highestWeight_scaled_tendsto n m r hn hm hr z p hp).div
    (highestTotal_scaled_tendsto n m r hn hm hr z) (by norm_num)
  simp only [div_one] at hratio
  have hrat : Tendsto (fun Q => (highestWeight (n Q) (m Q) z p : ℝ) /
      highestTotal (n Q) (m Q) z) atTop
      (𝓝 ((z.choose p : ℝ) * (1-r)^(z-p) * r^p)) := by
    apply hratio.congr'
    filter_upwards [hn.eventually (eventually_ge_atTop 1)] with Q hnQ
    have hn' : (n Q : ℝ) > 0 := by exact_mod_cast hnQ
    have hN : ((n Q : ℝ)+m Q)^z ≠ 0 := pow_ne_zero _ (ne_of_gt (by positivity))
    exact div_div_div_cancel_right₀ hN _ _
  exact (Real.continuous_sqrt.tendsto _ |>.comp hrat).const_mul ((-1 : ℝ)^(z-p))

 
theorem highestCoefficient_tendsto_all (n m : ℕ → ℕ) (r : ℝ)
    (hn : Tendsto n atTop atTop) (hm : Tendsto m atTop atTop)
    (hr : Tendsto (fun Q => (m Q : ℝ) / (n Q + m Q)) atTop (𝓝 r))
    (z p : ℕ) :
    Tendsto (fun Q => highestCoefficient (n Q) (m Q) z p) atTop
      (𝓝 ((-1 : ℝ)^(z-p) * Real.sqrt ((z.choose p : ℝ) * (1-r)^(z-p) * r^p))) := by
  by_cases hp : p ≤ z
  · exact highestCoefficient_tendsto n m r hn hm hr z p hp
  · simpa only [highestCoefficient_zero _ _ _ _ (by omega : z < p),
      Nat.choose_eq_zero_of_lt (by omega : z < p), Nat.cast_zero, zero_mul,
      Real.sqrt_zero, mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

 

theorem root_affine_ratio_tendsto (N a : ℕ → ℕ) (r b c : ℝ)
    (hN : Tendsto N atTop atTop)
    (ha : Tendsto (fun Q => (a Q : ℝ) / N Q) atTop (𝓝 r)) :
    Tendsto (fun Q => Real.sqrt (b*((a Q : ℝ)+c)) / Real.sqrt (N Q))
      atTop (𝓝 (Real.sqrt (b*r))) := by
  have hlim := (ha.add ((tendsto_const_div_atTop_nhds_zero_nat c).comp hN)).const_mul b
  simp only [add_zero] at hlim
  have hscaled := Real.continuous_sqrt.tendsto _ |>.comp hlim
  convert hscaled using 1
  funext Q
  rw [← Real.sqrt_div' _ (Nat.cast_nonneg (N Q)), mul_div_assoc, add_div]
  rfl

 

def coupledCoefficient (n m z : ℕ) : ℕ → ℕ → ℝ
  | 0, p => highestCoefficient n m z p
  | k+1, p =>
      ((if p = 0 then 0 else
         Real.sqrt ((p : ℝ)*((n : ℝ)+1-p)) * coupledCoefficient n m z k (p-1)) +
       Real.sqrt (((z+k+1 : ℕ) : ℝ)-p) *
         Real.sqrt ((m : ℝ)+p-z-k) * coupledCoefficient n m z k p) /
        Real.sqrt (((k+1 : ℕ) : ℝ)*((n : ℝ)+m-2*z-k))

 

theorem coupledCoefficient_zero (n m z k p : ℕ) (hp : z+k < p) :
    coupledCoefficient n m z k p = 0 := by
  induction k generalizing p with
  | zero => exact highestCoefficient_zero n m z p (by simpa using hp)
  | succ k ih =>
    rw [coupledCoefficient, ih p (by omega)]
    by_cases hp0 : p = 0
    · simp [hp0]
    · rw [ite_eq_right hp0, ih (p-1) (by omega)]
      simp

 
def oscillatorCoefficient (r : ℝ) (z : ℕ) : ℕ → ℕ → ℝ
  | 0, p => (-1 : ℝ)^(z-p) * Real.sqrt ((z.choose p : ℝ) * (1-r)^(z-p) * r^p)
  | k+1, p =>
      ((if p = 0 then 0 else Real.sqrt ((p : ℝ)*(1-r)) * oscillatorCoefficient r z k (p-1)) +
        Real.sqrt (((z+k+1 : ℕ) : ℝ)-p) * Real.sqrt r * oscillatorCoefficient r z k p) /
        Real.sqrt (k+1 : ℕ)

 
theorem oscillatorCoefficient_zero (r : ℝ) (z k p : ℕ) (hp : z+k < p) :
    oscillatorCoefficient r z k p = 0 := by
  induction k generalizing p with
  | zero =>
    simp [oscillatorCoefficient, Nat.choose_eq_zero_of_lt (by omega : z < p)]
  | succ k ih =>
    rw [oscillatorCoefficient, ih p (by omega)]
    by_cases hp0 : p = 0
    · simp [hp0]
    · rw [ite_eq_right hp0, ih (p-1) (by omega)]
      simp

 

theorem coupledCoefficient_tendsto (n m : ℕ → ℕ) (r : ℝ)
    (hn : Tendsto n atTop atTop) (hm : Tendsto m atTop atTop)
    (hr : Tendsto (fun Q => (m Q : ℝ) / (n Q + m Q)) atTop (𝓝 r))
    (z k p : ℕ) :
    Tendsto (fun Q => coupledCoefficient (n Q) (m Q) z k p)
      atTop (𝓝 (oscillatorCoefficient r z k p)) := by
  let N : ℕ → ℕ := fun Q => n Q + m Q
  have hN : Tendsto N atTop atTop := hn.atTop_add_atTop hm
  have hNratio : Tendsto (fun Q => (N Q : ℝ) / N Q) atTop (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hN.eventually (eventually_ge_atTop 1)] with Q hQ
    exact (div_self (by exact_mod_cast (by omega : N Q ≠ 0))).symm
  have hr' : Tendsto (fun Q => (m Q : ℝ) / N Q) atTop (𝓝 r) := by simpa [N] using hr
  have hc' : Tendsto (fun Q => (n Q : ℝ) / N Q) atTop (𝓝 (1-r)) := by
    simpa [N] using spin_complement_ratio_tendsto n m r hn hr
  induction k generalizing p with
  | zero => exact highestCoefficient_tendsto_all n m r hn hm hr z p
  | succ k ih =>
    have hfirst : Tendsto (fun Q =>
        (if p = 0 then 0 else
          (Real.sqrt ((p : ℝ)*((n Q : ℝ)+1-p)) / Real.sqrt (N Q)) *
            coupledCoefficient (n Q) (m Q) z k (p-1))) atTop
        (𝓝 (if p = 0 then 0 else
          Real.sqrt ((p : ℝ)*(1-r)) * oscillatorCoefficient r z k (p-1))) := by
      by_cases hp : p = 0
      · simp only [hp, ite_true]
        exact tendsto_const_nhds
      · simp only [hp, ite_false]
        have h := (root_affine_ratio_tendsto N n (1-r) p (1-p) hN hc').mul (ih (p-1))
        simpa only [add_sub_assoc] using h
    have hsecond : Tendsto (fun Q =>
        (Real.sqrt (((z+k+1 : ℕ) : ℝ)-p) *
          (Real.sqrt ((m Q : ℝ)+p-z-k) / Real.sqrt (N Q))) *
          coupledCoefficient (n Q) (m Q) z k p) atTop
        (𝓝 (Real.sqrt (((z+k+1 : ℕ) : ℝ)-p) * Real.sqrt r *
          oscillatorCoefficient r z k p)) := by
      have h := root_affine_ratio_tendsto N m r 1 ((p : ℝ)-z-k) hN hr'
      simp only [one_mul] at h
      have h' := (h.const_mul (Real.sqrt (((z+k+1 : ℕ) : ℝ)-p))).mul (ih p)
      simpa only [← add_sub_assoc] using h'
    have hden : Tendsto (fun Q =>
        Real.sqrt (((k+1 : ℕ) : ℝ)*((n Q : ℝ)+m Q-2*z-k)) / Real.sqrt (N Q))
        atTop (𝓝 (Real.sqrt (k+1 : ℕ))) := by
      have h := root_affine_ratio_tendsto N N 1 (k+1 : ℕ) (-2*z-k) hN hNratio
      simp only [mul_one] at h
      convert h using 1
      funext Q
      congr 2
      simp only [N, Nat.cast_add]
      ring
    have hden0 : Real.sqrt (k+1 : ℕ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
    have h := (hfirst.add hsecond).div hden hden0
    apply h.congr'
    filter_upwards [hN.eventually (eventually_ge_atTop 1)] with Q hQ
    have hN0 : Real.sqrt (N Q) ≠ 0 := Real.sqrt_ne_zero'.mpr (by exact_mod_cast (by omega : 0 < N Q))
    simp only [Pi.div_apply, coupledCoefficient]
    by_cases hp : p = 0
    · simp only [hp, ite_true, zero_add]
      field_simp [hN0]
    · simp only [hp, ite_false]
      field_simp [hN0]

 

theorem highestWeight_mul_descFactorial (n m z p : ℕ) (hp : p ≤ z) :
    highestWeight n m z p * n.descFactorial p =
      highestWeight n m z 0 * (z.choose p * (m-z+p).descFactorial p) := by
  simp only [highestWeight, Nat.sub_zero, Nat.choose_zero_right, one_mul,
    Nat.add_zero, Nat.descFactorial_zero, mul_one]
  calc
    _ = (z.choose p * (m-z+p).descFactorial p) *
        ((n-p).descFactorial (z-p) * n.descFactorial p) := by ring
    _ = _ := by rw [Nat.descFactorial_mul_descFactorial hp]; ring

 

theorem highestCoefficient_ratio {n m z p : ℕ} (hz : z ≤ n) (hp : p ≤ z) :
    highestCoefficient n m z p = (-1 : ℝ)^p *
      Real.sqrt ((z.choose p : ℝ) * (m-z+p).descFactorial p /
        n.descFactorial p) * highestCoefficient n m z 0 := by
  have hnp : (n.descFactorial p : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr (hp.trans hz)).ne'
  have he : (highestWeight n m z p : ℝ) / highestTotal n m z =
      ((z.choose p : ℝ) * (m-z+p).descFactorial p / n.descFactorial p) *
        ((highestWeight n m z 0 : ℝ) / highestTotal n m z) := by
    have h := congrArg (fun a : ℕ => (a : ℝ))
      (highestWeight_mul_descFactorial n m z p hp)
    push_cast at h
    have heq : (highestWeight n m z p : ℝ) =
        (z.choose p : ℝ) * (m-z+p).descFactorial p * highestWeight n m z 0 /
          n.descFactorial p := (eq_div_iff hnp).mpr (by nlinarith only [h])
    rw [heq]
    ring
  have hsign : (-1 : ℝ)^p * (-1 : ℝ)^z = (-1 : ℝ)^(z-p) := by
    calc
      _ = (-1 : ℝ)^p * ((-1 : ℝ)^(z-p) * (-1 : ℝ)^p) := by
        rw [← pow_add (-1 : ℝ) (z-p) p, Nat.sub_add_cancel hp]
      _ = ((-1 : ℝ)^p * (-1 : ℝ)^p) * (-1 : ℝ)^(z-p) := by ring
      _ = _ := by rw [← mul_pow]; norm_num
  simp only [highestCoefficient, Nat.sub_zero]
  rw [he, Real.sqrt_mul (by positivity)]
  calc
    _ = ((-1 : ℝ)^p * (-1 : ℝ)^z) *
        (Real.sqrt ((z.choose p : ℝ) * (m-z+p).descFactorial p /
          n.descFactorial p) *
        Real.sqrt ((highestWeight n m z 0 : ℝ) / highestTotal n m z)) := by rw [hsign]
    _ = _ := by ring

 
theorem highestCoefficient_last {n m z : ℕ} (hn : z ≤ n) (hm : z ≤ m) :
    highestCoefficient n m z z = (-1 : ℝ)^z *
      Real.sqrt ((m.descFactorial z : ℝ) / n.descFactorial z) *
        highestCoefficient n m z 0 := by
  simpa only [Nat.sub_add_cancel hm, Nat.choose_self, Nat.cast_one, one_mul] using
    highestCoefficient_ratio (m := m) hn (le_refl z)

 
theorem highestCoefficient_penultimate {n m z : ℕ} (hn : z ≤ n)
    (hm : z ≤ m) (hz : 1 ≤ z) :
    highestCoefficient n m z (z-1) = (-1 : ℝ)^(z-1) *
      Real.sqrt ((z : ℝ) * (m-1).descFactorial (z-1) /
        n.descFactorial (z-1)) * highestCoefficient n m z 0 := by
  have hs : m-z+(z-1) = m-1 := by omega
  simpa only [hs, Nat.choose_symm hz, Nat.choose_one_right] using
    highestCoefficient_ratio (m := m) hn (Nat.sub_le z 1)

end LaughlinFock
end

end OAI
