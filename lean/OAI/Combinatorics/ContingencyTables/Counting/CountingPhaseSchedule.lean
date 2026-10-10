import OAI.Combinatorics.ContingencyTables.Rooted.RootedHistoryStep

namespace OAI

/-! # Explicit scalar schedules for the adaptive counting phases

Every precision and sample length below is a rational or natural arithmetic
expression. In particular the dyadic exponents use a polynomial reciprocal
allowance, so no real logarithm is evaluated by the algorithm.
-/

namespace ContingencyTables.CountingPhaseSchedule

open scoped BigOperators

/-- Per-phase logarithmic tolerance. -/
def tolerance (H : ℕ) (epsilon : ℚ) : ℚ := epsilon/(800*(H+1))

/-- The integer form of the manuscript's observable coefficient. -/
def observable (p W : ℕ) : ℕ :=
  10*p^4*(9*(p*(1+8*p*W^4))+2*(8+32*p*W^6))

def observationCoefficient (p W : ℕ) : ℕ := 32000*p^8*observable p W

def observations (p W H : ℕ) (eta : ℚ) : ℕ :=
  ⌈(1024:ℚ)*(H+1)*observationCoefficient p W/eta^2⌉₊+1

def returnCap (p H tau : ℕ) : ℕ := 65536*(H+1)^2*(tau+1)*(p^2+1)

def noiseCoefficient (H tau N n : ℕ) : ℕ := 8*(N+1)+8*H*tau*(n+1)

def precision (H tau N n : ℕ) (eta : ℚ) : ℕ :=
  1024*(H+1)*noiseCoefficient H tau N n+⌈1/eta⌉₊+1

def noise (H tau N n : ℕ) (eta : ℚ) : ℚ :=
  1/(precision H tau N n eta:ℚ)

def initialPrecision (H : ℕ) : ℕ := 2048*(H+1)

lemma tolerance_pos (H : ℕ) (epsilon : ℚ) (he : 0 < epsilon) :
    0 < tolerance H epsilon := by
  unfold tolerance
  positivity

lemma tolerance_le_quarter (H : ℕ) (epsilon : ℚ) (he0 : 0 < epsilon)
    (he1 : epsilon < 1) : tolerance H epsilon ≤ 1/4 := by
  unfold tolerance
  apply (div_le_iff₀ (by positivity : (0:ℚ) < 800*(H+1))).mpr
  have hH : (1:ℚ) ≤ H+1 := by have h0 := Nat.cast_nonneg (α := ℚ) H; linarith
  nlinarith

lemma observations_pos (p W H : ℕ) (eta : ℚ) : 0 < observations p W H eta := by
  unfold observations
  omega

lemma returnCap_pos (p H tau : ℕ) : 0 < returnCap p H tau := by
  unfold returnCap
  positivity

lemma precision_pos (H tau N n : ℕ) (eta : ℚ) : 0 < precision H tau N n eta := by
  unfold precision
  omega

lemma noise_pos (H tau N n : ℕ) (eta : ℚ) : 0 < noise H tau N n eta := by
  unfold noise
  exact one_div_pos.mpr (by exact_mod_cast precision_pos H tau N n eta)

lemma noise_le_tolerance (H tau N n : ℕ) (eta : ℚ) (he : 0 < eta) :
    noise H tau N n eta ≤ eta := by
  have hceil := Nat.le_ceil (1/eta)
  have hbound : (1/eta:ℚ) ≤ precision H tau N n eta := by
    apply hceil.trans
    exact_mod_cast (show ⌈1/eta⌉₊ ≤ precision H tau N n eta by unfold precision; omega)
  have hp : (0:ℚ) < precision H tau N n eta := by
    exact_mod_cast precision_pos H tau N n eta
  unfold noise
  apply (div_le_iff₀ hp).mpr
  have hb := (div_le_iff₀ he).mp hbound
  nlinarith

lemma reciprocal_two_pow (k : ℕ) (hk : 0 < k) :
    1/(2:ℝ)^k ≤ 1/(k:ℝ) := by
  have hnat : k ≤ 2^k := Nat.lt_two_pow_self.le
  exact one_div_le_one_div_of_le (by exact_mod_cast hk) (by exact_mod_cast hnat)

lemma precision_error (H tau N n : ℕ) (eta : ℚ) :
    1/(2:ℝ)^(precision H tau N n eta) ≤ (noise H tau N n eta:ℝ) := by
  simpa only [noise,Rat.cast_div,Rat.cast_one,Rat.cast_natCast] using
    reciprocal_two_pow (precision H tau N n eta) (precision_pos H tau N n eta)

lemma initial_error (H : ℕ) :
    2/(2:ℝ)^(initialPrecision H) ≤ 1/(1024*((H:ℝ)+1)) := by
  have hk : 0 < initialPrecision H := by unfold initialPrecision; positivity
  have hp := mul_le_mul_of_nonneg_left (reciprocal_two_pow (initialPrecision H) hk)
    (show (0:ℝ) ≤ 2 by norm_num)
  have he : 2*(1/(initialPrecision H:ℝ))=1/(1024*((H:ℝ)+1)) := by
    simp only [initialPrecision,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one]
    field_simp
    ring
  calc
    2/(2:ℝ)^(initialPrecision H)=2*(1/(2:ℝ)^(initialPrecision H)) := by ring
    _ ≤ 2*(1/(initialPrecision H:ℝ)) := hp
    _ = _ := he

lemma observations_error (p W H : ℕ) (eta : ℚ) (he : 0 < eta) :
    (observationCoefficient p W:ℝ)/
      (((observations p W H eta+1:ℕ):ℝ)*(eta:ℝ)^2) ≤
        1/(1024*((H:ℝ)+1)) := by
  have heta : (0:ℝ) < eta := by exact_mod_cast he
  have hceil := Nat.le_ceil ((1024:ℚ)*(H+1)*observationCoefficient p W/eta^2)
  have hraw : (1024:ℝ)*((H:ℝ)+1)*observationCoefficient p W/(eta:ℝ)^2 ≤
      observations p W H eta+1 := by
    have hn : ⌈(1024:ℚ)*(H+1)*observationCoefficient p W/eta^2⌉₊ ≤
        observations p W H eta+1 := by unfold observations; omega
    have hh := hceil.trans (show
        (⌈(1024:ℚ)*(H+1)*observationCoefficient p W/eta^2⌉₊:ℚ) ≤
          observations p W H eta+1 by exact_mod_cast hn)
    exact_mod_cast hh
  have hmul := (div_le_iff₀ (sq_pos_of_pos heta)).mp hraw
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  push_cast
  nlinarith

lemma cap_error (p H tau : ℕ) :
    40*(H:ℝ)*tau*p^2/(returnCap p H tau:ℝ) ≤ 1/(1024*((H:ℝ)+1)) := by
  have hnat : 40960*H*tau*p^2*(H+1) ≤ returnCap p H tau := by
    unfold returnCap
    calc
      _ = 40960*(H*(H+1))*tau*p^2 := by ring
      _ ≤ 65536*((H+1)^2)*(tau+1)*(p^2+1) := by
        have hHH : H*(H+1) ≤ (H+1)^2 := by nlinarith
        exact Nat.mul_le_mul
          (Nat.mul_le_mul (Nat.mul_le_mul (by decide : 40960 ≤ 65536) hHH)
            (Nat.le_succ tau)) (Nat.le_succ (p^2))
  have hr : (0:ℝ) < returnCap p H tau := by exact_mod_cast returnCap_pos p H tau
  rw [div_le_div_iff₀ hr (by positivity)]
  have hb : ((40960*H*tau*p^2*(H+1):ℕ):ℝ) ≤ returnCap p H tau := by exact_mod_cast hnat
  push_cast at hb
  nlinarith

lemma noise_error (H tau N n : ℕ) (eta : ℚ) :
    (noiseCoefficient H tau N n:ℝ)*(noise H tau N n eta:ℝ) ≤
      1/(1024*((H:ℝ)+1)) := by
  have hnat : 1024*(H+1)*noiseCoefficient H tau N n ≤ precision H tau N n eta := by
    unfold precision
    omega
  have hp : (0:ℝ) < precision H tau N n eta := by
    exact_mod_cast precision_pos H tau N n eta
  simp only [noise,Rat.cast_div,Rat.cast_one,Rat.cast_natCast,mul_one_div]
  rw [div_le_div_iff₀ hp (by positivity)]
  have hb : ((1024*(H+1)*noiseCoefficient H tau N n:ℕ):ℝ) ≤
      precision H tau N n eta := by exact_mod_cast hnat
  push_cast at hb
  nlinarith

lemma logarithmic_error (H tau N n : ℕ) (epsilon : ℚ) (he : 0 < epsilon) :
    (H:ℝ)*(4*(noise H tau N n (tolerance H epsilon):ℝ)+
      4*(tolerance H epsilon:ℝ)) ≤ (epsilon:ℝ)/50 := by
  have hxi := noise_le_tolerance H tau N n (tolerance H epsilon) (tolerance_pos H epsilon he)
  have hxiR : (noise H tau N n (tolerance H epsilon):ℝ) ≤ tolerance H epsilon := by
    exact_mod_cast hxi
  have heR : (0:ℝ) < epsilon := by exact_mod_cast he
  have heq : (tolerance H epsilon:ℝ)=(epsilon:ℝ)/(800*((H:ℝ)+1)) := by
    simp only [tolerance,Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_add,
      Rat.cast_natCast,Rat.cast_one]
  have hm : (H:ℝ)+1 > 0 := by positivity
  have ht : (tolerance H epsilon:ℝ)*(800*((H:ℝ)+1))=(epsilon:ℝ) := by
    rw [heq]
    exact div_mul_cancel₀ _ (by positivity)
  have htol : (0:ℝ) < tolerance H epsilon := by exact_mod_cast tolerance_pos H epsilon he
  nlinarith

/-- The four error terms correspond to empirical observations,
initialization, restart caps and the accumulated query/transition error. -/
lemma combine_error (p H tau N n k h : ℕ) (c eta xi allowance : ℝ)
    (hxi : 0 ≤ xi) (hprec : 1/(2:ℝ)^k ≤ xi)
    (hobs : c/(((N+1:ℕ):ℝ)*eta^2) ≤ allowance)
    (hinit : 2/(2:ℝ)^h ≤ allowance)
    (hcap : 40*(H:ℝ)*tau*p^2/(n:ℝ) ≤ allowance)
    (hnoise : (noiseCoefficient H tau N n:ℝ)*xi ≤ allowance) :
    c/(((N+1:ℕ):ℝ)*eta^2)+
      (N:ℝ)*((6*xi+1/(2:ℝ)^k)/2)+
      2*(1/(2:ℝ)^h+(H:ℝ)*((tau:ℝ)*
        (20*(p:ℝ)^2/n+((n+1:ℕ):ℝ)*((6*xi+1/(2:ℝ)^k)/2))))+
      2*((N+1:ℕ):ℝ)*xi ≤ 4*allowance := by
  let e := (6*xi+1/(2:ℝ)^k)/2
  have he : e ≤ 4*xi := by dsimp only [e]; linarith
  have hrow : (N:ℝ)*e+2*(H:ℝ)*tau*((n+1:ℕ):ℝ)*e+
      2*((N+1:ℕ):ℝ)*xi ≤ (noiseCoefficient H tau N n:ℝ)*xi := by
    calc
      _ = ((N:ℝ)+2*(H:ℝ)*tau*((n+1:ℕ):ℝ))*e+
          2*((N+1:ℕ):ℝ)*xi := by ring
      _ ≤ ((N:ℝ)+2*(H:ℝ)*tau*((n+1:ℕ):ℝ))*(4*xi)+
          2*((N+1:ℕ):ℝ)*xi := by
        exact _root_.add_le_add (mul_le_mul_of_nonneg_left he (by positivity)) (le_refl _)
      _ ≤ (noiseCoefficient H tau N n:ℝ)*xi := by
        simp only [noiseCoefficient,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
        nlinarith [mul_nonneg (Nat.cast_nonneg N : (0:ℝ) ≤ N) hxi]
  have heq : c/(((N+1:ℕ):ℝ)*eta^2)+
      (N:ℝ)*((6*xi+1/(2:ℝ)^k)/2)+
      2*(1/(2:ℝ)^h+(H:ℝ)*((tau:ℝ)*
        (20*(p:ℝ)^2/n+((n+1:ℕ):ℝ)*((6*xi+1/(2:ℝ)^k)/2))))+
      2*((N+1:ℕ):ℝ)*xi =
        c/(((N+1:ℕ):ℝ)*eta^2)+2/(2:ℝ)^h+
          40*(H:ℝ)*tau*p^2/n+
          ((N:ℝ)*e+2*(H:ℝ)*tau*((n+1:ℕ):ℝ)*e+2*((N+1:ℕ):ℝ)*xi) := by
    dsimp only [e]
    ring
  rw [heq]
  linarith

end ContingencyTables.CountingPhaseSchedule

end OAI
