import Mathlib

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid

section
open Matrix
open scoped Matrix
variable {V : Type*}

def gridFloor (D : ℕ) (q : ℚ) : ℚ := (⌊(D:ℚ)*q⌋:ℚ)/(D:ℚ)

def realMatrix (A : Matrix V V ℚ) : Matrix V V ℝ := fun i j => (A i j:ℝ)

def gridMatrix (D : ℕ) (A : Matrix V V ℚ) : Matrix V V ℚ := fun i j => gridFloor D (A i j)

lemma gridFloor_bounds (D : ℕ) (hD : 0<D) (q : ℚ) :
    q-1/(D:ℚ)≤gridFloor D q ∧ gridFloor D q≤q := by
  have hDp : 0<(D:ℚ) := by exact_mod_cast hD
  have hlo := Int.floor_le ((D:ℚ)*q)
  have hhi := Int.lt_floor_add_one ((D:ℚ)*q)
  constructor
  · apply (le_div_iff₀ hDp).mpr
    have he : (q-1/(D:ℚ))*(D:ℚ)=(D:ℚ)*q-1 := by field_simp
    rw [he]
    linarith
  · apply (div_le_iff₀ hDp).mpr
    simpa only [mul_comm] using hlo

lemma gridFloor_error (D : ℕ) (hD : 0<D) (q : ℚ) :
    |(gridFloor D q:ℝ)-(q:ℝ)|≤1/(D:ℝ) := by
  have hh := gridFloor_bounds D hD q
  have h : |gridFloor D q-q|≤1/(D:ℚ) := by
    apply abs_le.mpr
    constructor <;> linarith [show (0:ℚ)≤1/(D:ℚ) by positivity]
  have hr := (Rat.cast_le (K:=ℝ)).mpr h
  simpa only [Rat.cast_abs,Rat.cast_sub,Rat.cast_div,Rat.cast_one,Rat.cast_natCast] using hr

lemma realMatrix_symm (A : Matrix V V ℚ) (hA : A.IsSymm) : (realMatrix A).IsHermitian := by
  apply isHermitian_iff_isSymm.mpr
  ext i j
  exact congrArg (fun q : ℚ => (q:ℝ)) (hA.apply i j)

lemma gridMatrix_symm (D : ℕ) (A : Matrix V V ℚ) (hA : A.IsSymm) :
    (gridMatrix D A).IsSymm := by
  ext i j
  exact congrArg (gridFloor D) (hA.apply i j)

lemma gridMatrix_error (D : ℕ) (hD : 0<D) (A : Matrix V V ℚ) :
    ∀ i j, |realMatrix (gridMatrix D A) i j-realMatrix A i j|≤1/(D:ℝ) := by
  intro i j
  exact gridFloor_error D hD (A i j)

lemma gridFloor_numerator_bound (D : ℕ) (hD : 0<D) (q : ℚ) (H : ℚ) (hH : |q|≤H) :
    |(⌊(D:ℚ)*q⌋:ℚ)|≤(D:ℚ)*H+1 := by
  have hDp : 0≤(D:ℚ) := by positivity
  have hq := abs_le.mp hH
  have hlo := Int.floor_le ((D:ℚ)*q)
  have hhi := Int.lt_floor_add_one ((D:ℚ)*q)
  have hm := mul_le_mul_of_nonneg_left hq.1 hDp
  have hp := mul_le_mul_of_nonneg_left hq.2 hDp
  apply abs_le.mpr
  constructor <;> nlinarith

end

def sqrtUpperFraction (p q D : ℕ) : ℚ :=
  ((Nat.sqrt (p*q*D^2)+1 : ℕ):ℚ)/((q*D:ℕ):ℚ)

lemma sqrtUpperFraction_bounds (p q D : ℕ) (hp : 0<p) (hq : 0<q) (hD : 0<D) :
    Real.sqrt ((p:ℝ)/(q:ℝ)) ≤ (sqrtUpperFraction p q D:ℝ) ∧
    (sqrtUpperFraction p q D:ℝ) ≤ (1+1/(D:ℝ))*Real.sqrt ((p:ℝ)/(q:ℝ)) := by
  let w := Real.sqrt ((p:ℝ)/(q:ℝ))
  have hpR : 0<(p:ℝ) := by exact_mod_cast hp
  have hqR : 0<(q:ℝ) := by exact_mod_cast hq
  have hDR : 0<(D:ℝ) := by exact_mod_cast hD
  have hw : 0≤w := Real.sqrt_nonneg _
  have hw2 : w^2=(p:ℝ)/(q:ℝ) := Real.sq_sqrt (div_nonneg hpR.le hqR.le)
  have hf : ((q:ℝ)*(D:ℝ)*w)^2=(p:ℝ)*(q:ℝ)*(D:ℝ)^2 := by
    rw [mul_pow,mul_pow,hw2]
    field_simp
  let k := Nat.sqrt (p*q*D^2)
  have hk2 : (k:ℝ)^2≤(p:ℝ)*(q:ℝ)*(D:ℝ)^2 := by
    exact_mod_cast Nat.sqrt_le' (p*q*D^2)
  have hks : (p:ℝ)*(q:ℝ)*(D:ℝ)^2<((k:ℝ)+1)^2 := by
    exact_mod_cast Nat.lt_succ_sqrt' (p*q*D^2)
  have hkw : (k:ℝ)≤(q:ℝ)*(D:ℝ)*w := by
    have : 0≤(q:ℝ)*(D:ℝ)*w := by positivity
    nlinarith
  have hwk : (q:ℝ)*(D:ℝ)*w≤(k:ℝ)+1 := by
    have : 0≤(k:ℝ) := by positivity
    nlinarith
  have hqw : 1≤(q:ℝ)*w := by
    have hp1 : (1:ℝ)≤p := by exact_mod_cast hp
    have hq1 : (1:ℝ)≤q := by exact_mod_cast hq
    have hab : (1:ℝ)≤(p:ℝ)*(q:ℝ) := by nlinarith
    have hs : ((q:ℝ)*w)^2=(p:ℝ)*(q:ℝ) := by rw [mul_pow,hw2]; field_simp
    have : 0≤(q:ℝ)*w := by positivity
    nlinarith
  have he : (sqrtUpperFraction p q D:ℝ)=((k:ℝ)+1)/((q:ℝ)*(D:ℝ)) := by
    simp [sqrtUpperFraction,k]
  rw [he]
  constructor
  · apply (le_div_iff₀ (mul_pos hqR hDR)).mpr
    nlinarith [hwk]
  · apply (div_le_iff₀ (mul_pos hqR hDR)).mpr
    have hh : ((1+1/(D:ℝ))*w)*((q:ℝ)*(D:ℝ))=(q:ℝ)*(D:ℝ)*w+(q:ℝ)*w := by
      field_simp
    rw [hh]
    linarith

end MetricKMedianRecovery.Ellipsoid

end OAI
