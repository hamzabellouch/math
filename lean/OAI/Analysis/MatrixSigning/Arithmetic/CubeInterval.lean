import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.ScalarPsi

namespace OAI

open Matrix

namespace CurrentKS.Scalar

def cubeInterval (q : ℚ) : ℕ → ℚ × ℚ
  | 0 => (0,1)
  | k+1 =>
    let s := cubeInterval q k
    let m := (s.1+s.2)/2
    if m^3 ≤ q then (m,s.2) else (s.1,m)

lemma cubeInterval_spec (q : ℚ) (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hq : (q:ℝ)=r^3) (k : ℕ) :
    0 ≤ (cubeInterval q k).1 ∧ (cubeInterval q k).2 ≤ 1 ∧
    ((cubeInterval q k).1:ℝ) ≤ r ∧ r ≤ ((cubeInterval q k).2:ℝ) ∧
    (cubeInterval q k).2-(cubeInterval q k).1=(1/2:ℚ)^k := by
  induction k with
  | zero => simpa [cubeInterval] using And.intro hr hr1
  | succ k ih =>
    have horder : (cubeInterval q k).1 ≤ (cubeInterval q k).2 := by
      exact_mod_cast ih.2.2.1.trans ih.2.2.2.1
    let m : ℚ := ((cubeInterval q k).1+(cubeInterval q k).2)/2
    have hml : (cubeInterval q k).1 ≤ m := by dsimp [m]; linarith
    have hmu : m ≤ (cubeInterval q k).2 := by dsimp [m]; linarith
    have hm : 0 ≤ m := ih.1.trans hml
    have hmr : (0:ℝ) ≤ m := by exact_mod_cast hm
    have he : cubeInterval q (k+1) = if m^3 ≤ q then (m,(cubeInterval q k).2) else ((cubeInterval q k).1,m) := rfl
    rw [he]
    split
    · rename_i h
      have hc : (m:ℝ)^3 ≤ r^3 := by rw [← hq]; exact_mod_cast h
      have hle := (pow_le_pow_iff_left₀ hmr hr (by decide : 3≠0)).mp hc
      refine ⟨hm,ih.2.1,hle,ih.2.2.2.1,?_⟩
      change (cubeInterval q k).2-m=(1/2:ℚ)^(k+1)
      rw [pow_succ,← ih.2.2.2.2]
      dsimp [m]
      ring
    · rename_i h
      have hc : r^3 ≤ (m:ℝ)^3 := by rw [← hq]; exact_mod_cast (le_of_lt (lt_of_not_ge h))
      have hle := (pow_le_pow_iff_left₀ hr hmr (by decide : 3≠0)).mp hc
      refine ⟨ih.1,hmu.trans ih.2.1,ih.2.2.1,hle,?_⟩
      change m-(cubeInterval q k).1=(1/2:ℚ)^(k+1)
      rw [pow_succ,← ih.2.2.2.2]
      dsimp [m]
      ring

lemma cubeInterval_error (q : ℚ) (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hq : (q:ℝ)=r^3) (k : ℕ) :
    |((cubeInterval q k).1:ℝ)-r| ≤ (1/2:ℝ)^k := by
  obtain ⟨_,_,hl,hu,hw⟩ := cubeInterval_spec q r hr hr1 hq k
  have hwr : ((cubeInterval q k).2:ℝ)-(cubeInterval q k).1=(1/2:ℝ)^k := by
    have hc := congrArg (fun z : ℚ => (z : ℝ)) hw
    norm_num only [Rat.cast_sub,Rat.cast_pow,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at hc
    exact hc
  rw [abs_of_nonpos (sub_nonpos.mpr hl)]
  linarith

lemma cubeInterval_lower_mem (q : ℚ) (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hq : (q:ℝ)=r^3) (k : ℕ) : (cubeInterval q k).1 ∈ Set.Icc (0:ℚ) 1 := by
  have h := cubeInterval_spec q r hr hr1 hq k
  exact ⟨h.1,by exact_mod_cast h.2.2.1.trans hr1⟩

lemma psi_closed_cube {x : ℝ} (hx : |x| ≤ 1) : psi x^3=1-x^2 := by
  have hb : 0 ≤ 1-x^2 := by
    obtain ⟨hl,hu⟩ := abs_le.mp hx
    nlinarith
  rw [psi,← Real.rpow_natCast,← Real.rpow_mul hb]
  norm_num
lemma psi_closed_bounds {x : ℝ} (hx : |x| ≤ 1) : 0 ≤ psi x ∧ psi x ≤ 1 := by
  have hc := psi_closed_cube hx
  have hb : 0 ≤ 1-x^2 := by
    obtain ⟨hl,hu⟩ := abs_le.mp hx
    nlinarith
  have hp : 0 ≤ psi x := Real.rpow_nonneg hb _
  refine ⟨hp,(pow_le_pow_iff_left₀ hp (by norm_num : (0:ℝ) ≤ 1) (by decide : 3≠0)).mp ?_⟩
  rw [hc]
  nlinarith [sq_nonneg x]

def approxPsi (x δ : ℚ) : ℚ := (cubeInterval (1-x^2) δ.den.size).1

lemma inverse_pow_size_le {δ : ℚ} (hδ : 0 < δ) : (1/2:ℚ)^δ.den.size ≤ δ := by
  have hd : (0:ℚ) < δ.den := by exact_mod_cast δ.den_pos
  have hp : (0:ℚ) < 2^δ.den.size := by positivity
  have hnum : (1:ℚ) ≤ δ.num := by exact_mod_cast (Int.add_one_le_iff.mpr (Rat.num_pos.mpr hδ))
  have hden : (δ.den:ℚ) ≤ 2^δ.den.size := by exact_mod_cast (Nat.lt_size_self δ.den).le
  rw [_root_.one_div_pow,one_div]
  calc
    (2^δ.den.size:ℚ)⁻¹ ≤ (δ.den:ℚ)⁻¹ := inv_anti₀ hd hden
    _ ≤ (δ.num:ℚ)/(δ.den:ℚ) := by rw [inv_eq_one_div]; exact div_le_div_of_nonneg_right hnum hd.le
    _ = δ := Rat.num_div_den δ

lemma approxPsi_spec (x δ : ℚ) (hx : |(x:ℝ)| ≤ 1) (hδ : 0 < δ) :
    approxPsi x δ ∈ Set.Icc (0:ℚ) 1 ∧ |(approxPsi x δ:ℝ)-psi (x:ℝ)| ≤ (δ:ℝ) := by
  obtain ⟨hp,hp1⟩ := psi_closed_bounds hx
  have hc : ((1-x^2:ℚ):ℝ)=psi (x:ℝ)^3 := by rw [psi_closed_cube hx]; push_cast; rfl
  refine ⟨cubeInterval_lower_mem _ _ hp hp1 hc _,?_⟩
  have he : (((1/2:ℚ)^δ.den.size : ℚ):ℝ) ≤ (δ:ℝ) := Rat.cast_le.mpr (inverse_pow_size_le hδ)
  norm_num only [Rat.cast_pow,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at he
  exact (cubeInterval_error _ _ hp hp1 hc _).trans he

end CurrentKS.Scalar

end OAI
