import OAI.NumberTheory.JointDickman.Arithmetic.FixedDivisorWeights
import OAI.NumberTheory.JointDickman.Amplification.UnitProgressionBinAverage

namespace OAI

/-! # Dividing a residue class and its averaging interval by a fixed divisor -/
namespace JointDickman
open Finset Classical

noncomputable def residueBinAverage {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (ζ : ι → ℂ) (μ : ℂ) (w : ArithmeticFunction ℝ)
    {q : ℕ} (r : ZMod q) (H z : ℝ) : ℂ :=
  (∑ n ∈ Ioc ⌊z⌋₊ ⌊z+H⌋₊, if (n : ZMod q) = r then
    (binLabel E ζ n-μ)*(w n : ℂ) else 0)/(H : ℂ)

theorem residueBinAverage_unit {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (ζ : ι → ℂ) (μ : ℂ) (w : ArithmeticFunction ℝ)
    {q : ℕ} (r : (ZMod q)ˣ) (H z : ℝ) :
    residueBinAverage E ζ μ w (r : ZMod q) H z = unitProgressionBinAverage E ζ μ w r H z := rfl

theorem natCast_fixed_residue_iff {d e a n : ℕ} (hd : d ≠ 0) :
    (n : ZMod (d*e)) = ((d*a : ℕ) : ZMod (d*e)) ↔
      d ∣ n ∧ (n/d : ℕ) ≡ a [MOD e] := by
  rw [ZMod.natCast_eq_natCast_iff]
  constructor
  · intro h
    have hm := h.of_dvd (dvd_mul_right d e)
    have hdn : d ∣ n := (hm.dvd_iff (dvd_refl d)).mpr (dvd_mul_right d a)
    refine ⟨hdn,?_⟩
    have hh : d*(n/d) ≡ d*a [MOD d*e] := by simpa only [Nat.mul_div_cancel' hdn] using h
    exact hh.mul_left_cancel' hd
  · rintro ⟨hdn,h⟩
    have hh := h.mul_left' d
    simpa only [Nat.mul_div_cancel' hdn] using hh

theorem sum_fixed_residue {R : Type*} [AddCommMonoid R]
    (f : ℕ → R) (l u d e a : ℕ) (hd : 0 < d) :
    (∑ n ∈ Ioc l u, if (n : ZMod (d*e)) = ((d*a : ℕ) : ZMod (d*e)) then f n else 0) =
      ∑ k ∈ Ioc (l/d) (u/d), if (k : ZMod e) = (a : ZMod e) then f (d*k) else 0 := by
  have he (n : ℕ) : (if (n : ZMod (d*e)) = ((d*a : ℕ) : ZMod (d*e)) then f n else 0) =
      if d ∣ n then (if (n/d : ℕ) ≡ a [MOD e] then f n else 0) else 0 := by
    simp only [natCast_fixed_residue_iff hd.ne']
    split_ifs <;> simp_all
  simp_rw [he]
  rw [sum_divisible_interval (fun n => if (n/d : ℕ) ≡ a [MOD e] then f n else 0) l u d hd]
  apply sum_congr rfl
  intro k _
  simp only [Nat.mul_div_cancel_left k hd,ZMod.natCast_eq_natCast_iff]

theorem residueBinAverage_dilate {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (ζ : ι → ℂ) (μ : ℂ)
    (w v : ArithmeticFunction ℝ) (c : ℝ)
    {d : ℕ} (hd : 0 < d) (e a : ℕ)
    (hweight : ∀ k, w (d*k) = c*v k)
    (hbin : ∀ k, binLabel E ζ (d*k) = binLabel E ζ k)
    {H : ℝ} (hH : 0 < H) (z : ℝ) :
    residueBinAverage E ζ μ w ((d*a : ℕ) : ZMod (d*e)) H z =
      (c : ℂ)/(d : ℂ)*
        residueBinAverage E ζ μ v
          (a : ZMod e) (H/d) (z/d) := by
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hHC : (H : ℂ) ≠ 0 := by exact_mod_cast hH.ne'
  unfold residueBinAverage
  rw [sum_fixed_residue _ _ _ _ _ _ hd]
  simp_rw [hweight,hbin,Complex.ofReal_mul]
  rw [show z/(d : ℝ)+H/d = (z+H)/d by ring,Nat.floor_div_natCast,Nat.floor_div_natCast]
  simp only [Complex.ofReal_div,Complex.ofReal_natCast]
  have he (k : ℕ) : (if (k : ZMod e) = a then
      (binLabel E ζ k-μ)*((c : ℂ)*
        (v k : ℂ)) else 0) =
      (c : ℂ)*
        (if (k : ZMod e) = a then (binLabel E ζ k-μ)*
          (v k : ℂ) else 0) := by
    split_ifs <;> ring
  simp_rw [he]
  rw [← mul_sum]
  field_simp

theorem residueBinAverage_fixed_divisor {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (ζ : ι → ℂ) (μ : ℂ)
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (t : ℕ → ℝ)
    {d : ℕ} (hd : 0 < d) (e a : ℕ)
    (hbin : ∀ k, binLabel E ζ (d*k) = binLabel E ζ k)
    {H : ℝ} (hH : 0 < H) (z : ℝ) :
    residueBinAverage E ζ μ (finitePrimeWeight P t) ((d*a : ℕ) : ZMod (d*e)) H z =
      ((finitePrimeWeight P t d : ℝ) : ℂ)/(d : ℂ)*
        residueBinAverage E ζ μ (finitePrimeWeight P (fun p => if p ∣ d then 1 else t p))
          (a : ZMod e) (H/d) (z/d) := by
  exact residueBinAverage_dilate E ζ μ _ _ (finitePrimeWeight P t d) hd e a
    (finitePrimeWeight_mul_fixed hP t hd.ne') hbin hH z

end JointDickman

end OAI
