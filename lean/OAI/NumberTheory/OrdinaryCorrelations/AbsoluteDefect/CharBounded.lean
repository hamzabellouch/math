import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.OneBounded
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Euler

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset

namespace OrdinaryCorrelations.ResidueCharacters
open scoped BigOperators
open Classical
open LocalExpansion

lemma char_bounded {q : ℕ} (χ : DirichletCharacter ℂ q) :
    OneBounded (fun n : ℕ => χ (n : ZMod q)) := fun _n => χ.norm_le_one _

lemma char_multiplicative {q : ℕ} (χ : DirichletCharacter ℂ q) :
    Multiplicative (fun n : ℕ => χ (n : ZMod q)) := by
  intro m n _ _ _
  simp only [Nat.cast_mul,map_mul]

lemma char_one {q : ℕ} (χ : DirichletCharacter ℂ q) : χ (1 : ZMod q) = 1 := map_one χ

lemma char_inv_eq_star {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {a : ZMod q} (ha : IsUnit a) : χ a⁻¹ = star (χ a) := by
  rw [MulChar.star_apply',MulChar.inv_apply_eq_inv']
  apply eq_inv_of_mul_eq_one_left
  rw [← map_mul,ZMod.inv_mul_of_unit a ha,map_one]

theorem unit_indicator {q : ℕ} (hq : 0 < q) (c m : ℕ) (hc : c.Coprime q) :
    (if m ≡ c [MOD q] then (1:ℂ) else 0) =
      (q.totient:ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
        star (χ (c:ZMod q)) * χ (m:ZMod q) := by
  let : NeZero q := ⟨hq.ne'⟩
  have hu : IsUnit (c:ZMod q) := (ZMod.isUnit_iff_coprime c q).mpr hc
  have he := DirichletCharacter.sum_char_inv_mul_char_eq ℂ hu (m:ZMod q)
  simp only [char_inv_eq_star _ hu] at he
  rw [he]
  have ht : (q.totient:ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hq).ne'
  have hi : (c:ZMod q) = (m:ZMod q) ↔ m ≡ c [MOD q] := by
    rw [eq_comm,ZMod.natCast_eq_natCast_iff]
  simp only [hi]
  split_ifs <;> simp [ht]

theorem dilated_indicator (d q c m : ℕ) (hd : 0 < d) (hq : 0 < q)
    (hc : c.Coprime q) :
    (if m ≡ d*c [MOD d*q] then (1:ℂ) else 0) =
      (q.totient:ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
        star (χ (c:ZMod q)) * dilation d (fun n => χ (n:ZMod q)) m := by
  by_cases hm : d ∣ m
  · conv_lhs => rw [← Nat.mul_div_cancel' hm]
    simp only [Nat.ModEq.mul_left_cancel_iff' hd.ne']
    simpa only [dilation,ite_eq_left hm] using unit_indicator hq c (m/d) hc
  · have hn : ¬ m ≡ d*c [MOD d*q] := by
      intro he
      have hem : m ≡ d*c [MOD d] := he.of_dvd (by exact dvd_mul_right d q)
      have hez : d*c ≡ 0 [MOD d] := Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right d c)
      exact hm (Nat.modEq_zero_iff_dvd.mp (hem.trans hez))
    simp [hn,dilation,hm]

theorem gcd_indicator (l b m : ℕ) (hl : 0 < l) :
    (if m ≡ b [MOD l] then (1:ℂ) else 0) =
      ((l / b.gcd l).totient:ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ (l / b.gcd l),
        star (χ ((b / b.gcd l):ZMod (l / b.gcd l))) *
          dilation (b.gcd l) (fun n => χ (n:ZMod (l / b.gcd l))) m := by
  have hd : 0 < b.gcd l := Nat.gcd_pos_of_pos_right b hl
  have hq : 0 < l / b.gcd l :=
    Nat.div_pos (Nat.le_of_dvd hl (Nat.gcd_dvd_right b l)) hd
  have he := dilated_indicator (b.gcd l) (l / b.gcd l) (b / b.gcd l) m hd hq
    (Nat.coprime_div_gcd_div_gcd hd)
  simpa only [Nat.mul_div_cancel' (Nat.gcd_dvd_left b l),
    Nat.mul_div_cancel' (Nat.gcd_dvd_right b l)] using he

end OrdinaryCorrelations.ResidueCharacters

end

end OAI
