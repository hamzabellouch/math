import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterPrimeDerivative
import Mathlib.NumberTheory.LSeries.SumCoeff

namespace OAI

/-! Explicit modulus dependence in nonprincipal character partial sums,
and the resulting exact Abel integral on its initial half-plane. -/

namespace TwoPointCorrelations

open Finset Filter Asymptotics MeasureTheory
open scoped Classical Topology

lemma mrt_character_shift {q : ℕ} (χ : DirichletCharacter ℂ q) (k n : ℕ) :
    χ ((q*k+n:ℕ):ZMod q)=χ (n:ZMod q) := by
  simp only [Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,zero_mul,zero_add]

lemma mrt_character_period_sum {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ≠1) :
    (∑ n∈range q,χ (n:ZMod q))=0 := by
  have hs := χ.sum_eq_zero_of_ne_one hχ
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ q =>
    calc
      _ = ∑ n : Fin (q+1),χ (n.val:ZMod (q+1)) :=
        (Fin.sum_univ_eq_sum_range (fun n : ℕ => χ (n:ZMod (q+1))) (q+1)).symm
      _ = ∑ n : ZMod (q+1),χ n := by
        apply sum_congr rfl
        intro n _
        exact congrArg χ (ZMod.natCast_zmod_val (n := q+1) n)
      _ = 0 := hs

lemma mrt_character_full_periods {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ≠1) (k : ℕ) :
    (∑ n∈range (q*k),χ (n:ZMod q))=0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ,sum_range_add,ih,zero_add]
    simp_rw [mrt_character_shift]
    exact mrt_character_period_sum χ hχ

lemma mrt_character_prefix_remainder {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ≠1) (N : ℕ) :
    (∑ n∈range N,χ (n:ZMod q))=∑ n∈range (N%q),χ (n:ZMod q) := by
  have hN : N=q*(N/q)+N%q := by
    simpa only [Nat.mul_comm] using (Nat.div_add_mod N q).symm
  conv_lhs => rw [hN,sum_range_add,mrt_character_full_periods χ hχ,zero_add]
  exact sum_congr rfl (fun n _ => mrt_character_shift χ (N/q) n)

theorem mrt_character_prefix_norm {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ≠1) (N : ℕ) :
    ‖∑ n∈range N,χ (n:ZMod q)‖≤(q:ℝ) := by
  rw [mrt_character_prefix_remainder χ hχ]
  calc
    _ ≤ ∑ n∈range (N%q),‖χ (n:ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ _n∈range (N%q),(1:ℝ) := sum_le_sum (fun n _ => χ.norm_le_one _)
    _ = (N%q:ℕ) := by simp
    _ ≤ (q:ℝ) := by exact_mod_cast (Nat.mod_lt N (NeZero.pos q)).le

lemma mrt_character_Icc_eq {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ≠1) (N : ℕ) :
    (∑ n∈Icc 1 N,χ (n:ZMod q))=∑ n∈range (N+1),χ (n:ZMod q) := by
  have hq : q≠1 := by
    intro hq
    subst q
    apply hχ
    ext n
    have hn : n=(1:ZMod 1) := Subsingleton.elim _ _
    simp [hn]
  let : Nontrivial (ZMod q) := ZMod.nontrivial_iff.mpr hq
  rw [Nat.range_succ_eq_Icc_zero]
  have hset : Icc 1 N=Ioc 0 N := by ext n; simp; omega
  rw [hset,←add_sum_Ioc_eq_sum_Icc (Nat.zero_le N),Nat.cast_zero,
    MulChar.map_zero χ,zero_add]

theorem mrt_character_Icc_norm {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ≠1) (N : ℕ) :
    ‖∑ n∈Icc 1 N,χ (n:ZMod q)‖≤(q:ℝ) := by
  rw [mrt_character_Icc_eq χ hχ]
  exact mrt_character_prefix_norm χ hχ (N+1)

lemma mrt_character_sum_bigO {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ≠1) :
    (fun N : ℕ => ∑ n∈Icc 1 N,χ (n:ZMod q)) =O[atTop]
      (fun N : ℕ => (N:ℝ)^(0:ℝ)) := by
  refine isBigO_iff.mpr ⟨(q:ℝ),Eventually.of_forall (fun N => ?_)⟩
  simpa only [Real.rpow_zero,norm_one,mul_one] using mrt_character_Icc_norm χ hχ N

theorem mrt_character_LFunction_Abel {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ≠1) {s : ℂ} (hs : 1<s.re) :
    DirichletCharacter.LFunction χ s =
      s*∫ t in Set.Ioi (1:ℝ),
        (∑ n∈Icc 1 ⌊t⌋₊,χ (n:ZMod q))*(t:ℂ)^(-(s+1)) := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  exact LSeries_eq_mul_integral (fun n => χ (n:ZMod q)) (by norm_num : (0:ℝ)≤0)
    (by linarith : (0:ℝ)<s.re) (χ.LSeriesSummable_of_one_lt_re hs)
    (mrt_character_sum_bigO χ hχ)

end TwoPointCorrelations

end OAI
