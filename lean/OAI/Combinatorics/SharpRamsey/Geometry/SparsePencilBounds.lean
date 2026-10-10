import Mathlib
import OAI.Combinatorics.SharpRamsey.Selection.SparseProductSharp

namespace OAI

section
namespace SharpLogRamsey.Incidence
open Finset
open scoped BigOperators

lemma geom_sum_le_twice_pow (q : ℝ) (hq : 2≤q) (n : ℕ) :
    (∑ i∈range (n+1),q^i)≤2*q^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have hh : 2*q^n≤q^(n+1) := by
      rw [pow_succ]
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hq (show 0≤q^n by positivity)
    linarith

lemma scalar_pencil_card (q s : ℝ) (hq : 2≤q) (hs : 0<s) (j : ℕ) (hj : 1≤j)
    (hsmall : s^2≤2*q^(j+1)) :
    (∑ i∈range j,q^i)≤4*(q^j/s)^2 := by
  have hq0 : 0≤q := by linarith
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hj
  have hcount : (∑ i∈range (1+m),q^i)≤2*q^m := by
    simpa [Nat.add_comm] using geom_sum_le_twice_pow q hq m
  have hmul := mul_le_mul hcount hsmall (sq_nonneg s) (by positivity : 0≤2*q^m)
  have he : (2*q^m)*(2*q^(1+m+1))=4*(q^(1+m))^2 := by ring
  rw [he] at hmul
  rw [div_pow, ←mul_div_assoc]
  apply (le_div_iff₀ (sq_pos_of_pos hs)).mpr
  exact hmul

lemma scalar_direction_three (q s : ℝ) (hq : 2≤q) (hs : 0<s)
    (hsmall : s^2≤2*q^4) : 1+q≤4*(q^3/s) := by
  have hq0 : 0≤q := by linarith
  have hq2 : 0≤q^2 := sq_nonneg q
  have hsle : s≤2*q^2 := by nlinarith [hsmall,sq_nonneg (s-2*q^2)]
  have he : (1+q)*(2*q^2)≤4*q^3 := by nlinarith [mul_nonneg hq2 (show 0≤q-1 by linarith)]
  have hh := (mul_le_mul_of_nonneg_left hsle (by linarith : 0≤1+q)).trans he
  rw [←mul_div_assoc]
  exact (le_div_iff₀ hs).mpr hh

lemma scalar_direction_two (q s : ℝ) (hq : 2≤q) (hs : 0<s)
    (hsmall : s^2≤2*q^3) : (1:ℝ)≤4*(q^2/s) := by
  have hq0 : 0≤q := by linarith
  have hq2 : 0≤q^2 := sq_nonneg q
  have hsle : s≤4*q^2 := by
    have hpow : 2*q^3≤16*(q^2)^2 := by
      nlinarith [mul_nonneg (show 0≤q^3 by positivity) (show 0≤q-1 by linarith)]
    nlinarith [hsmall,hpow,sq_nonneg (s-4*q^2)]
  rw [←mul_div_assoc]
  exact (le_div_iff₀ hs).mpr (by simpa using hsle)

section
variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]

theorem sparse_retained_pencil {n : ℕ} (hdim : Module.finrank K V=n+3)
    (S S' : Finset (Projectivization K V)) (hS' : S'.Nonempty) (hsub : S'⊆S)
    (T : Finset (Projectivization K (Module.Dual K V))) (hsmall : S.card≤T.card)
    (hsparse : (incidenceCount S T:ℝ)≤(S.card:ℝ)*T.card/(20*Nat.card K)) :
    ((∑ i∈range (n+2),Nat.card K^i):ℝ)≤
      4*((Nat.card K:ℝ)^(n+2)/(S'.card:ℝ))^2 := by
  have hq : (2:ℝ)≤Nat.card K := by
    have hh : 2≤Nat.card K := by have := (Finite.one_lt_card : 1<Nat.card K); omega
    exact_mod_cast hh
  have hs : (0:ℝ)<S'.card := by exact_mod_cast card_pos.mpr hS'
  have hh := sparse_smaller_square hdim S T hsmall hsparse
  have hsc : (S'.card:ℝ)≤S.card := by exact_mod_cast card_le_card hsub
  have hsq : (S'.card:ℝ)^2≤2*(Nat.card K:ℝ)^(n+2+1) := by
    exact (sq_le_sq₀ (by positivity) (by positivity)).mpr hsc |>.trans hh
  simpa only [Nat.cast_sum,Nat.cast_pow] using
    scalar_pencil_card (Nat.card K) S'.card hq hs (n+2) (by omega) hsq
end
end SharpLogRamsey.Incidence

end

end OAI
