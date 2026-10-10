import Mathlib
import OAI.Probability.LogConcave.Numerics.ScalarPicard

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.MeanTree
open scoped BigOperators

lemma flowWork_bound (p N y : ℕ) : flowWork p N 0 y+1≤(y+1)*(p+1)^N := by
  induction N with
  | zero => simp [flowWork,scalarPicard]
  | succ N ih =>
    have hp : 1≤(p+1)^N := Nat.one_le_pow N _ (by omega)
    have hy : y+1≤(y+1)*(p+1)^N := by nlinarith
    have he := Nat.mul_le_mul_left p ih
    change y+p*(1+0+flowWork p N 0 y)+1≤_
    rw [pow_succ]
    nlinarith

lemma kernelWork_bound (p q N y g : ℕ) :
    kernelWork p q N 0 y g+1≤(q+1)^N*(p+1)^(2*N+1)*(y+g+1) := by
  let U := flowWork p N 0 y
  let V := flowWork q N 0 (U+g)
  let W := flowWork p N 0 V
  have hP : 1≤(p+1)^N := Nat.one_le_pow N _ (by omega)
  have hQ : 1≤(q+1)^N := Nat.one_le_pow N _ (by omega)
  have hU : U+g+1≤(y+g+1)*(p+1)^N := by
    have he := flowWork_bound p N y
    change U+1≤_ at he
    nlinarith
  have hV : V+1≤(y+g+1)*(p+1)^N*(q+1)^N :=
    (flowWork_bound q N (U+g)).trans (Nat.mul_le_mul_right _ hU)
  have hW : W+1≤(y+g+1)*(p+1)^N*(q+1)^N*(p+1)^N :=
    (flowWork_bound p N V).trans (Nat.mul_le_mul_right _ hV)
  have hone : 1≤(y+g+1)*(p+1)^N*(q+1)^N*(p+1)^N := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hm := Nat.mul_le_mul_left p hW
  change p*(1+0+W)+1≤_
  have he : (q+1)^N*(p+1)^(2*N+1)*(y+g+1)=
      (p+1)*((y+g+1)*(p+1)^N*(q+1)^N*(p+1)^N) := by
    rw [pow_add,pow_one,show 2*N=N+N by omega,pow_add]
    ring
  rw [he]
  nlinarith

def velocityWorkCoefficient (q m N : ℕ) : ℕ := 4+(m+1)*(q+1)^N

lemma velocityWork_bound (p q m N : ℕ) (z : ℕ × ℕ) :
    (velocityWork p q m N 0 z).1+(velocityWork p q m N 0 z).2+1≤
      velocityWorkCoefficient q m N*(p+1)^(2*N+2)*(z.1+z.2+1) := by
  have hk := kernelWork_bound p q N z.1 z.2
  have hp : 1≤(p+1)^(2*N+1) := Nat.one_le_pow _ _ (by omega)
  have hh : kernelWork p q N 0 z.1 z.2≤(q+1)^N*(p+1)^(2*N+1)*(z.1+z.2+1) := by omega
  have hmul := Nat.mul_le_mul_left (p*(m+1)) hh
  have hg : (z.1+z.2+1)≤(p+1)^(2*N+1)*(z.1+z.2+1) := by nlinarith
  have hc : p*(m+1)*(q+1)^N+3≤(4+(m+1)*(q+1)^N)*(p+1) := by nlinarith
  have hh' := Nat.mul_le_mul_right ((p+1)^(2*N+1)*(z.1+z.2+1)) hc
  have hz : z.1+3≤3*(p+1)^(2*N+1)*(z.1+z.2+1) := by nlinarith
  change p*(m+1)*kernelWork p q N 0 z.1 z.2+(2+2*0+z.1)+1≤_
  unfold velocityWorkCoefficient
  rw [show 2*N+2=(2*N+1)+1 by omega,pow_add,pow_one]
  nlinarith

lemma vectorPicard_zero_bound (p q m N k : ℕ) (hk : 1≤k) (Nc : ℕ) :
    (vectorPicard k (velocityWork p q m N 0) (0,0) Nc).1+
      (vectorPicard k (velocityWork p q m N 0) (0,0) Nc).2+1≤
      (k*velocityWorkCoefficient q m N)^Nc*(p+1)^(Nc*(2*N+2)) := by
  induction Nc with
  | zero => simp [vectorPicard]
  | succ Nc ih =>
    let z := vectorPicard k (velocityWork p q m N 0) (0,0) Nc
    have hv := velocityWork_bound p q m N z
    have hm := Nat.mul_le_mul_left (k*velocityWorkCoefficient q m N*(p+1)^(2*N+2)) ih
    have hx := Nat.mul_le_mul_left k hv
    change 0+k*(velocityWork p q m N 0 z).1+(0+k*(velocityWork p q m N 0 z).2)+1≤_
    rw [pow_succ,Nat.succ_mul,pow_add]
    change z.1+z.2+1≤_ at ih
    nlinarith

lemma meanWork_polynomial (p q m N nc Nc : ℕ) :
    meanWork p q m N nc Nc 0 0 0≤
      (nc+1)*((nc+1)*velocityWorkCoefficient q m N)^Nc*(p+1)^(Nc*(2*N+2)) := by
  have he := vectorPicard_zero_bound p q m N (nc+1) (by omega) Nc
  have hm := Nat.mul_le_mul_left (nc+1) he
  unfold meanWork
  nlinarith

end LogConcaveSampling.MeanTree

end

end

end OAI
