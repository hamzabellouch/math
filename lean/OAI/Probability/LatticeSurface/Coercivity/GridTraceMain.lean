import Mathlib
import OAI.Probability.LatticeSurface.Coercivity.GridTrace
import OAI.Probability.LatticeSurface.Coercivity.GridTraceAnalytic
import OAI.Probability.LatticeSurface.Coercivity.GridTraceGeometry
import OAI.Probability.LatticeSurface.Coercivity.GridTraceKernel
import OAI.Probability.LatticeSurface.Coercivity.GridTraceScale
import OAI.Probability.LatticeSurface.Coercivity.GridTraceTelescope

namespace OAI

noncomputable section

open scoped BigOperators

open scoped BigOperators

namespace GridTrace.NatGrid

def energy (N : ℕ) (p : ℝ) (v : Vertex → ℝ) : ℝ :=
  ∑ e ∈ edges (0,0) (N,N), (edgeGrad v e)^p

theorem spread_trace (p α C : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hα : 2-p < α) (hC : 0 < C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ), 1 ≤ N → ∀ (ν v : Vertex → ℝ),
      (∀ x ∈ square N, 0 ≤ ν x) → (∑ x ∈ square N, ν x) ≤ C →
      (∀ x ∈ square N, ∀ r : ℝ, 0 ≤ r → r ≤ 2*(N:ℝ) →
        (∑ y ∈ ball N x r, ν y) ≤ C*((r+1)/(N:ℝ))^α) →
      |(∑ x ∈ square N, ν x*v x) - (∑ x ∈ square N, ν x)*avg (square N) v| ≤
        K*(N:ℝ)^(1-2/p)*(energy N p v)^(1/p) := by
  let q := Real.conjExponent p
  have hpq : p.HolderConjugate q := .conjExponent hp
  let β := 1+(α-2)/p
  have hβ : 0 < β := by
    dsimp [β]
    rw [← neg_lt_iff_pos_add']
    apply (lt_div_iff₀ hpq.pos).mpr
    linarith
  let D := (4*C*(5:ℝ)^α)^(1/p)*(128*C)^(1/q)
  have hD : 0 < D := by dsimp [D];positivity
  have hden : 0 < (2:ℝ)^β-1 := sub_pos.mpr (Real.one_lt_rpow (by norm_num) hβ)
  refine ⟨D*((2:ℝ)^β/((2:ℝ)^β-1)),mul_pos hD (div_pos (by positivity) hden),?_⟩
  intro N hN ν v hν hmass hspread
  have hNp : (0:ℝ) < N := by exact_mod_cast hN
  let M := Nat.log 2 N+1
  have hl := Nat.pow_log_le_self 2 (show N ≠ 0 by omega)
  have hM : N < 2^M := Nat.lt_pow_succ_log_self (by omega) N
  have hscale (k : ℕ) (hk : k < M) : 2^k ≤ N := by
    have hklog : k ≤ Nat.log 2 N := by dsimp [M] at hk;omega
    exact (Nat.pow_le_pow_right (by omega) hklog).trans hl
  have hlast : (2:ℝ)^M ≤ 2*N := by
    have hn : 2^M ≤ 2*N := by dsimp [M];rw [pow_succ];omega
    exact_mod_cast hn
  have hE : 0 ≤ (energy N p v)^(1/p) := by
    apply Real.rpow_nonneg
    exact Finset.sum_nonneg (fun e _ => Real.rpow_nonneg (by cases e <;> exact abs_nonneg _) _)
  have hstep (k : ℕ) (hk : k ∈ Finset.range M) :
      (∑ e ∈ edges (0,0) (N,N), localKernel N ν (2^k) e*edgeGrad v e) ≤
      D*(N:ℝ)^(-α/p)*((2:ℝ)^k)^β*(energy N p v)^(1/p) := by
    have hs : (1:ℕ) ≤ 2^k := Nat.one_le_two_pow
    have hsp : (0:ℝ) < ((2^k:ℕ):ℝ) := by positivity
    have hc := kernel_holder (edges (0,0) (N,N)) (localKernel N ν (2^k)) (edgeGrad v)
      p q ((4/((2^k:ℕ):ℝ))*C*((5*((2^k:ℕ):ℝ))/(N:ℝ))^α)
      (128*C*((2^k:ℕ):ℝ)) hpq (by positivity) (by positivity)
      (fun e _ => localKernel_nonneg hν e)
      (fun e he => localKernel_sup hN hs (by linarith) hC.le hν hspread he)
      (localKernel_sum hs hν hmass) (fun e _ => by cases e <;> exact abs_nonneg _)
    rw [kernel_scale p q α C N ((2^k:ℕ):ℝ) hpq hC hNp hsp] at hc
    simpa only [D,β,energy,Nat.cast_pow,Nat.cast_ofNat] using hc
  calc
    _ ≤ ∑ k ∈ Finset.range M, ∑ e ∈ edges (0,0) (N,N), localKernel N ν (2^k) e*edgeGrad v e :=
      weighted_telescope ν v hν hM hscale
    _ ≤ ∑ k ∈ Finset.range M, D*(N:ℝ)^(-α/p)*((2:ℝ)^k)^β*(energy N p v)^(1/p) :=
      Finset.sum_le_sum hstep
    _ = D*((N:ℝ)^(-α/p)*(∑ k ∈ Finset.range M, ((2:ℝ)^k)^β))*(energy N p v)^(1/p) := by
      simp only [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ D*((((2:ℝ)^β)/((2:ℝ)^β-1))*(N:ℝ)^(1-2/p))*(energy N p v)^(1/p) := by
      apply mul_le_mul_of_nonneg_right _ hE
      exact mul_le_mul_of_nonneg_left (dyadic_global_scale p α N hpq.pos hα hNp M hlast) hD.le
    _ = _ := by ring

end GridTrace.NatGrid

end

end OAI
