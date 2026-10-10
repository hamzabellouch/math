import Mathlib

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

namespace OrdinaryReverseSampling
open Finset MeasureTheory

lemma integer_grid_separated (c : ℝ) (N : ℕ) :
    ((range N).image (fun j : ℕ=>c+j) : Set ℝ).Pairwise (fun t u=>1≤|t-u|) := by
  classical
  intro t ht u hu htu
  obtain ⟨i,hi,rfl⟩ := mem_image.mp ht
  obtain ⟨j,hj,rfl⟩ := mem_image.mp hu
  have hij : i≠j := by intro h; subst j; exact htu rfl
  rcases lt_or_gt_of_ne hij with h|h
  · have hh : (i:ℝ)+1≤j := by exact_mod_cast (Nat.succ_le_iff.mpr h)
    have hh' := neg_le_abs ((c+i)-(c+j))
    linarith
  · have hh : (j:ℝ)+1 ≤ i := by exact_mod_cast (Nat.succ_le_iff.mpr h)
    have hh' := le_abs_self ((c+i)-(c+j))
    linarith

lemma grid_integral (F : ℝ→ℝ) (hF : Continuous F) (a : ℝ) (N : ℕ) :
    (∫u in (0:ℝ)..1,∑j∈range N,F (a+j+u)) = ∫t in a..a+N,F t := by
  rw [intervalIntegral.integral_finsetSum (s:=range N) (fun j hj=>(show Continuous (fun u : ℝ=>F (a+(j:ℕ)+u)) by fun_prop).intervalIntegrable _ _)]
  have he (j : ℕ) : (∫u in (0:ℝ)..1,F (a+j+u)) = ∫t in a+j..a+(j+1:ℕ),F t := by
    rw [intervalIntegral.integral_comp_add_left]
    congr 1 <;> push_cast <;> ring
  simp_rw [he]
  simpa only [Nat.cast_zero,add_zero] using
    (intervalIntegral.sum_integral_adjacent_intervals (a:=fun j:ℕ=>a+j)
      (fun j hj=>hF.intervalIntegrable _ _))

theorem integral_le_samples (F : ℝ→ℝ) (hF : Continuous F) {T E : ℝ}
    (hT : 0≤T) (hE : 0≤E)
    (hS : ∀S : Finset ℝ,(S:Set ℝ).Pairwise (fun t u=>1≤|t-u|) →
      (∀t∈S,|t|≤T) → (∑t∈S,F t)≤E) :
    (∫t in -T..T,F t)≤2*E := by
  classical
  let N := ⌊2*T⌋₊
  have hN : (N:ℝ)≤2*T := Nat.floor_le (by positivity : 0≤2*T)
  have hN' : 2*T<(N:ℝ)+1 := Nat.lt_floor_add_one (2*T)
  have hgrid (u : ℝ) (hu : u∈Set.Icc (0:ℝ) 1) :
      (∑j∈range N,F (-T+j+u))≤E := by
    let S := (range N).image (fun j:ℕ=>-T+u+j)
    have hs := hS S (integer_grid_separated (-T+u) N) (by
      intro t ht
      obtain ⟨j,hj,rfl⟩ := mem_image.mp ht
      have hj' : (j:ℝ)+1≤N := by exact_mod_cast (Nat.succ_le_iff.mpr (mem_range.mp hj))
      exact abs_le.mpr ⟨by linarith [hu.1],by linarith [hu.2]⟩)
    rw [sum_image] at hs
    · convert hs using 1
      apply sum_congr rfl
      intro j hj
      congr 1
      ring
    · intro i hi j hj hij
      exact Nat.cast_injective (add_left_cancel hij)
  have hmain := intervalIntegral.integral_mono_on («μ» := volume) (by norm_num : (0:ℝ)≤1)
    (Continuous.intervalIntegrable (by fun_prop) 0 1) intervalIntegrable_const hgrid
  rw [grid_integral F hF (-T) N,intervalIntegral.integral_const] at hmain
  norm_num only [sub_zero,one_smul] at hmain
  have hpoint (t : ℝ) (ht : t∈Set.Icc (-T+(N:ℝ)) T) : F t≤E := by
    have hh := hS {t} (by simp) (by
      intro u hu
      simp only [Finset.mem_singleton] at hu
      subst u
      exact abs_le.mpr ⟨by have := Nat.cast_nonneg (α:=ℝ) N; linarith [ht.1],ht.2⟩)
    simpa using hh
  have htail := intervalIntegral.integral_mono_on («μ» := volume) (by linarith : -T+(N:ℝ)≤T)
    (hF.intervalIntegrable _ _) intervalIntegrable_const hpoint
  rw [intervalIntegral.integral_const] at htail
  simp only [smul_eq_mul] at htail
  have he := intervalIntegral.integral_add_adjacent_intervals («μ» := volume)
    (hF.intervalIntegrable (-T) (-T+N)) (hF.intervalIntegrable (-T+N) T)
  have hlen : (T-(-T+(N:ℝ)))*E≤E := by nlinarith only [hN',hE]
  linarith only [hmain,htail,he,hlen]

end OrdinaryReverseSampling

end

end OAI
