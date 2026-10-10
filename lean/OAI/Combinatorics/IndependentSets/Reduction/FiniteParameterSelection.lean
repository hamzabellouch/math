import Mathlib
import OAI.Combinatorics.IndependentSets.PCP.LabelCoverData
import OAI.Combinatorics.IndependentSets.Reduction.FullAbsorptionSquare

namespace OAI

namespace LargeIndependentSets
open Coefficient
open scoped Classical BigOperators

theorem finite_parameter_selection {ε β L : ℝ} (hε : 0  <  ε) (hβ : 0  <  β)
    (hL : 0  ≤  L) (K : ℕ) :
    ∃ m : ℕ, 0  <  m ∧ ∃ ρ : ℚ, 0  <  ρ ∧ ρ  <  1 ∧
    L/m  <  β/2 ∧ (ρ:ℝ)*K  <  ε ∧
    ∃ s : ℕ, 2  ≤  s ∧ (1-levelMass m ρ ⟨m,by omega⟩)^s  <  ε ∧
    ∃ γ : ℝ, 0  <  γ ∧ (s:ℝ)*(2*γ)^2/β^2  <  ε ∧
    ∃ k : ℕ, 1  ≤  k ∧
    2*L/(m*2^k)  <  γ ∧ 2*L*s/(2^k)  <  ε := by
  obtain ⟨m,hm⟩ := exists_nat_gt (max (1:ℝ) (2*L/β))
  have hm1 : (1:ℝ)  <  m := (le_max_left _ _).trans_lt hm
  have hmp : 0  <  m := by exact_mod_cast (lt_trans (by norm_num : (0:ℝ) < 1) hm1)
  have hmβ : 2*L  <  (m:ℝ)*β := (div_lt_iff₀ hβ).mp ((le_max_right _ _).trans_lt hm)
  have hstep : L/m  <  β/2 := (div_lt_iff₀ (by positivity : (0:ℝ) < m)).mpr (by nlinarith)
  obtain ⟨ρ,hρ,hρb⟩ := exists_pos_rat_lt (show (0:ℝ) < min 1 (ε/(K+1)) by positivity)
  have hρR : (0:ℝ) < ρ := by exact_mod_cast hρ
  have hρ1 : ρ < 1 := by exact_mod_cast (hρb.trans_le (min_le_left _ _))
  have hρK : (ρ:ℝ)*K  <  ε := by
    have h := (lt_div_iff₀ (by positivity : (0:ℝ) < K+1)).mp (hρb.trans_le (min_le_right _ _))
    nlinarith
  have hpm := levelMass_pos m hρR ⟨m,by omega⟩
  have hpm1 : levelMass m ρ ⟨m,by omega⟩  ≤  1 := by
    rw [← levelMass_total m hρR.le]
    exact Finset.single_le_sum (fun k _ =>  levelMass_nonneg m hρR.le k) (Finset.mem_univ _)
  have hpow := (tendsto_pow_atTop_nhds_zero_of_lt_one (sub_nonneg.mpr hpm1)
    (show 1-levelMass m ρ ⟨m,by omega⟩ < 1 by linarith)).eventually_lt_const hε
  obtain ⟨s,hs,hsb⟩ := (hpow.and (Filter.eventually_ge_atTop 2)).exists
  let γ : ℝ := Real.sqrt (ε*β^2/(8*(s+1)))
  have hγ : 0  <  γ := Real.sqrt_pos.mpr (by positivity)
  have hγsq : γ^2 = ε*β^2/(8*(s+1)) := Real.sq_sqrt (by positivity)
  have hzero : (s:ℝ)*(2*γ)^2/β^2  <  ε := by
    apply (div_lt_iff₀ (sq_pos_of_pos hβ)).mpr
    have he := (div_mul_cancel₀ (ε*β^2) (by positivity : (8*(s+1):ℝ) ≠ 0))
    rw [← hγsq] at he
    nlinarith [sq_nonneg γ, sq_pos_of_pos hβ, show (0:ℝ) ≤ s by positivity]
  have hdy := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1/2:ℝ) < 1)
  have hz : 0  <  min (γ/(2*L+1)) (ε/(2*L*s+1)) := by positivity
  obtain ⟨k,hk,hkp⟩ := ((hdy.eventually_lt_const hz).and (Filter.eventually_ge_atTop 1)).exists
  have hpoweq : (1/2:ℝ)^k = 1/(2^k:ℝ) := by rw [div_pow,one_pow]
  rw [hpoweq] at hk
  have hkg : 2*L/(m*2^k)  <  γ := by
    have he := (lt_div_iff₀ (by positivity : (0:ℝ) < 2*L+1)).mp (hk.trans_le (min_le_left _ _))
    have hpos : (0:ℝ) < 2^k := by positivity
    have hh := (div_lt_iff₀ hpos).mp (show (2*L+1)/2^k < γ by simpa [div_eq_mul_inv, mul_comm] using he)
    apply (div_lt_iff₀ (by positivity : (0:ℝ) < m*2^k)).mpr
    nlinarith [mul_pos hγ hpos]
  have hke : 2*L*s/2^k  <  ε := by
    have he := (lt_div_iff₀ (by positivity : (0:ℝ) < 2*L*s+1)).mp (hk.trans_le (min_le_right _ _))
    have hpos : (0:ℝ) < 2^k := by positivity
    have hh := (div_lt_iff₀ hpos).mp (show (2*L*s+1)/2^k < ε by simpa [div_eq_mul_inv, mul_comm] using he)
    exact (div_lt_iff₀ hpos).mpr (by linarith)
  exact ⟨m,hmp,ρ,hρ,hρ1,hstep,hρK,s,hsb,hs,γ,hγ,hzero,k,hkp,hkg,hke⟩

lemma final_soundness_choice {ε : ℝ} (hε : 0 < ε) (r d : ℕ) :
    ∃ σ : ℚ, 0 < σ ∧ σ < 1 ∧ (4:ℝ)^r*d^2*σ < ε := by
  obtain ⟨σ,hσ,hσb⟩ := exists_pos_rat_lt
    (show (0:ℝ) < min 1 (ε/((4:ℝ)^r*d^2+1)) by positivity)
  have hσR : (0:ℝ) < σ := by exact_mod_cast hσ
  refine ⟨σ,hσ,?_,?_⟩
  · exact_mod_cast hσb.trans_le (min_le_left _ _)
  · have h := (lt_div_iff₀ (by positivity : (0:ℝ) < (4:ℝ)^r*d^2+1)).mp
      (hσb.trans_le (min_le_right _ _))
    nlinarith

end LargeIndependentSets

namespace LargeIndependentSets.PhaseTest
open scoped BigOperators Classical
open Coefficient BooleanJunta
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {M : ι → Type} [∀ j, Fintype (M j)]
variable {κ : Type} [Fintype κ]

def gridLocation (p : ∀ j, κ → M j) {m P : ℕ}
    (t : ι → Fin (m+1)) (θ : Sigma M → Fin P) : κ → ZMod (m*P) :=
  fun k => ∑ j, ((t j).val * (θ ⟨j,p j k⟩).val : ℕ)

omit [DecidableEq ι] [∀ index, Fintype (M index)] [Fintype κ] in
lemma gridLocation_phase (p : ∀ j, κ → M j) {m P : ℕ}
    (hm : 0 < m) (hP : 0 < P) (t : ι → Fin (m+1)) (θ : Sigma M → Fin P) :
    letI : NeZero (m*P) := ⟨Nat.ne_of_gt (Nat.mul_pos hm hP)⟩
    torusGrid (gridLocation p t θ) =
      phase p (fun j => value (t j)) (fun c => (θ c).val/(P:ℝ)) := by
  let : NeZero (m*P) := ⟨Nat.ne_of_gt (Nat.mul_pos hm hP)⟩
  funext k
  simp only [torusGrid, gridLocation, map_sum, phase]
  apply Finset.sum_congr rfl
  intro j _
  rw [ZMod.toAddCircle_natCast]
  congr 1
  simp only [value, Nat.cast_mul]
  ring

omit [DecidableEq ι] [∀ index, Fintype (M index)] [Fintype κ] in
lemma gridLocation_cube (p : ∀ j, κ → M j) {m : ℕ}
    (hm : 0 < m) (k : ℕ) (t : ι → Fin (m+1)) (v : Sigma M → Cube k) :
    letI : NeZero (m*2^k) := ⟨Nat.ne_of_gt (Nat.mul_pos hm (by positivity))⟩
    torusGrid (gridLocation p t (fun c => gridEquiv k (v c))) =
      phase p (fun j => value (t j)) (fun c => scalarCell (v c) 0) := by
  rw [gridLocation_phase p hm (by positivity)]
  congr 1
  funext c
  exact by simpa using (scalarCell_zero_grid (v c)).symm

end LargeIndependentSets.PhaseTest

end OAI
