import OAI.NumberTheory.JointDickman.Counting.EndpointCoefficientTest

namespace OAI

/-! # A coefficient box chosen from the fixed endpoint alone -/

namespace JointDickman
open Finset

noncomputable def endpointRowScale (T b : ℕ) : ℕ := ⌈(b : ℝ)/(2*T)⌉₊

def EndpointCoefficientWindow (B T b : ℕ) : Prop :=
  ∃ c : ℕ, 0 < c ∧ (B : ℝ) ≤ Real.log c ∧ Real.log c ≤ 2*B ∧
    T*c ≤ b ∧ b ≤ 2*T*c

/-- One box, determined solely by the first coefficient, contains every
possible quotient in its support window. -/
theorem endpointRowScale_window {B T b c : ℕ} (hB : 2 ≤ B) (hT : 0 < T)
    (hc : 0 < c) (hlog : (B : ℝ) ≤ Real.log c)
    (hlo : T*c ≤ b) (hhi : b ≤ 2*T*c) :
    Real.exp ((1/2 : ℝ)*B) ≤ (endpointRowScale T b : ℝ) ∧
      c ∈ Ico (endpointRowScale T b) (4*endpointRowScale T b) ∧
      T*endpointRowScale T b ≤ b := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hcr : (0 : ℝ) < c := by exact_mod_cast hc
  have hlo' : (T : ℝ)*c ≤ b := by exact_mod_cast hlo
  have hhi' : (b : ℝ) ≤ 2*T*c := by exact_mod_cast hhi
  have hqc : endpointRowScale T b ≤ c := by
    apply Nat.ceil_le.mpr
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < 2*T)).mpr (by nlinarith)
  have hbq : (b : ℝ) ≤ (endpointRowScale T b : ℝ)*(2*T) := by
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < 2*T)).mp (Nat.le_ceil _)
  have hcq : (c : ℝ) ≤ 2*(endpointRowScale T b : ℝ) := by nlinarith
  have hq0 : (0 : ℝ) < endpointRowScale T b := by nlinarith
  have hclt : c < 4*endpointRowScale T b := by exact_mod_cast (by nlinarith : (c : ℝ) < 4*(endpointRowScale T b : ℝ))
  have hexp : Real.exp (B : ℝ) ≤ c := (Real.exp_le_exp.mpr hlog).trans_eq (Real.exp_log hcr)
  have hB' : (2 : ℝ) ≤ B := by exact_mod_cast hB
  have he2 : (2 : ℝ) ≤ Real.exp ((1/2 : ℝ)*B) := by
    have hh := Real.add_one_le_exp ((1/2 : ℝ)*B)
    linarith
  have he : Real.exp (B : ℝ) = Real.exp ((1/2 : ℝ)*B)^2 := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  refine ⟨?_,mem_Ico.mpr ⟨hqc,hclt⟩,(Nat.mul_le_mul_left T hqc).trans hlo⟩
  rw [he] at hexp
  nlinarith

/-- All possible endpoint coefficients are in the fixed range needed for
the previously proved prime-product domination. -/
theorem endpointCoefficientWindow_size {B T b : ℕ} (hB : 10 ≤ B)
    (hT : (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B))
    (hw : EndpointCoefficientWindow B T b) :
    (b : ℝ) ≤ Real.exp ((16/5 : ℝ)*B) := by
  obtain ⟨c,hc,_,hcsize,_,hbc⟩ := hw
  have hcr : (0 : ℝ) < c := by exact_mod_cast hc
  have hce : (c : ℝ) ≤ Real.exp (2*B) := by
    rw [← Real.exp_log hcr]
    exact Real.exp_le_exp.mpr hcsize
  have hB' : (10 : ℝ) ≤ B := by exact_mod_cast hB
  have he2 : (2 : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) := by
    have hh := Real.add_one_le_exp ((1/10 : ℝ)*B)
    linarith
  calc
    (b : ℝ) ≤ 2*(T : ℝ)*c := by exact_mod_cast hbc
    _ ≤ Real.exp ((1/10 : ℝ)*B)*Real.exp ((1/10 : ℝ)*B)*Real.exp (2*B) := by
      exact mul_le_mul (mul_le_mul he2 hT (Nat.cast_nonneg T) (Real.exp_pos _).le)
        hce (Nat.cast_nonneg c) (by positivity)
    _ = Real.exp ((11/5 : ℝ)*B) := by
      rw [← Real.exp_add,← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [show (0 : ℝ) ≤ B from Nat.cast_nonneg B])

end JointDickman

end OAI
