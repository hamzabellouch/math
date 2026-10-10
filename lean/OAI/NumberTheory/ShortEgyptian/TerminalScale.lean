import OAI.NumberTheory.ShortEgyptian.TerminalExpansion

namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open scoped BigOperators
open Finset Classical

noncomputable def terminalSteps (S : ℝ) : ℕ := ⌈Real.log S/Real.log (10000/9999:ℝ)⌉₊
noncomputable def terminalLength (S : ℝ) : ℕ := binaryExponent S+1+terminalSteps S
noncomputable def terminalConstant : ℝ := 100000/Real.log 2+1/Real.log (10000/9999:ℝ)+3

lemma terminalSteps_power (S : ℝ) (hS : 0 < S) : S ≤ (10000/9999:ℝ)^terminalSteps S := by
  have hl : 0 < Real.log (10000/9999:ℝ) := Real.log_pos (by norm_num)
  have hh := (div_le_iff₀ hl).mp (Nat.le_ceil (Real.log S/Real.log (10000/9999:ℝ)))
  calc
    S = Real.exp (Real.log S) := (Real.exp_log hS).symm
    _ ≤ Real.exp ((terminalSteps S:ℝ)*Real.log (10000/9999:ℝ)) := Real.exp_le_exp.mpr hh
    _ = _ := by rw [Real.exp_nat_mul,Real.exp_log (show (0:ℝ)<10000/9999 by norm_num)]

lemma terminalLength_bound (S : ℝ) (hlog : 1 ≤ Real.log S) :
    (terminalLength S:ℝ) ≤ terminalConstant*Real.log S := by
  have h₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq : 0 < Real.log (10000/9999:ℝ) := Real.log_pos (by norm_num)
  have ha := Nat.ceil_lt_add_one (show 0 ≤ 100000*Real.log S/Real.log 2 by positivity)
  have hk := Nat.ceil_lt_add_one (show 0 ≤ Real.log S/Real.log (10000/9999:ℝ) by positivity)
  dsimp [terminalLength,binaryExponent,terminalSteps,terminalConstant]
  push_cast
  ring_nf at ha hk ⊢
  linarith

lemma residueSystem_terminal_induction (S : ℝ) (h : ListScale S) (C : ℕ) (R : ResidueSystem S C)
    (k u : ℕ) (hucap : (u:ℝ) ≤ Real.exp (scaleM S:ℝ))
    (hulog : Real.log u ≤ (10000/9999:ℝ)^k) :
    ∃ ns, IsUnitSum ((u:ℚ)/R.M) ns ∧ ns.length ≤ binaryExponent S+1+k := by
  have hM : 0 < R.M := by exact_mod_cast (Real.exp_pos S).trans R.M_lower
  have huM : u < R.M := by
    exact_mod_cast hucap.trans_lt ((Real.exp_le_exp.mpr h.m_bounds.2.2).trans_lt R.M_lower)
  have hb (u : ℕ) (hu : u ≤ 2^binaryExponent S) (hM' : u < R.M) :
      ∃ ns, IsUnitSum ((u:ℚ)/R.M) ns ∧ ns.length ≤ binaryExponent S+1 := by
    obtain ⟨ns,hns,heq,hlen⟩ := binary_unitSum _ R.M u hM R.binary_dvd hu
    refine ⟨ns,isUnitSum_of_positive hns heq ?_,hlen⟩
    exact (div_lt_one (by exact_mod_cast hM : (0:ℚ)<R.M)).mpr (by exact_mod_cast hM')
  induction k generalizing u with
  | zero =>
    have hu : u ≤ 2^binaryExponent S := by
      by_cases hu0 : u = 0
      · subst u; exact Nat.zero_le _
      have hup : 0 < (u:ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hu0)
      have hh := Real.exp_le_exp.mpr hulog
      rw [Real.exp_log hup,pow_zero] at hh
      have hhS : Real.exp 1 ≤ S^100000 := by
        rw [←Real.exp_log (pow_pos h.S_pos 100000),Real.log_pow]
        apply Real.exp_le_exp.mpr
        norm_num
        linarith [h.log_large]
      exact_mod_cast hh.trans (hhS.trans (binary_power_lower S h.S_pos))
    simpa only [Nat.add_zero] using hb u hu huM
  | succ k ih =>
    by_cases husmall : u ≤ 2^binaryExponent S
    · obtain ⟨ns,hns,hlen⟩ := hb u husmall huM
      exact ⟨ns,hns,by omega⟩
    · have hu0 : 0 < u := (Nat.zero_le (2^binaryExponent S)).trans_lt (lt_of_not_ge husmall)
      have hularge : S^100000 < (u:ℝ) := (binary_power_lower S h.S_pos).trans_lt (by exact_mod_cast lt_of_not_ge husmall)
      obtain ⟨t,ht,htM,hres⟩ := R.terminal u hularge hucap
      let v := residue t u (quotient t u)
      have hvu : v < u := (residue_spec ht hu0).1
      have hvM : v < R.M := hvu.trans huM
      have hvcap : (v:ℝ) ≤ Real.exp (scaleM S:ℝ) := (Nat.cast_le.mpr hvu.le).trans hucap
      have hvlog : Real.log v ≤ (10000/9999:ℝ)^k := by
        by_cases hv0 : v = 0
        · simp only [hv0,Nat.cast_zero,Real.log_zero]; positivity
        have hvp : 0 < (v:ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hv0)
        have hup : 0 < (u:ℝ) := by exact_mod_cast hu0
        have hh := Real.log_le_log hvp hres
        rw [Real.log_rpow hup] at hh
        have hp : (9999/10000:ℝ)*(10000/9999:ℝ)^(k+1) = (10000/9999:ℝ)^k := by
          rw [pow_succ]; ring
        exact hh.trans ((mul_le_mul_of_nonneg_left hulog (by norm_num : (0:ℝ)≤9999/10000)).trans_eq hp)
      obtain ⟨ns,hns,hlen⟩ := ih v hvcap hvlog hvM
      have hr : ∃ ns, IsUnitSum ((residue (1*t) u (quotient (1*t) u):ℚ)/(R.M*1)) ns ∧
          ns.length ≤ binaryExponent S+1+k := by simpa only [one_mul,mul_one] using And.intro hns hlen |> fun hh => ⟨ns,hh⟩
      have hh := residue_lift hM (by norm_num : 0 < (1:ℕ)) (by norm_num : 0 < (1:ℕ))
        (dvd_refl 1) hu0 (by simpa using huM) ht htM hr
      simpa only [Nat.cast_one,mul_one,Nat.add_assoc] using hh

lemma residueSystem_terminal (S : ℝ) (h : ListScale S) (C : ℕ) (R : ResidueSystem S C)
    (u : ℕ) (hucap : (u:ℝ) ≤ Real.exp (scaleM S:ℝ)) :
    ∃ ns, IsUnitSum ((u:ℚ)/R.M) ns ∧ ns.length ≤ terminalLength S := by
  apply residueSystem_terminal_induction S h C R (terminalSteps S) u hucap
  by_cases hu : u = 0
  · simp only [hu,Nat.cast_zero,Real.log_zero]; positivity
  have hup : 0 < (u:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hu
  have hh := (Real.log_le_iff_le_exp hup).mpr hucap
  exact hh.trans (h.m_bounds.2.2.trans (terminalSteps_power S h.S_pos))

end ShortEgyptian

end OAI
