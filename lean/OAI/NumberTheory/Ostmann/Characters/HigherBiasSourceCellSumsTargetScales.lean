import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceCellSumsTargets

namespace OAI

noncomputable section
namespace Ostmann.Characters.HigherBiasSource

theorem target_shell_ratio_bounds (b T u : ℝ) (hb : 0 < b)
    (hlo : T*Real.exp (-(2*u)) ≤ b) (hhi : b ≤ T*Real.exp (-u)) :
    Real.exp u ≤ T/b ∧ T/b ≤ Real.exp (2*u) := by
  rw [Real.exp_neg,←div_eq_mul_inv] at hlo hhi
  constructor
  · apply (le_div_iff₀ hb).mpr
    have hh := (le_div_iff₀ (Real.exp_pos u)).mp hhi
    nlinarith only [hh]
  · apply (div_le_iff₀ hb).mpr
    have hh := (div_le_iff₀ (Real.exp_pos (2*u))).mp hlo
    nlinarith only [hh]

theorem exists_target_interior_rounding_exponential (c : ℝ) (hc : 0 < c) (R : ℕ) :
    ∃ N : ℕ, 0 < N ∧ ∀ (b T u : ℝ) (a g s r : ℕ),
      1 ≤ b → 0 < g → 0 < s → r ≤ R → b ≤ (a:ℝ) →
      (a:ℝ)+(g:ℝ)*s ≤ 3*b → c*b ≤ (g:ℝ)*s →
      T*Real.exp (-(2*u)) ≤ b → b ≤ T*Real.exp (-u) → (N:ℝ) ≤ Real.exp u →
      ∃ n t : ℕ, r ≤ n ∧ r*s ≤ t ∧ t ≤ (n-r)*s ∧
        |((n*a+g*t:ℕ):ℝ)-T| ≤ (g:ℝ) ∧ Real.exp u/6 ≤ (n:ℝ) ∧
          (n:ℝ) ≤ 2*Real.exp (2*u) := by
  obtain ⟨N,hN,hh⟩ := exists_target_interior_rounding c hc R
  refine ⟨N,hN,?_⟩
  intro b T u a g s r hb hg hs hr ha hu hw hlo hhi hNu
  have hratio := target_shell_ratio_bounds b T u (lt_of_lt_of_le zero_lt_one hb) hlo hhi
  obtain ⟨n,t,hn,htlo,hthi,hterr,hnlo,hnhi⟩ :=
    hh b T a g s r hb hg hs hr ha hu hw (hNu.trans hratio.1)
  refine ⟨n,t,hn,htlo,hthi,hterr,?_,?_⟩
  · have hscaled := div_le_div_of_nonneg_right hratio.1 (by norm_num : (0:ℝ)≤6)
    have he : T/b/6=T/(6*b) := by ring
    rw [he] at hscaled
    exact hscaled.trans hnlo
  · have he : 2*T/b=2*(T/b) := by ring
    rw [he] at hnhi
    exact hnhi.trans (mul_le_mul_of_nonneg_left hratio.2 (by norm_num))

theorem exists_depth_target_interior_rounding (c ε : ℝ) (hc : 0 < c) (hε : 0 < ε) (R : ℕ) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ (b T : ℝ) (a g s r : ℕ),
      1 ≤ b → 0 < g → 0 < s → r ≤ R → b ≤ (a:ℝ) →
      (a:ℝ)+(g:ℝ)*s ≤ 3*b → c*b ≤ (g:ℝ)*s →
      T*Real.exp (-(2*(ε*k))) ≤ b → b ≤ T*Real.exp (-(ε*k)) →
      ∃ n t : ℕ, r ≤ n ∧ r*s ≤ t ∧ t ≤ (n-r)*s ∧
        |((n*a+g*t:ℕ):ℝ)-T| ≤ (g:ℝ) ∧ Real.exp (ε*k)/6 ≤ (n:ℝ) ∧
          (n:ℝ) ≤ 2*Real.exp (2*(ε*k)) := by
  obtain ⟨N,hN,hh⟩ := exists_target_interior_rounding_exponential c hc R
  obtain ⟨K,hK⟩ := exists_nat_gt (Real.log (N:ℝ)/ε)
  refine ⟨K,?_⟩
  intro k hk b T a g s r hb hg hs hr ha hu hw hlo hhi
  have hNe : (N:ℝ) ≤ Real.exp (ε*k) := by
    have hN0 : (0:ℝ) < N := by exact_mod_cast hN
    rw [←Real.exp_log hN0]
    apply Real.exp_le_exp.mpr
    have hlog := (div_lt_iff₀ hε).mp hK
    have hkc : (K:ℝ) ≤ k := by exact_mod_cast hk
    nlinarith only [hlog,mul_le_mul_of_nonneg_left hkc hε.le]
  exact hh b T (ε*k) a g s r hb hg hs hr ha hu hw hlo hhi hNe

end Ostmann.Characters.HigherBiasSource

end

end OAI
