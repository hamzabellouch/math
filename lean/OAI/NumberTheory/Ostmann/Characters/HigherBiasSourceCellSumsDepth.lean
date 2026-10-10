import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceCellSums
import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceCellSumsTargetScales

namespace OAI

noncomputable section
namespace Ostmann.Characters.HigherBiasSource

theorem exists_good_cell_target_lists_at_depth (c ε : ℝ) (hc : 0<c) (hε : 0<ε) :
    ∃ b0 : ℝ, 1≤b0 ∧ ∃ K : ℕ, ∀ k : ℕ, K≤k →
      ∀ (b T : ℝ) (I : Finset ℤ), b0≤b →
      (∀ x∈I,b≤(x:ℝ) ∧ (x:ℝ)≤Real.exp 1*b) → c*b≤(I.card:ℝ) →
      T*Real.exp (-(2*(ε*k)))≤b → b≤T*Real.exp (-(ε*k)) →
      ∃ l : List ℤ, (∀ x∈l,x∈I) ∧ |(l.sum:ℝ)-T|≤6/c ∧
        Real.exp (ε*k)/6≤(l.length:ℝ) ∧ (l.length:ℝ)≤2*Real.exp (2*(ε*k)) := by
  obtain ⟨b0,hb0,N,hN,hlist⟩ := exists_good_cell_target_lists c hc
  obtain ⟨K,hK⟩ := exists_nat_gt (Real.log (N:ℝ)/ε)
  refine ⟨b0,hb0,K,?_⟩
  intro k hk b T I hb hband hcard hlo hhi
  have hratio := target_shell_ratio_bounds b T (ε*k)
    (lt_of_lt_of_le zero_lt_one (hb0.trans hb)) hlo hhi
  have hNE : (N:ℝ)≤Real.exp (ε*k) := by
    rw [←Real.exp_log (by exact_mod_cast hN : (0:ℝ)<N)]
    apply Real.exp_le_exp.mpr
    have hh := (div_lt_iff₀ hε).mp hK
    have hkc : (K:ℝ)≤k := by exact_mod_cast hk
    nlinarith [mul_le_mul_of_nonneg_left hkc hε.le]
  obtain ⟨l,hmem,herr,hlenlo,hlenhi⟩ := hlist b T I hb hband hcard (hNE.trans hratio.1)
  refine ⟨l,hmem,herr,?_,?_⟩
  · have hh := div_le_div_of_nonneg_right hratio.1 (by norm_num : (0:ℝ)≤6)
    have he : T/b/6=T/(6*b) := by ring
    rw [he] at hh
    exact hh.trans hlenlo
  · have he : 2*T/b=2*(T/b) := by ring
    rw [he] at hlenhi
    exact hlenhi.trans (mul_le_mul_of_nonneg_left hratio.2 (by norm_num))

end Ostmann.Characters.HigherBiasSource

end

end OAI
