import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

namespace FiniteFactor
noncomputable section
/-- One block of the actual coupling, with two distinct width labels. The
boolean records whether this is the tagged block. -/
structure CouplingParameters where
  m : ℝ
  kappa : ℝ
  width : Fin 2 → ℝ
  tagged : Bool
  m_ge : 100 ≤ m
  kappa_nonneg : 0 ≤ kappa
  kappa_le : kappa ≤ 1/100
  width_lower : ∀ i, 1/m ≤ width i
  width_upper : ∀ i, width i ≤ 1/4

namespace CouplingParameters
variable (p : CouplingParameters)

theorem m_pos : 0 < p.m := by linarith [p.m_ge]
theorem width_pos (i : Fin 2) : 0 < p.width i :=
  (one_div_pos.mpr p.m_pos).trans_le (p.width_lower i)

def rho (i : Fin 2) : ℝ := p.kappa * Real.sqrt (p.width i / p.m)
def tagMass : ℝ := if p.tagged then 1/p.m else 0
def diagonalMass : ℝ := 1 - 2*p.rho 0 - 2*p.rho 1 - p.tagMass

theorem rho_nonneg (i : Fin 2) : 0 ≤ p.rho i :=
  mul_nonneg p.kappa_nonneg (Real.sqrt_nonneg _)

theorem rho_le (i : Fin 2) : p.rho i ≤ p.kappa * p.width i := by
  apply mul_le_mul_of_nonneg_left _ p.kappa_nonneg
  apply (Real.sqrt_le_iff).2
  refine ⟨(p.width_pos i).le, ?_⟩
  apply (div_le_iff₀ p.m_pos).2
  have h := (div_le_iff₀ p.m_pos).1 (p.width_lower i)
  nlinarith [p.width_pos i, mul_nonneg (p.width_pos i).le (sub_nonneg.mpr h)]

theorem rho_div_width_le (i : Fin 2) : p.rho i / p.width i ≤ p.kappa :=
  (div_le_iff₀ (p.width_pos i)).2 (p.rho_le i)

theorem rho_energy (i : Fin 2) : (p.rho i)^2 / p.width i = p.kappa^2 / p.m := by
  rw [rho, mul_pow, Real.sq_sqrt (div_nonneg (p.width_pos i).le p.m_pos.le)]
  field_simp [p.m_pos.ne', (p.width_pos i).ne']

theorem tagMass_nonneg : 0 ≤ p.tagMass := by
  unfold tagMass
  split
  · exact div_nonneg zero_le_one p.m_pos.le
  · exact le_rfl

theorem tagMass_le : p.tagMass ≤ 1/100 := by
  unfold tagMass
  split
  · exact one_div_le_one_div_of_le (by norm_num) p.m_ge
  · norm_num

theorem diagonalMass_lower : 98/100 ≤ p.diagonalMass := by
  have h₀ := (p.rho_le 0).trans (mul_le_mul_of_nonneg_left (p.width_upper 0) p.kappa_nonneg)
  have h₁ := (p.rho_le 1).trans (mul_le_mul_of_nonneg_left (p.width_upper 1) p.kappa_nonneg)
  unfold diagonalMass
  linarith [p.kappa_le, p.tagMass_le]

theorem diagonalMass_pos : 0 < p.diagonalMass := by linarith [p.diagonalMass_lower]

theorem diagonalMass_le : p.diagonalMass ≤ 1 := by
  unfold diagonalMass
  linarith [p.rho_nonneg 0, p.rho_nonneg 1, p.tagMass_nonneg]

/-- 0/1 are top/bottom of width 0, 2/3 of width 1, 4 is the tag.
In particular equal numerical widths do not identify labels. -/
def replacementMass : Fin 5 → ℝ :=
  ![p.rho 0, p.rho 0, p.rho 1, p.rho 1, p.tagMass]

def leftLength : Fin 5 → ℝ :=
  ![1-p.width 0/2, p.width 0/2, 1-p.width 1/2, p.width 1/2, 1/p.m]

def rightLength : Fin 5 → ℝ :=
  ![p.width 0/2, 1-p.width 0/2, p.width 1/2, 1-p.width 1/2, 1/p.m]

theorem replacementMass_nonneg (i : Fin 5) : 0 ≤ p.replacementMass i := by
  fin_cases i <;> simp [replacementMass, rho_nonneg, tagMass_nonneg]

theorem mass_sum : p.diagonalMass + ∑ i, p.replacementMass i = 1 := by
  simp [replacementMass, Fin.sum_univ_succ, diagonalMass]
  ring

theorem leftLength_pos (i : Fin 5) : 0 < p.leftLength i := by
  have h₀ := p.width_pos 0
  have h₁ := p.width_pos 1
  have hu₀ := p.width_upper 0
  have hu₁ := p.width_upper 1
  have hm := one_div_pos.mpr p.m_pos
  fin_cases i <;> simp [leftLength] <;> linarith [p.m_pos]

theorem rightLength_pos (i : Fin 5) : 0 < p.rightLength i := by
  have h₀ := p.width_pos 0
  have h₁ := p.width_pos 1
  have hu₀ := p.width_upper 0
  have hu₁ := p.width_upper 1
  have hm := one_div_pos.mpr p.m_pos
  fin_cases i <;> simp [rightLength] <;> linarith [p.m_pos]

theorem lengths_sum_le (i : Fin 5) : p.leftLength i + p.rightLength i ≤ 1 := by
  have hm : 1/p.m ≤ 1/100 := one_div_le_one_div_of_le (by norm_num) p.m_ge
  simp only [one_div] at hm
  fin_cases i <;> simp [leftLength, rightLength]
  linarith

end CouplingParameters
end
end FiniteFactor

end OAI
