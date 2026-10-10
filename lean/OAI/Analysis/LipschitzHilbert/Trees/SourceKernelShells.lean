import OAI.Analysis.LipschitzHilbert.Trees.SourceThreeGridMaximal
import OAI.Analysis.LipschitzHilbert.Estimates.PolynomialEnvelope
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

namespace OAI

/-! Dyadic annuli for a reproducing-kernel bound by actual interval
averages. Closed outer intervals and open inner intervals retain every
boundary point. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert

def kernelShell (c r : ℝ) : ℕ → Set ℝ
  | 0 => Icc (c-r) (c+r)
  | n+1 => Icc (c-(2:ℝ)^(n+1)*r) (c+(2:ℝ)^(n+1)*r) \
      Ioo (c-(2:ℝ)^n*r) (c+(2:ℝ)^n*r)

theorem kernelShell_measurable (c r : ℝ) (n : ℕ) : MeasurableSet (kernelShell c r n) := by
  cases n with
  | zero => exact measurableSet_Icc
  | succ n => exact measurableSet_Icc.diff measurableSet_Ioo

theorem kernelShell_subset (c r : ℝ) (n : ℕ) :
    kernelShell c r n⊆Icc (c-(2:ℝ)^n*r) (c+(2:ℝ)^n*r) := by
  cases n with
  | zero => simp only [kernelShell,pow_zero,one_mul,subset_refl]
  | succ n => exact fun _ hx => hx.1

theorem kernelShell_covers (c r : ℝ) (hr : 0<r) :
    (⋃ n, kernelShell c r n)=univ := by
  apply eq_univ_of_forall
  intro x
  by_cases hx : |x-c|≤r
  · have h := abs_le.mp hx
    exact mem_iUnion.mpr ⟨0,by constructor <;> linarith [h.1,h.2]⟩
  · have hd : 1≤|x-c|/r := (le_div_iff₀ hr).mpr (by linarith)
    obtain ⟨n,hlo,hhi⟩ := exists_nat_pow_near hd (by norm_num : (1:ℝ)<2)
    have hlo' := (le_div_iff₀ hr).mp hlo
    have hhi' := (div_lt_iff₀ hr).mp hhi
    refine mem_iUnion.mpr ⟨n+1,?_,?_⟩
    · exact ⟨by linarith [(neg_le_abs (x-c))],by linarith [(le_abs_self (x-c))]⟩
    · intro hin
      have hlt : |x-c|<(2:ℝ)^n*r := abs_lt.mpr ⟨by linarith [hin.1],by linarith [hin.2]⟩
      exact not_lt_of_ge hlo' hlt

theorem kernelShell_lower (c r : ℝ) (hr : 0<r) (n : ℕ) {x : ℝ}
    (hx : x∈kernelShell c r (n+1)) :
    (2:ℝ)^n≤|(x-c)/r| := by
  have hlow : (2:ℝ)^n*r≤|x-c| := by
    by_contra hn
    apply hx.2
    have h := abs_lt.mp (lt_of_not_ge hn)
    exact ⟨by linarith [h.1],by linarith [h.2]⟩
  rw [abs_div,abs_of_pos hr]
  exact (le_div_iff₀ hr).mpr hlow

/-- The inverse quadratic envelope has a geometric shell bound; after
multiplication by shell length, the remaining series has ratio one half. -/
theorem kernelShell_envelope (c r : ℝ) (hr : 0<r) (n : ℕ) {x : ℝ}
    (hx : x∈kernelShell c r n) :
    lineEnvelope c r 1 x≤4/((2:ℝ)^n)^2 := by
  have hden : 0<1+((x-c)/r)^2 := by positivity
  cases n with
  | zero =>
    simp only [pow_zero,one_pow,div_one]
    have h := lineEnvelope_antitone c r x (by omega : 0≤1)
    simp only [lineEnvelope,pow_zero,inv_one] at h
    exact h.trans (by norm_num)
  | succ n =>
    have hlow := kernelShell_lower c r hr n hx
    have hsq := pow_le_pow_left₀ (by positivity : 0≤(2:ℝ)^n) hlow 2
    rw [sq_abs] at hsq
    simp only [lineEnvelope,pow_one]
    rw [inv_eq_one_div,div_le_div_iff₀ hden (sq_pos_of_pos (by positivity))]
    rw [show (2:ℝ)^(n+1)=(2:ℝ)^n*2 by exact pow_succ _ _]
    nlinarith

end LipschitzHilbert

end

end OAI
