import Mathlib
import OAI.Probability.SKBarriers.Parisi.QuantileMinimizer

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def supportedCDFQuantile (α : StieltjesFunction ℝ) (t : ℝ) : ℝ :=
  sInf {x : ℝ | x ∈ Icc 0 1 ∧ t ≤ α x}

theorem supportedCDFQuantile_properties (α : StieltjesFunction ℝ)
    (hα1 : α 1=1) {t : ℝ} (ht : t ≤ 1) :
    supportedCDFQuantile α t ∈ Icc (0:ℝ) 1 ∧ t ≤ α (supportedCDFQuantile α t) := by
  let S : Set ℝ := {x | x ∈ Icc 0 1 ∧ t ≤ α x}
  have hn : S.Nonempty := ⟨1,⟨⟨zero_le_one,le_rfl⟩,by simpa only [hα1] using ht⟩⟩
  have hb : BddBelow S := ⟨0,fun x hx => hx.1.1⟩
  have hq : supportedCDFQuantile α t ∈ Icc (0:ℝ) 1 :=
    ⟨le_csInf hn (fun x hx => hx.1.1),csInf_le hb ⟨⟨zero_le_one,le_rfl⟩,by simpa only [hα1] using ht⟩⟩
  refine ⟨hq,?_⟩
  rw [← α.iInf_Ioi_eq (supportedCDFQuantile α t)]
  apply le_ciInf
  intro x
  obtain ⟨y,hy,hyx⟩ := exists_lt_of_csInf_lt hn x.2
  exact hy.2.trans (α.mono hyx.le)

theorem supportedCDFQuantile_le_iff (α : StieltjesFunction ℝ) (hα1 : α 1=1)
    {t x : ℝ} (ht : t ≤ 1) (hx : x ∈ Icc (0:ℝ) 1) :
    supportedCDFQuantile α t ≤ x ↔ t ≤ α x := by
  constructor
  · intro h
    exact (supportedCDFQuantile_properties α hα1 ht).2.trans (α.mono h)
  · intro h
    exact csInf_le ⟨0,fun _ hy => hy.1.1⟩ ⟨hx,h⟩

theorem supportedCDFQuantile_monotoneOn (α : StieltjesFunction ℝ) (hα1 : α 1=1) :
    MonotoneOn (supportedCDFQuantile α) (Iic 1) := by
  intro a ha b hb hab
  apply (supportedCDFQuantile_le_iff α hα1 ha
    (supportedCDFQuantile_properties α hα1 hb).1).mpr
  exact hab.trans (supportedCDFQuantile_properties α hα1 hb).2

def uniformCDFQuantiles (k : ℕ) (α : StieltjesFunction ℝ) (j : Fin (k+1)) : ℝ :=
  supportedCDFQuantile α (((j.val:ℝ)+1)/((k+1:ℕ):ℝ))

theorem uniformCDFQuantiles_admissible (k : ℕ) (α : StieltjesFunction ℝ) (hα1 : α 1=1) :
    uniformCDFQuantiles k α ∈ admissibleQuantiles k := by
  have ht (j : Fin (k+1)) : ((j.val:ℝ)+1)/((k+1:ℕ):ℝ) ≤ 1 := by
    apply (div_le_one (by positivity : (0:ℝ)<(k+1:ℕ))).mpr
    exact_mod_cast j.isLt
  constructor
  · intro i j hij
    exact supportedCDFQuantile_monotoneOn α hα1 (ht i) (ht j)
      (div_le_div_of_nonneg_right (by exact_mod_cast Nat.add_le_add_right hij 1) (by positivity))
  · intro j
    exact (supportedCDFQuantile_properties α hα1 (ht j)).1

end SK.Analytic

end
end

end OAI
