import OAI.MeasureTheory.Falconer.Shells.ShellMixtures
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem shellEnergy_eq_twice_positive (μ : Measure ℝ) [IsFiniteMeasure μ] (N : ℕ) :
    shellEnergy μ N = 2 *
      ∫ r in Icc ((2:ℝ)^((N:ℝ)-1)) ((2:ℝ)^((N:ℝ)+1)), ‖charFun μ r‖^2 := by
  let a := (2:ℝ)^((N:ℝ)-1)
  let b := (2:ℝ)^((N:ℝ)+1)
  have ha : 0 < a := by dsimp only [a]; positivity
  have hsets : dyadicShell N = Icc a b ∪ Icc (-b) (-a) := by
    ext r
    change (a ≤ |r| ∧ |r| ≤ b) ↔ (a ≤ r ∧ r ≤ b) ∨ (-b ≤ r ∧ r ≤ -a)
    rcases le_total 0 r with h | h
    · rw [abs_of_nonneg h]
      constructor
      · exact Or.inl
      · rintro (h | h)
        · exact h
        · exfalso; linarith
    · rw [abs_of_nonpos h]
      constructor
      · intro h; right; constructor <;> linarith
      · rintro (h | h)
        · exfalso; linarith
        · constructor <;> linarith
  have hdis : Disjoint (Icc a b) (Icc (-b) (-a)) := by
    apply Set.disjoint_left.mpr
    intro r h₀ h₁
    have := h₀.1
    have := h₁.2
    linarith
  have hi (c d : ℝ) : IntegrableOn (fun r => ‖charFun μ r‖^2) (Icc c d) :=
    (continuous_charFun.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hneg : (∫ r in Icc (-b) (-a), ‖charFun μ r‖^2) =
      ∫ r in Icc a b, ‖charFun μ r‖^2 := by
    have hemb : MeasurableEmbedding (fun x : ℝ => -x) := (Homeomorph.neg ℝ).measurableEmbedding
    have h := hemb.setIntegral_map
      (μ := (volume : Measure ℝ)) (fun r => ‖charFun μ r‖^2) (Icc (-b) (-a))
    rw [Measure.map_neg_eq_self] at h
    have hp : (fun x : ℝ => -x) ⁻¹' Icc (-b) (-a) = Icc a b := by
      ext x
      simp only [mem_preimage,mem_Icc]
      constructor <;> intro h <;> constructor <;> linarith
    simpa only [hp,fourier_energy_even] using h
  rw [shellEnergy,hsets,setIntegral_union hdis measurableSet_Icc (hi a b) (hi (-b) (-a)),hneg]
  ring

end PlanarFalconer

end OAI
