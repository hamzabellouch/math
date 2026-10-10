import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Sphere.SphereAmbient2

namespace OAI

/-! Graph energies and pair estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace CurrentFalconer
open Set MeasureTheory
open scoped ComplexConjugate ContDiff

lemma GraphSymbolJet.conj {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {b : V → V → ℂ} {m : ℕ} {s B : ℝ}
    (h : GraphSymbolJet b m s B) : GraphSymbolJet (fun x w => conj (b x w)) m s B := by
  refine ⟨Complex.continuous_conj.measurable.comp h.measurable,
    fun x => Complex.conjCLE.contDiff.comp (h.smooth x), h.nonneg, ?_⟩
  intro x j hj w hw
  have he := Complex.conjLIE.norm_iteratedFDeriv_comp_left (b x) w j
  change ‖iteratedFDeriv ℝ j (Complex.conjLIE ∘ b x) w‖ ≤ _
  rw [he]
  exact h.bound x j hj w hw

lemma GraphSymbolJet.mono_order {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {b : V → V → ℂ} {m n : ℕ} {s B : ℝ}
    (h : GraphSymbolJet b m s B) (hn : n ≤ m) : GraphSymbolJet b n s B :=
  ⟨h.measurable,h.smooth,h.nonneg,fun x j hj w hw => h.bound x j (hj.trans hn) w hw⟩

lemma GraphSymbolJet.mono_bound {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {b : V → V → ℂ} {m : ℕ} {s B C : ℝ}
    (h : GraphSymbolJet b m s B) (hs : 0 ≤ s) (hBC : B ≤ C) : GraphSymbolJet b m s C :=
  ⟨h.measurable,h.smooth,h.nonneg.trans hBC,fun x j hj w hw =>
    (h.bound x j hj w hw).trans (mul_le_mul_of_nonneg_right hBC (pow_nonneg hs _))⟩
end CurrentFalconer
end
end

end OAI
