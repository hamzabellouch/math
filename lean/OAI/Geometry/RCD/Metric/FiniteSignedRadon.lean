import OAI.Geometry.RCD.Coordinates.WeightedBilinearMeasure
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym

namespace OAI

/-! # Radon–Nikodym derivatives of finite signed coordinate sums -/

open Set Filter MeasureTheory
open scoped BigOperators

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]

omit [SigmaFinite μ] in
lemma signed_rnDeriv_zero : (0 : SignedMeasure X).rnDeriv μ = fun _ => 0 := by
  funext x
  simp only [SignedMeasure.rnDeriv_def,SignedMeasure.toJordanDecomposition_zero,
    JordanDecomposition.zero_posPart,JordanDecomposition.zero_negPart,sub_self]

lemma signed_rnDeriv_sum {ι : Type*} (s : Finset ι) (ν : ι → SignedMeasure X) :
    (∑ i ∈ s, ν i).rnDeriv μ =ᵐ[μ] fun x => ∑ i ∈ s, (ν i).rnDeriv μ x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,signed_rnDeriv_zero]
             exact Filter.EventuallyEq.rfl
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      filter_upwards [SignedMeasure.rnDeriv_add (ν i) (∑ j ∈ s, ν j) μ,ih] with x hx hy
      simpa only [Pi.add_apply,hy] using hx

lemma signed_rnDeriv_sum_smul {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (ν : ι → SignedMeasure X) :
    (∑ i ∈ s, c i • ν i).rnDeriv μ =ᵐ[μ] fun x => ∑ i ∈ s, c i*(ν i).rnDeriv μ x := by
  classical
  have h (i : ι) := SignedMeasure.rnDeriv_smul (ν i) μ (c i)
  have ha : ∀ᵐ x ∂μ, ∀ i ∈ s, (c i • ν i).rnDeriv μ x=c i*(ν i).rnDeriv μ x := by
    apply (ae_ball_iff s.countable_toSet).mpr
    intro i _
    exact (h i).mono fun x hx => by simpa only [Pi.smul_apply,smul_eq_mul] using hx
  filter_upwards [signed_rnDeriv_sum μ s (fun i => c i • ν i),ha] with x hx hy
  rw [hx]
  exact Finset.sum_congr rfl hy

end RegularPointCoordinates

end

end OAI
