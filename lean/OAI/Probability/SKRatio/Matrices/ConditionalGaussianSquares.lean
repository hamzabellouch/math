import Mathlib
import OAI.Probability.SKRatio.Matrices.WeightedGaussianSquares

namespace OAI

section
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set Real
namespace SKRatio.MatrixNet
open SKRatioClock.Regression
attribute [local instance] Classical.propDecidable

lemma weighted_square_product_tail {A u c : ℝ}
    (ht : ∀ {ι : Type} [Fintype ι] (s : Finset ι) (a : ι → ℝ),
      (∀ i∈s, |a i|≤A) → ∀ {n : ℕ}, 0<n → s.card≤n →
      standardArrayLaw ι {z | u ≤ |(∑ i∈s, a i*(z i^2-1))/(n:ℝ)|} ≤
        ENNReal.ofReal (3*exp (-c*n)))
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {ι : Type} [Fintype ι] (s : Finset ι) (a : Ω → ι → ℝ)
    (hma : ∀ i, Measurable (fun ω => a ω i)) (ha : ∀ ω i, i∈s → |a ω i|≤A)
    {n : ℕ} (hn : 0<n) (hc : s.card≤n) :
    (μ.prod (standardArrayLaw ι)) {p | u ≤ |(∑ i∈s, a p.1 i*(p.2 i^2-1))/(n:ℝ)|} ≤
      ENNReal.ofReal (3*exp (-c*n)) := by
  have hE : MeasurableSet {p : Ω × (ι → ℝ) |
      u ≤ |(∑ i∈s, a p.1 i*(p.2 i^2-1))/(n:ℝ)|} := by
    apply measurableSet_le measurable_const
    apply Measurable.abs
    apply Measurable.div_const
    exact Finset.measurable_sum _ (fun i _ => ((hma i).comp measurable_fst).mul
      (((measurable_pi_apply i).comp measurable_snd).pow_const 2 |>.sub measurable_const))
  rw [Measure.prod_apply hE]
  calc
    _ ≤ ∫⁻ _ω : Ω, ENNReal.ofReal (3*exp (-c*n)) ∂μ :=
      lintegral_mono (fun ω => ht s (a ω) (ha ω) hn hc)
    _ = _ := by simp

theorem weighted_square_conditioned_tail {A u : ℝ} (hA : 0≤A) (hu : 0<u) :
    ∃ c : ℝ, 0<c ∧ ∀ {ι : Type} [Fintype ι] (s : Finset ι)
      (a : ({i // i∉s} → ℝ) → s → ℝ),
      (∀ i, Measurable (fun y => a y i)) → (∀ y i, |a y i|≤A) →
      ∀ {n : ℕ}, 0<n → s.card≤n →
      standardArrayLaw ι {z | u ≤ |(∑ i : s,
        a (fun j => z j) i * (z i^2-1))/(n:ℝ)|} ≤
          ENNReal.ofReal (3*exp (-c*n)) := by
  classical
  obtain ⟨c,hc,ht⟩ := weighted_standard_square_tail hA hu
  refine ⟨c,hc,?_⟩
  intro ι _ s a hm ha n hn hs
  let E : Set (({i // i∉s} → ℝ) × (s → ℝ)) :=
    {p | u ≤ |(∑ i : s, a p.1 i*(p.2 i^2-1))/(n:ℝ)|}
  have hE : MeasurableSet E := by
    apply measurableSet_le measurable_const
    apply Measurable.abs
    apply Measurable.div_const
    exact Finset.measurable_sum _ (fun i _ => ((hm i).comp measurable_fst).mul
      (((measurable_pi_apply i).comp measurable_snd).pow_const 2 |>.sub measurable_const))
  have hp := measurePreserving_piEquivPiSubtypeProd
    (fun _ : ι => gaussianReal 0 1) (fun i => i∈s)
  have hp' := Measure.measurePreserving_swap.comp hp
  have he : {z : ι → ℝ | u ≤ |(∑ i : s, a (fun j => z j) i*(z i^2-1))/(n:ℝ)|} =
      (fun z => ((fun j : {i // i∉s} => z j), (fun j : s => z j))) ⁻¹' E := rfl
  rw [he]
  have hmap : MeasurePreserving (fun z : ι → ℝ =>
      ((fun j : {i // i∉s} => z j), (fun j : s => z j)))
      (standardArrayLaw ι) ((standardArrayLaw {i // i∉s}).prod (standardArrayLaw s)) := by
    convert! hp' using 1
    dsimp only [standardArrayLaw]
    congr 1
    congr 1
    exact Subsingleton.elim _ _

  rw [hmap.measure_preimage hE.nullMeasurableSet]
  exact weighted_square_product_tail ht (standardArrayLaw {i // i∉s})
    Finset.univ a hm (fun y i _ => ha y i) hn (by simpa using hs)

end SKRatio.MatrixNet

end
end

end OAI
