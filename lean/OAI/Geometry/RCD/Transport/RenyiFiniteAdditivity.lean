import OAI.Geometry.RCD.Transport.RenyiDisjointAdditivity
import OAI.Geometry.RCD.Transport.OptimalLengthLaw

namespace OAI

/-! # Finite length decomposition of the Rényi integral -/

open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X]

theorem mutuallySingular_finset_sum_right {ι : Type*} (ν : ι → Measure X)
    (μ : Measure X) (s : Finset ι) (h : ∀ i∈s, μ ⟂ₘ ν i) : μ ⟂ₘ ∑ i∈s, ν i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add_right
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem renyiPower_finset_additive {ι : Type*} (μ : Measure X) [IsFiniteMeasure μ]
    (ν : ι → Measure X) [∀ i, IsFiniteMeasure (ν i)] (s : Finset ι)
    (hs : ∀ i∈s, ∀ j∈s, i≠j → ν i ⟂ₘ ν j) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    (∫ x, ((∑ i∈s, ν i).rnDeriv μ x).toReal^q ∂μ) =
      ∑ i∈s, ∫ x, ((ν i).rnDeriv μ x).toReal^q ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    calc
      _ = ∫ _ : X, (0:ℝ) ∂μ := integral_congr_ae ((Measure.rnDeriv_zero μ).mono
        (fun x hx => by simp [hx,Real.zero_rpow hq0.ne']))
      _ = 0 := integral_zero X ℝ
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have hsep : ν a ⟂ₘ ∑ i∈s, ν i := mutuallySingular_finset_sum_right ν (ν a) s
      (fun i hi => hs a (Finset.mem_insert_self _ _) i (Finset.mem_insert_of_mem hi)
        (fun he => ha (he ▸ hi)))
    rw [renyiPower_add_mutuallySingular μ (ν a) _ hsep hq0 hq1,
      ih (fun i hi j hj hij => hs i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij),
      Finset.sum_insert ha]

end RegularPointCoordinates

end

end OAI
