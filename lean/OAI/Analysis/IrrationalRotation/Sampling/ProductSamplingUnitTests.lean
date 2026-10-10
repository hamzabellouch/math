import OAI.Analysis.IrrationalRotation.Sampling.ProductSamplingTestAlmostSure

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace Invariant233.ProductModel.SamplingWeights

theorem testedCoordinateWeight_univ_eq_Ico (endpoint : Bool)
    (I : Finset ℕ) (h α : ℝ) (i : ℕ) {s : ℝ}
    (hs : s ∈ Ico (0 : ℝ) 1) (t : ℝ) :
    testedCoordinateWeight endpoint I h α i univ univ s t =
      testedCoordinateWeight endpoint I h α i (Ico 0 1) (Ico 0 1) s t := by
  have hadd : Int.fract (s + t) ∈ Ico (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have hsub : Int.fract (s - t) ∈ Ico (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  cases endpoint <;> simp [testedCoordinateWeight, hs, hadd, hsub]

theorem testedProduct_univ_eq_Ico (endpoint : Bool) (D I : Finset ℕ)
    (h α : ℝ) (θ : ℕ → ℝ) (n : ℕ) (x : Base) :
    testedProduct endpoint D I h α (fun _ => univ) (fun _ => univ) θ n x =
      testedProduct endpoint D I h α (fun _ => Ico 0 1) (fun _ => Ico 0 1) θ n x := by
  apply Finset.prod_congr rfl
  intro i _
  exact testedCoordinateWeight_univ_eq_Ico endpoint I h α i
    (ProductCocycle.representative_mem_Ico (x i)) _

theorem testedIdeal_univ_eq_Ico (endpoint : Bool) (D I : Finset ℕ)
    (h α : ℝ) (x : Base) :
    testedIdeal endpoint D I h α (fun _ => univ) (fun _ => univ) x =
      testedIdeal endpoint D I h α (fun _ => Ico 0 1) (fun _ => Ico 0 1) x := by
  apply Finset.prod_congr rfl
  intro i _
  apply intervalIntegral.integral_congr
  intro t _
  exact testedCoordinateWeight_univ_eq_Ico endpoint I h α i
    (ProductCocycle.representative_mem_Ico (x i)) t

theorem sourceTestedError_univ_eq_Ico (p : ProductScaleData) (N : ℕ → Finset ℕ)
    (endpoint : Bool) (I : Finset ℕ) (j : ℕ) (θ : ℕ → ℝ) :
    sourceTestedError p N endpoint I (fun _ => univ) (fun _ => univ) j θ =
      sourceTestedError p N endpoint I (fun _ => Ico 0 1) (fun _ => Ico 0 1) j θ := by
  funext x
  simp only [sourceTestedError, testedProduct_univ_eq_Ico, testedIdeal_univ_eq_Ico]

theorem sourceTestedError_energy_univ_eq_Ico (p : ProductScaleData)
    (N : ℕ → Finset ℕ) (endpoint : Bool) (I : Finset ℕ) (j : ℕ) (θ : ℕ → ℝ) :
    (∫ x, (sourceTestedError p N endpoint I (fun _ => univ) (fun _ => univ)
      j θ x) ^ 2 ∂baseMeasure) =
    ∫ x, (sourceTestedError p N endpoint I (fun _ => Ico 0 1) (fun _ => Ico 0 1)
      j θ x) ^ 2 ∂baseMeasure := by
  rw [sourceTestedError_univ_eq_Ico]

end Invariant233.ProductModel.SamplingWeights

end

end OAI
