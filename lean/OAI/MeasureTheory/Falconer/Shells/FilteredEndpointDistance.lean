import OAI.MeasureTheory.Falconer.Shells.EndpointWeightedDistance
import OAI.MeasureTheory.Falconer.Fourier.ProductFilterIntegral

namespace OAI

/-! # Exact masked distance decomposition over a Borel product filter -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

noncomputable def filteredEndpointDistance (μ ν : Measure (Space d))
    (Γ : Set (Space d × Space d)) (B C : Space d → Space d → ℝ) : Measure ℝ :=
  (((μ.prod ν).restrict Γ).withDensity (fun z => ENNReal.ofReal (endpointDistanceWeight 1 B C z))).map
    (fun z => dist z.1 z.2)

 theorem filteredEndpointDistance_product_sum {ι : Type*} [Fintype ι]
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (A D : ι → Set (Space d))
    (hm : ∀ i, MeasurableSet (A i) ∧ MeasurableSet (D i))
    (hd : Pairwise fun i j => Disjoint (A i ×ˢ D i) (A j ×ˢ D j))
    (B C : Space d → Space d → ℝ) :
    filteredEndpointDistance μ ν (⋃ i, A i ×ˢ D i) B C =
      ∑ i, endpointWeightedDistance (μ.restrict (A i)) (ν.restrict (D i)) 1 1 1 B C := by
  classical
  unfold filteredEndpointDistance endpointWeightedDistance
  simp only [inv_one,one_mul]
  rw [finite_product_restriction μ ν A D hm hd,← Measure.sum_fintype,
    withDensity_sum,Measure.map_sum (by fun_prop),Measure.sum_fintype]

 theorem HasBorelProductPartition.masked_distance_sum
    {Γ : Set (Space d × Space d)} {K : ℝ} (hΓ : HasBorelProductPartition Γ K)
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (B C : Space d → Space d → ℝ) :
    ∃ n : ℕ, (n:ℝ) ≤ K ∧ ∃ A D : Fin n → Set (Space d),
      (∀ i, MeasurableSet (A i) ∧ MeasurableSet (D i)) ∧
      filteredEndpointDistance μ ν Γ B C =
        ∑ i, endpointWeightedDistance (μ.restrict (A i)) (ν.restrict (D i)) 1 1 1 B C := by
  obtain ⟨n,hn,A,D,hm,hd,rfl⟩ := hΓ
  exact ⟨n,hn,A,D,hm,filteredEndpointDistance_product_sum μ ν A D hm hd B C⟩

end Falconer

end OAI
