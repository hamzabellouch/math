import OAI.MeasureTheory.Falconer.Estimates.FinitePartitionMask
import OAI.MeasureTheory.Falconer.Shells.PartitionEndpointDistance

namespace OAI

/-! # A measurable mask on a pair of finite disjoint spatial partitions -/

namespace Falconer
open Set MeasureTheory
variable {d : ℕ} {ι κ : Type*}

theorem product_regions_disjoint (F : Finset ι) (G : Finset κ)
    (S : ι → Set (Space d)) (T : κ → Set (Space d))
    (hS : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (S i) (S j))
    (hT : ∀ i ∈ G, ∀ j ∈ G, i ≠ j → Disjoint (T i) (T j)) :
    ∀ i ∈ F.product G, ∀ j ∈ F.product G, i ≠ j →
      Disjoint (S i.1 ×ˢ T i.2) (S j.1 ×ˢ T j.2) := by
  intro i hi j hj hij
  obtain ⟨hi₁,hi₂⟩ := Finset.mem_product.mp hi
  obtain ⟨hj₁,hj₂⟩ := Finset.mem_product.mp hj
  apply Set.disjoint_left.mpr
  intro z hzi hzj
  by_cases h : i.1 = j.1
  · have hne : i.2 ≠ j.2 := fun h' => hij (Prod.ext h h')
    exact Set.disjoint_left.mp (hT i.2 hi₂ j.2 hj₂ hne) hzi.2 hzj.2
  · exact Set.disjoint_left.mp (hS i.1 hi₁ j.1 hj₁ h) hzi.1 hzj.1

noncomputable def productPartitionMask (F : Finset ι) (G : Finset κ)
    (S : ι → Set (Space d)) (T : κ → Set (Space d))
    (B C : ι × κ → Space d → Space d → ℝ) : Space d × Space d → ℝ :=
  finitePartitionMask (F.product G) (fun i => S i.1 ×ˢ T i.2)
    (fun i => endpointPairMask (B i) (C i))

theorem productPartitionMask_measurable (F : Finset ι) (G : Finset κ)
    (S : ι → Set (Space d)) (T : κ → Set (Space d))
    (B C : ι × κ → Space d → Space d → ℝ)
    (hS : ∀ i ∈ F, MeasurableSet (S i)) (hT : ∀ i ∈ G, MeasurableSet (T i))
    (hB : ∀ i ∈ F.product G, Measurable (Function.uncurry (B i)))
    (hC : ∀ i ∈ F.product G, Measurable (Function.uncurry (C i))) :
    Measurable (productPartitionMask F G S T B C) :=
  finitePartitionMask_measurable _ _ _
    (fun i hi => (hS i.1 (Finset.mem_product.mp hi).1).prod (hT i.2 (Finset.mem_product.mp hi).2))
    (fun i hi => endpointPairMask_measurable (B i) (C i) (hB i hi) (hC i hi))

theorem productPartitionMask_bounds (F : Finset ι) (G : Finset κ)
    (S : ι → Set (Space d)) (T : κ → Set (Space d))
    (B C : ι × κ → Space d → Space d → ℝ)
    (hS : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (S i) (S j))
    (hT : ∀ i ∈ G, ∀ j ∈ G, i ≠ j → Disjoint (T i) (T j))
    (hB : ∀ i ∈ F.product G, ∀ x w, B i x w ∈ Icc (0:ℝ) 1)
    (hC : ∀ i ∈ F.product G, ∀ x w, C i x w ∈ Icc (0:ℝ) 1)
    (z : Space d × Space d) : productPartitionMask F G S T B C z ∈ Icc (0:ℝ) 1 := by
  apply finitePartitionMask_bounds _ _ _ (product_regions_disjoint F G S T hS hT)
  intro i hi z
  have hb := hB i hi z.1 (NormedSpace.normalize (z.1-z.2))
  have hc := hC i hi z.2 (NormedSpace.normalize (z.1-z.2))
  exact ⟨mul_nonneg hb.1 hc.1,(mul_le_mul hb.2 hc.2 hc.1 zero_le_one).trans_eq (one_mul 1)⟩

theorem productPartitionMask_eq_one (F : Finset ι) (G : Finset κ)
    (S : ι → Set (Space d)) (T : κ → Set (Space d))
    (B C : ι × κ → Space d → Space d → ℝ)
    (hS : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (S i) (S j))
    (hT : ∀ i ∈ G, ∀ j ∈ G, i ≠ j → Disjoint (T i) (T j))
    {z : Space d × Space d} (hzS : z.1 ∈ ⋃ i ∈ F, S i) (hzT : z.2 ∈ ⋃ i ∈ G, T i)
    (hB : ∀ i ∈ F.product G, z.1 ∈ S i.1 → z.2 ∈ T i.2 →
      B i z.1 (NormedSpace.normalize (z.1-z.2)) = 1)
    (hC : ∀ i ∈ F.product G, z.1 ∈ S i.1 → z.2 ∈ T i.2 →
      C i z.2 (NormedSpace.normalize (z.1-z.2)) = 1) :
    productPartitionMask F G S T B C z = 1 := by
  obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp hzS
  obtain ⟨j,hj,hyj⟩ := mem_iUnion₂.mp hzT
  have hij : (i,j) ∈ F.product G := Finset.mem_product.mpr ⟨hi,hj⟩
  rw [productPartitionMask,finitePartitionMask_on _ _ _
    (product_regions_disjoint F G S T hS hT) hij ⟨hxi,hyj⟩]
  simp only [endpointPairMask,hB (i,j) hij hxi hyj,hC (i,j) hij hxi hyj,mul_one]

end Falconer

end OAI
