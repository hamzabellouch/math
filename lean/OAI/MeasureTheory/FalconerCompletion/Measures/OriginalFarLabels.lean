import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Graphs.NearGrid
import OAI.MeasureTheory.FalconerCompletion.Graphs.ScalarPairSymbol
import OAI.MeasureTheory.FalconerCompletion.Recursion.FarOriginalSet

namespace OAI

/-! Measures and the conditional distance-set completion. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer
open Set MeasureTheory _root_.OAI.GraphLiteralSupport.Attempt4FullFar
open scoped ComplexConjugate

noncomputable def originalFarLabelsND {d : ℕ} (h : ℕ) (A D : Finset (Fin d → ℤ)) :=
  ((A.product A).product (D.product D)).filter fun p =>
    ¬(Attempt4Near.nearGridND h p.1.1 p.1.2 ∧ Attempt4Near.nearGridND h p.2.1 p.2.2)

def originalFarRegionND {d : ℕ} (h : ℕ) (A D : Finset (Fin d → ℤ)) :
    Set ((EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
      (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))) :=
  ⋃ p∈originalFarLabelsND h A D, gridPairSetND h p.1 ×ˢ gridPairSetND h p.2

lemma originalFarRegionND_measurable {d : ℕ} (h : ℕ) (A D : Finset (Fin d → ℤ)) :
    MeasurableSet (originalFarRegionND h A D) := by
  exact Finset.measurableSet_biUnion _ (fun p _ =>
    (gridPairSetND_measurable h p.1).prod (gridPairSetND_measurable h p.2))

lemma original_nonnear_displacementND {d h : ℕ} {P Q : Fin d → ℤ}
    (hPQ : ¬Attempt4Near.nearGridND h P Q)
    {x y : EuclideanSpace ℝ (Fin d)} (hx : x∈ambientGridCell h P) (hy : y∈ambientGridCell h Q) :
    1/(4*(2:ℝ)^h)≤dist x y := by
  have hx' := Attempt4Near.ambientGridCell_dist_le hx (Attempt4Near.ambientGridCenter_mem h P)
  have hy' := Attempt4Near.ambientGridCell_dist_le (Attempt4Near.ambientGridCenter_mem h Q) hy
  have ht : dist (Attempt4Near.ambientGridCenter h P) (Attempt4Near.ambientGridCenter h Q) ≤
      dist (Attempt4Near.ambientGridCenter h P) x+dist x y+dist y (Attempt4Near.ambientGridCenter h Q) := by
    calc
      _ ≤ dist (Attempt4Near.ambientGridCenter h P) x+dist x (Attempt4Near.ambientGridCenter h Q) := dist_triangle _ _ _
      _ ≤ _ := by grw [dist_triangle x y (Attempt4Near.ambientGridCenter h Q)]; ring_nf; exact le_rfl
  have hn := lt_of_not_ge hPQ
  change 10*(d+1:ℝ)/(2:ℝ)^h<dist (Attempt4Near.ambientGridCenter h P) (Attempt4Near.ambientGridCenter h Q) at hn
  have hp : 0<(2:ℝ)^h := by positivity
  have hd : 0≤(d:ℝ)/(2:ℝ)^h := by positivity
  have hi : 0<1/(2:ℝ)^h := by positivity
  rw [mul_div_assoc,add_div] at hn
  have he : 1/(4*(2:ℝ)^h)=(1/(2:ℝ)^h)/4 := by ring
  rw [he]
  rw [add_div] at hx' hy'
  nlinarith

lemma originalFarRegionND_subset {d a h : ℕ} {A D : Finset (Fin d → ℤ)} {X Y : Fin d → ℤ}
    (hA : ∀ p∈A, ambientGridCell h p⊆ambientGridCell a X)
    (hD : ∀ q∈D, ambientGridCell h q⊆ambientGridCell a Y) :
    originalFarRegionND h A D⊆farOriginalSetND a h X Y := by
  intro z hz
  obtain ⟨p,hp,hz⟩ := mem_iUnion₂.mp hz
  obtain ⟨hp,hn⟩ := Finset.mem_filter.mp hp
  obtain ⟨hpA,hpD⟩ := Finset.mem_product.mp hp
  obtain ⟨hpi,hpk⟩ := Finset.mem_product.mp hpA
  obtain ⟨hpj,hpl⟩ := Finset.mem_product.mp hpD
  refine ⟨⟨⟨hA _ hpi hz.1.1,hA _ hpk hz.1.2⟩,⟨hD _ hpj hz.2.1,hD _ hpl hz.2.2⟩⟩,?_⟩
  by_cases hi : Attempt4Near.nearGridND h p.1.1 p.1.2
  · exact (original_nonnear_displacementND (fun hj => hn ⟨hi,hj⟩) hz.2.1 hz.2.2).trans (le_max_right _ _)
  · exact (original_nonnear_displacementND hi hz.1.1 hz.1.2).trans (le_max_left _ _)

lemma original_kernel_integrableND {n : ℕ} {Ψ : ℝ → ℝ} (hmΨ : Measurable Ψ) (hΨ : Integrable Ψ)
    (v : ℝ)
    (b c : (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) → EuclideanSpace ℝ (Fin (n+1)) → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    (η : Measure ((EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) ×
      (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))))) [IsFiniteMeasure η]
    {B C : ℝ} (hB : 0≤B) (hC : 0≤C)
    (hbd : ∀ z w, ‖w‖=1 → ‖b z w‖≤B) (hcd : ∀ z w, ‖w‖=1 → ‖c z w‖≤C) :
    Integrable (euclideanFarKernelND Ψ v b c) η :=
  (physical_kernel_joint_integrableND hmΨ hΨ v b c hb hc η hB hC hbd hcd).integral_prod_right

theorem original_far_kernel_partitionND {d : ℕ}
    (ρ κ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ρ] [IsFiniteMeasure κ]
    (h : ℕ) (A D : Finset (Fin d → ℤ))
    (F : ((EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
      (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))) → ℂ)
    (hF : Integrable F ((ρ.prod ρ).prod (κ.prod κ))) :
    (∫ z in originalFarRegionND h A D, F z ∂(ρ.prod ρ).prod (κ.prod κ)) =
      ∑ p∈originalFarLabelsND h A D, ∫ z, F z ∂(gridPairMeasureND ρ h p.1).prod (gridPairMeasureND κ h p.2) := by
  have hd : (originalFarLabelsND h A D : Set (((Fin d → ℤ) × (Fin d → ℤ)) × ((Fin d → ℤ) × (Fin d → ℤ)))).PairwiseDisjoint
      (fun p => gridPairSetND h p.1 ×ˢ gridPairSetND h p.2) := by
    intro p _ q _ hpq
    apply Set.disjoint_left.mpr
    intro z hp hq
    apply hpq
    apply Prod.ext
    · by_contra hn
      exact Set.disjoint_left.mp (gridPairSetND_disjoint hn) hp.1 hq.1
    · by_contra hn
      exact Set.disjoint_left.mp (gridPairSetND_disjoint hn) hp.2 hq.2
  rw [originalFarRegionND,integral_biUnion_finset _ (fun p _ => (gridPairSetND_measurable h p.1).prod
    (gridPairSetND_measurable h p.2)) hd (fun _ _ => hF.integrableOn)]
  apply Finset.sum_congr rfl
  intro p _
  rw [← Measure.prod_restrict]
  rfl

end CurrentFalconer
end GraphLiteralSupport
end
end

end OAI
