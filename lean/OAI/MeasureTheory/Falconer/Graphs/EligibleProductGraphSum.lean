import OAI.MeasureTheory.Falconer.Graphs.ProductGraphEnergy
import OAI.MeasureTheory.Falconer.Angular.AngularLabelEligibility

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

def graphProductSlotBin (j k : ℕ) (l : Fin 4) : ℕ := ![j,j,k,k] l

def GraphProductEligible (ρ : Fin 4 → Measure Plane) (X : Fin 4 → Set Plane)
    (b : Fin 4 → Plane → UnitCircle → ℂ) (m j k : ℕ) : Prop :=
  ∀ l, AngularLabelEligible (ρ l) (X l) (b l) m (graphProductSlotBin j k l)

theorem angular_label_eligible_of_transform_ne_zero {ρ : Measure Plane} {X : Set Plane}
    {b : Plane → UnitCircle → ℂ} {m j : ℕ} {u : UnitCircle} {M r : ℝ}
    (hu : circleAngularBin m j u ≠ 0) (ht : sourceAngularTransform ρ X M b r u ≠ 0) :
    AngularLabelEligible ρ X b m j := by
  by_contra h
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hu) ht (ineligible_transform_zero h M r u)

theorem sourceGraphFourTransform_product_eligible_of_ne_zero
    (ρ : Fin 4 → Measure Plane) (X : Fin 4 → Set Plane) (M : Fin 4 → ℝ)
    (b : Fin 4 → Plane → UnitCircle → ℂ) (plus : Bool) (m j k : ℕ) (r : ℝ) (u w : UnitCircle)
    (hn : sourceGraphFourTransform ρ X M b (graphProductWeight plus m j k) r u w ≠ 0) :
    GraphProductEligible ρ X b m j k := by
  have h := hn
  simp only [sourceGraphFourTransform,mul_ne_zero_iff,map_ne_zero] at h
  obtain ⟨⟨hW,h0,h1⟩,h2,h3⟩ := h
  have hu : circleAngularBin m j u ≠ 0 := by
    intro hz
    exact hW (by simp [graphProductWeight,graphBinWeight,hz])
  have hw : circleAngularBin m k w ≠ 0 := by
    intro hz
    exact hW (by simp [graphProductWeight,graphBinWeight,hz])
  intro l
  fin_cases l
  · exact angular_label_eligible_of_transform_ne_zero hu h0
  · exact angular_label_eligible_of_transform_ne_zero hu h1
  · exact angular_label_eligible_of_transform_ne_zero hw h2
  · exact angular_label_eligible_of_transform_ne_zero hw h3

theorem graphOriginalProductTerm_zero_of_ineligible
    (ρ : Fin 4 → Measure Plane) (X : Fin 4 → Set Plane) (M : Fin 4 → ℝ)
    (b : Fin 4 → Plane → UnitCircle → ℂ) (plus : Bool) (axis θ v : ℝ) (j k : ℕ) (Ψ : ℝ → ℝ)
    (hn : ¬GraphProductEligible ρ X b (angularBinCount θ) j k) :
    graphOriginalTerm ρ X M b false plus axis θ v j k Ψ = 0 := by
  have hz (r : ℝ) (u w : UnitCircle) :
      sourceGraphFourTransform ρ X M b (graphProductWeight plus (angularBinCount θ) j k) r u w = 0 := by
    by_contra h
    exact hn (sourceGraphFourTransform_product_eligible_of_ne_zero ρ X M b plus _ j k r u w h)
  simp only [graphOriginalTerm,graphSourceWeight,Bool.false_eq_true,↓reduceIte,hz,smul_zero,integral_zero]

def GraphProductIndexEligible (ρ : Fin 4 → Measure Plane) (Q : Fin 4 → DyadicSquare)
    (b : Fin 4 → Plane → UnitCircle → ℂ) (m : ℕ) (e : GraphNonedgeIndex) : Prop :=
  GraphProductEligible ρ (fun l => (graphQuadCells Q e.1 l).carrier) b m e.2.1.1 e.2.1.2

noncomputable def graphProductEligibleIndices (I : Finset GraphNonedgeIndex)
    (ρ : Fin 4 → Measure Plane) (Q : Fin 4 → DyadicSquare)
    (b : Fin 4 → Plane → UnitCircle → ℂ) (m : ℕ) : Finset GraphNonedgeIndex := by
  classical
  exact I.filter (GraphProductIndexEligible ρ Q b m)

theorem graphOriginalProductSum_eligible (I : Finset GraphNonedgeIndex)
    (ρ : Fin 4 → Measure Plane) (Q : Fin 4 → DyadicSquare) (M : Fin 4 → ℝ)
    (b : Fin 4 → Plane → UnitCircle → ℂ) (axis θ v : ℝ) (Ψ : ℝ → ℝ) :
    (∑ e ∈ I, graphOriginalTerm ρ (fun l => (graphQuadCells Q e.1 l).carrier) M b
      false e.2.2 axis θ v e.2.1.1 e.2.1.2 Ψ) =
    ∑ e ∈ graphProductEligibleIndices I ρ Q b (angularBinCount θ),
      graphOriginalTerm ρ (fun l => (graphQuadCells Q e.1 l).carrier) M b
        false e.2.2 axis θ v e.2.1.1 e.2.1.2 Ψ := by
  classical
  unfold graphProductEligibleIndices
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro e he hnot
  apply graphOriginalProductTerm_zero_of_ineligible
  intro h
  exact hnot (Finset.mem_filter.mpr ⟨he,h⟩)

theorem graphProductIndexEligible_witness
    (ρ : Fin 4 → Measure Plane) (Q : Fin 4 → DyadicSquare)
    (b : Fin 4 → Plane → UnitCircle → ℂ) (m : ℕ) (e : GraphNonedgeIndex)
    (he : GraphProductIndexEligible ρ Q b m e) (l : Fin 4)
    (G : Plane → UnitCircle → Prop)
    (hG : ∀ dir, ∀ᵐ x ∂(ρ l).restrict (graphQuadCells Q e.1 l).carrier, b l x dir ≠ 0 → G x dir) :
    ∃ dir ∈ tsupport (circleAngularBin m (graphProductSlotBin e.2.1.1 e.2.1.2 l)),
      ∃ x ∈ (graphQuadCells Q e.1 l).carrier, b l x dir ≠ 0 ∧ G x dir :=
  eligible_label_witness (graphQuadCells Q e.1 l).measurable (he l) G hG

end PlanarFalconer

end OAI
