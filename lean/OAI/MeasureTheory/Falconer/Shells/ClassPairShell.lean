import OAI.MeasureTheory.Falconer.Shells.ClassPairDistance
import OAI.MeasureTheory.Falconer.Shells.FilteredClassShell

namespace OAI

/-! # The assembled class law inherits the local shell bound -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal NNReal
variable {d : ℕ}

theorem regularizationPairDistance_shell_le {k : ℕ} (hdim : 1 ≤ d)
    (Q₁ Q₂ : DyadicCube d) (hQ₁ : 0 < Q₁.side) (hQ₂ : 0 < Q₂.side)
    (μ ν : Measure (Space d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (N B₁ B₂ : ℕ) (t₁ t₂ : ℝ≥0∞) (ht₁ : 0 < t₁) (ht₂ : 0 < t₂) (σ κ : ℝ)
    (p₁ p₂ : List ℕ → CellPath d)
    (he₁ : ∀ T ∈ regularizationIndex Q₁ μ N B₁ t₁, regularizationLabel Q₁ μ N B₁ (p₁ T) = T)
    (he₂ : ∀ T ∈ regularizationIndex Q₂ ν N B₂ t₂, regularizationLabel Q₂ ν N B₂ (p₂ T) = T)
    (c : List ℕ × List ℕ → ℕ) (A D : Fin k → Set (Space d))
    (hm : ∀ j, MeasurableSet (A j) ∧ MeasurableSet (D j))
    (hd : Pairwise fun j l => Disjoint (A j ×ˢ D j) (A l ×ˢ D l))
    {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2)
    {E : ℝ} (hE : 0 ≤ E)
    (hlocal : ∀ i ∈ (regularizationIndex Q₁ μ N B₁ t₁).product (regularizationIndex Q₂ ν N B₂ t₂),
      ∀ j : Fin k,
      (∫ r in Icc ((2:ℝ)^((N:ℝ)-1)) ((2:ℝ)^((N:ℝ)+1)),
        ‖charFun (endpointWeightedDistance ((sourceClass Q₁ μ N B₁ (p₁ i.1)).restrict (A j))
          ((sourceClass Q₂ ν N B₂ (p₂ i.2)).restrict (D j)) 1 1 1
          (sourceOuterMask Q₁ μ N B₁ σ κ (p₁ i.1) (c i))
          (sourceOuterMask Q₂ ν N B₂ σ κ (p₂ i.2) (c i))) r‖^2) ≤ E) :
    PlanarFalconer.shellEnergy
      (regularizationPairDistance Q₁ Q₂ μ ν N B₁ B₂ t₁ t₂ σ κ p₁ p₂ c (⋃ j, A j ×ˢ D j)) N ≤
        2*(k:ℝ)^2*E := by
  let : ∀ T, IsFiniteMeasure (sourceClass Q₁ μ N B₁ (p₁ T)) := fun _ => sourceClass_finite ..
  let : ∀ T, IsFiniteMeasure (sourceClass Q₂ ν N B₂ (p₂ T)) := fun _ => sourceClass_finite ..
  let τ := fun (i : List ℕ × List ℕ) (j : Fin k) =>
    endpointWeightedDistance ((sourceClass Q₁ μ N B₁ (p₁ i.1)).restrict (A j))
      ((sourceClass Q₂ ν N B₂ (p₂ i.2)).restrict (D j)) 1 1 1
      (sourceOuterMask Q₁ μ N B₁ σ κ (p₁ i.1) (c i))
      (sourceOuterMask Q₂ ν N B₂ σ κ (p₂ i.2) (c i))
  let : ∀ i j, IsFiniteMeasure (τ i j) := by
    intro i j
    apply endpointWeightedDistance_finite hdim _ _ zero_lt_one zero_lt_one hδ
      _ _ (fun x w => regularOuterMask_bounds _ _ _ _ _ _ _ x w)
      (fun x w => regularOuterMask_bounds _ _ _ _ _ _ _ x w)
    have hμ : (sourceClass Q₁ μ N B₁ (p₁ i.1)).restrict (A j) ≪ μ :=
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).trans (sourceClass_absolutelyContinuous ..)
    have hν : (sourceClass Q₂ ν N B₂ (p₂ i.2)).restrict (D j) ≪ ν :=
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).trans (sourceClass_absolutelyContinuous ..)
    filter_upwards [(hμ.prod hν).ae_le hsep] with z hz
    simpa only [div_one] using hz
  rw [regularizationPairDistance_eq_mixture Q₁ Q₂ μ ν N B₁ B₂ t₁ t₂ ht₁ ht₂ σ κ p₁ p₂ he₁ he₂ c A D hm hd]
  exact shellEnergy_filter_mixture _ (classPairWeight Q₁ Q₂ μ ν N B₁ B₂) k N τ
    (classPairWeight_sum_le_one Q₁ Q₂ hQ₁ hQ₂ μ ν N B₁ B₂ t₁ t₂) hE hlocal

end Falconer.Regularization

end OAI
