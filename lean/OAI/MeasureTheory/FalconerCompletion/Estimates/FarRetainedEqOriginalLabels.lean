import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Estimates.OriginalCellTransform
import OAI.MeasureTheory.FalconerCompletion.Measures.OriginalFarLabels

namespace OAI

/-! Quantitative estimates for the distance-set construction. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer
open Set MeasureTheory _root_.OAI.GraphLiteralSupport.Attempt4FullFar
open scoped ComplexConjugate

lemma farRetainedND_eq_original_labels {V : Type*} [MeasurableSpace V] {d : ℕ}
    (h : ℕ) (A D : Finset (Fin d → ℤ)) (U W : (Fin d → ℤ) → ℝ × V → ℂ)
    (r : ℝ) (z : V×V) :
    Attempt4Near.farRetainedND h A D U W r z =
      ∑ p∈originalFarLabelsND h A D,
        (U p.1.1 (r,z.1)*W p.2.2 (r,z.2))*conj (U p.1.2 (r,z.1)*W p.2.1 (r,z.2)) := by
  classical
  unfold Attempt4Near.farRetainedND originalFarLabelsND
  rw [Finset.sum_filter]
  simp only [Finset.product_eq_sprod,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro l hl
  have hs : Attempt4Near.nearGridND h l j↔Attempt4Near.nearGridND h j l := Attempt4Near.nearGridND_symm
  simp only [Attempt4Near.nearGridPairND,hs]
  split_ifs <;> simp_all

variable {n : ℕ}

lemma original_far_cross_identityND {Ψ : ℝ → ℝ} (hmΨ : Measurable Ψ) (hΨ : Integrable Ψ)
    (v : ℝ)
    (ρ κ : Measure (EuclideanSpace ℝ (Fin (n+1)))) [IsFiniteMeasure ρ] [IsFiniteMeasure κ]
    (h : ℕ) (A D : Finset (Fin (n+1) → ℤ)) (M N : ℝ)
    (b c : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    {B C : ℝ} (hB : 0≤B) (hC : 0≤C)
    (hbd : ∀ x w, ‖w‖=1 → ‖b x w‖≤B) (hcd : ∀ x w, ‖w‖=1 → ‖c x w‖≤C) :
    (((M*M)*(N*N))⁻¹:ℝ) • (∫ z in originalFarRegionND h A D,
      euclideanFarKernelND Ψ v (scalarPairSymbolND b) (scalarPairSymbolND c) z ∂(ρ.prod ρ).prod (κ.prod κ)) =
    ∑ p∈originalFarLabelsND h A D, ∫ u : ℝ, (Ψ u:ℂ)*
      physicalCrossMomentND ρ (ambientGridCell h p.1.1) (ambientGridCell h p.1.2) M b ((2:ℝ)^v*u)*
      conj (physicalCrossMomentND κ (ambientGridCell h p.2.1) (ambientGridCell h p.2.2) N c ((2:ℝ)^v*u)) := by
  have hbb : ∀ z w, ‖w‖=1 → ‖scalarPairSymbolND b z w‖≤B*B := by
    intro z w hw
    simp only [scalarPairSymbolND,norm_mul,Complex.norm_conj]
    exact mul_le_mul (hbd _ _ hw) (hbd _ _ hw) (norm_nonneg _) hB
  have hcc : ∀ z w, ‖w‖=1 → ‖scalarPairSymbolND c z w‖≤C*C := by
    intro z w hw
    simp only [scalarPairSymbolND,norm_mul,Complex.norm_conj]
    exact mul_le_mul (hcd _ _ hw) (hcd _ _ hw) (norm_nonneg _) hC
  have hi := original_kernel_integrableND hmΨ hΨ v _ _ (scalarPairSymbolND_measurable hb)
    (scalarPairSymbolND_measurable hc) ((ρ.prod ρ).prod (κ.prod κ))
    (mul_nonneg hB hB) (mul_nonneg hC hC) hbb hcc
  rw [original_far_kernel_partitionND ρ κ h A D _ hi,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [gridPairMeasureND_eq_prod,gridPairMeasureND_eq_prod]
  exact physical_cross_energy_identityND hmΨ hΨ v ρ κ _ _ _ _ M N b c hb hc hB hC hbd hcd

theorem original_far_energy_identityND {Ψ : ℝ → ℝ} (hmΨ : Measurable Ψ) (hΨ : Integrable Ψ)
    (v : ℝ)
    (ρ κ : Measure (EuclideanSpace ℝ (Fin (n+1)))) [IsFiniteMeasure ρ] [IsFiniteMeasure κ]
    (h : ℕ) (A D : Finset (Fin (n+1) → ℤ)) (M N : ℝ)
    (b c : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    {B C : ℝ} (hB : 0≤B) (hC : 0≤C)
    (hbd : ∀ x w, ‖w‖=1 → ‖b x w‖≤B) (hcd : ∀ x w, ‖w‖=1 → ‖c x w‖≤C) :
    (((M*M)*(N*N))⁻¹:ℝ) • (∫ z in originalFarRegionND h A D,
      euclideanFarKernelND Ψ v (scalarPairSymbolND b) (scalarPairSymbolND c) z ∂(ρ.prod ρ).prod (κ.prod κ)) =
    ∫ p : ℝ × (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))),
      (Ψ p.1:ℂ)*Attempt4Near.farRetainedND h A D
        (fun i q => originalCellTransformND ρ h M b i ((2:ℝ)^v*q.1,q.2))
        (fun j q => originalCellTransformND κ h N c j ((2:ℝ)^v*q.1,q.2)) p.1 p.2
      ∂volume.prod ((canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1)))).prod
        (canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1))))) := by
  classical
  let V := EuclideanSpace ℝ (Fin (n+1))
  let μ := canonicalSphereMeasureND V
  let U := fun (i : Fin (n+1) → ℤ) (q : ℝ×V) => originalCellTransformND ρ h M b i ((2:ℝ)^v*q.1,q.2)
  let W := fun (j : Fin (n+1) → ℤ) (q : ℝ×V) => originalCellTransformND κ h N c j ((2:ℝ)^v*q.1,q.2)
  have hUm (i) : Measurable (U i) :=
    (sourceAngularTransformND_measurable ρ _ _ hb).comp ((measurable_const.mul measurable_fst).prodMk measurable_snd)
  have hWm (j) : Measurable (W j) :=
    (sourceAngularTransformND_measurable κ _ _ hc).comp ((measurable_const.mul measurable_fst).prodMk measurable_snd)
  let Bs := fun i => |M⁻¹| *(ρ (ambientGridCell h i)).toReal*B
  let Cs := fun j => |N⁻¹| *(κ (ambientGridCell h j)).toReal*C
  have hUb (i) : ∀ r, ∀ᵐ w ∂μ, ‖U i (r,w)‖≤Bs i := by
    intro r
    filter_upwards [canonicalSphereMeasureND_ae_norm] with w hw
    exact sourceAngularTransformND_norm_le ρ _ _ b _ w (fun x => hbd x w hw)
  have hWb (j) : ∀ r, ∀ᵐ w ∂μ, ‖W j (r,w)‖≤Cs j := by
    intro r
    filter_upwards [canonicalSphereMeasureND_ae_norm] with w hw
    exact sourceAngularTransformND_norm_le κ _ _ c _ w (fun x => hcd x w hw)
  let F := fun (p : ((Fin (n+1) → ℤ) × (Fin (n+1) → ℤ)) × ((Fin (n+1) → ℤ) × (Fin (n+1) → ℤ))) (z : ℝ×(V×V)) => (Ψ z.1:ℂ)*
    ((U p.1.1 (z.1,z.2.1)*W p.2.2 (z.1,z.2.2))*conj (U p.1.2 (z.1,z.2.1)*W p.2.1 (z.1,z.2.2)))
  have hFi (p) : Integrable (F p) (volume.prod (μ.prod μ)) :=
    Attempt4Near.angular_four_term_integrableND μ (hUm _) (hUm _) (hWm _) (hWm _)
      (hUb _) (hUb _) (hWb _) (hWb _) hmΨ hΨ
  trans ∑ p∈originalFarLabelsND h A D, ∫ z, F p z ∂volume.prod (μ.prod μ)
  · rw [original_far_cross_identityND hmΨ hΨ v ρ κ h A D M N b c hb hc hB hC hbd hcd]
    apply Finset.sum_congr rfl
    intro p hp
    rw [integral_prod _ (hFi p)]
    apply integral_congr_ae
    filter_upwards with u
    dsimp [F]
    rw [integral_const_mul]
    have he : (fun z : V×V => (U p.1.1 (u,z.1)*W p.2.2 (u,z.2))*
        conj (U p.1.2 (u,z.1)*W p.2.1 (u,z.2))) =
      (fun z : V×V => (U p.1.1 (u,z.1)*conj (U p.1.2 (u,z.1)))*
        conj (W p.2.1 (u,z.2)*conj (W p.2.2 (u,z.2)))) := by
      funext z
      simp only [map_mul,Complex.conj_conj]
      ring
    rw [he,integral_prod_mul
      (fun w : V => U p.1.1 (u,w)*conj (U p.1.2 (u,w)))
      (fun w : V => conj (W p.2.1 (u,w)*conj (W p.2.2 (u,w)))),integral_conj]
    exact mul_assoc _ _ _
  · rw [← integral_finsetSum _ (fun p _ => hFi p)]
    apply integral_congr_ae
    filter_upwards with z
    rw [farRetainedND_eq_original_labels,Finset.mul_sum]

end CurrentFalconer
end GraphLiteralSupport
end
end

end OAI
