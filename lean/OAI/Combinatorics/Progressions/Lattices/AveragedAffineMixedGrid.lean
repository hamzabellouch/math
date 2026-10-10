import OAI.Combinatorics.Progressions.Lattices.AveragedAffineGrid

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem averagedAffine_mixed_grid_error
    {P : Type*} [Fintype P]
    {W D G Z α : Type*} [MeasurableSpace W] [Fintype D] [Fintype α] [DecidableEq α]
    {B O J N : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
    [∀ d, Fintype (J d)] [∀ d, Fintype (N d)]
    (h : D → ℕ) (eK : ∀ d, J d → SamplerTupleIndex G B h →₀ ℕ)
    (eN : ∀ d, N d → SamplerTupleIndex G B h →₀ ℕ)
    (index : ∀ d, B d → J d ⊕ N d)
    (s : ∀ d, O d ↪ J d) (A : ∀ d, (O d → ℝ) ≃L[ℝ] (O d → ℝ))
    (F : ∀ d, (UnselectedColumn (s d) → ℝ) →L[ℝ] (O d → ℝ))
    (sets : ∀ d, O d → Finset α) (extra : G → Option α → Z)
    (c w : ∀ d, J d ⊕ N d → ℝ) (z : W → Z → ℝ)
    (hz : ∀ j, Measurable (fun a => z a j))
    (hw : ∀ d j, 0 < w d j) (R : D → ℝ≥0) (hsupport : ∀ d j, |c d j|+w d j ≤ R d)
    (t : ℝ≥0) (ht : 0 < t) (ht1 : t ≤ 1)
    (δ : D → ℝ≥0) (hδ : ∀ d, 0 < δ d) (hwidth : ∀ d j, (δ d : ℝ) ≤ w d j)
    (Cap Lip : ℝ≥0) (hCap : 1 ≤ Cap)
    (hcap : ∀ d, pivotKernelCap (UnselectedColumn (s d)) (A d) (R d)
      ((t*δ d)⁻¹^Fintype.card (J d)) ≤ Cap)
    (hlip : ∀ d, pivotKernelLip (UnselectedColumn (s d)) (A d) (R d)
      (affineProductProfileLip (J d) (t*δ d)) ≤ Lip)
    (degree : D → ℕ) (hd : ∀ d n, (eN d n).sum (fun _ k => k) ≤ degree d)
    (Ro : ℝ≥0) (hRo : ∀ d, normalizedJetOutputRadius α (N d) (A d) (F d)
      (degree d) (R d) (R d) ≤ Ro)
    (η : ℝ≥0) (hη : 0 < η) {Csum Wsum Ri : ℝ} (hRi : 0 ≤ Ri) (hRiRo : Ri+η ≤ Ro)
    (hcsum : ∀ d, (∑ b, (|c d (index d b)|+|w d (index d b)|)) ≤ Csum)
    (hwsum : ∀ d, (∑ j, (|c d j|+|w d j|)) ≤ Wsum)
    (hideal : ∀ d o, Wsum+(2 : ℝ)^(sets d o).card*(Csum*((Fintype.card α : ℝ)+1)^h d) ≤ Ri)
    (μ : Measure W) [IsProbabilityMeasure μ] (hzbox : ∀ᵐ a ∂μ, ∀ j, |z a j| ≤ 1) {ε : ℝ}
    (he : (∫ p : W × ((Σ d, O d) → ℝ),
      |averagedRegularizedIdeal h (fun d => Sum.elim (eK d) (eN d)) index c w sets η p.2 -
        smallAffineMixtureDensity h eK eN s A F sets extra c w t z p.1 p.2| ∂μ.prod volume) ≤ ε)
    (select : P ↪ (Σ d, O d))
    (a S : W × (UnselectedColumn select → ℝ) → P → ℝ)
    (hS : ∀ p j, 0 < S p j) {mesh M : ℝ}
    (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1) (hmesh : ∀ p j, 1/S p j ≤ mesh)
    (grid : W × (UnselectedColumn select → ℝ) → Finset (P → ℤ)) (mask : W × (UnselectedColumn select → ℝ) → (P → ℤ) → ℝ)
    (φ : W × (UnselectedColumn select → ℝ) → (P → ℤ) → ℂ)
    (hM : 0 ≤ M) (hmask : ∀ p k, k ∈ grid p → |mask p k| ≤ M)
    (hφ : ∀ p k, k ∈ grid p → ‖φ p k‖ ≤ 1) :
    let f := averagedRegularizedIdeal h (fun d => Sum.elim (eK d) (eN d)) index c w sets η
    let g := smallAffineMixtureDensity h eK eN s A F sets extra c w t z
    ‖∫ p : W × (UnselectedColumn select → ℝ),
      gridDensityTest (selectedOutputSlice select f p.2) (a p) (S p) (grid p) (mask p) (φ p)-
      gridDensityTest (selectedOutputSlice select (g p.1) p.2) (a p) (S p) (grid p) (mask p) (φ p) ∂μ.prod volume‖ ≤
      M*(ε+(2*(Ro : ℝ))^Fintype.card (UnselectedColumn select)*
        ((2*(Ro : ℝ)+2)^Fintype.card P*
          ((affineProductProfileLip (Σ d, O d) η : ℝ)+(Fintype.card D*Lip*Cap^Fintype.card D : ℝ≥0))*mesh)) := by
  dsimp only
  obtain ⟨hi, hgood⟩ := averagedAffine_density_data h eK eN index s A F sets extra c w z hz hw R hsupport
    t ht ht1 δ hδ hwidth Cap Lip hCap hcap hlip degree hd Ro hRo η hη hRi hRiRo
    hcsum hwsum hideal μ hzbox
  exact mixed_output_grid_error select μ
    (fun _ => averagedRegularizedIdeal h (fun d => Sum.elim (eK d) (eN d)) index c w sets η)
    (smallAffineMixtureDensity h eK eN s A F sets extra c w t z) Ro hgood hi he
    a S hS hmesh0 hmesh1 hmesh grid mask φ hM hmask hφ

end Erdos3

end

end OAI
