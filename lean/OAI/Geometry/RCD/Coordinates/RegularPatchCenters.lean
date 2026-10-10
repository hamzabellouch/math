import OAI.Geometry.RCD.Coordinates.RegularPinchingField
import OAI.Geometry.RCD.Coordinates.PatchCoverData

namespace OAI

/-! # Fixed patch centers for the actual local mass matrices -/

open Set Metric MeasureTheory
open scoped ENNReal NNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The positive energy floor chooses each patch center before its mass
matrix is fixed. Thus the displacement bound uses the actual mean and
Bochner mass at the chosen center, with no third-center hypothesis. -/
theorem RegularPinchingField.exists_patch_centers {K : ℝ} {n : ℕ}
    {hX : NoncollapsedRCD K n X} [(hausdorff n X).Regular]
    {base : X} {ker : ℝ → X → X → ℝ}
    {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker}
    {enlargement zeta C budget : ℝ} {d : RegularBilinearData hX base hk enlargement zeta}
    (f : RegularPinchingField d C budget) (hC : 0 ≤ C) (i : ℕ) {ι : Type*}
    (patch : ι → Set {q : X // q ∈ ball base (d.radius / 32)})
    (hne : ∀ j, (patch j).Nonempty)
    (hdiam : ∀ j, ∀ x ∈ patch j, ∀ z ∈ patch j,
      dist x.val z.val ≤ distanceSourceRadius d.radius i / 512) :
    ∃ center : ι → {q : X // q ∈ ball base (d.radius / 32)},
      ∀ j, center j ∈ patch j ∧
        (d.pinchingMassMatrix (center j).val (center j).property i).IsPositive ∧
        ∀ x ∈ patch j,
          ⟪d.values x.val - d.values (center j).val,
            d.pinchingMassMatrix (center j).val (center j).property i
              (d.values x.val - d.values (center j).val)⟫_ℝ ≤
            (3 * C) * (distanceSourceRadius d.radius i) ^ 2 * f.energy x i := by
  obtain ⟨center, hcenter⟩ := exists_patch_energy_centers patch (fun q => f.energy q i) hne
    (fun _ => ⟨f.floor i, f.floor_pos i, fun q _ => f.energy_floor q i⟩)
  refine ⟨center, fun j => ⟨(hcenter j).1, d.pinchingMassMatrix_isPositive _ _ i, ?_⟩⟩
  intro x hx
  exact centered_patch_energy_le
    (X := {q : X // q ∈ ball base (d.radius / 32)}) (E := Euclidean n)
    (energy := fun q => f.energy q i) (fun q => d.values q.val)
    (d.pinchingMassMatrix (center j).val (center j).property i)
    hC ((hcenter j).2 x hx)
    (f.directional x (center j) i (hdiam j x hx (center j) (hcenter j).1))

/-- Apply the selection to the actual normalized cutoffs of a localized
finite cover. The overlap radius controls the pair distance required by
pinching; no regularity of the source energy is needed. -/
theorem RegularPinchingField.exists_normalized_centers {K : ℝ} {n : ℕ}
    {hX : NoncollapsedRCD K n X} [(hausdorff n X).Regular]
    {base : X} {ker : ℝ → X → X → ℝ}
    {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker}
    {enlargement zeta C budget : ℝ} {d : RegularBilinearData hX base hk enlargement zeta}
    (f : RegularPinchingField d C budget) (hC : 0 ≤ C) (i : ℕ)
    (A : Set X) (r : ℝ≥0) (T : X → Euclidean n →L[ℝ] Euclidean n)
    (psi : Euclidean n → ℝ) (s : Finset X) {N : ℕ} {L R : ℝ}
    (cover : IsLocalizedPatchCover A r d.values s (normalizedPatchCutoff r d.values T psi) N L R)
    (hzero : psi 0 = 1) (hA : A ⊆ ball base (d.radius / 32))
    (hsmall : 2 * L * (r : ℝ) ≤ distanceSourceRadius d.radius i / 512) :
    ∃ center : {y : X // y ∈ s} → {q : X // q ∈ ball base (d.radius / 32)},
      ∀ y, (center y).val ∈ normalizedPatchDomain A r d.values T psi y.val ∧
        ∀ x : {q : X // q ∈ ball base (d.radius / 32)},
          x.val ∈ normalizedPatchDomain A r d.values T psi y.val →
          ⟪d.values x.val - d.values (center y).val,
            d.pinchingMassMatrix (center y).val (center y).property i
              (d.values x.val - d.values (center y).val)⟫_ℝ ≤
            (3 * C) * (distanceSourceRadius d.radius i) ^ 2 * f.energy x i := by
  let patch := fun y : {y : X // y ∈ s} =>
    {q : {q : X // q ∈ ball base (d.radius / 32)} |
      q.val ∈ normalizedPatchDomain A r d.values T psi y.val}
  have hne (y) : (patch y).Nonempty := by
    refine ⟨⟨y.val, hA (cover.center_mem y.property)⟩, ?_⟩
    exact self_mem_normalizedPatchDomain A r d.values T psi (cover.center_mem y.property) hzero
  have hdiam (y) (x) (hx : x ∈ patch y) (z) (hz : z ∈ patch y) :
      dist x.val z.val ≤ distanceSourceRadius d.radius i / 512 := by
    have hx' := cover.active_localized x.val hx.1 y.val y.property hx.2
    have hz' := cover.active_localized z.val hz.1 y.val y.property hz.2
    have ht := dist_triangle x.val y.val z.val
    rw [dist_comm y.val z.val] at ht
    linarith
  obtain ⟨center, hc⟩ := f.exists_patch_centers hC i patch hne hdiam
  exact ⟨center, fun y => ⟨(hc y).1, fun x hx => (hc y).2.2 x hx⟩⟩

end RegularPointCoordinates

end

end OAI
