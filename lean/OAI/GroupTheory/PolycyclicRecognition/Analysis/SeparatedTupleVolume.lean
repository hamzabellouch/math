import OAI.GroupTheory.PolycyclicRecognition.Algebra.TupleLiftProjection
import OAI.GroupTheory.PolycyclicRecognition.Analysis.FactorProductPacking

namespace OAI

/-! # Nilpotent increment volume from separated ambient endpoint tuples

Thickening chosen lifts gives disjoint cells even when the factor map has
a kernel. Projection discards only the volume of the bounded Cartan
coordinates; changing to increments preserves the remaining Haar volume.
-/

noncomputable section
namespace PolycyclicRecognition

open Set MeasureTheory
open scoped ENNReal

variable {N D G : Type*} [Group N] [Group D] [Group G]

def tupleFactorAction (φ : D →* MulAut N) (h : ℕ) :
    (Fin h → D) →* MulAut (Fin h → N) where
  toFun d := MulEquiv.piCongrRight (fun i => φ (d i))
  map_one' := by ext n i; simp
  map_mul' d e := by ext n i; simp

variable [TopologicalSpace N] [T2Space N] [SecondCountableTopology N]
  [TopologicalSpace D] [T2Space D] [SecondCountableTopology D]
  [MeasurableSpace N] [MeasurableSpace D] [BorelSpace N] [BorelSpace D]
  [IsTopologicalGroup N] [IsTopologicalGroup D]
  [MetricSpace G] [IsIsometricSMul G G]

/-- The lower-volume part of `tuple-lift-volume`, with the individual lifts
and their thickening retained for the subsequent box estimates. -/
theorem exists_increment_volume_of_separated_tuples
    (φ : D →* MulAut N) (ι : N →* G) (κ : D →* G)
    (hc : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (μ : Measure N) (ν : Measure D) [SigmaFinite μ] [SigmaFinite ν]
    [μ.IsMulLeftInvariant] [ν.IsMulLeftInvariant]
    (hφ : ∀ d, MeasurePreserving (φ d) μ μ) (hφc : ∀ d, Continuous (φ d))
    (h : ℕ) (s : Finset (Fin h → G))
    (p : (Fin h → G) → (Fin h → N) × (Fin h → D))
    (U : Set ((Fin h → N) × (Fin h → D))) (hU : IsCompact U)
    {ρ : ℝ}
    (hp : ∀ x ∈ s, ∀ i, ι ((p x).1 i) * κ ((p x).2 i) = x i)
    (hsmall : ∀ z ∈ U, dist (1 : Fin h → G) (fun i => ι (z.1 i) * κ (z.2 i)) < ρ / 2)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ρ ≤ dist x y)
    (Q : Set (Fin h → D))
    (hQ : ∀ x ∈ s, ∀ z ∈ U, (p x).2 * z.2 ∈ Q) :
    ∃ I : Set (Fin h → N), IsCompact I ∧ MeasurableSet I ∧
      (s.card : ℝ≥0∞) * ((Measure.pi fun _ : Fin h => μ).prod
        (Measure.pi fun _ : Fin h => ν)) U ≤
          (Measure.pi fun _ : Fin h => μ) I * (Measure.pi fun _ : Fin h => ν) Q ∧
      ∀ u ∈ I, ∃ x ∈ s, ∃ z ∈ U,
        prefixCoordinateEquiv h u = fun i => (p x).1 i * φ ((p x).2 i) (z.1 i) := by
  let φh := tupleFactorAction φ h
  let ιh := MonoidHom.piMap (fun _ : Fin h => ι)
  let κh := MonoidHom.piMap (fun _ : Fin h => κ)
  have hch (d : Fin h → D) (n : Fin h → N) :
      ιh (φh d n) = κh d * ιh n * (κh d)⁻¹ := by
    ext i
    exact hc (d i) (n i)
  have hφh (d : Fin h → D) : MeasurePreserving (φh d)
      (Measure.pi fun _ => μ) (Measure.pi fun _ => μ) :=
    measurePreserving_pi _ _ (fun i => hφ (d i))
  have hφhc (d : Fin h → D) : Continuous (φh d) :=
    continuous_pi (fun i => (hφc (d i)).comp (continuous_apply i))
  let K := ⋃ x ∈ s, factorTranslate φh (p x) '' U
  have hK : IsCompact K := s.isCompact_biUnion (fun x _ => hU.image
    ((continuous_const.mul ((hφhc (p x).2).comp continuous_fst)).prodMk
      (continuous_const.mul continuous_snd)))
  have hmass := factor_separated_card_mul_le φh ιh κh hch
    (Measure.pi fun _ : Fin h => μ) (Measure.pi fun _ : Fin h => ν) hφh
    s p U K hU.measurableSet
    (fun x hx => funext (hp x hx)) hsmall hsep
    (fun x hx => subset_iUnion₂_of_subset x hx Subset.rfl)
  have hKQ : ∀ z ∈ K, z.2 ∈ Q := by
    intro z hz
    obtain ⟨x, hx, v, hv, rfl⟩ := mem_iUnion₂.mp hz
    exact hQ x hx v hv
  obtain ⟨hI, hvol⟩ := tuple_lift_projection_volume μ (Measure.pi fun _ : Fin h => ν) h hK hKQ
  refine ⟨tupleIncrementRegion h K,
    (hK.image continuous_fst).image (continuous_prefixCoordinateEquiv_symm h),
    hI, hmass.trans hvol, ?_⟩
  intro u hu
  obtain ⟨y, ⟨v, hv, rfl⟩, he⟩ := hu
  obtain ⟨x, hx, z, hz, rfl⟩ := mem_iUnion₂.mp hv
  refine ⟨x, hx, z, hz, ?_⟩
  rw [← he, MeasurableEquiv.apply_symm_apply]
  rfl

end PolycyclicRecognition

end

end OAI
