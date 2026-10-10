import OAI.GroupTheory.PolycyclicRecognition.Analysis.ProbeTileSelector
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ConeProbeIntrinsicTiles
import Mathlib.MeasureTheory.Group.Arithmetic

namespace OAI

/-! # The three measurable samplers from an actual ideal tiling -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped Pointwise

variable {I N Z : Type*} [Group I] [TopologicalSpace I] [IsTopologicalGroup I]
  [MeasurableSpace I] [BorelSpace I] [Group N] [TopologicalSpace N]
  [IsTopologicalGroup N] [MeasurableSpace N] [BorelSpace N]
  [SecondCountableTopology I] [SecondCountableTopology N]
  [MeasurableSpace Z]

/-- A finite measurable tiling supplies the actual first-sheet, reverse-anchor,
and within-tile samplers. Their group increments are the original endpoints,
so choosing a tile never replaces a counted point by another representative. -/
theorem exists_measurable_tiled_probe_samplers
    (ι : I →* N) (hι : Measurable ι) (φ : I ≃ₜ* I) (k : N)
    (hφ : ∀ z, ι (φ z) = k * ι z * k⁻¹)
    (σ : Z → N) (hσ : Measurable σ)
    (U Banchor Bsmall : Set I) {m : ℕ} (anchor : Fin m → I)
    (tile : Fin m → Set I) (hm : ∀ j, MeasurableSet (tile j))
    (hd : Pairwise (fun j l => Disjoint (tile j) (tile l)))
    (hu : (⋃ j, tile j) = U)
    (ha : ∀ j, φ.symm (anchor j) ∈ Banchor)
    (ht : ∀ j, tile j ⊆ anchor j • (φ '' Bsmall)) :
    ∃ (index : U → Fin m) (probe : Fin 3 → Z × U → N),
      Measurable index ∧ (∀ j, Measurable (probe j)) ∧
      (∀ y, probe 0 y = ι y.2.val * σ y.1) ∧
      (∀ y, probe 1 y = ι (φ.symm (anchor (index y.2)))) ∧
      (∀ y, probe 2 y = ι (φ.symm ((anchor (index y.2))⁻¹ * y.2.val))) ∧
      (∀ y, probe 1 y ∈ ι '' Banchor) ∧
      (∀ y, probe 2 y ∈ ι '' Bsmall) ∧
      (∀ (S : MulAut N) n y,
        n * S (probe 0 y) = coneProbeFirst S n (ι y.2.val) (σ y.1)) ∧
      (∀ (S : MulAut N) n y,
        (n * S k) * S (probe 1 y) =
          coneProbeSecond S n (ι (anchor (index y.2))) k) ∧
      ∀ (S : MulAut N) n y,
        coneProbeSecond S n (ι (anchor (index y.2))) k * S (probe 2 y) =
          coneProbeSecond S n (ι y.2.val) k := by
  obtain ⟨index, hindex, hmem, _⟩ := exists_measurable_probe_tile_index U tile hm hd hu
  let selected : Z × U → I := fun y => anchor (index y.2)
  have hselected : Measurable selected :=
    (measurable_of_countable anchor).comp (hindex.comp measurable_snd)
  have hcoord : Measurable (fun y : Z × U => y.2.val) :=
    measurable_subtype_coe.comp measurable_snd
  let probe : Fin 3 → Z × U → N := ![
    fun y => ι y.2.val * σ y.1,
    fun y => ι (φ.symm (selected y)),
    fun y => ι (φ.symm ((selected y)⁻¹ * y.2.val))]
  have hp : ∀ j, Measurable (probe j) := by
    intro j
    fin_cases j
    · exact (hι.comp hcoord).mul (hσ.comp measurable_fst)
    · exact hι.comp (φ.symm.continuous.measurable.comp hselected)
    · exact hι.comp (φ.symm.continuous.measurable.comp (hselected.inv.mul hcoord))
  have hback (z : I) : ι (φ.symm z) = k⁻¹ * ι z * k := by
    have hh := hφ (φ.symm z)
    rw [φ.apply_symm_apply] at hh
    rw [hh]
    simp [mul_assoc]
  refine ⟨index, probe, hindex, hp, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro y
    exact ⟨φ.symm (anchor (index y.2)), ha _, rfl⟩
  · intro y
    exact ⟨φ.symm ((anchor (index y.2))⁻¹ * y.2.val),
      intrinsic_probe_tile_mem φ.toMulEquiv _ _ _ (ht _ (hmem y.2)), rfl⟩
  · intro S n y
    rfl
  · intro S n y
    change (n * S k) * S (ι (φ.symm (anchor (index y.2)))) = _
    rw [hback]
    simp [coneProbeSecond, map_mul, mul_assoc]
  · intro S n y
    change coneProbeSecond S n (ι (anchor (index y.2))) k *
      S (ι (φ.symm ((anchor (index y.2))⁻¹ * y.2.val))) = _
    rw [hback]
    simp [coneProbeSecond, map_mul, mul_assoc]

end PolycyclicRecognition

end

end OAI
