import OAI.GroupTheory.PolycyclicRecognition.Analysis.FiniteTranslateCover
import Mathlib.Topology.Algebra.Group.Compact

namespace OAI

/-! # Measurable tilings by conjugated small boxes -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal Pointwise

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]

/-- A measure-preserving group automorphism can distort tiles without
altering the cardinality bound. The doubled small box suffices for a
measurable partition of the large box. -/
theorem finite_conjugate_tiling (μ : Measure G) [μ.IsMulLeftInvariant]
    (e : G ≃ₜ* G) (he : MeasurePreserving e μ μ)
    (S B Bplus R : Set G) (hS : MeasurableSet S)
    (hB : IsCompact B) (hBplus : IsCompact Bplus)
    (hB0 : μ B ≠ 0) (hBtop : μ B ≠ ⊤) (hRtop : μ R ≠ ⊤)
    (hcontain : S * (e '' B) ⊆ R) (hdouble : B * B⁻¹ ⊆ Bplus) :
    ∃ (n : ℕ) (anchor : Fin n → G) (tile : Fin n → Set G),
      (∀ i, anchor i ∈ S) ∧
      (∀ i, MeasurableSet (tile i)) ∧
      Pairwise (fun i j => Disjoint (tile i) (tile j)) ∧
      (⋃ i, tile i) = S ∧
      (∀ i, tile i ⊆ anchor i • (e '' Bplus)) ∧
      (n : ℝ≥0∞) * μ B ≤ μ R := by
  classical
  have hmeas : MeasurableSet (e '' B) := (hB.image e.continuous).isClosed.measurableSet
  have hvol : μ (e '' B) = μ B := by
    calc
      μ (e '' B) = (Measure.map e μ) (e '' B) := by rw [he.map_eq]
      _ = μ (e ⁻¹' (e '' B)) := Measure.map_apply e.continuous.measurable hmeas
      _ = μ B := by rw [Set.preimage_image_eq _ e.injective]
  obtain ⟨t, ht, _hdisj, hcount, hcover⟩ := exists_finite_translate_cover μ
    S (e '' B) R hmeas (hvol ▸ hB0) (hvol ▸ hBtop) hRtop (by
      intro a ha x hx
      obtain ⟨b, hb, rfl⟩ := mem_smul_set.mp hx
      exact hcontain (Set.mul_mem_mul ha hb))
  let f : Fin (Fintype.card t) ≃ t := (Fintype.equivFin t).symm
  let anchor : Fin (Fintype.card t) → G := fun i => (f i).val
  let U : Fin (Fintype.card t) → Set G := fun i => anchor i • (e '' Bplus)
  have hU : ∀ i, MeasurableSet (U i) := fun i =>
    ((hBplus.image e.continuous).isClosed.measurableSet).const_smul (anchor i)
  have hdouble' : (e '' B) * (e '' B)⁻¹ ⊆ e '' Bplus := by
    rw [← Set.image_inv, ← Set.image_mul]
    exact Set.image_mono hdouble
  have hc : S ⊆ ⋃ i, U i := by
    intro x hx
    obtain ⟨a, ha⟩ := mem_iUnion.mp (hcover hx)
    obtain ⟨hat, hxa⟩ := mem_iUnion.mp ha
    let i := f.symm ⟨a, hat⟩
    refine mem_iUnion.mpr ⟨i, ?_⟩
    have hai : anchor i = a := congrArg Subtype.val (f.apply_symm_apply ⟨a, hat⟩)
    change x ∈ anchor i • (e '' Bplus)
    rw [hai]
    exact Set.smul_set_mono hdouble' hxa
  obtain ⟨tile, htile, hd, hu, hsub⟩ :=
    measurable_partition_of_finite_cover S hS U hU hc
  refine ⟨Fintype.card t, anchor, tile, (fun i => ht (f i).property),
    htile, hd, hu, (fun i => (hsub i).trans inter_subset_right), ?_⟩
  simpa only [Fintype.card_coe, hvol] using hcount

end PolycyclicRecognition

end

end OAI
