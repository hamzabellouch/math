import OAI.NumberTheory.DukePrimeDegree.Dynamics.OrbitGenericity
import Mathlib.Topology.Compactness.SigmaCompact

namespace OAI

/-!
# Invariant measures on actual lattice orbits

The quotient by the actual point stabilizer injects into the lattice space.
For a closed matrix subgroup this injection is a Borel embedding, even when
the orbit is not closed. A finite invariant measure concentrated on that
orbit therefore pulls back to a finite invariant measure on the quotient.

This discharges the measure-transfer part of the homogeneous-orbit argument;
it does not assert the existence of a homogeneous orbit supporting a given
measure.
-/

noncomputable section
open MeasureTheory Set Matrix
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma latticeOrbitPoint_injective {n : ℕ} (g : G n) (H : Subgroup (G n)) :
    Function.Injective (latticeOrbitPoint g H) := by
  intro x y hxy
  induction x using Quotient.inductionOn with
  | h a =>
    induction y using Quotient.inductionOn with
    | h b =>
      apply Quotient.sound
      have hab := Quotient.exact hxy
      change QuotientGroup.rightRel (integralGroup n) (g * a.val) (g * b.val) at hab
      change QuotientGroup.rightRel (pointOrbitStabilizer g H) a b
      rw [QuotientGroup.rightRel_apply] at hab ⊢
      change g * (b.val * a.val⁻¹) * g⁻¹ ∈ integralGroup n
      simpa only [_root_.mul_inv_rev, mul_assoc] using hab

private lemma measurableEmbedding_of_continuous_injective_sigmaCompact
    {α β : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
    [SigmaCompactSpace α] [TopologicalSpace β] [T2Space β]
    [MeasurableSpace β] [BorelSpace β] (f : α → β)
    (hf : Continuous f) (hinj : Function.Injective f) : MeasurableEmbedding f := by
  refine ⟨hinj, hf.measurable, ?_⟩
  intro s hs
  have hcover : f '' s = ⋃ k : ℕ, f '' (s ∩ compactCovering α k) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨k, hk⟩ := exists_mem_compactCovering x
      exact mem_iUnion.mpr ⟨k, x, ⟨hx, hk⟩, rfl⟩
    · intro hy
      obtain ⟨k, x, hx, hxy⟩ := mem_iUnion.mp hy
      exact ⟨x, hx.1, hxy⟩
  rw [hcover]
  apply MeasurableSet.iUnion
  intro k
  let C := compactCovering α k
  let : CompactSpace C := (isCompact_iff_compactSpace.mp (isCompact_compactCovering α k))
  let fc : C → β := fun x => f x.val
  have hfc : Topology.IsClosedEmbedding fc :=
    (hf.comp continuous_subtype_val).isClosedEmbedding (hinj.comp Subtype.val_injective)
  have he : f '' (s ∩ C) = fc '' ((↑) ⁻¹' s : Set C) := by
    ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      exact ⟨⟨x, hx.2⟩, hx.1, hxy⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x.val, ⟨hx, x.property⟩, hxy⟩
  rw [he]
  exact hfc.measurableEmbedding.measurableSet_image' (measurable_subtype_coe hs)

lemma latticeOrbitPoint_measurableEmbedding {n : ℕ} (g : G n) (H : Subgroup (G n))
    (hH : IsClosed (H : Set (G n))) : MeasurableEmbedding (latticeOrbitPoint g H) := by
  let : SigmaCompactSpace H := hH.sigmaCompactSpace
  let : SigmaCompactSpace (LatticeOrbitQuotient g H) := by
    apply isSigmaCompact_univ_iff.mp
    have h := isSigmaCompact_range
      (continuous_quotient_mk' : Continuous (fun x : H =>
        (Quotient.mk _ x : LatticeOrbitQuotient g H)))
    change IsSigmaCompact (range (fun x : H =>
      (Quotient.mk _ x : LatticeOrbitQuotient g H))) at h
    rwa [Set.range_eq_univ.mpr Quotient.mk_surjective] at h
  exact measurableEmbedding_of_continuous_injective_sigmaCompact _
    (continuous_latticeOrbitPoint g H) (latticeOrbitPoint_injective g H)

lemma isClosed_blockMatrixGroup {n : ℕ} (r : Setoid (Fin n)) :
    IsClosed (blockMatrixGroup r : Set (G n)) := by
  have he : (blockMatrixGroup r : Set (G n)) =
      ⋂ c : Fin n → ℝ, ⋂ (_hc : c ∈ blockCoordinateAlgebra r),
        {g : G n | slMatrixConjugation g (Matrix.diagonal c) = Matrix.diagonal c} := by
    ext g
    simp only [mem_iInter, mem_ofPred_eq]
    rfl
  rw [he]
  apply isClosed_iInter
  intro c
  apply isClosed_iInter
  intro _
  apply isClosed_eq _ continuous_const
  unfold slMatrixConjugation
  fun_prop

/-- Pullback through the actual orbit injection recovers the ambient measure
when that measure is concentrated on the orbit. -/
lemma latticeOrbitPoint_map_comap {n : ℕ} (g : G n) (H : Subgroup (G n))
    (hH : IsClosed (H : Set (G n))) (μ : Measure (X n))
    (horbit : ∀ᵐ x ∂μ, x ∈ range (latticeOrbitPoint g H)) :
    (μ.comap (latticeOrbitPoint g H)).map (latticeOrbitPoint g H) = μ := by
  rw [(latticeOrbitPoint_measurableEmbedding g H hH).map_comap,
    Measure.restrict_eq_self_of_ae_mem horbit]

lemma latticeOrbitPoint_comap_invariant {n : ℕ} (g : G n) (H : Subgroup (G n))
    (hH : IsClosed (H : Set (G n))) (μ : Measure (X n))
    (horbit : ∀ᵐ x ∂μ, x ∈ range (latticeOrbitPoint g H))
    (hinv : ∀ h : H, μ.map (fun x => rightAction x h.val) = μ) (h : H) :
    (μ.comap (latticeOrbitPoint g H)).map
      (fun x => latticeOrbitRightAction g H x h) = μ.comap (latticeOrbitPoint g H) := by
  let F := latticeOrbitPoint g H
  let R := fun x => latticeOrbitRightAction g H x h
  have hF := latticeOrbitPoint_measurableEmbedding g H hH
  have hmap := latticeOrbitPoint_map_comap g H hH μ horbit
  apply hF.map_injective
  calc
    _ = (μ.comap F).map (F ∘ R) :=
      Measure.map_map hF.measurable (continuous_latticeOrbitRightAction g H h).measurable
    _ = (μ.comap F).map ((fun x => rightAction x h.val) ∘ F) := by
      congr 1
      funext x
      exact latticeOrbitPoint_rightAction g H x h
    _ = ((μ.comap F).map F).map (fun x => rightAction x h.val) :=
      (Measure.map_map (continuous_rightAction h.val).measurable hF.measurable).symm
    _ = μ := by rw [hmap, hinv h]
    _ = (μ.comap F).map F := hmap.symm

/-- The prime-degree finite-orbit obstruction stated directly for a measure on
the lattice space. No measure on a quotient is an additional hypothesis. -/
theorem block_partition_universal_of_invariant_orbit_measure {d : ℕ}
    (hn : (d + 1).Prime) (g : G (d + 1)) (r : Setoid (Fin (d + 1)))
    (hnontrivial : ∃ i j, i ≠ j ∧ r i j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ] (hμ : μ ≠ 0)
    (horbit : ∀ᵐ x ∂μ, x ∈ range (latticeOrbitPoint g (blockMatrixGroup r)))
    (hinv : ∀ h : blockMatrixGroup r, μ.map (fun x => rightAction x h.val) = μ) :
    ∀ i j, r i j := by
  let ν := μ.comap (latticeOrbitPoint g (blockMatrixGroup r))
  have hν : ν ≠ 0 := by
    intro hzero
    have he := latticeOrbitPoint_map_comap g (blockMatrixGroup r)
      (isClosed_blockMatrixGroup r) μ horbit
    change ν.map _ = μ at he
    rw [hzero, Measure.map_zero] at he
    exact hμ he.symm
  apply block_partition_universal_of_invariant_finite_orbit hn g r hnontrivial ν hν
  exact latticeOrbitPoint_comap_invariant g (blockMatrixGroup r)
    (isClosed_blockMatrixGroup r) μ horbit hinv

end DukePrimeDegree

end

end OAI
