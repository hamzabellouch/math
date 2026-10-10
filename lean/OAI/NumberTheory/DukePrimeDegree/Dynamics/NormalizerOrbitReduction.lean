import OAI.NumberTheory.DukePrimeDegree.Dynamics.OrbitMeasureTransfer
import OAI.NumberTheory.DukePrimeDegree.Dynamics.BlockNormalizerFiniteIndex

namespace OAI

/-!
# From a normalizer orbit to one block orbit

The finite normalizer quotient gives a finite cover by block-group orbits.
Each such orbit is Borel and diagonal invariant. Diagonal ergodicity thus
places the whole measure on one of them. These are direct consequences of
an actual normalizer-orbit support statement, not an assertion that every
root-invariant measure already has that support.
-/

noncomputable section
open MeasureTheory Set Filter Matrix
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma latticeOrbitPoint_range_preimage {n : ℕ} (g : G n) (H : Subgroup (G n)) (h : H) :
    (fun x => rightAction x h.val) ⁻¹' range (latticeOrbitPoint g H) =
      range (latticeOrbitPoint g H) := by
  have hmap (a : H) : Set.MapsTo (fun x => rightAction x a.val)
      (range (latticeOrbitPoint g H)) (range (latticeOrbitPoint g H)) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨latticeOrbitRightAction g H x a, latticeOrbitPoint_rightAction g H x a⟩
  ext x
  constructor
  · intro hx
    have hi := hmap h⁻¹ hx
    simpa only [Subgroup.coe_inv, rightAction_mul, mul_inv_cancel, rightAction_one] using hi
  · intro hx
    exact hmap h hx

lemma scalarNormalizer_orbit_covered_by_blockOrbits {n : ℕ}
    (g : G n) (r : Setoid (Fin n)) :
    range (latticeOrbitPoint g (blockScalarNormalizer r)) ⊆
      ⋃ c : blockScalarNormalizer r ⧸
          (blockMatrixGroup r).comap (blockScalarNormalizer r).subtype,
        range (latticeOrbitPoint (g * c.out.val) (blockMatrixGroup r)) := by
  rintro _ ⟨x, rfl⟩
  induction x using Quotient.inductionOn with
  | h a =>
    let c : blockScalarNormalizer r ⧸
        (blockMatrixGroup r).comap (blockScalarNormalizer r).subtype := QuotientGroup.mk a
    have hrel : QuotientGroup.leftRel
        ((blockMatrixGroup r).comap (blockScalarNormalizer r).subtype) c.out a :=
      Quotient.exact (Quotient.out_eq' c)
    rw [QuotientGroup.leftRel_apply] at hrel
    have hk : (c.out⁻¹ * a).val ∈ blockMatrixGroup r := hrel
    let h : blockMatrixGroup r := ⟨(c.out⁻¹ * a).val, hk⟩
    refine mem_iUnion.mpr ⟨c, ⟨Quotient.mk _ h, ?_⟩⟩
    change Quotient.mk _ ((g * c.out.val) * (c.out⁻¹ * a).val) =
      (Quotient.mk _ (g * a.val) : X n)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, mul_inv_cancel_left]

/-- Diagonal ergodicity selects one block orbit from an actual normalizer
orbit. No invariance under disconnected normalizer components is needed. -/
theorem exists_block_orbit_of_scalarNormalizer_orbit {d : ℕ}
    (g : G (d + 1)) (r : Setoid (Fin (d + 1)))
    (μ : Measure (X (d + 1))) (hμ : μ ≠ 0)
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d + 1)) μ]
    (horbit : ∀ᵐ x ∂μ, x ∈ range (latticeOrbitPoint g (blockScalarNormalizer r))) :
    ∃ g' : G (d + 1), ∀ᵐ x ∂μ, x ∈ range (latticeOrbitPoint g' (blockMatrixGroup r)) := by
  let C := blockScalarNormalizer r ⧸
    (blockMatrixGroup r).comap (blockScalarNormalizer r).subtype
  let : Finite C := finite_blockNormalizer_quotient r
  let S : C → Set (X (d + 1)) := fun c =>
    range (latticeOrbitPoint (g * c.out.val) (blockMatrixGroup r))
  have hs (c : C) : MeasurableSet (S c) :=
    (latticeOrbitPoint_measurableEmbedding (g * c.out.val) (blockMatrixGroup r)
      (isClosed_blockMatrixGroup r)).measurableSet_range
  have hconst (c : C) : (∀ᵐ x ∂μ, x ∈ S c) ∨ (∀ᵐ x ∂μ, x ∉ S c) := by
    apply eventuallyEmptyOrUniv_iff.mp
    apply aeconst_of_forall_preimage_smul_ae_eq (Multiplicative (LogCoordinates d))
      (hs c).nullMeasurableSet
    intro u
    change (fun x => rightAction x (diagonalFlow u.toAdd)) ⁻¹' S c =ᵐ[μ] S c
    have he := latticeOrbitPoint_range_preimage (g * c.out.val) (blockMatrixGroup r)
      ⟨diagonalFlow u.toAdd, diagonalFlow_mem_blockMatrixGroup r u.toAdd⟩
    change (fun x => rightAction x (diagonalFlow u.toAdd)) ⁻¹' S c = S c at he
    rw [he]
  suffices ∃ c : C, ∀ᵐ x ∂μ, x ∈ S c by
    obtain ⟨c, hc⟩ := this
    exact ⟨g * c.out.val, hc⟩
  by_contra hnone
  have hall : ∀ᵐ x ∂μ, ∀ c : C, x ∉ S c := by
    rw [ae_all_iff]
    intro c
    exact (hconst c).resolve_left (fun hc => hnone ⟨c, hc⟩)
  have : NeBot (ae μ) := ae_neBot.mpr hμ
  obtain ⟨x, hx, havoid⟩ := (horbit.and hall).exists
  obtain ⟨c, hc⟩ := mem_iUnion.mp (scalarNormalizer_orbit_covered_by_blockOrbits g r hx)
  exact havoid c hc

/-- The prime-degree obstruction also applies to a measure supported on
one full block-normalizer orbit. -/
theorem block_partition_universal_of_invariant_normalizerOrbit {d : ℕ}
    (hn : (d + 1).Prime) (g : G (d + 1)) (r : Setoid (Fin (d + 1)))
    (hnontrivial : ∃ i j, i ≠ j ∧ r i j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ] (hμ : μ ≠ 0)
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d + 1)) μ]
    (horbit : ∀ᵐ x ∂μ, x ∈ range (latticeOrbitPoint g (blockScalarNormalizer r)))
    (hinv : ∀ h : blockMatrixGroup r, μ.map (fun x => rightAction x h.val) = μ) :
    ∀ i j, r i j := by
  obtain ⟨g', hg'⟩ := exists_block_orbit_of_scalarNormalizer_orbit g r μ hμ horbit
  exact block_partition_universal_of_invariant_orbit_measure hn g' r hnontrivial μ hμ hg' hinv

end DukePrimeDegree

end

end OAI
