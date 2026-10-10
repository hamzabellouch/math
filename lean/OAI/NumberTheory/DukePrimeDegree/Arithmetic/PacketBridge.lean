import OAI.NumberTheory.DukePrimeDegree.Arithmetic.LatticeBasis
import OAI.NumberTheory.DukePrimeDegree.Geometry.EmbeddingMatrix
import OAI.NumberTheory.PrimePackets.PacketAlgebra

namespace OAI

/-!
# Full lattices in the existing packet model

The packet development records a chosen integer basis in its full-lattice
structure. Our finite-generation definition produces that basis. This
conversion preserves the actual submodule and multiplier order.
-/

namespace DukePrimeDegree

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

/-- Equip a full lattice with the basis expected by the packet model. -/
noncomputable def FullLattice.toPacket (M : FullLattice K)
    (hn : Module.finrank ℚ K = n) : PrimeDegreePackets.FullLattice n K where
  carrier := M.toSubmodule
  basis := M.integralBasis.reindex (finCongr hn)
  spans := M.span_eq_top

@[simp] lemma FullLattice.toPacket_carrier (M : FullLattice K)
    (hn : Module.finrank ℚ K = n) : (M.toPacket hn).carrier = M.toSubmodule := rfl

@[simp] lemma FullLattice.toPacket_multiplierOrder (M : FullLattice K)
    (hn : Module.finrank ℚ K = n) :
    PrimeDegreePackets.multiplierOrder (M.toPacket hn) =
      (multiplierOrder M.toSubmodule).toSubring.toAddSubgroup := by
  ext x
  rfl

/-- Convert the complex-embedding ordering to the real-embedding ordering
used by the row-lattice packet model. Total reality makes this bijective. -/
noncomputable def EmbeddingOrder.toRealOrder [NumberField.IsTotallyReal K]
    (σ : EmbeddingOrder K n) : PrimeDegreePackets.OrderedEmbeddings n K :=
  Equiv.ofBijective (orderedRealEmbedding σ) (by
    constructor
    · intro i j hij
      apply σ.injective
      apply AlgHom.ext
      intro x
      have h := congrArg (fun f : K →+* ℝ => (f x : ℂ)) hij
      simpa only [orderedRealEmbedding_complex] using h
    · intro τ
      let τc : K →ₐ[ℚ] ℂ := (Complex.ofRealHom.comp τ).toRatAlgHom
      obtain ⟨i, hi⟩ := σ.surjective τc
      refine ⟨i, ?_⟩
      ext x
      apply Complex.ofReal_injective
      rw [orderedRealEmbedding_complex, hi]
      rfl)

@[simp] lemma EmbeddingOrder.toRealOrder_apply [NumberField.IsTotallyReal K]
    (σ : EmbeddingOrder K n) (i : Fin n) : σ.toRealOrder i = orderedRealEmbedding σ i := rfl

end DukePrimeDegree

end OAI
