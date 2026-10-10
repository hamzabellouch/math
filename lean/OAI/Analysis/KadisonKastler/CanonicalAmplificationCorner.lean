import OAI.Analysis.KadisonKastler.CanonicalAmplification
import OAI.Analysis.KadisonKastler.FiniteBlockExtension

namespace OAI

/-! # The initial corner of the actual amplification

Compression to the initial matrix coordinate recovers precisely the
original algebra. In the canonical Hilbert sum this is the transported
original representation, so a finite diffuse factor gives an actual
finite diffuse initial corner.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : Submodule ℂ H} [CompleteSpace E]

namespace FullMatrixCorner

variable (F : FullMatrixCorner E)

theorem blockElement_zero_zero (T : E →L[ℂ] E) :
    F.blockElement 0 0 T = cornerExtension E T := by
  rw [blockElement, F.zero_zero, starProjection_mul_cornerExtension,
    cornerExtension_mul_starProjection]

theorem matrixEntry_cornerExtension (T : E →L[ℂ] E) (i j : ℕ) :
    F.matrixEntry (cornerExtension E T) i j = if i = 0 ∧ 0 = j then T else 0 := by
  rw [← F.blockElement_zero_zero T, F.matrixEntry_blockElement]

/-- Extension by zero belongs to the amplification exactly when the
corner operator belongs to its original algebra. -/
theorem cornerExtension_mem_amplifiedAlgebra_iff
    (M : VonNeumannAlgebra E) (T : E →L[ℂ] E) :
    cornerExtension E T ∈ F.amplifiedAlgebra M ↔ T ∈ M := by
  rw [F.mem_amplifiedAlgebra_iff]
  constructor
  · intro h
    have h0 := h 0 0
    rw [F.matrixEntry_cornerExtension, ite_eq_left ⟨rfl, rfl⟩] at h0
    exact h0
  · intro h i j
    rw [F.matrixEntry_cornerExtension]
    split_ifs
    · exact h
    · exact M.zero_mem

/-- The represented first corner of the amplification is the input
algebra itself. -/
theorem representedCorner_amplifiedAlgebra (M : VonNeumannAlgebra E) :
    representedCorner E (F.amplifiedAlgebra M)
      (F.zero_zero ▸ F.entry_mem_amplifiedAlgebra M 0 0) = M := by
  apply VonNeumannAlgebra.ext
  intro T
  exact F.cornerExtension_mem_amplifiedAlgebra_iff M T

end FullMatrixCorner

variable (H)

theorem canonicalInitialProjection_mem (M : VonNeumannAlgebra H) :
    (canonicalInitialSpace H).starProjection ∈ canonicalAmplifiedAlgebra H M :=
  (canonicalMatrixCorner H).zero_zero ▸
    canonicalMatrixUnit_mem_canonicalAmplifiedAlgebra H M 0 0

/-- In canonical coordinates the first corner is exactly the spatially
transported original algebra. -/
theorem representedCorner_canonicalAmplifiedAlgebra (M : VonNeumannAlgebra H) :
    representedCorner (canonicalInitialSpace H) (canonicalAmplifiedAlgebra H M)
      (canonicalInitialProjection_mem H M) = canonicalCornerAlgebra H M :=
  (canonicalMatrixCorner H).representedCorner_amplifiedAlgebra (canonicalCornerAlgebra H M)

theorem representedCorner_canonicalAmplifiedAlgebra_isII1 {M : VonNeumannAlgebra H}
    (hM : Generator.IsII1Factor M.toStarSubalgebra) :
    Generator.IsII1Factor
      (representedCorner (canonicalInitialSpace H) (canonicalAmplifiedAlgebra H M)
        (canonicalInitialProjection_mem H M)).toStarSubalgebra := by
  rw [representedCorner_canonicalAmplifiedAlgebra]
  exact spatialTransportAlgebra_isII1 (canonicalInitialEquiv H) hM

end

end KadisonKastler

end OAI
