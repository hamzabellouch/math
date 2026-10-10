import OAI.Analysis.KadisonKastler.SupportCompressedStages
import OAI.Analysis.KadisonKastler.SupportTransferredState
import OAI.Analysis.KadisonKastler.SymmetricSupportTransfer
import OAI.Analysis.KadisonKastler.MatrixCentralizerTests

namespace OAI

/-! # The expected subfactor from a nonfaithful central line

The support corner and its conjugate support restore a cyclic separating
vector on the original representation. Thus the central line need not
itself consist of separating vectors before the corner transfer.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [TopologicalSpace.SeparableSpace H]
  {M : VonNeumannAlgebra H}

theorem expectedMatrixSubfactorModel_of_supported_central_line
    (hM : TypeIIIFactor M) (A : ℕ → FiniteMatrixStage M)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra))
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hleft : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hright : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hunit : ‖ξ‖ = 1) (hJξ : J ξ = ξ)
    (hξ : ξ ∈ matrixCentralVectorSpace A J)
    (hline : matrixCentralVectorSpace A J ≤ Submodule.span ℂ {ξ}) :
    Nonempty (ExpectedMatrixSubfactorModel M) := by
  have hne : ξ ≠ 0 := by
    intro h
    have h01 : (0 : ℝ) = 1 := by simpa only [h,norm_zero] using hunit
    exact zero_ne_one h01
  obtain ⟨v,w,hv,hw,hvp,hwq⟩ :=
    exists_symmetric_support_isometries M hM J hJ hleft hright ξ hJξ hne
  have hvp' : v * star v = (vectorSupportProjection M ξ).val := Subtype.ext hvp
  have hc (n : ℕ) (i j : Fin (A n).size) :
      (v * star v) * (A n).units.entry i j = (A n).units.entry i j * (v * star v) := by
    apply Subtype.ext
    change (v.val * star v.val) * ((A n).units.entry i j).val =
      ((A n).units.entry i j).val * (v.val * star v.val)
    rw [hvp]
    exact matrixCentralVector_support_commutes A J hleft ξ hξ n i j
  let B := supportCompressedStages A v hv hc
  let Ω := star (v.val * w.val) ξ
  have hn : ‖Ω‖ = 1 := (support_transfer_norm M ξ v w hv hw hvp hwq).trans hunit
  have hcyc : DenseRange (algebraVectorMap M Ω) :=
    support_transfer_cyclic M ξ v w hw hwq (by rw [hvp,vectorSupportProjection_apply])
  have hsep : Function.Injective (algebraVectorMap M Ω) := by
    intro a b hab
    apply sub_eq_zero.mp
    apply support_transfer_separating M ξ v w hv hvp
      (by rw [hwq,vectorSupportProjection_apply]) (a - b)
    change a.val Ω - b.val Ω = 0
    exact sub_eq_zero.mpr hab
  apply expectedMatrixSubfactorModel_of_centralizing_stages B
    (supportCompressedStages_mono A v hv hc hA) Ω hn hcyc hsep
  · intro n a ha x
    let a' : Algebra M := ⟨a,matrixUnitConcreteAlgebra_le (B n).units ha⟩
    have hcA (i j : Fin (A n).size) (y : Algebra M) :
        inner ℂ ξ (((A n).units.entry i j * y).val ξ) =
          inner ℂ ξ ((y * (A n).units.entry i j).val ξ) :=
      matrixCentralVectorSpace_centralizes A J hJ hleft ξ hξ n _
        (((A n).units.mem_concreteAlgebra _).mpr ((A n).units.entry_mem i j)) y
    have hcB (i j : Fin (B n).size) (y : Algebra M) :
        inner ℂ Ω (((B n).units.entry i j * y).val Ω) =
          inner ℂ Ω ((y * (B n).units.entry i j).val Ω) :=
      supportCompressedMatrixUnits_centralizes (A n).units ξ hcA v w hv (hc n) hwq i j y
    exact matrixUnits_vector_centralizes (B n).units Ω hcB a' x
      (((B n).units.mem_concreteAlgebra a').mp ha)
  · exact supportCompressedStages_irreducible A J hleft ξ hξ hline v hv hvp' hc

end

end KadisonKastler

end OAI
