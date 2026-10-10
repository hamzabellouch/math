import OAI.Analysis.KadisonKastler.RelativeProjectionInsertion
import OAI.Analysis.KadisonKastler.NormalizedStageReference
import OAI.Analysis.KadisonKastler.ExpectedFromProjectionCuts

namespace OAI

/-! # Expected matrix subfactors from relative bicentralizer triviality

Faithful-state homogeneity and scalar bicentralizers for finite-matrix
relative algebras give expected matrix subfactors on the original space.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

local instance expectedRelativeRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

theorem expectedMatrixSubfactorModel_of_relative_bicentralizers
    (hM : TypeIIIFactor M) (ξ : H) (hunit : ‖ξ‖=1)
    (hsep : Function.Injective (algebraVectorMap M ξ))
    (hcyc : DenseRange (algebraVectorMap M ξ)) (d : ModularConjugationData M ξ)
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic d.conjugation a ξ))
    (hhom : ∀ E : FiniteMatrixStage M, FaithfulVectorStateHomogeneity E.units.relativeVonNeumann)
    (hscalar : ∀ (E : FiniteMatrixStage M) (ω : H),
      ω ∈ modularPositiveCone (M := M) d.conjugation ξ → ‖ω‖=1 →
      Function.Injective (algebraVectorMap M ω) →
      ω ∈ centralVectorSpace (matrixUnitConcreteAlgebra E.units) d.conjugation →
      ∀ b : Algebra E.units.relativeVonNeumann, stateBicentralizerMember ω b →
        ∃ z : ℂ, b=z • 1) :
    Nonempty (ExpectedMatrixSubfactorModel M) := by
  apply expectedMatrixSubfactorModel_of_projection_cuts_with_gap hM ξ hunit d (1/128)
    (by norm_num) (by norm_num)
  intro E η hηE horth δ hδ
  by_cases hη : η=0
  · refine ⟨E,⟨0,IsStarProjection.zero _⟩,matrixStageCentralProjection E d.conjugation ξ,
      le_rfl,E.units.concreteAlgebra.zero_mem,Submodule.starProjection_apply_mem _ _,?_,?_⟩
    · simpa only [sub_self,norm_zero] using hδ.le
    · simp only [hη,map_zero,sub_self,norm_zero]
      norm_num
  obtain ⟨ω,n,hn,hn1,hscale,hωunit,hωcone,hωsep,hωE⟩ :=
    exists_normalized_matrix_reference E d.conjugation d.involutive (d.right_mem le_rfl)
      ξ d.fixes_vector hunit hsep hpos
  have horthω : inner ℂ ω η=0 := by
    have hz : inner ℂ η (n • ω)=0 := hscale.symm ▸ horth
    rw [inner_smul_right_eq_smul] at hz
    have he : inner ℂ η ω=0 := (smul_eq_zero.mp hz).resolve_left hn.ne'
    exact inner_eq_zero_symm.mp he
  obtain ⟨F,p,ζ,hEF,hp,hζ,hclose,hgap⟩ := hM.exists_relative_projection_insertion E (hhom E)
    d.conjugation d.involutive (d.right_mem le_rfl) d.left_mem ξ d.fixes_vector hcyc hpos
    ω hωcone hωunit hωsep hωE (hscalar E ω hωcone hωunit hωsep hωE)
    η hη hηE horthω δ hδ
  refine ⟨F,p,n • ζ,hEF,hp,?_,?_,hgap⟩
  · exact (centralVectorSpace (matrixUnitConcreteAlgebra F.units) d.conjugation).smul_of_tower_mem n hζ
  · rw [← hscale,← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos hn]
    have hd : ‖ω-ζ‖ ≤ δ := by rwa [norm_sub_rev]
    exact (mul_le_mul_of_nonneg_left hd hn.le).trans (by nlinarith)

end

end KadisonKastler

end OAI
