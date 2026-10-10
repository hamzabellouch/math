import OAI.Algebra.Finitistic.Encoding.PresentationReindex
import OAI.Algebra.Finitistic.Selection.SelectionAlgebra

namespace OAI

namespace LittleFinitistic.SelectionEncoding
open QuadraticPresentation QuadraticEncoding

/-- Concrete finite coefficient data, with an exact presentation equivalence. -/
structure Encoding (k R : Type*) [Field k] [Ring R] [Algebra k R] where
  generators : ℕ
  equations : ℕ
  relations : Relations k generators equations
  equiv : Original k (Fin generators) (QuotientAction.polynomial relations) ≃ₐ[k] R

universe u v w
variable {k : Type u} {R : Type v} [Field k] [Ring R] [Algebra k R] (E : Encoding k R)

noncomputable def generator (h : Fin E.generators) : R :=
  E.equiv (originalMap k (Fin E.generators) (QuotientAction.polynomial E.relations)
    (FreeAlgebra.ι k h))

/-- These concrete elements of R satisfy every coefficient equation. -/
theorem generator_relations (j : Fin E.equations) :
    (∑ h, ∑ l, E.relations.quadratic j h l • (generator E h * generator E l)) +
    (∑ h, E.relations.linear j h • generator E h) + E.relations.constant j • (1 : R) = 0 := by
  have h := congrArg E.equiv (original_relation k (Fin E.generators)
    (QuotientAction.polynomial E.relations) j)
  simpa only [QuotientAction.polynomial,map_add,map_sum,map_smul,map_mul,map_one,map_zero,generator]
    using h

abbrev directedAlgebra := B E.relations

noncomputable instance : Ring (directedAlgebra E) :=
  ThreeVertexAlgebra.instRing (composition E.relations)

theorem directedAlgebra_finiteDimensional : FiniteDimensional k (directedAlgebra E) :=
  QuadraticEncoding.finiteDimensional E.relations

open CategoryTheory in
theorem directedAlgebra_globalDimension_le_two :
    (⨆ N : ModuleCat.{max u w} (directedAlgebra E), projectiveDimension N) ≤ (2 : ℕ) ∧
    (⨆ N : ModuleCat.{max u w} (directedAlgebra E)ᵐᵒᵖ, projectiveDimension N) ≤ (2 : ℕ) :=
  QuadraticEncoding.globalDimension_le_two E.relations

/-- The actual Section 2 selecting algebra has one fixed concrete finite encoding. -/
noncomputable def auxiliaryEncoding : Encoding ℂ SelectionRing :=
  Classical.choice (by
    obtain ⟨d,t,P,⟨E⟩⟩ := PresentationReindex.auxiliaryGroupAlgebra_has_encoding
    exact ⟨⟨d,t,P,E⟩⟩)
end LittleFinitistic.SelectionEncoding

end OAI
