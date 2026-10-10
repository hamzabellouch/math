import OAI.Algebra.AuslanderReiten.BaseChange.ScalarExtensionComplete
import OAI.Algebra.AuslanderReiten.BaseChange.ScalarExtensionExt
import OAI.Algebra.AuslanderReiten.BaseChange.ScalarExtensionDescent
import OAI.Algebra.AuslanderReiten.BaseChange.ScalarExtensionStructure
import Mathlib.RingTheory.TensorProduct.Finite

namespace OAI

noncomputable section

namespace ArExplicit

open scoped TensorProduct

universe u v

variable {k R M : Type u} [Field k] [Ring R] [Algebra k R]
variable [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
variable (E : Type (max u v)) [Field E] [Algebra k E]

attribute [local instance] scalarExtensionModule

theorem MainConclusions.scalarExtension (h : MainConclusions k R M) :
    MainConclusions E (E ⊗[k] R) (E ⊗[k] M) := by
  obtain ⟨hR, hM, hn, hgp, hself, _, ⟨e⟩, hrad⟩ := h
  let := hR
  let := hM
  let : Module.Finite R M := Module.Finite.of_restrictScalars_finite k R M
  have hgpE := hgp.scalarExtension k E R M
  let f : R →ₐ[k] (Fin 8 → k) := e.toAlgHom.comp (Ideal.Quotient.mkₐ k (Ring.jacobson R))
  have hf : Function.Surjective f := e.surjective.comp (Ideal.Quotient.mk_surjective)
  have hJ : Ring.jacobson R = RingHom.ker f := by
    ext x
    change x ∈ Ring.jacobson R ↔ e (Ideal.Quotient.mk (Ring.jacobson R) x) = 0
    rw [map_eq_zero_iff e e.injective, Ideal.Quotient.eq_zero_iff_mem]
  exact ⟨inferInstance, inferInstance, nonprojective_scalarExtension k E R hn,
    hgpE, hself.scalarExtension k E R M M hgp, hgpE.positiveExt_regular,
    ⟨scalarExtension_semisimpleQuotientEquiv E f hf hJ⟩,
    scalarExtension_radical_pow_ne_bot E 4 hrad⟩

theorem fullMainTheorem_of_mainConclusions (c : Candidate)
    (h : MainConclusions BaseField c.R c.M) : FullMainTheorem.{v} := by
  refine ⟨c, h, ?_⟩
  intro E _ _
  exact h.scalarExtension E

end ArExplicit

end

end OAI
