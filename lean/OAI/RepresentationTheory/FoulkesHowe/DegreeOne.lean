import OAI.RepresentationTheory.FoulkesHowe.Model

namespace OAI

noncomputable section
universe u
namespace Problem346

variable (V : Type u) [AddCommGroup V] [Module ℂ V]

lemma symmetricAlgebra_ι_injective :
    Function.Injective (SymmetricAlgebra.ι ℂ V) := by
  let : Module ℂᵐᵒᵖ V := Module.compHom _ ((RingHom.id ℂ).fromOpposite mul_comm)
  have : IsCentralScalar ℂ V := ⟨fun _ _ => rfl⟩
  intro x y h
  have h' := congrArg (SymmetricAlgebra.lift (TrivSqZeroExt.inrHom ℂ V)) h
  apply TrivSqZeroExt.inr_injective (R := ℂ)
  simpa using h'

@[simp] lemma symMonomialRaw_one (v : Fin 1 → V) :
    symMonomialRaw 1 V v = SymmetricAlgebra.ι ℂ V (v 0) := by
  simp [symMonomialRaw]

lemma symPowSubmodule_one :
    symPowSubmodule 1 V = LinearMap.range (SymmetricAlgebra.ι ℂ V) := by
  have h : Set.range (symMonomialRaw 1 V) =
      Set.range (SymmetricAlgebra.ι ℂ V) := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨v 0, (symMonomialRaw_one V v).symm⟩
    · rintro ⟨v, rfl⟩
      exact ⟨fun _ => v, symMonomialRaw_one V (fun _ => v)⟩
  rw [symPowSubmodule, h]
  exact Submodule.span_eq (LinearMap.range (SymmetricAlgebra.ι ℂ V))

/-- The canonical inclusion of a vector into the degree-one symmetric power. -/
def symPowOneIntro : V →ₗ[ℂ] SymPow 1 V :=
  (SymmetricAlgebra.ι ℂ V).codRestrict (symPowSubmodule 1 V) (by
    intro v
    rw [symPowSubmodule_one]
    exact ⟨v, rfl⟩)

@[simp] lemma symPowOneIntro_coe (v : V) :
    (symPowOneIntro V v : SymmetricAlgebra ℂ V) = SymmetricAlgebra.ι ℂ V v := rfl

lemma symPowOneIntro_bijective : Function.Bijective (symPowOneIntro V) := by
  constructor
  · intro x y h
    apply symmetricAlgebra_ι_injective V
    exact congrArg Subtype.val h
  · intro x
    have hx := x.property
    have hx' : (x : SymmetricAlgebra ℂ V) ∈ LinearMap.range (SymmetricAlgebra.ι ℂ V) := by
      simpa only [symPowSubmodule_one] using hx
    rcases hx' with ⟨v, hv⟩
    exact ⟨v, Subtype.ext hv⟩

/-- The degree-one symmetric power is canonically the original vector space. -/
def symPowOneEquiv : SymPow 1 V ≃ₗ[ℂ] V :=
  (LinearEquiv.ofBijective (symPowOneIntro V) (symPowOneIntro_bijective V)).symm

@[simp] lemma symPowOneEquiv_symm_apply (v : V) :
    (symPowOneEquiv V).symm v = symMonomial 1 V (fun _ => v) := by
  apply Subtype.ext
  exact (symMonomialRaw_one V (fun _ => v)).symm

@[simp] lemma symPowOneEquiv_symMonomial (v : Fin 1 → V) :
    symPowOneEquiv V (symMonomial 1 V v) = v 0 := by
  apply (symPowOneEquiv V).symm.injective
  simp only [LinearEquiv.symm_apply_apply, symPowOneEquiv_symm_apply]
  apply Subtype.ext
  simp only [symMonomial, symMonomialRaw_one]

end Problem346

end

end OAI
