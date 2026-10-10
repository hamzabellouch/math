import OAI.Algebra.AuslanderReiten.Triangular.Triangular
import OAI.Algebra.AuslanderReiten.Algebras.Radical
import Mathlib.RingTheory.Ideal.Quotient.Operations

namespace OAI

namespace ArExplicit.Triangular

variable {R F : Type*} [Ring R] [AddCommGroup F]
variable [Module R F] [Module Rᵐᵒᵖ F] [SMulCommClass R Rᵐᵒᵖ F]

theorem diagonal_kernel_square :
    (RingHom.ker (diagonal (R := R) (F := F))) ^ 2 = ⊥ := by
  apply le_antisymm _ bot_le
  rw [Submodule.pow_succ, Submodule.pow_one]
  apply Ideal.mul_le.mpr
  intro a ha b hb
  change (a.top, a.bottom) = (0, 0) at ha
  change (b.top, b.bottom) = (0, 0) at hb
  have ha₁ : a.top = 0 := congrArg Prod.fst ha
  have ha₂ : a.bottom = 0 := congrArg Prod.snd ha
  have hb₁ : b.top = 0 := congrArg Prod.fst hb
  have hb₂ : b.bottom = 0 := congrArg Prod.snd hb
  change a * b = 0
  ext <;> simp [ha₁, ha₂, hb₁, hb₂]

theorem radical_eq_comap :
    Ring.jacobson (Triangular R F) = Ideal.comap diagonal (Ring.jacobson (R × R)) := by
  apply jacobson_eq_comap_of_nil_kernel _ diagonal_surjective
  intro a ha
  refine ⟨2, ?_⟩
  have h := Ideal.pow_mem_pow ha 2
  simpa only [diagonal_kernel_square, Ideal.mem_bot] using h

theorem mem_jacobson_iff (a : Triangular R F) :
    a ∈ Ring.jacobson (Triangular R F) ↔
      a.top ∈ Ring.jacobson R ∧ a.bottom ∈ Ring.jacobson R := by
  rw [radical_eq_comap]
  exact mem_jacobson_prod_iff (a.top, a.bottom)

section Scalars

variable (k : Type*) [CommRing k] [Algebra k R] [Module k F]
variable [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass k Rᵐᵒᵖ F]

def diagonalAlg : Triangular R F →ₐ[k] R × R where
  __ := diagonal
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one]
    rfl

variable {S : Type*} [Ring S] [Algebra k S]

def quotientMap (f : R →ₐ[k] S) : Triangular R F →ₐ[k] S × S :=
  (f.prodMap f).comp (diagonalAlg k)

theorem quotientMap_surjective (f : R →ₐ[k] S) (hf : Function.Surjective f) :
    Function.Surjective (quotientMap (F := F) k f) := by
  rintro ⟨s, t⟩
  obtain ⟨r, hr⟩ := hf s
  obtain ⟨r', hr'⟩ := hf t
  exact ⟨⟨r, r', 0⟩, Prod.ext hr hr'⟩

theorem radical_eq_ker_quotientMap (f : R →ₐ[k] S)
    (hf : Ring.jacobson R = RingHom.ker f) :
    Ring.jacobson (Triangular R F) = RingHom.ker (quotientMap k f) := by
  ext a
  rw [mem_jacobson_iff, hf]
  change (f a.top = 0 ∧ f a.bottom = 0) ↔ (f a.top, f a.bottom) = (0, 0)
  simp only [Prod.mk.injEq]

noncomputable def semisimpleQuotientEquiv (f : R →ₐ[k] S)
    (hsurj : Function.Surjective f) (hker : Ring.jacobson R = RingHom.ker f) :
    (Triangular R F ⧸ Ring.jacobson (Triangular R F)) ≃ₐ[k] S × S :=
  (Ideal.quotientEquivAlgOfEq k (radical_eq_ker_quotientMap k f hker)).trans
    (Ideal.quotientKerAlgEquivOfSurjective (quotientMap_surjective k f hsurj))

end Scalars
end ArExplicit.Triangular

end OAI
