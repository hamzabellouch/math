import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.Algebra.Homology.Linear

namespace OAI

namespace LittleFinitistic.ChainRepresentatives
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open HomologicalComplex

variable {k : Type*} [CommRing k]
variable {V : Type*} [Category V] [Preadditive V] [Linear k V]
variable {ι : Type*} {s : ComplexShape ι}

/-- Choosing chain representatives of a finite quadratic diagram supplies actual,
specified null-homotopies for all its relations. -/
theorem quadratic_chain_representatives (na nb nr : ℕ)
    (D₀ D₁ D₂ : HomologicalComplex V s)
    (a : Fin na → ((HomotopyCategory.quotient V s).obj D₀ ⟶
      (HomotopyCategory.quotient V s).obj D₁))
    (b : Fin nb → ((HomotopyCategory.quotient V s).obj D₁ ⟶
      (HomotopyCategory.quotient V s).obj D₂))
    (c : Fin nr → Fin na → Fin nb → k)
    (hc : ∀ t, ∑ i, ∑ j, c t i j • (a i ≫ b j) = 0) :
    ∃ (f : Fin na → (D₀ ⟶ D₁)) (g : Fin nb → (D₁ ⟶ D₂)),
      (∀ i, (HomotopyCategory.quotient V s).map (f i) = a i) ∧
      (∀ j, (HomotopyCategory.quotient V s).map (g j) = b j) ∧
      Nonempty (∀ t, Homotopy (∑ i, ∑ j, c t i j • (f i ≫ g j)) 0) := by
  classical
  let q := HomotopyCategory.quotient V s
  let f := fun i => q.preimage (a i)
  let g := fun j => q.preimage (b j)
  have hf (i) : q.map (f i) = a i := q.map_preimage _
  have hg (j) : q.map (g j) = b j := q.map_preimage _
  refine ⟨f,g,hf,hg,⟨fun t => ?_⟩⟩
  apply HomotopyCategory.homotopyOfEq
  change q.map (∑ i, ∑ j, c t i j • (f i ≫ g j)) = q.map 0
  simp only [Functor.map_sum,Functor.map_smul,Functor.map_comp,hf,hg,Functor.map_zero,hc]

/-- In cochain conventions the chosen homotopy has degree minus one, with the
exact differential equation used in the tensor construction. -/
theorem cochain_null_homotopy_equation {D E : CochainComplex V ℤ}
    (f : D ⟶ E) (h : Homotopy f 0) (i : ℤ) :
    f.f i = D.d i (i+1) ≫ h.hom (i+1) i + h.hom i (i-1) ≫ E.d (i-1) i := by
  have hi := h.comm i
  rw [dNext_eq h.hom (show (ComplexShape.up ℤ).Rel i (i+1) by simp),
    prevD_eq h.hom (show (ComplexShape.up ℤ).Rel (i-1) i by simp)] at hi
  simpa only [zero_f,add_zero] using hi
end LittleFinitistic.ChainRepresentatives

end OAI
