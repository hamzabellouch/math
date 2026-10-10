import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedRelabel
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedSupportTelescopingActual

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedSupportTransport
open SymbolicHistory TemplateSupportRemoval TemplateOneSidedSupportTelescoping
open TemplateOneSidedRelabel Template
attribute [local instance] Classical.propDecidable
variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

def relabelFamilies (π : ι ≃ κ) (D : ι → Finset (Expr ι)) (i : κ) : Finset (Expr κ) :=
  (D (π.symm i)).image (relabel π)

theorem setZero_rename (π : ι ≃ κ) (i : ι) (P : MvPolynomial ι ℤ) :
    ZeroVariable.setZero (π i) (MvPolynomial.rename π P)=
      MvPolynomial.rename π (ZeroVariable.setZero i P) := by
  have hh : (ZeroVariable.setZero (π i)).comp (MvPolynomial.rename π).toRingHom =
      (MvPolynomial.rename π).toRingHom.comp (ZeroVariable.setZero i) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [ZeroVariable.setZero]
    · intro j
      by_cases hj : j=i
      · subst j
        simp [ZeroVariable.setZero]
      · have hp : π j≠π i := fun h=>hj (π.injective h)
        simp [ZeroVariable.setZero,hj,hp]
  exact congrArg (fun h : MvPolynomial ι ℤ →+* MvPolynomial κ ℤ=>h P) hh

theorem eraseCoordinate_relabel_ne_zero (π : ι ≃ κ) (i : ι) (q : Expr ι) :
    eraseCoordinate (π i) (relabel π q).numerator≠0 ↔ eraseCoordinate i q.numerator≠0 := by
  rw [eraseCoordinate_ne_zero_iff,eraseCoordinate_ne_zero_iff,relabel_numerator,setZero_rename]
  exact not_congr (MvPolynomial.rename_eq_zero_iff_of_injective _ π.injective)

omit [DecidableEq ι] [DecidableEq κ] in
@[simp] theorem familyCoprime_relabel [DecidableEq ι] [DecidableEq κ]
    (π : ι ≃ κ) (D : ι → Finset (Expr ι))
    (i : ι) (a : κ → ℤ) :
    familyCoprime (relabelFamilies π D) (π i) a ↔
      familyCoprime D i (fun j=>a (π j)) := by
  simp only [familyCoprime,relabelFamilies,π.symm_apply_apply,Finset.forall_mem_image,
    relabel_integerEval]

@[simp] theorem familyPolynomial_relabel (π : ι ≃ κ) (D : ι → Finset (Expr ι)) (i : ι) :
    familyPolynomial (relabelFamilies π D) (π i) ↔ familyPolynomial D i := by
  simp only [familyPolynomial,relabelFamilies,π.symm_apply_apply,Finset.forall_mem_image,
    eraseCoordinate_relabel_ne_zero]

theorem hybridSupport_relabel (π : ι ≃ κ) (D : ι → Finset (Expr ι))
    (removed : Finset ι) (core : (ι → ℤ) → Prop) (a : κ → ℤ) :
    hybridSupport (removed.map π.toEmbedding) (fun x=>core (fun i=>x (π i)))
      (familyCoprime (relabelFamilies π D)) (familyPolynomial (relabelFamilies π D)) a ↔
    hybridSupport removed core (familyCoprime D) (familyPolynomial D) (fun i=>a (π i)) := by
  unfold hybridSupport
  apply and_congr_right
  intro _
  constructor
  · intro h i
    have hh := h (π i)
    simpa only [Finset.mem_map_equiv,π.symm_apply_apply,
      familyCoprime_relabel,familyPolynomial_relabel] using hh
  · intro h i
    obtain ⟨j,rfl⟩ := π.surjective i
    simpa only [Finset.mem_map_equiv,π.symm_apply_apply,
      familyCoprime_relabel,familyPolynomial_relabel] using h j

theorem hybridValue_relabel (π : ι ≃ κ) (D : ι → Finset (Expr ι))
    (removed : Finset ι) (core : (ι → ℤ) → Prop) (f : (ι → ℤ) → ℂ) (a : κ → ℤ) :
    hybridValue (removed.map π.toEmbedding) (fun x=>core (fun i=>x (π i)))
      (familyCoprime (relabelFamilies π D)) (familyPolynomial (relabelFamilies π D))
      (fun x=>f (fun i=>x (π i))) a =
    hybridValue removed core (familyCoprime D) (familyPolynomial D) f (fun i=>a (π i)) := by
  simp only [hybridValue,hybridSupport_relabel]

end Ostmann.Characters.TemplateOneSidedSupportTransport

end

end OAI
