import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import OAI.Algebra.Finitistic.Encoding.QuadraticCoefficients
import OAI.Algebra.Finitistic.Localization.QuotientAction
import OAI.Algebra.Finitistic.Encoding.AuxiliaryQuadraticPresentation

namespace OAI

namespace LittleFinitistic.PresentationReindex
open QuadraticPresentation

variable {k : Type*} [Field k] {α β κ ι : Type*}

noncomputable def renameHom (e : α ≃ β) : FreeAlgebra k α →ₐ[k] FreeAlgebra k β :=
  FreeAlgebra.lift k (fun a => FreeAlgebra.ι k (e a))

@[simp] theorem rename_ι (e : α ≃ β) (a : α) :
    renameHom (k := k) e (FreeAlgebra.ι k a) = FreeAlgebra.ι k (e a) := by
  simp [renameHom]

noncomputable def rename (e : α ≃ β) : FreeAlgebra k α ≃ₐ[k] FreeAlgebra k β :=
  AlgEquiv.ofAlgHom (renameHom e) (renameHom e.symm)
    (by apply FreeAlgebra.hom_ext; funext a; simp)
    (by apply FreeAlgebra.hom_ext; funext a; simp)

@[simp] theorem rename_apply (e : α ≃ β) (p : FreeAlgebra k α) : rename e p = renameHom e p := rfl

@[simp] theorem rename_word (e : α ≃ β) (w : List α) :
    renameHom (k := k) e (word k α w) = word k β (w.map e) := by
  unfold word
  rw [map_list_prod]
  simp only [List.map_map,Function.comp_def,rename_ι]

lemma rename_degree (e : α ≃ β) {p : FreeAlgebra k α} {n : ℕ}
    (hp : p ∈ degreeLE k α n) : rename e p ∈ degreeLE k β n := by
  induction hp using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨w,hw,rfl⟩
    simpa using word_mem_degreeLE (R := k) (w.map e) n (by simpa using hw)
  | zero => simp
  | add x y hx hy ihx ihy => simpa using (degreeLE k β n).add_mem ihx ihy
  | smul r x hx ih => simpa using (degreeLE k β n).smul_mem r ih

variable (e : α ≃ β) (j : κ ≃ ι) (p : κ → FreeAlgebra k α)

noncomputable def renamedRelation (i : ι) : FreeAlgebra k β := rename e (p (j.symm i))

noncomputable def forward : Original k α p →ₐ[k] Original k β (renamedRelation e j p) :=
  (original k α p).liftₐ ((originalMap k β (renamedRelation e j p)).comp (rename e).toAlgHom)
    (RingCon.ringConGen_le.mpr (by
      rintro x y ⟨i,rfl,rfl⟩
      change originalMap k β (renamedRelation e j p) (rename e (p i)) = _
      have h := original_relation k β (renamedRelation e j p) (j i)
      simpa [renamedRelation] using h))

noncomputable def backward : Original k β (renamedRelation e j p) →ₐ[k] Original k α p :=
  (original k β (renamedRelation e j p)).liftₐ
    ((originalMap k α p).comp (rename e).symm.toAlgHom)
    (RingCon.ringConGen_le.mpr (by
      rintro x y ⟨i,rfl,rfl⟩
      change originalMap k α p ((rename e).symm (rename e (p (j.symm i)))) = _
      simpa only [AlgEquiv.symm_apply_apply,map_zero,AlgHom.comp_apply] using original_relation k α p (j.symm i)))

@[simp] theorem forward_mk (f : FreeAlgebra k α) :
    forward e j p (originalMap k α p f) =
      originalMap k β (renamedRelation e j p) (rename e f) := rfl

@[simp] theorem backward_mk (f : FreeAlgebra k β) :
    backward e j p (originalMap k β (renamedRelation e j p) f) =
      originalMap k α p ((rename e).symm f) := rfl

/-- Relabeling finite generators and relations preserves the actual presented algebra. -/
noncomputable def presentationEquiv : Original k α p ≃ₐ[k] Original k β (renamedRelation e j p) :=
  AlgEquiv.ofAlgHom (forward e j p) (backward e j p)
    (by
      apply AlgHom.ext
      intro x
      obtain ⟨f,rfl⟩ := (original k β (renamedRelation e j p)).mkₐ_surjective (α := k) x
      change forward e j p (backward e j p
        (originalMap k β (renamedRelation e j p) f)) = originalMap k β (renamedRelation e j p) f
      rw [backward_mk,forward_mk,AlgEquiv.apply_symm_apply])
    (by
      apply AlgHom.ext
      intro x
      obtain ⟨f,rfl⟩ := (original k α p).mkₐ_surjective (α := k) x
      change backward e j p (forward e j p (originalMap k α p f)) = originalMap k α p f
      rw [forward_mk,backward_mk,AlgEquiv.symm_apply_apply])

/-- Every finite list of quadratic polynomials has the concrete coefficient interface
used by the three-vertex algebra. -/
theorem exists_relations {d t : ℕ} (p : Fin t → FreeAlgebra k (Fin d))
    (hp : ∀ i, p i ∈ degreeLE k (Fin d) 2) :
    ∃ P : QuadraticEncoding.Relations k d t, ∀ i, QuotientAction.polynomial P i = p i := by
  classical
  choose c l q h using fun i => exists_coefficients k (Fin d) (p i) (hp i)
  refine ⟨⟨c,l,q⟩,?_⟩
  intro i
  rw [← h i]
  simp only [QuotientAction.polynomial,coefficientPolynomial,Algebra.algebraMap_eq_smul_one]
  abel

/-- Finite generator and equation types may both be replaced by Fin, and all
coefficient choices preserve the exact quotient algebra. -/
theorem finite_quadratic_encoding [Finite α] [Finite κ]
    (p : κ → FreeAlgebra k α) (hp : ∀ i, p i ∈ degreeLE k α 2) :
    ∃ (d t : ℕ) (P : QuadraticEncoding.Relations k d t),
      Nonempty (Original k (Fin d) (QuotientAction.polynomial P) ≃ₐ[k] Original k α p) := by
  classical
  let := Fintype.ofFinite α
  let := Fintype.ofFinite κ
  let e := Fintype.equivFin α
  let j := Fintype.equivFin κ
  let p' := renamedRelation e j p
  have hp' (i) : p' i ∈ degreeLE k (Fin (Fintype.card α)) 2 := rename_degree e (hp (j.symm i))
  obtain ⟨P,hP⟩ := exists_relations p' hp'
  refine ⟨Fintype.card α,Fintype.card κ,P,?_⟩
  have heq : QuotientAction.polynomial P = p' := funext hP
  rw [heq]
  exact ⟨(presentationEquiv e j p).symm⟩

/-- The entire actual complex group algebra feeds the finite directed encoding. -/
theorem auxiliaryGroupAlgebra_has_encoding :
    ∃ (d t : ℕ) (P : QuadraticEncoding.Relations ℂ d t),
      Nonempty (Original ℂ (Fin d) (QuotientAction.polynomial P) ≃ₐ[ℂ]
        MonoidAlgebra ℂ Presentation.AuxiliaryGroup) := by
  obtain ⟨d,t,P,⟨E⟩⟩ := finite_quadratic_encoding auxiliaryRelation auxiliaryRelation_degree
  exact ⟨d,t,P,⟨E.trans auxiliaryQuadraticEquiv⟩⟩

end LittleFinitistic.PresentationReindex

end OAI
