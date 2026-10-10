import OAI.Algebra.Finitistic.Rectification.SourceFiltrationExact

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open LittleFinitistic.RectificationTotal
noncomputable section
namespace ExternalTensor.Section4.SourceFiltration
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable {A J R : Type} [Fintype A] [Fintype J] [Fintype R]
variable (t : AssemblyData (C := BiComplex k B) (A := A) (J := J) (R := R))

@[reassoc (attr := simp)]
theorem inr_prod {S : Type u} [Ring S] (X Y : ModuleCat.{u} S) :
    (biprod.inr : Y ⟶ X ⊞ Y) ≫ (ModuleCat.biprodIsoProd X Y).hom =
      ModuleCat.ofHom (LinearMap.inr S X Y) := by
  apply (cancel_mono (ModuleCat.biprodIsoProd X Y).inv).1
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply biprod.hom_ext
  · simp only [Category.assoc, ModuleCat.biprodIsoProd_inv_comp_fst, biprod.inr_fst]
    rfl
  · simp only [Category.assoc, ModuleCat.biprodIsoProd_inv_comp_snd, biprod.inr_snd]
    rfl

omit [Fintype R] in
/-- The canonical zero-column inclusion has exactly its original term coordinate. -/
theorem inclusion_product (n : ℤ) :
    (inclusion (p2 t) 0 (h2 t)).f n ≫ (totalTermIso (p2 t) 0 (h2 t) n).hom =
      ModuleCat.ofHom (LinearMap.inr (Enveloping k B)
        (Z.X (n+2) × Z.X (n+1)) (t.V₂.X n)) := by
  dsimp only [totalTermIso, termIso, LittleFinitistic.RectificationTotal.inclusion]
  erw [Iso.trans_hom, Iso.trans_hom, Iso.trans_hom,
    biprod.mapIso_hom, Iso.refl_hom, biprod.mapIso_hom, Iso.refl_hom]
  erw [← Category.assoc, ← Category.assoc, ← Category.assoc,
    cone_inr_termIso, biprod.inr_map, Category.id_comp, biprod.inr_map, Category.id_comp]
  exact inr_prod _ _

omit [Fintype R] in
/-- Removing the two zero columns preserves the actual V2 inclusion. -/
theorem inclusion2_bijective (n : ℤ) :
    Function.Bijective ((inclusion (p2 t) 0 (h2 t)).f n) := by
  let e := (totalTermIso (p2 t) 0 (h2 t) n).toLinearEquiv
  have he (x : t.V₂.X n) : e ((inclusion (p2 t) 0 (h2 t)).f n x) = ((0,0),x) :=
    congrArg (fun a => a x) (inclusion_product t n)
  refine ⟨?_, ?_⟩
  · intro x y hxy
    have := congrArg e hxy
    simpa only [he] using congrArg Prod.snd this
  · intro y
    refine ⟨(e y).2, e.injective ?_⟩
    rw [he]
    exact Prod.ext (Subsingleton.elim _ _) rfl

instance inclusion2_isIso : IsIso (inclusion (p2 t) 0 (h2 t)) := by
  have (n : ℤ) : IsIso ((inclusion (p2 t) 0 (h2 t)).f n) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (inclusion2_bijective t n)
  exact HomologicalComplex.Hom.isIso_of_components _

def v2Iso : t.V₂ ≅ total (p2 t) 0 (h2 t) := asIso (inclusion (p2 t) 0 (h2 t))

/-- F>=2 really is V2, embedded by its original vertex summand inclusion. -/
def v2Inclusion : t.V₂ ⟶ total (p1 t) 0 (h1 t) :=
  biprod.inr ≫ inclusion (p1 t) 0 (h1 t)

omit [Fintype R] in
theorem v2Inclusion_eq : v2Inclusion t = (v2Iso t).hom ≫ (include2 t).totalMap := by
  symm
  exact (include2 t).inclusion_totalMap

omit [Fintype R] in
/-- The source-one sequence with V2 itself as its first term. -/
theorem v2_shortExact (n : ℤ) :
    Function.Injective ((v2Inclusion t).f n) ∧
    Function.Exact ((v2Inclusion t).f n) ((quotient1 t).totalMap.f n) ∧
    Function.Surjective ((quotient1 t).totalMap.f n) := by
  have E := source1_shortExact t n
  have I := inclusion2_bijective t n
  rw [v2Inclusion_eq]
  refine ⟨E.1.comp I.1, ?_, E.2.2⟩
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx⟩ := (E.2.1 y).mp hy
    obtain ⟨z, rfl⟩ := I.2 x
    exact ⟨z, hx⟩
  · rintro ⟨x, rfl⟩
    exact E.2.1.apply_apply_eq_zero _

variable (h : Homotopy (t.q ≫ t.p) 0)
/-- The composite filtration inclusion is the original V2-to-total map. -/
theorem v2_nested : v2Inclusion t ≫ (include1 t h).totalMap =
    t.in₂ ≫ inclusion t.p t.q h := by
  dsimp only [v2Inclusion]
  rw [Category.assoc, (include1 t h).inclusion_totalMap]
  rfl
end ExternalTensor.Section4.SourceFiltration

end

end OAI
