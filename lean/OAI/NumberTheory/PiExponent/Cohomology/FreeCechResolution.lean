import OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology

namespace OAI

namespace PiExponent.GeometrySupport.FreeCechResolution

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology TopologicalSpace

universe u

def tupleSimplex (V : Type u) : SimplicialObject (Type u) where
  obj n := ToType n.unop → V
  map f := ↾fun t => t ∘ f.unop.toOrderHom
  map_id _ := rfl
  map_comp _ _ := rfl

def tupleAugmented (V : Type u) : SimplicialObject.Augmented (Type u) :=
  (tupleSimplex V).augmentOfIsTerminal Types.isTerminalPUnit

def tupleExtraDegeneracy {V : Type u} (p : V) :
    (tupleAugmented V).ExtraDegeneracy where
  s' := ↾fun _ _ => p
  s n := ↾fun t => Fin.cons p t
  s'_comp_ε := rfl
  s₀_comp_δ₁ := by
    ext t
    funext i
    fin_cases i
    rfl
  s_comp_δ₀ n := by
    ext t
    funext i
    rfl
  s_comp_δ n i := by
    ext t
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · change (Fin.cons p t : Fin (n + 3) → V) (i.succ.succAbove j.succ) = t (i.succAbove j)
      simp only [Fin.succ_succAbove_succ]
      rfl
  s_comp_σ n i := by
    ext t
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · change (Fin.cons p t : Fin (n + 2) → V) (i.succ.predAbove j.succ) = t (i.predAbove j)
      simp only [Fin.succ_predAbove_succ]
      rfl

def freeTupleComplex (R : RingCat.{u}) (V : Type u) : ChainComplex (ModuleCat R) ℕ :=
  AlternatingFaceMapComplex.obj (tupleSimplex V ⋙ ModuleCat.free R)

theorem freeTupleComplex_exact (R : RingCat.{u}) (V : Type u) (q : ℕ) :
    (freeTupleComplex R V).ExactAt (q + 1) := by
  classical
  cases isEmpty_or_nonempty V with
  | inl h =>
    let : IsEmpty (Fin (q + 2) → V) := ⟨fun t => isEmptyElim (t 0)⟩
    change ((freeTupleComplex R V).sc (q + 1)).Exact
    apply ShortComplex.exact_of_isZero_X₂
    have hz : Subsingleton (((Fin (q + 2) → V) →₀ R)) := inferInstance
    exact ModuleCat.isZero_of_subsingleton (ModuleCat.of R ((Fin (q + 2) → V) →₀ R))
  | inr h =>
    let p : V := Classical.choice h
    let e := ((tupleExtraDegeneracy p).map (ModuleCat.free R)).homotopyEquiv
    apply (exactAt_iff_of_quasiIsoAt e.hom (q + 1)).2
    exact HomologicalComplex.exactAt_single_obj (ComplexShape.down ℕ) 0 _
      (q + 1) (by omega)

def coverVertices {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X) :
    (Opens X)ᵒᵖ ⥤ Type u where
  obj W := {i : ι // W.unop ≤ U i}
  map f := ↾fun i => ⟨i.val, (leOfHom f.unop).trans i.property⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def tuplePresheaf {C : Type u} [Category.{u} C] (V : Cᵒᵖ ⥤ Type u) :
    SimplicialObject (Cᵒᵖ ⥤ Type u) where
  obj n :=
    { obj W := ToType n.unop → V.obj W
      map f := ↾fun t i => V.map f (t i)
      map_id W := by ext t i; simp
      map_comp f g := by ext t i; simp }
  map f := { app W := ↾fun t => t ∘ f.unop.toOrderHom }
  map_id _ := rfl
  map_comp _ _ := rfl

def freePresheafComplex {C : Type u} [Category.{u} C] (R : Cᵒᵖ ⥤ RingCat.{u})
    (V : Cᵒᵖ ⥤ Type u) : ChainComplex (PresheafOfModules.{u} R) ℕ :=
  AlternatingFaceMapComplex.obj (tuplePresheaf V ⋙ PresheafOfModules.free R)

theorem exact_of_objectwise {C : Type u} [Category.{u} C]
    (R : Cᵒᵖ ⥤ RingCat.{u}) (S : ShortComplex (PresheafOfModules.{u} R))
    (hS : ∀ W, (S.map (PresheafOfModules.evaluation R W)).Exact) : S.Exact := by
  simp only [ShortComplex.exact_iff_isZero_homology] at hS ⊢
  rw [IsZero.iff_id_eq_zero]
  ext1 W
  apply (IsZero.of_iso (hS W)
    (S.mapHomologyIso (PresheafOfModules.evaluation R W)).symm).eq_of_src

theorem evaluation_freePresheafComplex {C : Type u} [Category.{u} C]
    (R : Cᵒᵖ ⥤ RingCat.{u}) (V : Cᵒᵖ ⥤ Type u) (W : Cᵒᵖ) :
    ((PresheafOfModules.evaluation R W).mapHomologicalComplex _).obj
      (freePresheafComplex R V) = freeTupleComplex (R.obj W) (V.obj W) := by
  change ((alternatingFaceMapComplex _ ⋙
    (PresheafOfModules.evaluation R W).mapHomologicalComplex _).obj
      (tuplePresheaf V ⋙ PresheafOfModules.free R)) = _
  rw [map_alternatingFaceMapComplex]
  rfl

theorem freePresheafComplex_exact {C : Type u} [Category.{u} C]
    (R : Cᵒᵖ ⥤ RingCat.{u}) (V : Cᵒᵖ ⥤ Type u) (q : ℕ) :
    (freePresheafComplex R V).ExactAt (q + 1) := by
  change ((freePresheafComplex R V).sc (q + 1)).Exact
  apply exact_of_objectwise R
  intro W
  have h := freeTupleComplex_exact (R.obj W) (V.obj W) q
  rw [← evaluation_freePresheafComplex R V W] at h
  exact h

def freeSheafComplex {X : TopCat.{u}}
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (V : (Opens X)ᵒᵖ ⥤ Type u) : ChainComplex (SheafOfModules.{u} R) ℕ :=
  ((PresheafOfModules.sheafification (𝟙 R.obj)).mapHomologicalComplex _).obj
    (freePresheafComplex R.obj V)

theorem freeSheafComplex_exact {X : TopCat.{u}}
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (V : (Opens X)ᵒᵖ ⥤ Type u) (q : ℕ) :
    (freeSheafComplex R V).ExactAt (q + 1) := by
  change (((freePresheafComplex R.obj V).sc (q + 1)).map
    (PresheafOfModules.sheafification (𝟙 R.obj))).Exact
  exact (freePresheafComplex_exact R.obj V q).map _

end
end PiExponent.GeometrySupport.FreeCechResolution

end OAI
