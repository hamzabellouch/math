import OAI.CategoryTheory.ThickClosure.PeriodicSplitting

namespace OAI

noncomputable section
open scoped BigOperators nonZeroDivisors
open LinearMap Submodule
open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace HahnWilson.PeriodicDerived
section Localization
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open HahnWilson.PrincipalModules HahnWilson.PeriodicSplitting
universe u w
variable (R : Type u) [Ring R] (D : ℕ)

abbrev PeriodicComplex := ChainComplex (ModuleCat.{u} R) (ZMod D)

def GradedFiniteFree (P : PeriodicComplex R D) : Prop :=
  (∀ i j, P.d i j = 0) ∧ ∀ i, Module.Free R (P.X i) ∧ Module.Finite R (P.X i)

inductive FiniteCell : PeriodicComplex R D → Prop
  | free {P} (h : GradedFiniteFree R D P) : FiniteCell P
  | cone {P Q} (f : P ⟶ Q) (hP : FiniteCell P) (hQ : FiniteCell Q) :
      FiniteCell (homotopyCofiber f)
  | iso {P Q} (e : P ≅ Q) (hP : FiniteCell P) : FiniteCell Q

variable [(HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.down (ZMod D))).HasLocalization.{w}]

abbrev _root_.OAI.HahnWilson.PeriodicDerived :=
  HomologicalComplexUpToQuasiIso (ModuleCat.{u} R) (ComplexShape.down (ZMod D))

abbrev Q : PeriodicComplex R D ⥤ PeriodicDerived R D :=
  HomologicalComplexUpToQuasiIso.Q

abbrev homology (i : ZMod D) : PeriodicDerived R D ⥤ ModuleCat.{u} R :=
  HomologicalComplexUpToQuasiIso.homologyFunctor _ _ i

def IsPerfect (P : PeriodicDerived R D) : Prop :=
  ∃ C : PeriodicComplex R D, FiniteCell R D C ∧
    Nonempty (Retract P ((Q R D).obj C))

end Localization

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open HahnWilson.PrincipalModules HahnWilson.PeriodicSplitting
universe u w
variable {R : Type u} [Ring R] {D : ℕ}

lemma finiteCell_terms {P : PeriodicComplex R D} (hP : FiniteCell R D P) :
    ∀ i, Module.Free R (P.X i) ∧ Module.Finite R (P.X i) := by
  induction hP with
  | free h => exact h.2
  | @cone P Q f hP hQ ihP ihQ =>
      intro i
      let := (ihP (i - 1)).1
      let := (ihP (i - 1)).2
      let := (ihQ i).1
      let := (ihQ i).2
      let e := (homotopyCofiber.XIsoBiprod f i (i - 1)
        (sub_add_cancel i 1)).toLinearEquiv.trans
        (ModuleCat.biprodIsoProd (P.X (i - 1)) (Q.X i)).toLinearEquiv
      exact ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm⟩
  | @iso P Q e hP ih =>
      intro i
      let := (ih i).1
      let := (ih i).2
      let el : (P.X i) ≃ₗ[R] (Q.X i) :=
        ((HomologicalComplex.eval _ _ i).mapIso e).toLinearEquiv
      exact ⟨Module.Free.of_equiv el, Module.Finite.equiv el⟩

lemma down_prev (i : ZMod D) : (ComplexShape.down (ZMod D)).Rel i (i - 1) :=
  sub_add_cancel i 1

lemma cofiber_XIso_hom_snd {P Q : PeriodicComplex R D} (f : P ⟶ Q)
    (i j : ZMod D) (hij : (ComplexShape.down (ZMod D)).Rel i j) :
    (homotopyCofiber.XIsoBiprod f i j hij).hom ≫ biprod.snd =
      homotopyCofiber.sndX f i := by
  obtain rfl := (ComplexShape.down (ZMod D)).next_eq' hij
  simp only [homotopyCofiber.sndX, dite_eq_left hij]

section ResolutionCell
variable (F G : ZMod D → ModuleCat.{u} R) (r : ∀ i, G i ⟶ F i)

def diagonalFamilyMap : diagonalComplex G ⟶ diagonalComplex F where
  f := r
  comm' i j hij := by
    change r i ≫ (diagonalComplex F).d i j = (diagonalComplex G).d i j ≫ r j
    rw [diagonalComplex_d, diagonalComplex_d]
    simp

def resolutionConeIso : homotopyCofiber (diagonalFamilyMap F G r) ≅
    resolutionComplex F G r := by
  classical
  let φ := diagonalFamilyMap F G r
  let e (i : ZMod D) : (homotopyCofiber φ).X i ≅ (resolutionComplex F G r).X i :=
    homotopyCofiber.XIsoBiprod φ i (i - 1) (down_prev i) ≪≫
      biprod.braiding (G (i - 1)) (F i)
  have efst (i : ZMod D) : (e i).hom ≫ biprod.fst = homotopyCofiber.sndX φ i := by
    dsimp [e]
    rw [Category.assoc, biprod.braiding_hom, biprod.lift_fst]
    exact cofiber_XIso_hom_snd φ i (i - 1) (down_prev i)
  have esnd (i : ZMod D) : (e i).hom ≫ biprod.snd =
      homotopyCofiber.fstX φ i (i - 1) (down_prev i) := by
    dsimp [e, homotopyCofiber.fstX]
    simp only [Category.assoc, biprod.braiding_hom, biprod.lift_snd]
  refine Hom.isoOfComponents e ?_
  intro i j hij
  have hji : j = i - 1 := eq_sub_iff_add_eq.mpr hij
  subst j
  rw [resolutionComplex_d_prev]
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.inl_fst, Category.comp_id]
    rw [← Category.assoc, esnd, efst]
    change _ = homotopyCofiber.d φ i (i - 1) ≫ homotopyCofiber.sndX φ (i - 1)
    rw [homotopyCofiber.d_sndX φ i (i - 1) (down_prev i)]
    have hz : (diagonalComplex F).d i (i - 1) = 0 := diagonalComplex_d F _ _
    change _ = _ + _ ≫ (diagonalComplex F).d i (i - 1)
    rw [hz, CategoryTheory.Limits.comp_zero, add_zero]
    rfl
  · simp only [Category.assoc, biprod.inl_snd, CategoryTheory.Limits.comp_zero]
    change 0 = homotopyCofiber.d φ i (i - 1) ≫ (e (i - 1)).hom ≫ biprod.snd
    rw [esnd, homotopyCofiber.d_fstX φ i (i - 1) (i - 1 - 1)
      (down_prev i) (down_prev (i - 1))]
    have hz : (diagonalComplex G).d (i - 1) (i - 1 - 1) = 0 := diagonalComplex_d G _ _
    change 0 = -(_ ≫ (diagonalComplex G).d (i - 1) (i - 1 - 1))
    rw [hz, CategoryTheory.Limits.comp_zero, neg_zero]

lemma resolution_finiteCell (hF : ∀ i, Module.Free R (F i) ∧ Module.Finite R (F i))
    (hG : ∀ i, Module.Free R (G i) ∧ Module.Finite R (G i)) :
    FiniteCell R D (resolutionComplex F G r) := by
  apply FiniteCell.iso (resolutionConeIso F G r)
  apply FiniteCell.cone
  · exact FiniteCell.free ⟨diagonalComplex_d G,hG⟩
  · exact FiniteCell.free ⟨diagonalComplex_d F,hF⟩

end ResolutionCell

variable [IsDomain R] [IsPrincipalIdealRing R]
  [IsPrincipalIdealRing Rᵐᵒᵖ]

omit [IsDomain R] [IsPrincipalIdealRing Rᵐᵒᵖ] in
lemma finite_homology_of_finite_terms (P : PeriodicComplex R D)
    (h : ∀ i, Module.Finite R (P.X i)) (i : ZMod D) :
    Module.Finite R (P.homology i) := by
  let := h i
  let : Module.Finite R (P.cycles i) :=
    Module.Finite.of_injective (P.iCycles i).hom
      ((ModuleCat.mono_iff_injective _).mp inferInstance)
  exact Module.Finite.of_surjective (P.homologyπ i).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

variable [(HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.down (ZMod D))).HasLocalization.{w}]

omit [IsDomain R] [IsPrincipalIdealRing Rᵐᵒᵖ] in
theorem perfect_homology_finite (P : PeriodicDerived R D) (hP : IsPerfect R D P) :
    ∀ i, Module.Finite R ((homology R D i).obj P) := by
  obtain ⟨C,hC,⟨ret⟩⟩ := hP
  intro i
  let := finite_homology_of_finite_terms C (fun i => (finiteCell_terms hC i).2) i
  let e := (HomologicalComplexUpToQuasiIso.homologyFunctorFactors
    (ModuleCat.{u} R) (ComplexShape.down (ZMod D)) i).app C
  let : Module.Finite R ((homology R D i).obj ((Q R D).obj C)) :=
    Module.Finite.equiv (show C.homology i ≃ₗ[R]
      (homology R D i).obj ((Q R D).obj C) from e.toLinearEquiv.symm)
  let ret' := ret.map (homology R D i)
  exact Module.Finite.of_surjective ret'.r.hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

omit [IsDomain R] [IsPrincipalIdealRing R] [IsPrincipalIdealRing Rᵐᵒᵖ] in
lemma perfect_of_iso {P P' : PeriodicDerived R D} (e : P ≅ P')
    (h : IsPerfect R D P') : IsPerfect R D P := by
  obtain ⟨C,hC,⟨ret⟩⟩ := h
  exact ⟨C,hC,⟨(Retract.ofIso e).trans ret⟩⟩

omit [IsPrincipalIdealRing Rᵐᵒᵖ] in
lemma diagonal_perfect (H : ZMod D → ModuleCat.{u} R)
    (hfin : ∀ i, Module.Finite R (H i)) :
    IsPerfect R D ((Q R D).obj (diagonalComplex H)) := by
  classical
  have hex (i : ZMod D) := @exists_categorical_resolution R _ _ _ (H i) (hfin i)
  choose n m r p w hr hp using hex
  let F : ZMod D → ModuleCat.{u} R := fun i => ModuleCat.of R (Fin (n i) → R)
  let G : ZMod D → ModuleCat.{u} R := fun i => ModuleCat.of R (Fin (m i) → R)
  let C := resolutionComplex F G r
  let f : C ⟶ diagonalComplex H := diagonalMap F G H r p w
  have hf : QuasiIso f := diagonalMap_quasiIso F G H r p w hr (fun i => (hp i).some)
  let : IsIso ((Q R D).map f) :=
    HomologicalComplexUpToQuasiIso.isIso_Q_map_iff_mem_quasiIso f |>.mpr
      ((mem_quasiIso_iff f).mpr hf)
  refine ⟨C,resolution_finiteCell F G r (fun _ => ⟨inferInstance,inferInstance⟩)
    (fun _ => ⟨inferInstance,inferInstance⟩),?_⟩
  exact ⟨Retract.ofIso (asIso ((Q R D).map f)).symm⟩

lemma derived_homology_splitting (hD : 0 < D) (heven : Even D)
    (P : PeriodicComplex R D) (hfin : ∀ i, Module.Finite R (P.homology i)) :
    Nonempty ((Q R D).obj P ≅ (Q R D).obj (homologyDiagonal P)) := by
  obtain ⟨C,f,g,hf,hg,_⟩ := periodic_homology_splitting hD heven P hfin
  let : IsIso ((Q R D).map f) :=
    HomologicalComplexUpToQuasiIso.isIso_Q_map_iff_mem_quasiIso f |>.mpr
      ((mem_quasiIso_iff f).mpr hf)
  let : IsIso ((Q R D).map g) :=
    HomologicalComplexUpToQuasiIso.isIso_Q_map_iff_mem_quasiIso g |>.mpr
      ((mem_quasiIso_iff g).mpr hg)
  exact ⟨(asIso ((Q R D).map f)).symm ≪≫ asIso ((Q R D).map g)⟩

theorem perfect_splitting (hD : 0 < D) (heven : Even D)
    (P : PeriodicDerived R D) (hP : IsPerfect R D P) :
    ∃ (V L : ZMod D → ModuleCat.{u} R),
      (∀ i, Module.Free R (V i) ∧ Module.Finite R (V i)) ∧
      (∀ i, IsTorsionModule R (L i)) ∧
      IsPerfect R D ((Q R D).obj (diagonalComplex L)) ∧
      Nonempty (P ≅ (Q R D).obj
        (diagonalComplex (fun i => ModuleCat.of R ((V i) × (L i))))) := by
  classical
  let : (Q R D).EssSurj := Localization.essSurj (Q R D)
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.down (ZMod D)))
  let C := (Q R D).objPreimage P
  let e : (Q R D).obj C ≅ P := (Q R D).objObjPreimageIso P
  have hC := perfect_of_iso e hP
  have hfin (i : ZMod D) : Module.Finite R (C.homology i) := by
    let := perfect_homology_finite ((Q R D).obj C) hC i
    let ei := (HomologicalComplexUpToQuasiIso.homologyFunctorFactors
      (ModuleCat.{u} R) (ComplexShape.down (ZMod D)) i).app C
    exact Module.Finite.equiv (show (homology R D i).obj ((Q R D).obj C) ≃ₗ[R]
      C.homology i from ei.toLinearEquiv)
  have hex (i : ZMod D) := @torsion_free_decomposition R _ _ _ _
    (C.homology i) _ _ (hfin i)
  choose T V hcomp htor hfree hvfin using hex
  let Vf (i : ZMod D) : ModuleCat.{u} R := ModuleCat.of R (V i)
  let Lf (i : ZMod D) : ModuleCat.{u} R := ModuleCat.of R (T i)
  have hlf (i : ZMod D) : Module.Finite R (Lf i) := by
    let := hfin i
    exact Module.Finite.of_injective (T i).subtype Subtype.val_injective
  refine ⟨Vf,Lf,fun i => ⟨hfree i,hvfin i⟩,htor,diagonal_perfect Lf hlf,?_⟩
  let eh : homologyDiagonal C ≅
      diagonalComplex (fun i => ModuleCat.of R ((Vf i) × (Lf i))) :=
    Hom.isoOfComponents (fun i => (Submodule.prodEquivOfIsCompl (V i) (T i)
      (hcomp i).symm).symm.toModuleIso) (by
        intro i j hij
        change _ ≫ (diagonalComplex _).d i j = (homologyDiagonal C).d i j ≫ _
        change _ ≫ (diagonalComplex _).d i j = (diagonalComplex _).d i j ≫ _
        rw [diagonalComplex_d, diagonalComplex_d]
        simp)
  obtain ⟨es⟩ := derived_homology_splitting hD heven C hfin
  exact ⟨e.symm ≪≫ es ≪≫ (Q R D).mapIso eh⟩

end HahnWilson.PeriodicDerived

end

end OAI
