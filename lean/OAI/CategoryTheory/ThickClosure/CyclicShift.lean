import OAI.CategoryTheory.ThickClosure.Unroll

namespace OAI

noncomputable section
open scoped BigOperators nonZeroDivisors
open LinearMap Submodule
open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace HahnWilson.CyclicShift
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open HahnWilson.Unroll
universe u
variable (R : Type u) [Ring R] (D : ℕ)

def cyclicShift (n : ℤ) : PC R D ⥤ PC R D where
  obj P :=
    { X := fun i => P.X (i - (n : ZMod D))
      d := fun i j => n.negOnePow • P.d (i - (n : ZMod D)) (j - (n : ZMod D))
      d_comp_d' := by
        intros
        simp only [Linear.comp_units_smul, Linear.units_smul_comp, d_comp_d, smul_zero]
      shape := by
        intro i j hij
        rw [P.shape, smul_zero]
        intro h
        apply hij
        change j+1=i
        change j-(n : ZMod D)+1 = i-(n : ZMod D) at h
        exact sub_left_inj.mp (by simpa only [sub_add_eq_add_sub] using h) }
  map f :=
    { f := fun i => f.f (i - (n : ZMod D))
      comm' := by
        intros
        simp only [Linear.comp_units_smul, Hom.comm, Linear.units_smul_comp] }
  map_id := by intros; rfl
  map_comp := by intros; rfl

def shiftZeroIso : cyclicShift R D 0 ≅ 𝟭 (PC R D) :=
  NatIso.ofComponents (fun P => Hom.isoOfComponents
    (fun i => P.XIsoOfEq (by simp))
    (by intro i j hij; dsimp [cyclicShift]; simp only [one_smul, XIsoOfEq_hom_comp_d, d_comp_XIsoOfEq_hom]))
    (by intro P Q f; ext i; simp [cyclicShift, XIsoOfEq])

def shiftAddIso (n m : ℤ) :
    cyclicShift R D (n+m) ≅ cyclicShift R D n ⋙ cyclicShift R D m :=
  NatIso.ofComponents (fun P => Hom.isoOfComponents
    (fun i => P.XIsoOfEq (by simp only [Int.cast_add]; abel))
    (by
      intro i j hij
      dsimp [cyclicShift]
      simp only [Int.negOnePow_add, Linear.units_smul_comp, Linear.comp_units_smul,
        d_comp_XIsoOfEq_hom, XIsoOfEq_hom_comp_d, smul_smul]
      congr 1
      exact mul_comm _ _))
    (by
      intro P Q f
      apply Hom.ext
      funext i
      exact XIsoOfEq_hom_naturality f (by simp only [Int.cast_add]; abel))

theorem shift_zero : Nonempty (cyclicShift R D 0 ≅ 𝟭 (PC R D)) := ⟨shiftZeroIso R D⟩

theorem shift_add (n m : ℤ) : Nonempty
    (cyclicShift R D (n+m) ≅ cyclicShift R D n ⋙ cyclicShift R D m) :=
  ⟨shiftAddIso R D n m⟩

def unrollShiftIso (n : ℤ) :
    cyclicShift R D n ⋙ functor R D ≅ functor R D ⋙
      CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ) n :=
  NatIso.ofComponents (fun P => Hom.isoOfComponents
    (fun i => P.XIsoOfEq (by simp only [Int.cast_add]; abel))
    (by
      intro i j hij
      have hj : i+1=j := hij
      subst j
      simp [cyclicShift, functor, obj, CochainComplex.of.d, add_right_comm i n 1,
        Linear.comp_units_smul, Linear.units_smul_comp]))
    (by
      intro P Q f
      apply Hom.ext
      funext i
      exact XIsoOfEq_hom_naturality f (by simp only [Int.cast_add]; abel))

theorem unroll_shift (n : ℤ) : Nonempty
    (cyclicShift R D n ⋙ functor R D ≅ functor R D ⋙
      CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ) n) :=
  ⟨unrollShiftIso R D n⟩

section ShiftStructure

attribute [local simp] XIsoOfEq
instance : HasShift (PC R D) ℤ := hasShiftMk _ _
  { F := cyclicShift R D
    zero := shiftZeroIso R D
    add := shiftAddIso R D
    assoc_hom_app := by
      intros
      apply Hom.ext
      funext i
      simp [shiftAddIso, cyclicShift, XIsoOfEq]
      erw [eqToHom_f]
      simp
    zero_add_hom_app := by
      intros
      apply Hom.ext
      funext i
      simp [shiftAddIso, shiftZeroIso, cyclicShift, XIsoOfEq]
      erw [eqToHom_f]
      simp
    add_zero_hom_app := by
      intros
      apply Hom.ext
      funext i
      simp [shiftAddIso, shiftZeroIso, cyclicShift, XIsoOfEq]
      erw [eqToHom_f]
      simp }

@[simp] lemma shiftZero_hom_f (P : PC R D) (i : ZMod D) :
    ((CategoryTheory.shiftFunctorZero (PC R D) ℤ).hom.app P).f i =
      (P.XIsoOfEq (show i - (0 : ℤ) = i by simp)).hom := by tauto

@[simp] lemma shiftAdd_hom_f (P : PC R D) (n m : ℤ) (i : ZMod D) :
    ((CategoryTheory.shiftFunctorAdd (PC R D) n m).hom.app P).f i =
      (P.XIsoOfEq (show i - ((n+m : ℤ) : ZMod D) = i - (m : ZMod D) - (n : ZMod D)
        by simp only [Int.cast_add]; abel)).hom := by tauto

instance : (Unroll.functor R D).CommShift ℤ where
  commShiftIso := unrollShiftIso R D
  commShiftIso_zero := by
    apply Iso.ext
    apply NatTrans.ext
    funext P
    apply Hom.ext
    funext i
    simp [Functor.CommShift.isoZero, unrollShiftIso, XIsoOfEq,
      Unroll.functor, Unroll.map, cyclicShift,
      CochainComplex.shiftFunctorZero_inv_app_f]
    dsimp only [Hom.isoOfComponents]
    exact (eqToHom_trans _ _).symm
  commShiftIso_add n m := by
    apply Iso.ext
    apply NatTrans.ext
    funext P
    apply Hom.ext
    funext i
    simp [Functor.CommShift.isoAdd, unrollShiftIso, XIsoOfEq,
      Unroll.functor, cyclicShift]
    dsimp only [Functor.CommShift.isoAdd', Hom.isoOfComponents,
      Functor.isoWhiskerLeft, Functor.isoWhiskerRight]
    simp [Unroll.map, CochainComplex.shiftFunctorAdd_inv_app_f,
      shiftFunctorAdd'_eq_shiftFunctorAdd]
    erw [eqToHom_trans, eqToHom_trans, eqToHom_trans]
    · rfl
    · change P.X (- (i : ZMod D) - (m : ZMod D) - (n : ZMod D)) =
        P.X (- ((i + m : ℤ) : ZMod D) - (n : ZMod D))
      congr 1
      simp only [Int.cast_add]
      abel
    · change P.X (- ((i + m : ℤ) : ZMod D) - (n : ZMod D)) =
        P.X (- ((i + m + n : ℤ) : ZMod D))
      congr 1
      simp only [Int.cast_add]
      abel

end ShiftStructure

lemma quasiIso_iff_unroll {P Q : PC R D} (f : P ⟶ Q) :
    QuasiIso ((Unroll.functor R D).map f) ↔ QuasiIso f := by
  constructor
  · intro h
    rw [quasiIso_iff]
    intro i
    obtain ⟨n, hn⟩ := ZMod.intCast_surjective (-i)
    have hi : -(n : ZMod D) = i := by rw [hn]; simp
    rw [quasiIsoAt_iff_isIso_homologyMap, ← hi]
    have := h
    exact (NatIso.isIso_map_iff (homologyIso R D n) f).mp
      (inferInstanceAs (IsIso (homologyMap ((Unroll.functor R D).map f) n)))
  · intro h
    have := h
    exact map_quasiIso R D f

lemma quasiIso_shift_iff {P Q : PC R D} (f : P ⟶ Q) (n : ℤ) :
    QuasiIso ((cyclicShift R D n).map f) ↔ QuasiIso f := by
  rw [← quasiIso_iff_unroll R D]
  let e : Arrow.mk ((cyclicShift R D n ⋙ Unroll.functor R D).map f) ≅
      Arrow.mk ((Unroll.functor R D ⋙ CategoryTheory.shiftFunctor _ n).map f) :=
    Arrow.isoMk ((unrollShiftIso R D n).app P) ((unrollShiftIso R D n).app Q)
      ((unrollShiftIso R D n).hom.naturality f).symm
  change QuasiIso ((cyclicShift R D n ⋙ Unroll.functor R D).map f) ↔ _
  rw [quasiIso_iff_of_arrow_mk_iso _ _ e]
  change QuasiIso ((CategoryTheory.shiftFunctor _ n).map ((Unroll.functor R D).map f)) ↔ _
  rw [CochainComplex.quasiIso_shift_iff, quasiIso_iff_unroll]

instance quasiIso_isCompatibleWithShift : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.down (ZMod D))).IsCompatibleWithShift ℤ where
  condition n := by
    ext P Q f
    exact quasiIso_shift_iff R D f n

end HahnWilson.CyclicShift

end

end OAI
