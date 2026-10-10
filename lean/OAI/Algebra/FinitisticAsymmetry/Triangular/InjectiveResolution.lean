import Mathlib
import OAI.Algebra.FinitisticAsymmetry.Triangular.InjectiveCorners

namespace OAI

noncomputable section

open CategoryTheory
namespace LittleFinitistic.CummingsConstruction
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {k C ι : Type u} [Field k] [Ring C] [Algebra k C]
variable (χ : C →ₐ[k] (ι → k)) (i : ι)

def oldCharacter : T χ →+* k :=
  (Pi.evalRingHom (fun _ : Sum ι ι => k) (.inl i)).comp (augmentation χ).toRingHom

def newCharacter : T χ →+* k :=
  (Pi.evalRingHom (fun _ : Sum ι ι => k) (.inr i)).comp (augmentation χ).toRingHom

def newProjection : T χ →+* DualNumber k where
  toFun r := r.fst.2 i
  map_one' := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

abbrev oldSimple := (ModuleCat.restrictScalars (oldCharacter χ i)).obj (ModuleCat.of k k)
abbrev newSimple := (ModuleCat.restrictScalars (newCharacter χ i)).obj (ModuleCat.of k k)
abbrev newRegular := (ModuleCat.restrictScalars (newProjection χ i)).obj (ModuleCat.of (DualNumber k) (DualNumber k))
abbrev newInjectiveObj := ModuleCat.of (T χ) (NewInjective χ i)

def newRegularι : newRegular χ i ⟶ newInjectiveObj χ i := ModuleCat.ofHom
  (X := newRegular χ i) (Y := newInjectiveObj χ i) (show
    newRegular χ i →ₗ[T χ] newInjectiveObj χ i from {
  toFun := fun x => (0,x.fst,x.snd)
  map_add' := fun x y => by
    apply NewInjective.ext (χ := χ) (i := i)
    · exact (zero_add (0 : k)).symm
    · rfl
    · rfl
  map_smul' := fun r x => by
    apply NewInjective.ext (χ := χ) (i := i)
    · change (0 : k) = cval χ i r * 0
      simp
    · rfl
    · change ehead χ i r*x.snd + etail χ i r*x.fst =
        oval χ i r*0 + etail χ i r*x.fst + ehead χ i r*x.snd
      ring })

def newInjectiveπ : newInjectiveObj χ i ⟶ oldSimple χ i := ModuleCat.ofHom
  (X := newInjectiveObj χ i) (Y := oldSimple χ i) (show
    newInjectiveObj χ i →ₗ[T χ] oldSimple χ i from {
  toFun := fun x => x.1
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl })

def newRegularπ : newRegular χ i ⟶ newSimple χ i := ModuleCat.ofHom
  (X := newRegular χ i) (Y := newSimple χ i) (show
    newRegular χ i →ₗ[T χ] newSimple χ i from {
  toFun := fun x => x.fst
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl })

def newSimpleι : newSimple χ i ⟶ newRegular χ i := ModuleCat.ofHom
  (X := newSimple χ i) (Y := newRegular χ i) (show
    newSimple χ i →ₗ[T χ] newRegular χ i from {
  toFun := fun a => (0,a)
  map_add' := fun a b => by
    apply TrivSqZeroExt.ext
    · exact (zero_add (0 : k)).symm
    · rfl
  map_smul' := fun r a => by
    apply TrivSqZeroExt.ext
    · change (0 : k) = ehead χ i r * 0
      simp
    · change ehead χ i r*(show k from a) = ehead χ i r*(show k from a) + etail χ i r*0
      simp })

def newDifferential : newInjectiveObj χ i ⟶ newInjectiveObj χ i := ModuleCat.ofHom
  (X := newInjectiveObj χ i) (Y := newInjectiveObj χ i) (show
    newInjectiveObj χ i →ₗ[T χ] newInjectiveObj χ i from {
  toFun := fun x => (0,0,x.2.1)
  map_add' := fun x y => by
    apply NewInjective.ext (χ := χ) (i := i)
    · exact (zero_add (0 : k)).symm
    · exact (zero_add (0 : k)).symm
    · rfl
  map_smul' := fun r x => by
    apply NewInjective.ext (χ := χ) (i := i)
    · change (0 : k) = cval χ i r * 0
      simp
    · change (0 : k) = ehead χ i r * 0
      simp
    · change ehead χ i r*x.2.1 = oval χ i r*0 + etail χ i r*0 + ehead χ i r*x.2.1
      simp })

def epsDifferential : newRegular χ i ⟶ newRegular χ i := newRegularπ χ i ≫ newSimpleι χ i

@[simp] lemma newDifferential_sq : newDifferential χ i ≫ newDifferential χ i = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

@[simp] lemma epsDifferential_sq : epsDifferential χ i ≫ epsDifferential χ i = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

lemma newRegularι_comm : newRegularι χ i ≫ newDifferential χ i =
    epsDifferential χ i ≫ newRegularι χ i := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

lemma newInjectiveπ_comm : newDifferential χ i ≫ newInjectiveπ χ i = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

lemma newRegularι_π : newRegularι χ i ≫ newInjectiveπ χ i = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

lemma newRegular_exact :
    (ShortComplex.mk (newRegularι χ i) (newInjectiveπ χ i) (newRegularι_π χ i)).ShortExact where
  mono_f := by
    rw [ModuleCat.mono_iff_injective]
    intro x y h
    apply TrivSqZeroExt.ext
    · exact congrArg (fun z : NewInjective χ i => z.2.1) h
    · exact congrArg (fun z : NewInjective χ i => z.2.2) h
  epi_g := by
    rw [ModuleCat.epi_iff_surjective]
    intro a
    exact ⟨(a,0,0), rfl⟩
  exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    refine ⟨(x.2.1,x.2.2), ?_⟩
    apply NewInjective.ext (χ := χ) (i := i)
    · exact hx.symm
    · rfl
    · rfl

def periodicInjective : ChainComplex (ModuleCat (T χ)) ℕ :=
  ChainComplex.of (fun _ => newInjectiveObj χ i) (fun _ => newDifferential χ i)
    (fun _ => newDifferential_sq χ i)

def periodicRegular : ChainComplex (ModuleCat (T χ)) ℕ :=
  ChainComplex.of (fun _ => newRegular χ i) (fun _ => epsDifferential χ i)
    (fun _ => epsDifferential_sq χ i)

def periodicOld : ChainComplex (ModuleCat (T χ)) ℕ :=
  ChainComplex.of (fun _ => oldSimple χ i) (fun _ => 0) (fun _ => by simp)

def periodicι : periodicRegular χ i ⟶ periodicInjective χ i :=
  ChainComplex.ofHom (fun _ => newRegularι χ i) (fun n => by
    simpa [periodicInjective, periodicRegular] using newRegularι_comm χ i)

def periodicπ : periodicInjective χ i ⟶ periodicOld χ i :=
  ChainComplex.ofHom (fun _ => newInjectiveπ χ i) (fun n => by
    simpa [periodicInjective, periodicOld] using (newInjectiveπ_comm χ i).symm)

lemma periodicι_π : periodicι χ i ≫ periodicπ χ i = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  exact newRegularι_π χ i

lemma periodic_shortExact :
    (ShortComplex.mk (periodicι χ i) (periodicπ χ i) (periodicι_π χ i)).ShortExact where
  mono_f := HomologicalComplex.mono_of_mono_f _ (fun _ => (newRegular_exact χ i).mono_f)
  epi_g := HomologicalComplex.epi_of_epi_f _ (fun _ => (newRegular_exact χ i).epi_g)
  exact := HomologicalComplex.exact_of_degreewise_exact _ (fun _ => (newRegular_exact χ i).exact)

lemma epsDifferential_π : epsDifferential χ i ≫ newRegularπ χ i = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

lemma epsDifferential_exact :
    (ShortComplex.mk (epsDifferential χ i) (epsDifferential χ i)
      (epsDifferential_sq χ i)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  have hx' : x.fst = 0 := congrArg TrivSqZeroExt.snd hx
  refine ⟨(x.snd,0), ?_⟩
  apply TrivSqZeroExt.ext
  · exact hx'.symm
  · rfl

lemma epsDifferential_π_exact :
    (ShortComplex.mk (epsDifferential χ i) (newRegularπ χ i)
      (epsDifferential_π χ i)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  refine ⟨(x.snd,0), ?_⟩
  apply TrivSqZeroExt.ext
  · exact hx.symm
  · rfl

instance newRegularπ_epi : Epi (newRegularπ χ i) := by
  rw [ModuleCat.epi_iff_surjective]
  intro a
  exact ⟨(a,0), rfl⟩

def periodicAug : periodicRegular χ i ⟶ (ChainComplex.single₀ (ModuleCat (T χ))).obj
    (newSimple χ i) :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨newRegularπ χ i, epsDifferential_π χ i⟩

instance periodicAug_quasiIso : QuasiIso (periodicAug χ i) := ⟨fun n => by
  cases n with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
    · exact ⟨epsDifferential_π_exact χ i, newRegularπ_epi χ i⟩
    all_goals rfl
  | succ n =>
    rw [quasiIsoAt_iff_exactAt']
    · rw [HomologicalComplex.exactAt_iff' _ (n+2) (n+1) n (by simp) (by simp)]
      have hd : ChainComplex.of.d (fun _ : ℕ => newRegular χ i)
          (fun _ : ℕ => epsDifferential χ i) (n+2) (n+1) = epsDifferential χ i :=
        ChainComplex.of_d _ _ (n+1)
      simpa only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor',
        periodicRegular, hd, ChainComplex.of_d] using epsDifferential_exact χ i
    · apply ChainComplex.exactAt_succ_single_obj⟩

end LittleFinitistic.CummingsConstruction

end

end OAI
