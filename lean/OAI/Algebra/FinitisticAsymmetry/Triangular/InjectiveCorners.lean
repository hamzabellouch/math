import Mathlib
import OAI.Algebra.FinitisticAsymmetry.Triangular.Socle

namespace OAI

noncomputable section

open CategoryTheory
namespace LittleFinitistic.CummingsConstruction

section
universe u
variable {k C ι : Type u} [Field k] [Ring C] [Algebra k C]
variable (χ : C →ₐ[k] (ι → k)) (i : ι)

def cval (r : T χ) : k := χ r.fst.1 i
def ehead (r : T χ) : k := (r.fst.2 i).fst
def etail (r : T χ) : k := (r.fst.2 i).snd
def oval (r : T χ) : k := (SimpleSum.value (TriangularConstruction.offValue r.snd)) i

@[simp] lemma cval_mul (r s : T χ) : cval χ i (r*s) = cval χ i r * cval χ i s := by
  change χ (r.fst.1 * s.fst.1) i = _
  simp [cval]
@[simp] lemma ehead_mul (r s : T χ) : ehead χ i (r*s) = ehead χ i r * ehead χ i s := rfl
@[simp] lemma etail_mul (r s : T χ) : etail χ i (r*s) = ehead χ i r * etail χ i s + ehead χ i s * etail χ i r := by
  change _ * _ + _ * _ = _
  change (r.fst.2 i).fst * (s.fst.2 i).snd + (r.fst.2 i).snd * (s.fst.2 i).fst = _
  dsimp only [ehead, etail]
  ring
@[simp] lemma oval_mul (r s : T χ) : oval χ i (r*s) = ehead χ i r * oval χ i s + cval χ i s * oval χ i r := rfl

def NewInjective (_χ : C →ₐ[k] (ι → k)) (_i : ι) := k × (k × k)
namespace NewInjective

def value (x : NewInjective χ i) : k × (k × k) := x

@[ext] lemma ext {x y : NewInjective χ i}
    (h₁ : (value χ i x).1 = (value χ i y).1)
    (h₂ : (value χ i x).2.1 = (value χ i y).2.1)
    (h₃ : (value χ i x).2.2 = (value χ i y).2.2) : x = y :=
  Prod.ext h₁ (Prod.ext h₂ h₃)
instance : AddCommGroup (NewInjective χ i) := inferInstanceAs (AddCommGroup (k × (k × k)))

def act (r : T χ) (x : NewInjective χ i) : NewInjective χ i :=
  (cval χ i r * (value χ i x).1,
    ehead χ i r * (value χ i x).2.1,
    oval χ i r * (value χ i x).1 + etail χ i r * (value χ i x).2.1 + ehead χ i r * (value χ i x).2.2)

instance : SMul (T χ) (NewInjective χ i) := ⟨act χ i⟩

instance : Module (T χ) (NewInjective χ i) where
  one_smul x := by
    change (χ 1 i * _, (1 * _, 0 * _ + 0 * _ + 1 * _)) = value χ i x
    simp
  mul_smul r s x := by
    change act χ i (r*s) x = act χ i r (act χ i s x)
    simp only [act, value, cval_mul, ehead_mul, etail_mul, oval_mul]
    apply ext <;> dsimp [value, NewInjective] <;> ring
  smul_zero r := by
    change act χ i r (0,0,0) = (0,0,0)
    simp only [act, value, mul_zero, add_zero]
    rfl
  smul_add r x y := by
    apply ext
    · change cval χ i r * (x.1 + y.1) = cval χ i r*x.1 + cval χ i r*y.1
      ring
    · change ehead χ i r * (x.2.1 + y.2.1) = ehead χ i r*x.2.1 + ehead χ i r*y.2.1
      ring
    · change oval χ i r * (x.1+y.1) + etail χ i r * (x.2.1+y.2.1) +
        ehead χ i r * (x.2.2+y.2.2) =
        (oval χ i r*x.1 + etail χ i r*x.2.1 + ehead χ i r*x.2.2) +
        (oval χ i r*y.1 + etail χ i r*y.2.1 + ehead χ i r*y.2.2)
      ring
  add_smul r s x := by
    apply ext
    · change χ (r.fst.1+s.fst.1) i * x.1 = χ r.fst.1 i*x.1 + χ s.fst.1 i*x.1
      simp [map_add, add_mul]
    · change ((r.fst.2 i).fst + (s.fst.2 i).fst)*x.2.1 =
        (r.fst.2 i).fst*x.2.1 + (s.fst.2 i).fst*x.2.1
      ring
    · change (oval χ i r + oval χ i s)*x.1 +
        (etail χ i r + etail χ i s)*x.2.1 +
        (ehead χ i r + ehead χ i s)*x.2.2 =
        (oval χ i r*x.1 + etail χ i r*x.2.1 + ehead χ i r*x.2.2) +
        (oval χ i s*x.1 + etail χ i s*x.2.1 + ehead χ i s*x.2.2)
      ring
  zero_smul x := by
    change (χ 0 i * _, (0 * _, 0 * _ + 0 * _ + 0 * _)) = (0,0,0)
    simp

end NewInjective
end

section
open CategoryTheory
universe u
variable {k C ι : Type u} [Field k] [Ring C] [Algebra k C]
variable (χ : C →ₐ[k] (ι → k)) (i : ι) [DecidableEq ι]

def newIdem : T χ := ((0, Pi.single i 1), 0)

lemma newIdem_mul (r : T χ) : newIdem χ i * r =
    oval χ i r • socle χ (.inl i) + etail χ i r • socle χ (.inr i) +
    ehead χ i r • newIdem χ i := by
  apply TrivSqZeroExt.ext
  · apply Prod.ext
    · change (0 : C) * r.fst.1 = _
      change 0 * r.fst.1 = (oval χ i r) • (0 : C) + (etail χ i r) • 0 + (ehead χ i r) • 0
      simp
    · change (Pi.single i 1 : ι → DualNumber k) * r.fst.2 =
        (oval χ i r) • (0 : ι → DualNumber k) +
        (etail χ i r) • (Pi.single i (DualNumber.eps : DualNumber k) : ι → DualNumber k) +
        (ehead χ i r) • (Pi.single i (1 : DualNumber k) : ι → DualNumber k)
      ext j : 1
      by_cases hj : j = i
      · subst j
        apply TrivSqZeroExt.ext <;>
          simp [etail, ehead]
      · apply TrivSqZeroExt.ext <;>
          simp [hj]
  · change (newAugmentation (Pi.single i 1 : ι → DualNumber k) *
      SimpleSum.value (TriangularConstruction.offValue r.snd) +
      SimpleSum.rightCharacter χ (MulOpposite.op r.fst.1) * 0) = _
    change (newAugmentation (Pi.single i 1 : ι → DualNumber k) *
      SimpleSum.value (TriangularConstruction.offValue r.snd) +
      SimpleSum.rightCharacter χ (MulOpposite.op r.fst.1) * 0) =
      (oval χ i r) • (Pi.single i (1 : k) : ι → k) + (etail χ i r) • 0 + (ehead χ i r) • 0
    ext j
    by_cases hj : j = i
    · subst j
      simp [oval, newAugmentation]
    · simp [oval, newAugmentation, hj]

lemma field_module_injective (V : ModuleCat.{u} k) : Injective V where
  factors {X Y} g f hf := by
    obtain ⟨s, hs⟩ := f.hom.exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr ((ModuleCat.mono_iff_injective f).mp hf))
    refine ⟨ModuleCat.ofHom (g.hom.comp s), ?_⟩
    apply ModuleCat.hom_ext
    change g.hom.comp (s.comp f.hom) = g.hom
    rw [hs, LinearMap.comp_id]

abbrev coindField := (ModuleCat.coextendScalars (algebraMap k (T χ))).obj (ModuleCat.of k k)

instance coindField_injective : Injective (coindField χ) :=
  (ModuleCat.restrictCoextendScalarsAdj (algebraMap k (T χ))).map_injective _
    (field_module_injective (ModuleCat.of k k))

omit [DecidableEq ι] in
lemma coindField_smul_eval
    (h : (ModuleCat.restrictScalars (algebraMap k (T χ))).obj
      (ModuleCat.of (T χ) (T χ)) →ₗ[k] k) (a : k) (r : T χ) :
    h (a • r) = a • h r := by
  have scalar_eq := h.map_smul a r
  change h (algebraMap k (T χ) a * r) = a • h r at scalar_eq
  calc
    h (a • r) = h (algebraMap k (T χ) a * r) := congrArg h (Algebra.smul_def a r)
    _ = a • h r := scalar_eq

omit [DecidableEq ι] in
lemma coindField_add_eval
    (h : (ModuleCat.restrictScalars (algebraMap k (T χ))).obj
      (ModuleCat.of (T χ) (T χ)) →ₗ[k] k) (r s : T χ) :
    h (r+s) = h r + h s := h.map_add r s

def newInjectiveRetraction : coindField χ ⟶ ModuleCat.of (T χ) (NewInjective χ i) :=
  ModuleCat.ofHom {
    toFun := fun h => (h (socle χ (.inl i)), h (socle χ (.inr i)), h (newIdem χ i))
    map_add' := fun _ _ => rfl
    map_smul' := fun r h => by
      apply NewInjective.ext
      · change h (socle χ (.inl i) * r) = cval χ i r * h (socle χ (.inl i))
        rw [socle_mul, coindField_smul_eval]
        rfl
      · change h (socle χ (.inr i) * r) = ehead χ i r * h (socle χ (.inr i))
        rw [socle_mul, coindField_smul_eval]
        rfl
      · change h (newIdem χ i * r) = oval χ i r * h (socle χ (.inl i)) +
          etail χ i r * h (socle χ (.inr i)) + ehead χ i r * h (newIdem χ i)
        rw [newIdem_mul, coindField_add_eval, coindField_add_eval, coindField_smul_eval,
          coindField_smul_eval, coindField_smul_eval]
        rfl }

end

open CategoryTheory
universe u
variable {k C ι : Type u} [Field k] [Ring C] [Algebra k C]
variable (χ : C →ₐ[k] (ι → k)) (i : ι) [DecidableEq ι]

def lastCoordinate : (ModuleCat.restrictScalars (algebraMap k (T χ))).obj
    (ModuleCat.of (T χ) (NewInjective χ i)) ⟶ ModuleCat.of k k := ModuleCat.ofHom
  (X := (ModuleCat.restrictScalars (algebraMap k (T χ))).obj
    (ModuleCat.of (T χ) (NewInjective χ i))) (Y := ModuleCat.of k k)
  (show (ModuleCat.restrictScalars (algebraMap k (T χ))).obj
    (ModuleCat.of (T χ) (NewInjective χ i)) →ₗ[k] k from {
  toFun := fun x => (NewInjective.value χ i x).2.2
  map_add' := fun _ _ => rfl
  map_smul' := fun a x => by
    change (NewInjective.act χ i ((algebraMap k (T χ)) a) x).2.2 = a * x.2.2
    change (0 * x.1 + 0 * x.2.1 + a * x.2.2) = a * x.2.2
    simp })

def newInjectiveInclusion : ModuleCat.of (T χ) (NewInjective χ i) ⟶ coindField χ :=
  ModuleCat.RestrictionCoextensionAdj.HomEquiv.fromRestriction _ (lastCoordinate χ i)

omit [DecidableEq ι] in
lemma newInjectiveInclusion_apply (x : NewInjective χ i) (r : T χ) :
    (newInjectiveInclusion χ i x) r = (NewInjective.act χ i r x).2.2 := by
  change (ModuleCat.RestrictionCoextensionAdj.HomEquiv.fromRestriction _
    (lastCoordinate χ i)).hom x r = _
  rw [ModuleCat.RestrictionCoextensionAdj.HomEquiv.fromRestriction_hom_apply_apply]
  change (r • x : NewInjective χ i).2.2 = _
  rfl

lemma newInjectiveInclusion_retraction :
    newInjectiveInclusion χ i ≫ newInjectiveRetraction χ i = 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (newInjectiveRetraction χ i (newInjectiveInclusion χ i x)) = x
  apply NewInjective.ext (χ := χ) (i := i)
  · change (newInjectiveInclusion χ i x) (socle χ (.inl i)) = x.1
    rw [newInjectiveInclusion_apply]
    change (NewInjective.act χ i (socle χ (.inl i)) x).2.2 = x.1
    change (Pi.single (M := fun _ : ι => k) i 1) i * x.1 + 0 * x.2.1 + 0 * x.2.2 = x.1
    simp
  · change (newInjectiveInclusion χ i x) (socle χ (.inr i)) = x.2.1
    rw [newInjectiveInclusion_apply]
    change (NewInjective.act χ i (socle χ (.inr i)) x).2.2 = x.2.1
    simp [NewInjective.act, NewInjective.value, oval, etail, ehead, socle, TriangularConstruction.offValue, SimpleSum.value]
    try exact Or.inl rfl
  · change (newInjectiveInclusion χ i x) (newIdem χ i) = x.2.2
    rw [newInjectiveInclusion_apply]
    change (NewInjective.act χ i (newIdem χ i) x).2.2 = x.2.2
    simp [NewInjective.act, NewInjective.value, oval, etail, ehead, newIdem, TriangularConstruction.offValue, SimpleSum.value]
    exact Or.inl rfl

lemma newInjective_injective : Injective (ModuleCat.of (T χ) (NewInjective χ i)) := by
  exact (show CategoryTheory.Retract (ModuleCat.of (T χ) (NewInjective χ i))
    (coindField χ) from ⟨newInjectiveInclusion χ i, newInjectiveRetraction χ i,
      newInjectiveInclusion_retraction χ i⟩).injective

end LittleFinitistic.CummingsConstruction

end

end OAI
