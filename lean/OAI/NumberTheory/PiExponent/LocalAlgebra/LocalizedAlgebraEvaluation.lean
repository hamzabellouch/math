import Mathlib

namespace OAI

namespace PiExponent.LocalizedAlgebraEvaluation
noncomputable section
variable {P A B : Type*} [CommRing P] [CommRing A] [CommRing B] [Algebra P A]
variable (S : Submonoid P) (T : Submonoid B) (f : A →+* B)
  (hf : ∀ s : S, f (algebraMap P A s.val) ∈ T)

def denominatorMap : S →* T where
  toFun s := ⟨f (algebraMap P A s.val), hf s⟩
  map_one' := Subtype.ext (by simp)
  map_mul' s t := Subtype.ext (by simp)

@[simp] theorem denominatorMap_val (s : S) :
    (denominatorMap S T f hf s).val = f (algebraMap P A s.val) := rfl

def evaluation : LocalizedModule S A →+ Localization T where
  toFun z := z.liftOn
    (fun p => IsLocalization.mk' (Localization T) (f p.1) (denominatorMap S T f hf p.2))
    (by
      rintro ⟨m,s⟩ ⟨m',s'⟩ ⟨u, hu⟩
      apply (IsLocalization.eq (M := T) (S := Localization T)).mpr
      refine ⟨denominatorMap S T f hf u, ?_⟩
      change f (algebraMap P A u.val) * (f (algebraMap P A s'.val) * f m) =
        f (algebraMap P A u.val) * (f (algebraMap P A s.val) * f m')
      simpa only [Submonoid.smul_def, Algebra.smul_def, map_mul] using congrArg f hu)
  map_zero' := by
    rw [← LocalizedModule.zero_mk (1 : S), LocalizedModule.liftOn_mk,
      map_zero, IsLocalization.mk'_zero]
  map_add' z w := by
    induction z, w using LocalizedModule.induction_on₂ with
    | h m m' s s' =>
      simp only [LocalizedModule.mk_add_mk, LocalizedModule.liftOn_mk,
        Submonoid.smul_def, Algebra.smul_def, map_add, map_mul]
      simpa only [denominatorMap_val, mul_comm] using
        (IsLocalization.mk'_add (M := T) (S := Localization T) (f m) (f m')
          (denominatorMap S T f hf s) (denominatorMap S T f hf s'))

@[simp] theorem evaluation_mk (m : A) (s : S) :
    evaluation S T f hf (LocalizedModule.mk m s) =
      IsLocalization.mk' (Localization T) (f m) (denominatorMap S T f hf s) :=
by
  simp only [evaluation, AddMonoidHom.coe_mk, ZeroHom.coe_mk, LocalizedModule.liftOn_mk]

theorem evaluation_smul (p : P) (z : LocalizedModule S A) :
    evaluation S T f hf (p • z) =
      algebraMap B (Localization T) (f (algebraMap P A p)) * evaluation S T f hf z := by
  induction z using LocalizedModule.induction_on with
  | h m s =>
    rw [LocalizedModule.smul'_mk, evaluation_mk, evaluation_mk]
    simp only [Algebra.smul_def, map_mul]
    exact (IsLocalization.mul_mk'_eq_mk'_of_mul _ _ _).symm

end
end PiExponent.LocalizedAlgebraEvaluation

end OAI
