import OAI.GroupTheory.PolycyclicRecognition.Finiteness.StableResolutionIdentity

namespace OAI

/-! # Syzygy maps modulo projective factors

A lift through the projective middle term induces an endomorphism of the next
syzygy. Changing the lift changes that endomorphism by a projective factor.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
attribute [local instance 2300] Submodule.Quotient.module
variable {G : Type} [Group G]
variable (P : ProjectiveResolution (trivialIntegral G)) (n : ℕ)

abbrev resolutionSyzygy := P.complex.opcycles n

def resolutionSyzygyLift (f : resolutionSyzygy P n ⟶ resolutionSyzygy P n) :
    P.complex.X n ⟶ P.complex.X n :=
  Projective.factorThru (P.complex.pOpcycles n ≫ f) (P.complex.pOpcycles n)

@[reassoc]
theorem resolutionSyzygyLift_comm (f : resolutionSyzygy P n ⟶ resolutionSyzygy P n) :
    resolutionSyzygyLift P n f ≫ P.complex.pOpcycles n = P.complex.pOpcycles n ≫ f :=
  Projective.factorThru_comp _ _

def resolutionSyzygyMap (f : resolutionSyzygy P n ⟶ resolutionSyzygy P n) :
    resolutionSyzygy P (n + 1) ⟶ resolutionSyzygy P (n + 1) := by
  let S := resolutionOpcyclesSequence P n
  have hS := resolutionOpcyclesSequence_shortExact P n
  let : Mono S.f := hS.mono_f
  exact hS.exact.lift (S.f ≫ resolutionSyzygyLift P n f) (by
    change (P.complex.fromOpcycles (n + 1) n ≫ resolutionSyzygyLift P n f) ≫
      P.complex.pOpcycles n = 0
    rw [Category.assoc, resolutionSyzygyLift_comm, ← Category.assoc]
    have hz : P.complex.fromOpcycles (n + 1) n ≫ P.complex.pOpcycles n = 0 := S.zero
    exact (congrArg (fun a => a ≫ f) hz).trans (zero_comp))

@[reassoc]
theorem resolutionSyzygyMap_comm (f : resolutionSyzygy P n ⟶ resolutionSyzygy P n) :
    resolutionSyzygyMap P n f ≫ P.complex.fromOpcycles (n + 1) n =
      P.complex.fromOpcycles (n + 1) n ≫ resolutionSyzygyLift P n f := by
  let := (resolutionOpcyclesSequence_shortExact P n).mono_f
  apply ShortComplex.Exact.lift_f

theorem resolutionSyzygyMap_stable_of_lift
    (f : resolutionSyzygy P n ⟶ resolutionSyzygy P n)
    (l : P.complex.X n ⟶ P.complex.X n)
    (hl : l ≫ P.complex.pOpcycles n = P.complex.pOpcycles n ≫ f)
    (s : resolutionSyzygy P (n + 1) ⟶ resolutionSyzygy P (n + 1))
    (hs : s ≫ P.complex.fromOpcycles (n + 1) n = P.complex.fromOpcycles (n + 1) n ≫ l) :
    stableRepresentationClass _ _ (resolutionSyzygyMap P n f) =
      stableRepresentationClass _ _ s := by
  let S := resolutionOpcyclesSequence P n
  have hS := resolutionOpcyclesSequence_shortExact P n
  let : Mono S.f := hS.mono_f
  have hz : (resolutionSyzygyLift P n f - l) ≫ S.g = 0 := by
    change (resolutionSyzygyLift P n f - l) ≫ P.complex.pOpcycles n = 0
    rw [Preadditive.sub_comp, resolutionSyzygyLift_comm, hl, sub_self]
  let v : P.complex.X n ⟶ resolutionSyzygy P (n + 1) :=
    hS.exact.lift (resolutionSyzygyLift P n f - l) hz
  have hv : v ≫ P.complex.fromOpcycles (n + 1) n = resolutionSyzygyLift P n f - l :=
    hS.exact.lift_f _ hz
  apply (stableRepresentationClass_eq_iff_projective_factor _ _).mpr
  refine ⟨P.complex.X n, inferInstance, S.f, v, ?_⟩
  apply (cancel_mono S.f).mp
  change (P.complex.fromOpcycles (n + 1) n ≫ v) ≫ P.complex.fromOpcycles (n + 1) n =
    (resolutionSyzygyMap P n f - s) ≫ P.complex.fromOpcycles (n + 1) n
  rw [Category.assoc, hv, Preadditive.comp_sub, Preadditive.sub_comp]
  exact congrArg₂ (fun x y => x - y) (resolutionSyzygyMap_comm P n f).symm hs.symm

theorem resolutionSyzygyMap_stable_identity :
    stableRepresentationClass _ _ (resolutionSyzygyMap P n (𝟙 _)) =
      stableRepresentationClass _ _ (𝟙 (resolutionSyzygy P (n + 1))) := by
  apply resolutionSyzygyMap_stable_of_lift P n (𝟙 _) (𝟙 _)
  · simp
  · simp

def resolutionSyzygyStableMap :
    (resolutionSyzygy P n ⟶ resolutionSyzygy P n) →ₗ[ℤ]
      StableRepresentationHom (resolutionSyzygy P (n + 1)) (resolutionSyzygy P (n + 1)) := by
  let a : (resolutionSyzygy P n ⟶ resolutionSyzygy P n) →+
      StableRepresentationHom (resolutionSyzygy P (n + 1)) (resolutionSyzygy P (n + 1)) :=
    AddMonoidHom.mk' (fun f => stableRepresentationClass _ _ (resolutionSyzygyMap P n f)) (by
      intro f g
      have h := resolutionSyzygyMap_stable_of_lift P n (f + g)
        (resolutionSyzygyLift P n f + resolutionSyzygyLift P n g)
        (by simp only [Preadditive.add_comp, Preadditive.comp_add, resolutionSyzygyLift_comm])
        (resolutionSyzygyMap P n f + resolutionSyzygyMap P n g)
        (by simp only [Preadditive.add_comp, Preadditive.comp_add, resolutionSyzygyMap_comm])
      exact h.trans (map_add _ _ _))
  exact { a with map_smul' := fun r f => map_intCast_smul a ℤ ℤ r f }

theorem resolutionSyzygyStableMap_eq_zero_of_projective_factor
    (f : resolutionSyzygy P n ⟶ resolutionSyzygy P n)
    (hf : stableRepresentationClass _ _ f = 0) : resolutionSyzygyStableMap P n f = 0 := by
  obtain ⟨Q, hQ, u, v, huv⟩ :=
    (stableRepresentationClass_eq_zero_iff_projective_factor f).mp hf
  let := hQ
  let S := resolutionOpcyclesSequence P n
  let a := Projective.factorThru v (P.complex.pOpcycles n)
  have ha : a ≫ P.complex.pOpcycles n = v := Projective.factorThru_comp _ _
  have h := resolutionSyzygyMap_stable_of_lift P n f
    (P.complex.pOpcycles n ≫ u ≫ a)
    (by rw [Category.assoc, Category.assoc, ha, huv])
    0 (by
      rw [zero_comp, ← Category.assoc, ← Category.assoc]
      change 0 = (S.f ≫ S.g) ≫ u ≫ a
      simp only [S.zero, zero_comp])
  exact h.trans ((stableRepresentationClass _ _).map_zero)

def resolutionStableSyzygyTransition :
    StableRepresentationHom (resolutionSyzygy P n) (resolutionSyzygy P n) →ₗ[ℤ]
      StableRepresentationHom (resolutionSyzygy P (n + 1)) (resolutionSyzygy P (n + 1)) :=
  (projectiveFactorSubmodule _ _).liftQ (resolutionSyzygyStableMap P n) (by
    intro f hf
    apply resolutionSyzygyStableMap_eq_zero_of_projective_factor P n f
    exact (Submodule.Quotient.mk_eq_zero _).mpr hf)

@[simp]
theorem resolutionStableSyzygyTransition_class
    (f : resolutionSyzygy P n ⟶ resolutionSyzygy P n) :
    resolutionStableSyzygyTransition P n (stableRepresentationClass _ _ f) =
      stableRepresentationClass _ _ (resolutionSyzygyMap P n f) := rfl

theorem resolutionStableSyzygyTransition_identity :
    resolutionStableSyzygyTransition P n (stableRepresentationClass _ _ (𝟙 _)) =
      stableRepresentationClass _ _ (𝟙 (resolutionSyzygy P (n + 1))) :=
  resolutionSyzygyMap_stable_identity P n

end PolycyclicRecognition

end

end OAI
