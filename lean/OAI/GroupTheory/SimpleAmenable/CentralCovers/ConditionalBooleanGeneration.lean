import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.TrackTranslationChart

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ConditionalBooleanGeneration

open scoped commutatorElement

theorem conditional_inter_commutator {a m : ℕ} (U V : polygonAlgebra a)
    (g h : Equiv.Perm (Fin m)) :
    conditionalHom (U ⊓ V) ⁅g,h⁆ = ⁅conditionalHom U g,conditionalHom V h⁆ := by
  classical
  apply Subtype.ext
  apply Equiv.ext
  intro p
  change conditionalPerm (U ⊓ V) ⁅g,h⁆ p =
    conditionalPerm U g (conditionalPerm V h
      ((conditionalPerm U g).symm ((conditionalPerm V h).symm p)))
  obtain ⟨i,p⟩ := p
  by_cases hU : p ∈ U.val <;> by_cases hV : p ∈ V.val <;>
    simp_all [conditionalPerm,commutatorElement_def,Equiv.Perm.mul_apply]

theorem conditional_complement {a m : ℕ} (U : polygonAlgebra a)
    (g : Equiv.Perm (Fin m)) :
    conditionalHom Uᶜ g = conditionalHom (wholePolygon a) g * (conditionalHom U g)⁻¹ := by
  classical
  apply Subtype.ext
  apply Equiv.ext
  intro p
  change conditionalPerm Uᶜ g p =
    conditionalPerm (wholePolygon a) g ((conditionalPerm U g).symm p)
  obtain ⟨i,p⟩ := p
  by_cases hp : p ∈ U.val <;> simp_all [conditionalPerm,wholePolygon]

def ConditionalAvailable {a m : ℕ} {E : Type*} [Group E]
    (φ : E →* Equiv.Perm (Fin m)) (H : Subgroup (polygonFullGroup a m))
    (U : polygonAlgebra a) : Prop := ∀ g, conditionalHom U (φ g) ∈ H

theorem conditionalAvailable_inter {a m : ℕ} {E : Type*} [Group E] [Group.IsPerfect E]
    (φ : E →* Equiv.Perm (Fin m)) (H : Subgroup (polygonFullGroup a m))
    {U V : polygonAlgebra a} (hU : ConditionalAvailable φ H U)
    (hV : ConditionalAvailable φ H V) : ConditionalAvailable φ H (U ⊓ V) := by
  let K := H.comap ((conditionalHom (U ⊓ V)).comp φ)
  have hK : commutator E ≤ K := by
    rw [commutator_def]
    apply Subgroup.commutator_le.mpr
    intro x _ y _
    change conditionalHom (U ⊓ V) (φ ⁅x,y⁆) ∈ H
    rw [map_commutatorElement,conditional_inter_commutator]
    exact Subgroup.commutator_le_self H (Subgroup.commutator_mem_commutator (hU x) (hV y))
  intro x
  exact hK (Group.IsPerfect.commutator_eq_top (G := E) ▸ Subgroup.mem_top x)

theorem conditionalAvailable_compl {a m : ℕ} {E : Type*} [Group E]
    (φ : E →* Equiv.Perm (Fin m)) (H : Subgroup (polygonFullGroup a m))
    (hwhole : ConditionalAvailable φ H (wholePolygon a))
    {U : polygonAlgebra a} (hU : ConditionalAvailable φ H U) :
    ConditionalAvailable φ H Uᶜ := by
  intro x
  rw [conditional_complement]
  exact H.mul_mem (hwhole x) (H.inv_mem (hU x))

theorem conditionalAvailable_union {a m : ℕ} {E : Type*} [Group E] [Group.IsPerfect E]
    (φ : E →* Equiv.Perm (Fin m)) (H : Subgroup (polygonFullGroup a m))
    (hwhole : ConditionalAvailable φ H (wholePolygon a))
    {U V : polygonAlgebra a} (hU : ConditionalAvailable φ H U)
    (hV : ConditionalAvailable φ H V) : ConditionalAvailable φ H (U ⊔ V) := by
  have hh := conditionalAvailable_compl φ H hwhole
    (conditionalAvailable_inter φ H (conditionalAvailable_compl φ H hwhole hU)
      (conditionalAvailable_compl φ H hwhole hV))
  simpa only [compl_inf,compl_compl] using hh

noncomputable def conditionalBoolean {a m : ℕ} {E : Type*} [Group E] [Group.IsPerfect E]
    (φ : E →* Equiv.Perm (Fin m)) (H : Subgroup (polygonFullGroup a m))
    (hwhole : ConditionalAvailable φ H (wholePolygon a)) :
    BooleanSubalgebra (Set (GenericSquare a)) where
  carrier := {U | ∃ hU : U ∈ polygonAlgebra a, ConditionalAvailable φ H ⟨U,hU⟩}
  infClosed' := by
    rintro U ⟨hU,hU'⟩ V ⟨hV,hV'⟩
    exact ⟨BooleanSubalgebra.inf_mem hU hV,conditionalAvailable_inter φ H hU' hV'⟩
  supClosed' := by
    rintro U ⟨hU,hU'⟩ V ⟨hV,hV'⟩
    exact ⟨BooleanSubalgebra.sup_mem hU hV,conditionalAvailable_union φ H hwhole hU' hV'⟩
  compl_mem' := by
    rintro U ⟨hU,hU'⟩
    exact ⟨BooleanSubalgebra.compl_mem hU,conditionalAvailable_compl φ H hwhole hU'⟩
  bot_mem' := by
    refine ⟨BooleanSubalgebra.bot_mem,?_⟩
    intro x
    have he : conditionalHom (⟨∅,BooleanSubalgebra.bot_mem⟩ : polygonAlgebra a) (φ x) = 1 := by
      apply Subtype.ext
      apply Equiv.ext
      intro p
      simp [conditionalHom,conditionalPerm]
    change conditionalHom (⟨∅,BooleanSubalgebra.bot_mem⟩ : polygonAlgebra a) (φ x) ∈ H
    rw [he]
    exact H.one_mem

noncomputable def trackTranslationAddHom (a m : ℕ) :
    (Fin m → CutRing × CutRing) →+ Additive (polygonFullGroup a m) where
  toFun d := Additive.ofMul (trackTranslation d)
  map_zero' := trackTranslation_zero
  map_add' := trackTranslation_add

theorem trackTranslation_zsmul {a m : ℕ} (n : ℤ) (d : Fin m → CutRing × CutRing) :
    trackTranslation (a := a) (n • d) = (trackTranslation d)^n :=
  (trackTranslationAddHom a m).map_zsmul n d

theorem trackTranslation_reduce {a m : ℕ} (d : Fin m → CutRing × CutRing) :
    trackTranslation (a := a) d = trackTranslation
      (fun i => (((d i).1.im : CutRing)*cutTau,((d i).2.im : CutRing)*cutTau)) := by
  apply Subtype.ext
  apply Equiv.ext
  intro p
  change (p.1,translation a (d p.1) p.2) = _
  rw [translation_reduce]
  rfl

noncomputable def sourceGenerated (a : ℕ) (r : CutRing) (m : ℕ) :
    Subgroup (polygonFullGroup a (m+1)) := Subgroup.closure (Set.range (sourceGenerator a r m))

theorem sourceGenerator_mem_generated (a : ℕ) (r : CutRing) (m : ℕ)
    (s : SourceGeneratorLabel m) : sourceGenerator a r m s ∈ sourceGenerated a r m :=
  Subgroup.subset_closure ⟨s,rfl⟩

theorem sourceGenerated_le_alternating (a : ℕ) (r : CutRing) (m : ℕ) (hm : 2 ≤ m) :
    sourceGenerated a r m ≤ polygonAlternatingGroup a (m+1) := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨s,rfl⟩
  exact sourceGenerator_mem a r m hm s

theorem balanced_translation_generated (a : ℕ) (r : CutRing) (m : ℕ)
    (i : Fin (m+1)) (v : CutRing × CutRing) :
    trackTranslation (a := a) (Pi.single i v - Pi.single (Fin.last m) v) ∈ sourceGenerated a r m := by
  classical
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp
  let dx : Fin (m+1) → CutRing × CutRing := Pi.single i.castSucc (cutTau,0) - Pi.single (Fin.last m) (cutTau,0)
  let dy : Fin (m+1) → CutRing × CutRing := Pi.single i.castSucc (0,cutTau) - Pi.single (Fin.last m) (0,cutTau)
  have hx : trackTranslation (a := a) dx ∈ sourceGenerated a r m :=
    sourceGenerator_mem_generated a r m (Sum.inr (i,0))
  have hy : trackTranslation (a := a) dy ∈ sourceGenerated a r m := by
    simpa only [sourceGenerator,show (1 : Fin 2) ≠ 0 by decide,ite_false]
      using sourceGenerator_mem_generated a r m (Sum.inr (i,1))
  have he : trackTranslation (a := a) (Pi.single i.castSucc v - Pi.single (Fin.last m) v) =
      trackTranslation (v.1.im • dx + v.2.im • dy) := by
    let d : Fin (m+1) → CutRing × CutRing := Pi.single i.castSucc v - Pi.single (Fin.last m) v
    change trackTranslation d = _
    rw [trackTranslation_reduce d]
    congr 1
    funext k
    by_cases hki : k = i.castSucc <;> by_cases hkl : k = Fin.last m <;>
      apply Prod.ext <;> simp [d,dx,dy,hki,hkl,zsmul_eq_mul]
  rw [he,trackTranslation_add,trackTranslation_zsmul,trackTranslation_zsmul]
  exact (sourceGenerated a r m).mul_mem ((sourceGenerated a r m).zpow_mem hx _)
    ((sourceGenerated a r m).zpow_mem hy _)

theorem balanced_difference_generated (a : ℕ) (r : CutRing) (m : ℕ)
    (i j : Fin (m+1)) (v : CutRing × CutRing) :
    trackTranslation (a := a) (Pi.single j v - Pi.single i v) ∈ sourceGenerated a r m := by
  have he : (Pi.single j v - Pi.single i v : Fin (m+1) → CutRing × CutRing) =
      (Pi.single j v - Pi.single (Fin.last m) v) -
        (Pi.single i v - Pi.single (Fin.last m) v) := by abel
  rw [he,trackTranslation_sub]
  exact (sourceGenerated a r m).mul_mem (balanced_translation_generated a r m j v)
    ((sourceGenerated a r m).inv_mem (balanced_translation_generated a r m i v))

end ConditionalBooleanGeneration

end SimpleAmenable
end
end

end OAI
