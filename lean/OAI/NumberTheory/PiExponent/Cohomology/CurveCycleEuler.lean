import OAI.NumberTheory.PiExponent.Ampleness.ClosedAmpleRestriction
import OAI.NumberTheory.PiExponent.Cohomology.CurveTensorEuler
import OAI.NumberTheory.PiExponent.Geometry.CurveCycleLengths

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
open PiExponent.SectionZeroIdeal

def componentEulerDegree {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of ℂ))
    (L : LineBundle X) (C : irreducibleComponents X) : ℤ :=
  eulerCharacteristic (reducedComponentι X C ≫ p) 1
    (L.pullback (reducedComponentι X C)).sheaf -
  eulerCharacteristic (reducedComponentι X C ≫ p) 1 (structureSheaf (reducedComponent X C))

def cycleEulerDegree {X : Scheme.{0}} [NoetherianSpace X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L : LineBundle X) : ℤ := by
  classical
  letI : Fintype (irreducibleComponents X) :=
    NoetherianSpace.finite_irreducibleComponents.fintype
  exact ∑ C : irreducibleComponents X,
    (componentMultiplicity X C : ℤ) * componentEulerDegree p L C

theorem componentEulerDegree_tensor {X : Scheme.{0}} [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1) (H : LineBundle X) (hH : H.IsAmple)
    (L M : LineBundle X) (C : irreducibleComponents X) :
    componentEulerDegree p (L.tensor M) C =
      componentEulerDegree p L C + componentEulerDegree p M C := by
  let i := reducedComponentι X C
  let : IsLocallyNoetherian (reducedComponent X C) :=
    LocallyOfFiniteType.isLocallyNoetherian (i ≫ p)
  let : CompactSpace (reducedComponent X C) :=
    QuasiCompact.compactSpace_of_compactSpace (i ≫ p)
  let : IsNoetherian (reducedComponent X C) := {}
  have hdim : topologicalKrullDim (reducedComponent X C) ≤ 1 :=
    i.isEmbedding.isInducing.topologicalKrullDim_le.trans hd
  have h := tensor_euler_add (i ≫ p) hdim (H.pullback i)
    (hH.pullback_closedImmersion H i) (L.pullback i) (M.pullback i)
  have he := eulerCharacteristic_iso (i ≫ p) (PiExponentSeshadri.PullbackTensor.iso i L M) 1
  unfold componentEulerDegree
  change eulerCharacteristic (i ≫ p) 1 ((L.tensor M).pullback i).sheaf =
    eulerCharacteristic (i ≫ p) 1 ((L.pullback i).tensor (M.pullback i)).sheaf at he
  rw [he]
  dsimp only [i] at h he ⊢
  omega

theorem cycleEulerDegree_tensor {X : Scheme.{0}} [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1) (H : LineBundle X) (hH : H.IsAmple)
    (L M : LineBundle X) :
    cycleEulerDegree p (L.tensor M) = cycleEulerDegree p L + cycleEulerDegree p M := by
  classical
  unfold cycleEulerDegree
  simp only [componentEulerDegree_tensor p hd H hH L M,mul_add,Finset.sum_add_distrib]

theorem componentEulerDegree_zero_of_dimension_le_zero {X : Scheme.{0}}
    [IsLocallyNoetherian X] (p : X ⟶ Spec (CommRingCat.of ℂ))
    (L : LineBundle X) (C : irreducibleComponents X)
    (hdim : topologicalKrullDim (reducedComponent X C) ≤ 0) :
    componentEulerDegree p L C = 0 := by
  let : IsLocallyNoetherian (reducedComponent X C) :=
    LocallyOfFiniteType.isLocallyNoetherian (reducedComponentι X C)
  obtain ⟨e⟩ := NumericalAmpleness.lineBundle_trivial_of_dim_le_zero hdim
    (L.pullback (reducedComponentι X C))
  exact sub_eq_zero.mpr (eulerCharacteristic_iso (reducedComponentι X C ≫ p) e 1)

theorem regular_section_tensor_euler_eq_cycle {X : Scheme.{0}}
    [IsNoetherian X] [Nonempty X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1) (H : LineBundle X) (hH : H.IsAmple)
    (L M : LineBundle X) (s : GlobalSections X L.sheaf) [Mono s] :
    eulerCharacteristic p 1 (L.tensor M).sheaf - eulerCharacteristic p 1 M.sheaf =
      cycleEulerDegree p L := by
  classical
  let : Fintype (irreducibleComponents X) :=
    NoetherianSpace.finite_irreducibleComponents.fintype
  let : Finite (zeroIdeal L s).subscheme :=
    GeneralCartierDegreeLength.finite_zeroIdeal_of_mono p hd L s
  let : Fintype (zeroIdeal L s).subscheme := Fintype.ofFinite _
  let : ∀ C : irreducibleComponents X,
    Fintype (zeroIdeal (L.pullback (reducedComponentι X C))
      (pullbackSection (reducedComponentι X C) s)).subscheme := fun _ => Fintype.ofFinite _
  have hcomponent (C : irreducibleComponents X) :
      componentEulerDegree p L C =
        ∑ z, ((stalkLength (zeroIdeal (L.pullback (reducedComponentι X C))
          (pullbackSection (reducedComponentι X C) s)).subscheme z).toNat : ℤ) := by
    let i := reducedComponentι X C
    let LC := L.pullback i
    let sC := pullbackSection i s
    have hsC : Mono sC := regular_component_section_mono X C L s
    have hdim : topologicalKrullDim (reducedComponent X C) ≤ 1 :=
      i.isEmbedding.isInducing.topologicalKrullDim_le.trans hd
    have hc := @regular_section_tensor_euler_eq_lengths _ inferInstance (i ≫ p)
      inferInstance hdim (H.pullback i) (hH.pullback_closedImmersion H i)
      LC (LC.pow 0) sC hsC
    have he := eulerCharacteristic_iso (i ≫ p) (moduleTensorRightUnit LC.sheaf) 1
    change eulerCharacteristic (i ≫ p) 1 (LC.tensor (LC.pow 0)).sheaf =
      eulerCharacteristic (i ≫ p) 1 LC.sheaf at he
    rw [he] at hc
    exact hc
  have hlength := zero_lengthNat_eq_component_sum hd L s
  have hlengthZ :
      (∑ y : (zeroIdeal L s).subscheme, ((stalkLength (zeroIdeal L s).subscheme y).toNat : ℤ)) =
        ∑ C : irreducibleComponents X, (componentMultiplicity X C : ℤ) *
          ∑ z, ((stalkLength (zeroIdeal (L.pullback (reducedComponentι X C))
            (pullbackSection (reducedComponentι X C) s)).subscheme z).toNat : ℤ) := by
    exact_mod_cast hlength
  calc
    eulerCharacteristic p 1 (L.tensor M).sheaf - eulerCharacteristic p 1 M.sheaf =
        ∑ y : (zeroIdeal L s).subscheme, ((stalkLength (zeroIdeal L s).subscheme y).toNat : ℤ) :=
      regular_section_tensor_euler_eq_lengths p hd H hH L M s
    _ = ∑ C : irreducibleComponents X, (componentMultiplicity X C : ℤ) *
          ∑ z, ((stalkLength (zeroIdeal (L.pullback (reducedComponentι X C))
            (pullbackSection (reducedComponentι X C) s)).subscheme z).toNat : ℤ) := hlengthZ
    _ = cycleEulerDegree p L := by
      unfold cycleEulerDegree
      apply Finset.sum_congr rfl
      intro C _
      exact congrArg (fun n : ℤ => (componentMultiplicity X C : ℤ) * n) (hcomponent C).symm

theorem tensor_euler_eq_cycle {X : Scheme.{0}} [IsNoetherian X] [Nonempty X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1) (H : LineBundle X) (hH : H.IsAmple)
    (L M : LineBundle X) :
    eulerCharacteristic p 1 (L.tensor M).sheaf - eulerCharacteristic p 1 M.sheaf =
      cycleEulerDegree p L := by
  obtain ⟨B,s,t,hs,ht⟩ := NumericalAmpleness.exists_regular_twist_pair p H L hH
  let : Mono s := hs
  let : Mono t := ht
  have h₁ := regular_section_tensor_euler_eq_cycle p hd H hH (L.tensor B) M s
  have h₂ := regular_section_tensor_euler_eq_cycle p hd H hH B (L.tensor M) t
  have hcycle := cycleEulerDegree_tensor p hd H hH L B
  have ha := eulerCharacteristic_iso p
    (moduleTensorIso (moduleTensorComm L.sheaf B.sheaf) (Iso.refl M.sheaf) ≪≫
      lineTensorAssoc B L M) 1
  change eulerCharacteristic p 1 ((L.tensor B).tensor M).sheaf =
    eulerCharacteristic p 1 (B.tensor (L.tensor M)).sheaf at ha
  omega

end
end PiExponent.CurveCycle

end OAI
