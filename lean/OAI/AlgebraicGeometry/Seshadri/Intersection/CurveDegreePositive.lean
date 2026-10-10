import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Intersection.SectionEuler

namespace OAI

section
noncomputable section
                                             
section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open MaximalSeshadri.Projective MaximalSeshadri.Frames MaximalSeshadri.SectionOpens

variable {X : Scheme.{0}}

lemma flasque_zero_of_global_subsingleton (M : X.Modules)
    [TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)]
    [Subsingleton Γ(M,⊤)] : IsZero M := by
  apply (IsZero.iff_id_eq_zero _).mpr
  ext U x
  have hs : Function.Surjective (M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op) :=
    (AddCommGrpCat.epi_iff_surjective _).mp
      (TopCat.Presheaf.IsFlasque.epi
        (F := ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).obj)
        (homOfLE (le_top : U ≤ ⊤)).op)
  let : Subsingleton Γ(M,U) := ⟨fun x y => by
    obtain ⟨a,rfl⟩ := hs x
    obtain ⟨b,rfl⟩ := hs y
    exact congrArg _ (Subsingleton.elim a b)⟩
  exact Subsingleton.elim _ _

variable [IsIntegral X] [IsNoetherian X]
variable {σ : Type} [Fintype σ]
variable (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X = 1) {A : X.Modules}
    (a : σ → (O X ⟶ A)) (ha : (⨆ i, isoOpen (a i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism (baseScalars p) a ha)]
include hd a ha

theorem projective_section_positive_degree (L : LineBundle X)
    (s : O X ⟶ L.sheaf) (hs : s ≠ 0) (hz : isoOpen s ≠ ⊤) :
    0 < eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (O X) := by
  let := Module.compHom Γ(cokernel s,⊤) (baseScalars p)
  let := Module.compHom (cohomology (cokernel s) 0) (baseScalars p)
  let := projective_section_cokernel_finite p hd a ha L s hs 0
  let : Module.Finite ℂ Γ(cokernel s,⊤) :=
    Module.Finite.of_surjective (cohomologyZeroSections p (cokernel s)).toLinearMap
      (cohomologyZeroSections p (cokernel s)).surjective
  rw [projective_section_euler_difference p hd a ha L s hs]
  have ht : Nontrivial Γ(cokernel s,⊤) := by
    by_contra hn
    let : Subsingleton Γ(cokernel s,⊤) := not_nontrivial_iff_subsingleton.mp hn
    have hzero := @flasque_zero_of_global_subsingleton X (cokernel s)
      (L.cokernel_flasque hd.le s hs) inferInstance
    let := CategoryTheory.Preadditive.epi_of_isZero_cokernel s hzero
    let : Mono s := L.mono_section s hs
    let : IsIso s := isIso_of_mono_of_epi s
    apply hz
    apply top_unique
    intro x _
    exact (mem_isoOpen_iff s x).mpr ⟨⊤,trivial,inferInstance⟩
  let := ht
  exact_mod_cast Module.finrank_pos

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
