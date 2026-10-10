import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.SmallFormalGlobal
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.ConcurrentGeometry
import OAI.GroupTheory.SimpleAmenable.CentralCovers.GridPrimitiveInputs

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FormalLawCovariance
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι : Type*} [Finite ι]

omit [Finite ι] in

theorem smallPrimitiveEval_translate_local (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing)) (u : CutRing × CutRing)
    (S : Finset (Fin (m+1))) (F : CommonFrame a r m hm S u)
    (w : SmallFamilyWord (Fin (m+1)) ι) (hw : w ∈ smallFamilyLocal S) :
    smallFamilyEval (B.smallPrimitiveInputs hlarge (translatedTemplate P u)) w=
      (MulAut.conj (B.t F.k)).toMonoidHom
        (smallFamilyEval (B.smallPrimitiveInputs hlarge P) w) := by
  apply MonoidHom.eqOn_closure (f := smallFamilyEval (B.smallPrimitiveInputs hlarge (translatedTemplate P u)))
    (g := (MulAut.conj (B.t F.k)).toMonoidHom.comp (smallFamilyEval (B.smallPrimitiveInputs hlarge P))) ?_ hw
  rintro w ⟨⟨I,i,s⟩,hIS,rfl⟩
  simp only [MonoidHom.comp_apply,smallFamilyEval_of]
  let FI : CommonFrame a r m hm I.val u :=
    ⟨F.k,F.d,F.projection,fun k hk => F.common k (hIS hk)⟩
  have hh := congrFun (B.primitiveFamily_conjugate I.val
    (smallAlphabetBalance hlarge I.val (by rw [I.property.2]; omega))
    (smallAlphabetBalance_notMem hlarge I.val (by rw [I.property.2]; omega)) P u FI) i
  exact DFunLike.congr_fun hh s

theorem smallPrimitive_formal_translate (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : HasCentralLaw (smallFamilyModel (fun i : ι => {σ : ι → Bool | σ i=true}))
      (smallFamilyEval (B.smallPrimitiveInputs hlarge P)).rangeRestrict)
    (u : CutRing × CutRing) :
    HasCentralLaw (smallFamilyModel (fun i : ι => {σ : ι → Bool | σ i=true}))
      (smallFamilyEval (B.smallPrimitiveInputs hlarge (translatedTemplate P u))).rangeRestrict := by
  apply smallFamily_assignment_law _ (fun σ τ he => funext (fun i => Bool.eq_iff_iff.mpr (he i))) _ ?_
    (by simpa using (by omega : 5 ≤ m+1))
  intro S hS w hw hv v hvS
  let F := commonFrame a r m hm S (smallAlphabetBalance hlarge S hS)
    (smallAlphabetBalance_notMem hlarge S hS) u
  rw [B.smallPrimitiveEval_translate_local hlarge P u S F w hw,
    B.smallPrimitiveEval_translate_local hlarge P u S F v hvS]
  apply Commute.map
  have hz := (hasCentralLaw_iff _ _).mp h w hv
  have he := Subgroup.mem_center_iff.mp hz ((smallFamilyEval (B.smallPrimitiveInputs hlarge P)).rangeRestrict v)
  exact (show Commute (smallFamilyEval (B.smallPrimitiveInputs hlarge P) v)
    (smallFamilyEval (B.smallPrimitiveInputs hlarge P) w) from congrArg Subtype.val he).symm

namespace PatchAtlas
variable {B} (A : B.PatchAtlas)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

include A in

theorem translated_slope_coordinate_formal_law (hlarge : 25 ≤ m+1)
    (hr : 0<ordinary r ∧ ordinary r<1/2) (ha : 0<a)
    (d j : Fin 2) (u v : CutRing × CutRing) :
    HasCentralLaw (smallFamilyModel (fun i : Fin 2 => {σ : Fin 2 → Bool | σ i=true}))
      (smallFamilyEval (B.smallPrimitiveInputs (by omega)
        ![(slopeTestIndex d,u),(coordinateTestIndex j,v)])).rangeRestrict := by
  have hh := B.smallPrimitive_formal_translate (by omega)
    ![(slopeTestIndex d,0),(coordinateTestIndex j,v-u)]
    (A.slope_coordinate_formal_law hlarge hr ha d j (v-u)) u
  have he : translatedTemplate ![(slopeTestIndex d,0),(coordinateTestIndex j,v-u)] u=
      ![(slopeTestIndex d,u),(coordinateTestIndex j,v)] := by
    funext i
    fin_cases i <;> simp [translatedTemplate,add_sub_cancel]
  rwa [he] at hh

end PatchAtlas
end InitialCoverSystem
end FormalLawCovariance

end SimpleAmenable
end
end

end OAI
