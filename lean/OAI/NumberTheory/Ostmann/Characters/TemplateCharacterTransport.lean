import OAI.NumberTheory.Ostmann.Characters.TemplateCharacterTransportCore
import OAI.NumberTheory.Ostmann.Characters.TemplateConstituentsGraph

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable

theorem constituentRow_reindex {G:Type*} [CommGroup G] (k n:ℕ) (hn:n<k)
    (width:Role→ℕ) (i:(schedule k (n+1)).Constituent width)
    (z:(schedule k (n+1)).Constituent width→G) :
    rowProduct (constituentGraph k (n+1) width i) z =
      rowProduct
        (transferGraph (collapsedConstituentGraph (schedule k n) n width (pivotSlot k n hn)
          (graph k n) (intraGraph k n)) (nextConstituentEquiv (schedule k n) n width i))
        (fun h => z ((nextConstituentEquiv (schedule k n) n width).symm h)) := by
  classical
  unfold rowProduct
  rw [← (nextConstituentEquiv (schedule k n) n width).symm.prod_comp
    (fun h => z h ^ constituentGraph k (n+1) width i h)]
  simp only [constituentGraph_succ k n hn,Equiv.apply_symm_apply]

theorem character_constituent_copied_transport {F:Type*} [CommRing F]
    (χ:MulChar F ℂ) (k n:ℕ) (hn:n<k) (width:Role→ℕ)
    (i:CopiedConstituent (schedule k n) n width) (t:Bool) (ν:ℂˣ) (P u:Fˣ)
    (z:(schedule k (n+1)).Constituent width→Fˣ)
    (hP:P=u*∏h:CopiedConstituent (schedule k n) n width,
      z ((nextConstituentEquiv (schedule k n) n width).symm (.inl (h,!t)))) :
    let b := collapsedConstituentGraph (schedule k n) n width (pivotSlot k n hn)
      (graph k n) (intraGraph k n)
    let e := nextConstituentEquiv (schedule k n) n width
    (ν*oldCopiedRow b i t (χ.toUnitHom P) (fun h => χ.toUnitHom (z (e.symm h))))^copySign t =
      (ν^copySign t*(χ.toUnitHom u)^(copySign t*b (some (.inl i)) none))*
        rowProduct (constituentGraph k (n+1) width (e.symm (.inl (i,t))))
          (fun h => χ.toUnitHom (z h)) := by
  classical
  dsimp only
  have hP' : χ.toUnitHom P=χ.toUnitHom u*
      ∏h:CopiedConstituent (schedule k n) n width,
        χ.toUnitHom (z ((nextConstituentEquiv (schedule k n) n width).symm (.inl (h,!t)))) := by
    rw [hP,map_mul,map_prod]
  have hh := copied_row_transport
    (collapsedConstituentGraph (schedule k n) n width (pivotSlot k n hn) (graph k n) (intraGraph k n))
    i t ν (χ.toUnitHom P) (χ.toUnitHom u)
    (fun h => χ.toUnitHom (z ((nextConstituentEquiv (schedule k n) n width).symm h)))
    (by simp [collapsedConstituentGraph,liftGraph]) hP'
  rw [constituentRow_reindex k n hn,Equiv.apply_symm_apply]
  exact hh

theorem character_constituent_shared_transport {F:Type*} [CommRing F]
    (χ:MulChar F ℂ) (k n:ℕ) (hn:n<k) (width:Role→ℕ)
    (i:OutsideConstituent (schedule k n) n width) (νL νR:ℂˣ) (P:Fˣ)
    (z:(schedule k (n+1)).Constituent width→Fˣ) :
    let b := collapsedConstituentGraph (schedule k n) n width (pivotSlot k n hn)
      (graph k n) (intraGraph k n)
    let e := nextConstituentEquiv (schedule k n) n width
    let Z := fun h => χ.toUnitHom (z (e.symm h))
    (νL*(χ.toUnitHom P)^b (some (.inr i)) none*
        (∏h,Z (.inl (h,true))^b (some (.inr i)) (some (.inl h)))*
        (∏y,Z (.inr y)^b (some (.inr i)) (some (.inr y)))) /
    (νR*(χ.toUnitHom P)^b (some (.inr i)) none*
        (∏h,Z (.inl (h,false))^b (some (.inr i)) (some (.inl h)))*
        (∏y,Z (.inr y)^b (some (.inr i)) (some (.inr y)))) =
      (νL/νR)*rowProduct (constituentGraph k (n+1) width (e.symm (.inr i)))
        (fun h => χ.toUnitHom (z h)) := by
  classical
  dsimp only
  rw [constituentRow_reindex k n hn,Equiv.apply_symm_apply]
  exact shared_row_transport
    (H := CopiedConstituent (schedule k n) n width)
    (Y := OutsideConstituent (schedule k n) n width) (G := ℂˣ)
    (collapsedConstituentGraph (schedule k n) n width (pivotSlot k n hn)
      (graph k n) (intraGraph k n)) i νL νR (χ.toUnitHom P)
    (fun h => χ.toUnitHom (z ((nextConstituentEquiv (schedule k n) n width).symm h)))

theorem complex_copySign (z:ℂ) (hz:‖z‖=1) (t:Bool) :
    z^copySign t=if t then z else conj z := by
  cases t <;> simp [copySign,Complex.inv_eq_conj hz]

end Ostmann.Characters.Template

end

end OAI
