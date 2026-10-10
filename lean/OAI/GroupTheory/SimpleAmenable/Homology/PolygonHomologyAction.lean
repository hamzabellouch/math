import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.PolygonAlternatingStabilization

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PolygonHomologyAction

open Classical Set
namespace PolygonTracks
variable {a k n : ℕ}

theorem stabilize_fix_outside (g : polygonFullGroup a n) (x : TrackPoint a (k+n))
    (hx : x∉Set.range (rightIncl a k n)) : (stabilize a k n g).val x=x := by
  obtain ⟨y,rfl⟩ := (join a k n).surjective x
  cases y with
  | inl y => exact stabilize_left g y
  | inr y => exact False.elim (hx ⟨y,rfl⟩)

theorem conjugate_stabilize_eq (f c : polygonFullGroup a (k+n))
    (hc : ∀x : TrackPoint a n,c.val (rightIncl a k n x)=f.val (rightIncl a k n x))
    (g : polygonFullGroup a n) :
    f*stabilize a k n g*f⁻¹=c*stabilize a k n g*c⁻¹ := by
  apply Subtype.ext
  apply Equiv.ext
  intro y
  obtain ⟨x,rfl⟩ := f.val.surjective y
  change f.val ((stabilize a k n g).val (f.val.symm (f.val x)))=
    c.val ((stabilize a k n g).val (c.val.symm (f.val x)))
  rw [f.val.symm_apply_apply]
  by_cases hx : x∈Set.range (rightIncl a k n)
  · obtain ⟨z,rfl⟩ := hx
    rw [←hc z,c.val.symm_apply_apply]
    change f.val ((stabilize a k n g).val (z.1.natAdd k,z.2))=
      c.val ((stabilize a k n g).val (z.1.natAdd k,z.2))
    rw [stabilize_right]
    exact (hc (g.val z)).symm
  · have hz : c.val.symm (f.val x)∉Set.range (rightIncl a k n) := by
      rintro ⟨z,hz⟩
      have hg : f.val (rightIncl a k n z)=f.val x := by
        rw [←hc z,hz,c.val.apply_symm_apply]
      exact hx ⟨z,f.val.injective hg⟩
    rw [stabilize_fix_outside g x hx,stabilize_fix_outside g _ hz,c.val.apply_symm_apply]

noncomputable def fullConjugation (a m : ℕ) (f : polygonFullGroup a m) :
    polygonAlternatingGroup a m →* polygonAlternatingGroup a m :=
  (MulAut.conj f).toMonoidHom.restrict (fun g hg =>
    (polygonAlternatingGroup_normal a m).conj_mem g hg f)

@[simp] theorem fullConjugation_val (f : polygonFullGroup a (k+n))
    (g : polygonAlternatingGroup a (k+n)) :
    (fullConjugation a (k+n) f g).val=f*g.val*f⁻¹ := rfl

theorem conjugation_stabilize_inner (f : polygonFullGroup a (k+n)) (hm : 6*n+7<k+n) :
    ∃c : polygonAlternatingGroup a (k+n),
      (fullConjugation a (k+n) f).comp (stabilizeAlternating a k n)=
      (MulAut.conj c).toMonoidHom.comp (stabilizeAlternating a k n) := by
  obtain ⟨c,hc⟩ := exists_alternating_agrees_right f hm
  refine ⟨c,?_⟩
  apply MonoidHom.ext
  intro g
  apply Subtype.ext
  exact conjugate_stabilize_eq f c.val hc g.val

theorem mapH2_fullConjugation_comp_stabilize (f : polygonFullGroup a (k+n))
    (hm : 6*n+7<k+n) :
    (IntegralHomology.mapH2 (fullConjugation a (k+n) f)).comp
      (IntegralHomology.mapH2 (stabilizeAlternating a k n))=
      IntegralHomology.mapH2 (stabilizeAlternating a k n) := by
  obtain ⟨c,hc⟩ := conjugation_stabilize_inner f hm
  rw [←IntegralHomology.mapH2_comp,hc,IntegralHomology.mapH2_conjugate]

theorem mapH2_fullConjugation_eq_id_of_surjective
    (hm : 6*n+7<k+n)
    (hs : Function.Surjective (IntegralHomology.mapH2 (stabilizeAlternating a k n)))
    (f : polygonFullGroup a (k+n)) :
    IntegralHomology.mapH2 (fullConjugation a (k+n) f)=LinearMap.id := by
  apply LinearMap.ext
  intro z
  obtain ⟨w,rfl⟩ := hs z
  exact LinearMap.congr_fun (mapH2_fullConjugation_comp_stabilize f hm) w

end PolygonTracks
end PolygonHomologyAction

end SimpleAmenable
end
end

end OAI
