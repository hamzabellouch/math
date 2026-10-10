import OAI.NumberTheory.PiExponent.Ampleness.AmpleProjectiveSections
import OAI.NumberTheory.PiExponent.Approximation.MixedSectionExtension
import OAI.NumberTheory.PiExponent.Approximation.TensorMixedSection

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Frames PiExponentSeshadri.TensorPure
variable {X : Scheme.{0}}

theorem LineBundle.divisible_mixed_extension [IsIntegral X] [CompactSpace X] (L M : LineBundle X)
    (s : O X ⟶ L.sheaf) (hD : (sectionOpen X s : Set X).Nonempty)
    (w : Γ(M.sheaf,sectionOpen X s)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ t : O X ⟶ ((L.pow (n+1)).tensor M).sheaf,
      sectionOpen X t ≤ sectionOpen X s ∧
      t.app (sectionOpen X s) (1 : Γ(X,sectionOpen X s)) =
        pure (L.pow (n+1)).sheaf M.sheaf (sectionOpen X s)
          ((powerSection s (n+1)).app (sectionOpen X s) (1 : Γ(X,sectionOpen X s))) w := by
  obtain ⟨N,hN⟩ := L.mixed_extension M s hD w
  refine ⟨N,fun n hn => ?_⟩
  obtain ⟨t,ht⟩ := hN n hn
  let q := tensorSection s t ≫ (lineTensorAssoc L (L.pow n) M).inv
  refine ⟨q,?_,?_⟩
  · change SectionOpens.isoOpen (tensorSection s t ≫ (lineTensorAssoc L (L.pow n) M).symm.hom) ≤ _
    erw [SectionOpens.isoOpen_postcomp,section_open L ((L.pow n).tensor M)]
    exact inf_le_left
  · let D := sectionOpen X s
    change (lineTensorAssoc L (L.pow n) M).inv.app D ((tensorSection s t).app D (1 : Γ(X,D))) = _
    have h := (section_apply s t D).trans
      (congrArg (pure L.sheaf ((L.pow n).tensor M).sheaf D (s.app D (1 : Γ(X,D)))) ht)
    exact (congrArg ((lineTensorAssoc L (L.pow n) M).inv.app D) h).trans
      ((assoc_inv_pure L (L.pow n) M D _ _ w).trans
       (congrArg (fun z => pure (L.pow (n+1)).sheaf M.sheaf D z w) (power_succ_apply s n D).symm))

theorem LineBundle.mixed_frame_extension [IsIntegral X] [CompactSpace X] (L M : LineBundle X)
    (s : O X ⟶ L.sheaf) (hD : (sectionOpen X s : Set X).Nonempty)
    (e : M.sheaf.restrict (sectionOpen X s).ι ≅ O (sectionOpen X s).toScheme) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ t : O X ⟶ ((L.pow (n+1)).tensor M).sheaf,
      sectionOpen X t = sectionOpen X s ∧
      t.app (sectionOpen X s) (1 : Γ(X,sectionOpen X s)) =
        pure (L.pow (n+1)).sheaf M.sheaf (sectionOpen X s)
          ((powerSection s (n+1)).app (sectionOpen X s) (1 : Γ(X,sectionOpen X s)))
          (openSectionEquiv M.sheaf (sectionOpen X s) e.inv) := by
  obtain ⟨N,hN⟩ := L.divisible_mixed_extension M s hD
    (openSectionEquiv M.sheaf (sectionOpen X s) e.inv)
  refine ⟨N,fun n hn => ?_⟩
  obtain ⟨t,ht,hv⟩ := hN n hn
  refine ⟨t,le_antisymm ht ?_,hv⟩
  have hi : IsIso (restrictSection (sectionOpen X s).ι (powerSection s (n+1))) := by
    have hs := L.sectionOpen_power s (by omega : 0 < n+1)
    exact isIso_restricted_section _ _ hs
  exact mixed_value_open (sectionOpen X s) (powerSection s (n+1)) e.inv t hv

end
end PiExponentSeshadri.Geometry

end OAI
