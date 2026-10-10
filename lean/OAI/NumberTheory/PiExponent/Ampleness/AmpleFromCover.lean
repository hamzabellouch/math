import OAI.NumberTheory.PiExponent.Ampleness.AmpleProjectiveSections
import OAI.NumberTheory.PiExponent.Approximation.TensorSectionOpen

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Frames PiExponentSeshadri.Projective PiExponentSeshadri.TensorPure
variable {X : Scheme.{0}}

theorem LineBundle.section_basicOpen [IsIntegral X] [CompactSpace X]
    (L : LineBundle X) (s : O X ⟶ L.sheaf)
    (hne : (sectionOpen X s : Set X).Nonempty) (f : Γ(X,sectionOpen X s)) :
    ∃ n : ℕ, 0 < n ∧ ∃ t : O X ⟶ (L.pow n).sheaf,
      sectionOpen X t = X.basicOpen f := by
  let U := sectionOpen X s
  obtain ⟨N,hN⟩ := L.power_extension_ratio s hne (U.topIso.inv f)
  let n := max N 1
  have hn : 0 < n := lt_of_lt_of_le (by decide : 0<1) (le_max_right N 1)
  obtain ⟨t,ht⟩ := hN n (le_max_left N 1)
  let q := tensorSection s t
  have hsub : SectionOpens.isoOpen q ≤ U := by
    exact (section_open L (L.pow n) s t).le.trans inf_le_left
  have hi : IsIso (restrictSection U.ι (powerSection s n)) :=
    isIso_restricted_section _ _ (L.sectionOpen_power s hn)
  let e : (L.pow n).sheaf.restrict U.ι ≅ O U.toScheme :=
    (asIso (restrictSection U.ι (powerSection s n))).symm
  have hcoef : coefficient e (restrictSection U.ι t) = U.topIso.inv f := by
    apply coefficient_ratio e (powerSection s n) t
    · exact coefficient_frame e
    · exact ht
  have hnorm : coefficient (sectionFrame s) (restrictSection U.ι s) = 1 :=
    sectionFrame_normalized s
  have hpre : U.ι ⁻¹ᵁ SectionOpens.isoOpen q = U.toScheme.basicOpen (U.topIso.inv f) := by
    refine (preimage_isoOpen q U.ι (tensorFrame L (L.pow n) U (sectionFrame s) e)).trans ?_
    apply congrArg U.toScheme.basicOpen
    exact (local_section_coefficient L (L.pow n) U (sectionFrame s) e s t).trans
      ((congrArg₂ (fun (a b : Γ(U.toScheme, ⊤)) => a * b) hnorm hcoef).trans
        (one_mul _))
  refine ⟨n+1,by omega,q,?_⟩
  change SectionOpens.isoOpen q = _
  calc
    _ = U.ι ''ᵁ (U.ι ⁻¹ᵁ SectionOpens.isoOpen q) := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf,Scheme.Opens.opensRange_ι,inf_eq_right.mpr hsub]
    _ = _ := by rw [hpre,U.ι_image_basicOpen_topIso_inv]

theorem LineBundle.ample_of_affine_section_cover [IsIntegral X] [CompactSpace X]
    (L : LineBundle X) {ι : Type*} (s : ι → (O X ⟶ L.sheaf))
    (hc : (⨆ i, sectionOpen X (s i)) = ⊤)
    (ha : ∀ i, IsAffineOpen (sectionOpen X (s i))) : L.IsAmple := by
  intro x V hx
  have hc' : x ∈ ⨆ i, sectionOpen X (s i) := by rw [hc]; trivial
  obtain ⟨i,hi⟩ := Opens.mem_iSup.mp hc'
  obtain ⟨f,hf,hxf⟩ := (ha i).exists_basicOpen_le ⟨x,hx⟩ hi
  obtain ⟨n,hn,t,ht⟩ := L.section_basicOpen (s i) ⟨x,hi⟩ f
  exact ⟨n,hn,t,ht.symm ▸ hxf,ht.le.trans hf,ht.symm ▸ (ha i).basicOpen f⟩

end
end PiExponentSeshadri.Geometry

end OAI
