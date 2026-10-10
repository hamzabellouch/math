import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Cohomology.MixedDivisibleExtension
import OAI.AlgebraicGeometry.Seshadri.Sheaves.AmpleFramedCover

namespace OAI


                                        
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective MaximalSeshadri.TensorPure

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
  let sectionTrivialization : L.sheaf.restrict U.ι ≅ O U.toScheme := sectionFrame s
  have hnorm : coefficient sectionTrivialization (restrictSection U.ι s) = 1 :=
    sectionFrame_normalized s
  have hpre : U.ι ⁻¹ᵁ SectionOpens.isoOpen q = U.toScheme.basicOpen (U.topIso.inv f) := by
    refine (preimage_isoOpen q U.ι (tensorFrame L (L.pow n) U sectionTrivialization e)).trans ?_
    exact congrArg (fun value : Γ(U.toScheme,⊤) => U.toScheme.basicOpen value)
      ((local_section_coefficient L (L.pow n) U sectionTrivialization e s t).trans
        (by rw [hnorm,hcoef,one_mul]))
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

theorem LineBundle.exists_ample_twist [IsIntegral X] [CompactSpace X]
    (L M : LineBundle X) (hL : L.IsAmple) :
    ∃ d : ℕ, 0 < d ∧ ((L.pow d).tensor M).IsAmple := by
  classical
  obtain ⟨a,ha,-,ι,hi,s,hs,hsa,hsn,he⟩ := L.ample_framed_cover M hL 1 (by decide)
  choose N hN using fun i => (L.pow a).mixed_frame_extension M (s i) (hsn i)
    (Classical.choice (he i))
  let n := Finset.univ.sup N
  choose t ht hval using fun i => hN i n (Finset.le_sup (Finset.mem_univ i))
  let e : (((L.pow a).pow (n+1)).tensor M).sheaf ≅ ((L.pow (a*(n+1))).tensor M).sheaf :=
    moduleTensorIso (linePowerMul L a (n+1)) (Iso.refl M.sheaf)
  let q (i : ι) : O X ⟶ ((L.pow (a*(n+1))).tensor M).sheaf := t i ≫ e.hom
  have hq (i : ι) : sectionOpen X (q i) = sectionOpen X (s i) := by
    exact (SectionOpens.isoOpen_postcomp (t i) e).trans (ht i)
  refine ⟨a*(n+1),Nat.mul_pos ha (by omega),
    ((L.pow (a*(n+1))).tensor M).ample_of_affine_section_cover q ?_ ?_⟩
  · simpa only [hq] using hs
  · intro i
    rw [hq]
    exact hsa i
end
end MaximalSeshadri.Geometry

end


end OAI
