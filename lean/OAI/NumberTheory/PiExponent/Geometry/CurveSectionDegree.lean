import OAI.NumberTheory.PiExponent.Geometry.CartierDegreeLength
import OAI.NumberTheory.PiExponent.Geometry.SectionZeroStalk

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames

namespace PiExponent.CurveSectionDegree


variable {X : Scheme.{0}}

structure AffineFrameAt (L : LineBundle X) (x : X) where
  openSet : X.affineOpens
  mem : x ∈ openSet.1
  frame : L.sheaf.restrict openSet.1.ι ≅ O openSet.1.toScheme

 theorem nonempty_affineFrameAt (L : LineBundle X) (x : X) : Nonempty (AffineFrameAt L x) := by
  obtain ⟨V, hxV, ⟨eV⟩⟩ := L.locallyRankOne x
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset hxV
  exact ⟨⟨⟨U,hU⟩, hxU, restrictOpenFrame hUV eV⟩⟩

def affineFrameAt (L : LineBundle X) (x : X) : AffineFrameAt L x :=
  Classical.choice (nonempty_affineFrameAt L x)

def coefficientGermAt (L : LineBundle X) (s : GlobalSections X L.sheaf) (x : X) :
    X.presheaf.stalk x :=
  SectionZeroStalk.sectionGerm L s (affineFrameAt L x).openSet
    (affineFrameAt L x).frame x (affineFrameAt L x).mem

theorem zeroPoint_ne_generic [IsIntegral X]
    (L : LineBundle X) (s : GlobalSections X L.sheaf) (hs : s ≠ 0)
    (y : (SectionZeroIdeal.zeroIdeal L s).subscheme) :
    (SectionZeroIdeal.zeroIdeal L s).subschemeι y ≠ genericPoint X := by
  let I := SectionZeroIdeal.zeroIdeal L s
  intro hy
  have hg : genericPoint X ∈ (I.support : Set X) := by
    rw [← I.range_subschemeι]
    exact ⟨y,hy⟩
  have htop : (Set.univ : Set X) ⊆ I.support := by
    rw [← genericPoint_spec X]
    exact closure_minimal (Set.singleton_subset_iff.mpr hg) I.support.isClosed
  apply SectionZeroIdeal.zeroIdeal_ne_bot L s hs
  apply Scheme.IdealSheafData.support_eq_top_iff.mp
  exact TopologicalSpace.Closeds.ext (Set.Subset.antisymm (Set.subset_univ _) htop)

theorem euler_difference_eq_sum_zero_orders [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1)
    (L : LineBundle X) (s : GlobalSections X L.sheaf) (hs : s ≠ 0)
    (hDVR : ∀ x : X, x ≠ genericPoint X → IsDiscreteValuationRing (X.presheaf.stalk x))
    (hfiniteO : ∀ n ≤ 1, letI := Module.compHom (cohomology (structureSheaf X) n) (baseScalars p)
      FiniteDimensional ℂ (cohomology (structureSheaf X) n))
    (hfiniteL : ∀ n ≤ 1, letI := Module.compHom (cohomology L.sheaf n) (baseScalars p)
      FiniteDimensional ℂ (cohomology L.sheaf n))
    [Subsingleton (cohomology (structureSheaf X) 2)] :
    letI : Finite (SectionZeroIdeal.zeroIdeal L s).subscheme :=
      finite_subscheme_of_curve p hd _ (SectionZeroIdeal.zeroIdeal_ne_bot L s hs)
    letI : Fintype (SectionZeroIdeal.zeroIdeal L s).subscheme := Fintype.ofFinite _
    eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (structureSheaf X) =
      ∑ y : (SectionZeroIdeal.zeroIdeal L s).subscheme,
        letI := hDVR _ (zeroPoint_ne_generic L s hs y)
        ((IsDiscreteValuationRing.addVal
          (X.presheaf.stalk ((SectionZeroIdeal.zeroIdeal L s).subschemeι y))
          (coefficientGermAt L s ((SectionZeroIdeal.zeroIdeal L s).subschemeι y))).toNat : ℤ) := by
  let I := SectionZeroIdeal.zeroIdeal L s
  have hI : I ≠ ⊥ := SectionZeroIdeal.zeroIdeal_ne_bot L s hs
  let : Finite I.subscheme := finite_subscheme_of_curve p hd I hI
  let : Fintype I.subscheme := Fintype.ofFinite _
  let : Mono s := L.mono_section s hs
  have heq : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ e : (L.pow 0).sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ d : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
        I.ideal U = Ideal.span {U.1.topIso.hom
          (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map s ≫ d.hom))} := by
    intro x
    let F := affineFrameAt L x
    refine ⟨F.openSet, F.mem, Scheme.Modules.restrictUnitIso F.openSet.1.ι, F.frame, ?_⟩
    have h := SectionZeroIdeal.zeroIdeal_on_frame L s F.openSet F.frame
    simp only [coefficient, restrictSection] at h
    erw [Category.assoc] at h
    exact h
  let : Subsingleton (cohomology (L.pow 0).sheaf 2) := by
    change Subsingleton (cohomology (structureSheaf X) 2)
    infer_instance
  have hh := @CartierDegreeLength.cartier_euler_difference_eq_sum_local_lengths
    X inferInstance p inferInstance hd (L.pow 0) L s (L.mono_section s hs)
    I hI heq hfiniteO hfiniteL inferInstance
  refine hh.trans (Finset.sum_congr rfl fun y _ => ?_)
  let := hDVR _ (zeroPoint_ne_generic L s hs y)
  have h := SectionZeroStalk.zero_stalk_length_eq_order L s hs
    (affineFrameAt L (I.subschemeι y)).openSet
    (affineFrameAt L (I.subschemeι y)).frame y
    (affineFrameAt L (I.subschemeι y)).mem
  exact congrArg (fun n : ℕ∞ => (n.toNat : ℤ)) h

end PiExponent.CurveSectionDegree

end

end OAI
