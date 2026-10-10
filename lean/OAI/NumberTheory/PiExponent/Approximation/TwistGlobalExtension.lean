import OAI.NumberTheory.PiExponent.Approximation.SectionOpens
import OAI.NumberTheory.PiExponent.Approximation.TwistSectionClearing
import OAI.NumberTheory.PiExponent.Geometry.SheafSectionGluing
import OAI.NumberTheory.PiExponent.LocalAlgebra.TwistLocalExtension

namespace OAI

namespace PiExponent.TwistGlobalExtension
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.GlobalSectionClearing PiExponent.SheafSectionGluing
variable {X : Scheme}

lemma section_open_image {L : X.Modules} (s : structureSheaf X ⟶ L)
    (U : X.Opens) (e : L.restrict U.ι ≅ structureSheaf U.toScheme) :
    U.ι ''ᵁ U.toScheme.basicOpen (coefficient e (restrictSection U.ι s)) =
      U ⊓ sectionOpen X s := by
  change U.ι ''ᵁ U.toScheme.basicOpen (coefficient e (restrictSection U.ι s)) =
    U ⊓ PiExponentSeshadri.SectionOpens.isoOpen s
  rw [← preimage_isoOpen s U.ι e, Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι]
  rfl

theorem local_twist_extension_ambient (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (U : X.Opens) [NoetherianSpace U.toScheme]
    (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme)
    (M : X.Modules) [M.IsQuasicoherent] (x : OpenSections M (sectionOpen X s)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ y : OpenSections ((moduleTwistFunctor L n).obj M) U,
      openRestriction ((moduleTwistFunctor L n).obj M)
        (show U ⊓ sectionOpen X s ≤ U from inf_le_left) y =
      mapSection ((moduleTwistSection L s n).app M) (U ⊓ sectionOpen X s)
        (openRestriction M inf_le_right x) := by
  let V := U.toScheme.basicOpen (coefficient e (restrictSection U.ι s))
  let W := U.ι ''ᵁ V
  have hWU : W ≤ U := U.ι_image_le V
  have hW : W = U ⊓ sectionOpen X s := section_open_image s U e
  have hWD : W ≤ sectionOpen X s := hW.le.trans inf_le_right
  let x0 : Γ(M.restrict U.ι,V) := M.presheaf.map (homOfLE hWD).op x
  obtain ⟨N, hN⟩ := local_twist_extension_section L s U e M x0
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨z, hz⟩ := hN n hn
  let P := (moduleTwistFunctor L n).obj M
  let z0 : OpenSections P (U.ι ''ᵁ ⊤) := z
  let y : OpenSections P U := openSectionsCongr P U.ι_image_top z0
  refine ⟨y, ?_⟩
  have ht := openSectionsCongr_naturality P (rfl : W = W) U.ι_image_top
    (U.ι.image_mono (show V ≤ ⊤ from le_top)) hWU z0
  have hres : openRestriction P hWU y =
      mapSection ((moduleTwistSection L s n).app M) W (openRestriction M hWD x) := by
    exact ht.symm.trans hz
  have hh := congrArg (openSectionsCongr P hW) hres
  rw [openSectionsCongr_naturality P hW rfl hWU inf_le_left, mapSection_congr] at hh
  change openRestriction P (show U ⊓ sectionOpen X s ≤ U from inf_le_left) y =
    mapSection ((moduleTwistSection L s n).app M) (U ⊓ sectionOpen X s)
      (openSectionsCongr M hW (openRestriction M hWD x)) at hh
  rw [openSectionsCongr_naturality M hW rfl hWD inf_le_right] at hh
  exact hh

theorem finite_local_twist_extensions [NoetherianSpace X] (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type*} [Fintype ι] (U : ι → X.Opens)
    (e : ∀ i, L.sheaf.restrict (U i).ι ≅ structureSheaf (U i).toScheme)
    (x : OpenSections M (sectionOpen X s)) :
    ∃ N : ℕ, ∃ y : ∀ i, OpenSections ((moduleTwistFunctor L N).obj M) (U i),
      ∀ i, openRestriction ((moduleTwistFunctor L N).obj M)
        (show U i ⊓ sectionOpen X s ≤ U i from inf_le_left) (y i) =
      mapSection ((moduleTwistSection L s N).app M) (U i ⊓ sectionOpen X s)
        (openRestriction M inf_le_right x) := by
  classical
  have H (i : ι) := by
    letI : NoetherianSpace (U i).toScheme := NoetherianSpace.set (U i : Set X)
    exact local_twist_extension_ambient L s (U i) (e i) M x
  choose N hN using H
  let m := Finset.univ.sup N
  choose y hy using fun i => hN i m (Finset.le_sup (f := N) (Finset.mem_univ i))
  exact ⟨m, y, hy⟩

lemma mapSection_twistSection_add (L : LineBundle X) (s : structureSheaf X ⟶ L.sheaf)
    (M : X.Modules) (D : X.Opens) (x : OpenSections M D) (n k : ℕ) :
    mapSection ((moduleTwistForward L s n k).app M) D
      (mapSection ((moduleTwistSection L s n).app M) D x) =
    mapSection ((moduleTwistSection L s (n+k)).app M) D x := by
  exact congrArg (fun t => mapSection (t.app M) D x) (moduleTwistSection_add L s n k).symm

theorem finite_cover_twist_gluing [NoetherianSpace X] (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type*} [Fintype ι] (U : ι → X.Opens) (hcover : (⨆ i, U i) = ⊤)
    (x : OpenSections M (sectionOpen X s)) (N : ℕ)
    (y : ∀ i, OpenSections ((moduleTwistFunctor L N).obj M) (U i))
    (hy : ∀ i, openRestriction ((moduleTwistFunctor L N).obj M)
        (show U i ⊓ sectionOpen X s ≤ U i from inf_le_left) (y i) =
      mapSection ((moduleTwistSection L s N).app M) (U i ⊓ sectionOpen X s)
        (openRestriction M inf_le_right x)) :
    ∃ K : ℕ, ∃ z : OpenSections ((moduleTwistFunctor L (N+K)).obj M) ⊤,
      openRestriction ((moduleTwistFunctor L (N+K)).obj M)
        (show sectionOpen X s ≤ ⊤ from le_top) z =
      mapSection ((moduleTwistSection L s (N+K)).app M) (sectionOpen X s) x := by
  classical
  let P := (moduleTwistFunctor L N).obj M
  let a := mapSection ((moduleTwistSection L s N).app M) (sectionOpen X s) x
  have hya (i : ι) : openRestriction P (show U i ⊓ sectionOpen X s ≤ U i from inf_le_left) (y i) =
      openRestriction P inf_le_right a :=
    (hy i).trans (mapSection_naturality ((moduleTwistSection L s N).app M) inf_le_right x)
  let diff (ij : ι × ι) := openRestriction P (show U ij.1 ⊓ U ij.2 ≤ U ij.1 from inf_le_left) (y ij.1) -
    openRestriction P (show U ij.1 ⊓ U ij.2 ≤ U ij.2 from inf_le_right) (y ij.2)
  have H (ij : ι × ι) :=
    PiExponent.TwistSectionClearing.twistForward_section_zero L s M N (U ij.1 ⊓ U ij.2)
      (diff ij) (overlap_difference_zero U (sectionOpen X s) a y hya ij.1 ij.2)
  choose K hK using H
  let k := Finset.univ.sup K
  have hcompat (i j : ι) :
      mapSection ((moduleTwistForward L s N k).app M) (U i ⊓ U j)
        (openRestriction P inf_le_left (y i)) =
      mapSection ((moduleTwistForward L s N k).app M) (U i ⊓ U j)
        (openRestriction P inf_le_right (y j)) := by
    have h := hK (i,j) k (Finset.le_sup (f := K) (Finset.mem_univ (i,j)))
    change mapSection ((moduleTwistForward L s N k).app M) (U i ⊓ U j)
      (openRestriction P inf_le_left (y i) - openRestriction P inf_le_right (y j)) = 0 at h
    rwa [map_sub, sub_eq_zero] at h
  obtain ⟨z, hz⟩ := glue_after_map ((moduleTwistForward L s N k).app M) U hcover y hcompat
  refine ⟨k, z, ?_⟩
  exact (restriction_of_glued_map ((moduleTwistForward L s N k).app M) U hcover
    (sectionOpen X s) a y hya z hz).trans (mapSection_twistSection_add L s M _ x N k)

theorem exists_global_twist_extension [NoetherianSpace X] (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (M : X.Modules) [M.IsQuasicoherent]
    (x : OpenSections M (sectionOpen X s)) :
    ∃ N : ℕ, ∃ z : OpenSections ((moduleTwistFunctor L N).obj M) ⊤,
      openRestriction ((moduleTwistFunctor L N).obj M)
        (show sectionOpen X s ≤ ⊤ from le_top) z =
      mapSection ((moduleTwistSection L s N).app M) (sectionOpen X s) x := by
  classical
  choose U hUx he using L.locallyRankOne
  obtain ⟨I, hI⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (U x : Set X)) (fun x => (U x).isOpen)
    (by intro x _; exact Set.mem_iUnion.mpr ⟨x, hUx x⟩)
  have hcover : (⨆ i : I, U i.val) = ⊤ := by
    apply le_antisymm le_top
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hI hx)
    obtain ⟨hi, hxU⟩ := Set.mem_iUnion.mp hi
    exact Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hxU⟩
  let e (i : I) := Classical.choice (he i.val)
  obtain ⟨N, y, hy⟩ := finite_local_twist_extensions L s M (fun i : I => U i.val) e x
  obtain ⟨K, z, hz⟩ := finite_cover_twist_gluing L s M (fun i : I => U i.val) hcover x N y hy
  exact ⟨N+K, z, hz⟩

theorem global_twist_extension [NoetherianSpace X] (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (M : X.Modules) [M.IsQuasicoherent]
    (x : OpenSections M (sectionOpen X s)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ z : OpenSections ((moduleTwistFunctor L n).obj M) ⊤,
      openRestriction ((moduleTwistFunctor L n).obj M)
        (show sectionOpen X s ≤ ⊤ from le_top) z =
      mapSection ((moduleTwistSection L s n).app M) (sectionOpen X s) x := by
  obtain ⟨N, z, hz⟩ := exists_global_twist_extension L s M x
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  refine ⟨mapSection ((moduleTwistForward L s N k).app M) ⊤ z, ?_⟩
  rw [← mapSection_naturality, hz]
  exact mapSection_twistSection_add L s M _ x N k

theorem global_twist_extension_native [NoetherianSpace X] (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (M : X.Modules) [M.IsQuasicoherent]
    (x : Γ(M,sectionOpen X s)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ z : Γ((moduleTwistFunctor L n).obj M,⊤),
      ((moduleTwistFunctor L n).obj M).presheaf.map
        (homOfLE (show sectionOpen X s ≤ ⊤ from le_top)).op z =
      ((moduleTwistSection L s n).app M).app (sectionOpen X s) x :=
  global_twist_extension L s M x

end
end PiExponent.TwistGlobalExtension

end OAI
