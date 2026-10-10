import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.PullbackSectionOpenExact
import OAI.AlgebraicGeometry.Seshadri.Geometry.AmpleFromCover
import OAI.AlgebraicGeometry.Seshadri.Divisors.MixedSectionOpen
import OAI.AlgebraicGeometry.Seshadri.Blowup.BlowupAffineSections

namespace OAI


                                                  
section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.SectionOpens MaximalSeshadri.Projective

variable {X : Scheme.{0}}

theorem LineBundle.eventual_twist_affine_cover [IsIntegral X] [CompactSpace X]
    (P J : LineBundle X) {κ : Type} (t : κ → (O X ⟶ P.sheaf))
    (ht : (⨆ i,isoOpen (t i)) = ⊤)
    (hlocal : ∀ i, ∃ (α : Type)
      (w : α → (O (isoOpen (t i)).toScheme ⟶ J.sheaf.restrict (isoOpen (t i)).ι)),
        (⨆ a,isoOpen (w a)) = ⊤ ∧ ∀ a, IsAffineOpen (isoOpen (w a))) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ (σ : Type) (_ : Fintype σ)
      (s : σ → (O X ⟶ ((P.pow (n+1)).tensor J).sheaf)),
        (⨆ a,isoOpen (s a)) = ⊤ ∧
        (∀ a, IsAffineOpen (isoOpen (s a))) ∧
        (∀ a, (isoOpen (s a) : Set X).Nonempty) := by
  classical
  choose α w hw hwa using hlocal
  have hex (x : X) : ∃ i, x ∈ isoOpen (t i) := by
    apply Opens.mem_iSup.mp
    rw [ht]; trivial
  choose i hi using hex
  have hex' (x : X) : ∃ a, (⟨x,hi x⟩ : (isoOpen (t (i x))).toScheme) ∈
      isoOpen (w (i x) a) := by
    apply Opens.mem_iSup.mp
    exact (hw (i x)).ge trivial
  choose a ha using hex'
  let V (x : X) : X.Opens := (isoOpen (t (i x))).ι ''ᵁ isoOpen (w (i x) (a x))
  have hxV (x : X) : x ∈ V x := ⟨⟨x,hi x⟩,ha x,rfl⟩
  obtain ⟨F,hF⟩ := isCompact_univ.elim_finite_subcover (fun x => (V x : Set X))
    (fun x => (V x).isOpen) (by intro x _; exact Set.mem_iUnion.mpr ⟨x,hxV x⟩)
  choose N hN using fun x : F => P.mixed_section_open_extension J (t (i x.val))
    ⟨x.val,hi x.val⟩ (w (i x.val) (a x.val))
  refine ⟨Finset.univ.sup N, fun n hn => ?_⟩
  choose s hs using fun x : F => hN x n ((Finset.le_sup (Finset.mem_univ x)).trans hn)
  refine ⟨F,inferInstance,s,?_,?_,?_⟩
  · apply top_unique
    intro x _
    obtain ⟨y,hy⟩ := Set.mem_iUnion.mp (hF (show x ∈ Set.univ from trivial))
    obtain ⟨hyF,hxy⟩ := Set.mem_iUnion.mp hy
    apply Opens.mem_iSup.mpr
    refine ⟨⟨y,hyF⟩,?_⟩
    rw [show isoOpen (s ⟨y,hyF⟩) = V y from hs ⟨y,hyF⟩]
    exact hxy
  · intro x
    rw [show isoOpen (s x) = V x.val from hs x]
    exact (hwa (i x.val) (a x.val)).image_of_isOpenImmersion _
  · intro x
    rw [show isoOpen (s x) = V x.val from hs x]
    exact ⟨x.val,hxV x.val⟩

variable {B : Scheme.{0}} {I : X.IdealSheafData} {π : B ⟶ X}

theorem IsBlowup.eventual_ample_exceptional_twist [IsIntegral B] [CompactSpace B]
    [CompactSpace X] (hπ : IsBlowup I π) (L : LineBundle X) (hL : L.IsAmple)
    (J : LineBundle B) (ι : J.sheaf ⟶ O B) (hJ : PresentsPullbackIdeal I π J ι) :
    ∃ a N : ℕ, 0 < a ∧ ∀ n : ℕ, N ≤ n →
      ((((L.pow a).pullback π).pow (n+1)).tensor J).IsAmple := by
  classical
  obtain ⟨a,ha,l,s,hs,hsa,-⟩ := L.ample_common_degree_cover hL
  let P := (L.pow a).pullback π
  let t (i : Fin l) : O B ⟶ P.sheaf := pullbackSection π (s i)
  have ht i : isoOpen (t i) = π ⁻¹ᵁ isoOpen (s i) := pullback_isoOpen_eq (L.pow a) (s i) π
  have hc : (⨆ i,isoOpen (t i)) = ⊤ := pullback_sections_cover s hs π
  have hloc (i : Fin l) : ∃ (α : Type)
      (w : α → (O (isoOpen (t i)).toScheme ⟶ J.sheaf.restrict (isoOpen (t i)).ι)),
        (⨆ a,isoOpen (w a)) = ⊤ ∧ ∀ a, IsAffineOpen (isoOpen (w a)) := by
    rw [ht]
    let U : X.affineOpens := ⟨isoOpen (s i),hsa i⟩
    let : IsAffine U.1.toScheme := U.2
    exact (hπ.morphismRestrict U.1).affine_section_cover (J.restrict (π ⁻¹ᵁ U.1).ι)
      (InvertibleLocal.restrictedInclusion J ι (π ⁻¹ᵁ U.1).ι)
      (presents_morphismRestrict J ι hJ U)
  obtain ⟨N,hN⟩ := P.eventual_twist_affine_cover J t hc hloc
  refine ⟨a,N,ha,fun n hn => ?_⟩
  obtain ⟨σ,hσ,q,hq,hqa,-⟩ := hN n hn
  exact ((P.pow (n+1)).tensor J).ample_of_affine_section_cover q hq hqa

end
end MaximalSeshadri.Geometry

end

end OAI
