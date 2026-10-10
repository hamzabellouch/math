import OAI.NumberTheory.PiExponent.Ampleness.AmpleFromCover
import OAI.NumberTheory.PiExponent.Approximation.MixedSectionOpenExtension

namespace OAI


namespace PiExponentSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Frames PiExponentSeshadri.SectionOpens PiExponentSeshadri.Projective
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
    erw [hw]; trivial
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

end
end PiExponentSeshadri.Geometry

end OAI
