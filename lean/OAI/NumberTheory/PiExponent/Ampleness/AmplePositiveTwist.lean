import OAI.NumberTheory.PiExponent.Ampleness.AmpleFromCover
import OAI.NumberTheory.PiExponent.Approximation.FrameSubopens
import OAI.NumberTheory.PiExponent.Approximation.MixedFrameExtension

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Frames PiExponentSeshadri.TensorPure PiExponentSeshadri.Projective
variable {X : Scheme.{0}}

theorem LineBundle.ample_framed_cover [CompactSpace X] (L M : LineBundle X)
    (hL : L.IsAmple) (a : ℕ) (ha : 0 < a) :
    ∃ d : ℕ, 0 < d ∧ a ∣ d ∧ ∃ ι : Type, ∃ _ : Fintype ι,
      ∃ s : ι → GlobalSections X (L.pow d).sheaf,
        (⨆ i, sectionOpen X (s i)) = ⊤ ∧
        (∀ i, IsAffineOpen (sectionOpen X (s i))) ∧
        (∀ i, (sectionOpen X (s i) : Set X).Nonempty) ∧
        (∀ i, Nonempty (M.sheaf.restrict (sectionOpen X (s i)).ι ≅ O (sectionOpen X (s i)).toScheme)) := by
  classical
  choose V hV e using M.locallyRankOne
  have hh (x : X) := hL x (V x) (hV x)
  choose d hd s hs hsub haff using hh
  obtain ⟨I,hI⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (sectionOpen X (s x) : Set X)) (fun x => (sectionOpen X (s x)).isOpen)
    (by intro x _; exact Set.mem_iUnion.mpr ⟨x,hs x⟩)
  obtain ⟨n,hn,t,ht⟩ := L.common_degree (fun i : I => d i.val)
    (fun i => hd i.val) (fun i => s i.val)
  let f := linePowerMul L n a
  let q (i : I) : GlobalSections X (L.pow (n*a)).sheaf :=
    powerSection (t i) a ≫ f.hom
  have hq (i : I) : sectionOpen X (q i) = sectionOpen X (s i.val) := by
    change SectionOpens.isoOpen (powerSection (t i) a ≫ f.hom) = _
    erw [SectionOpens.isoOpen_postcomp]
    exact ((L.pow n).sectionOpen_power (t i) ha).trans (ht i)
  refine ⟨n*a,Nat.mul_pos hn ha,dvd_mul_left a n,I,inferInstance,q,?_,?_,?_,?_⟩
  · apply top_unique
    intro x _
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hI (show x ∈ Set.univ from trivial))
    obtain ⟨hi,hx⟩ := Set.mem_iUnion.mp hi
    refine Opens.mem_iSup.mpr ⟨⟨i,hi⟩,?_⟩
    rw [hq]
    exact hx
  · intro i
    rw [hq]
    exact haff i.val
  · intro i
    rw [hq]
    exact ⟨i.val,hs i.val⟩
  · intro i
    exact ⟨Frames.restrictOpenFrame ((hq i).le.trans (hsub i.val)) (Classical.choice (e i.val))⟩

theorem LineBundle.exists_ample_twist [IsIntegral X] [CompactSpace X]
    (L M : LineBundle X) (hL : L.IsAmple) :
    ∃ d : ℕ, 0 < d ∧ ((L.pow d).tensor M).IsAmple := by
  classical
  obtain ⟨a,ha,-,ι,hi,s,hs,hsa,hsn,he⟩ := L.ample_framed_cover M hL 1 (by decide)
  choose N hN using fun i => (L.pow a).mixed_frame_extension M (s i) (hsn i)
    (Classical.choice (he i))
  let n := Finset.univ.sup N
  choose t ht hval using fun i => hN i n (Finset.le_sup (Finset.mem_univ i))
  let e := moduleTensorIso (linePowerMul L a (n+1)) (Iso.refl M.sheaf)
  let q (i : ι) : GlobalSections X ((L.pow (a*(n+1))).tensor M).sheaf :=
    t i ≫ e.hom
  have hq (i : ι) : sectionOpen X (q i) = sectionOpen X (s i) := by
    change SectionOpens.isoOpen (t i ≫ e.hom) = _
    erw [SectionOpens.isoOpen_postcomp]
    exact ht i
  refine ⟨a*(n+1),Nat.mul_pos ha (by omega),
    ((L.pow (a*(n+1))).tensor M).ample_of_affine_section_cover q ?_ ?_⟩
  · simpa only [hq] using hs
  · intro i
    rw [hq]
    exact hsa i

end
end PiExponentSeshadri.Geometry

end OAI
