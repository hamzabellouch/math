import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.ControlledPatching
import OAI.GroupTheory.SimpleAmenable.CentralCovers.SmallFormalGlobal
import OAI.GroupTheory.SimpleAmenable.CentralCovers.SmallStarRelators
import OAI.GroupTheory.SimpleAmenable.CentralCovers.PrimitiveFormalSectors

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FormalGridPieces
variable {α H ι D : Type*} [Fintype α] [DecidableEq α] [Group H]
    [Group.IsPerfect (alternatingGroup α)] {κ : ι → Type*}
    (F : (i : ι) → Option (κ i) → TrackStar α →* H)
    (T : ∀ i, FormalStarTable (F i)) (U : (i : ι) → Set (κ i → Bool))
    (C : (i : ι) → D → Set (κ i → Bool))

noncomputable def formalGridInput (i : ι) : TrackStar α →* H := (T i).sector (U i)
noncomputable def formalGridPiece (d : D) (i : ι) : TrackStar α →* H :=
  (T i).sector (U i ∩ C i d)

theorem formalGridInput_split (d : D) (i : ι) (s : TrackStar α) :
    formalGridInput F T U i s=formalGridPiece F T U C d i s*
      formalGridPiece F T U (fun i d => (C i d)ᶜ) d i s := by
  have hd : Disjoint (U i ∩ C i d) (U i ∩ (C i d)ᶜ) := by
    apply Set.disjoint_left.mpr
    intro σ hs ht
    exact ht.2 hs.2
  have he : (U i ∩ C i d) ∪ (U i ∩ (C i d)ᶜ)=U i := by
    ext σ
    simp only [Set.mem_union,Set.mem_inter_iff,Set.mem_compl_iff]
    tauto
  exact (congrArg (fun V => (T i).sector V s) he).symm.trans ((T i).sector_union hd s)

theorem formalGridPiece_supported [∀ i, Finite (κ i)] (L : Finset α → Subgroup H)
    (hF : ∀ i j, SmallSupported L (F i j)) (d : D) (i : ι) :
    SmallSupported L (formalGridPiece F T U C d i) :=
  (T i).sector_supported L (hF i) _

theorem formalGridPiece_control (c : alternatingGroup α →* H)
    (hc : ∀ i, F i none=c.comp (universalProjection _))
    (j : D → TrackStar α →* H) (hj : ∀ i d, (T i).sector (C i d)=j d) (d : D) (i : ι) :
    SmallControlled c (formalGridPiece F T U C d i) (j d) := by
  have hh := (T i).sector_control (show U i ∩ C i d ⊆ C i d from Set.inter_subset_right)
  rw [hj,hc] at hh
  intro I s x hx
  exact hh (universalMap (subtypeAlternatingHom I.val) s) x hx

theorem formalGridPieces_generate [Fintype D]
    (hd : ∀ i, Pairwise fun d e => Disjoint (C i d) (C i e))
    (hcover : ∀ i σ, ∃ d, σ ∈ C i d) :
    (⨆ i, (formalGridInput F T U i).range : Subgroup H) ≤
      ⨆ d, ⨆ i, (formalGridPiece F T U C d i).range := by
  apply iSup_le
  intro i
  have hh := (T i).sector_range_le_partition (fun d => U i ∩ C i d) (U i)
    (fun d e hde => (hd i hde).mono Set.inter_subset_right Set.inter_subset_right)
    (fun σ => by
      constructor
      · intro hσ
        obtain ⟨d,hd⟩ := hcover i σ
        exact ⟨d,hσ,hd⟩
      · rintro ⟨d,hd⟩
        exact hd.1)
  exact hh.trans (iSup_mono fun d => le_iSup (fun i => (formalGridPiece F T U C d i).range) i)

theorem formalGridInputs_normalize [∀ i, Finite (κ i)]
    (L : Finset α → Subgroup H) (c : alternatingGroup α →* H)
    (h20 : 20 ≤ Fintype.card α)
    (hconj : ∀ σ I, ∀ x ∈ L I, c σ*x*(c σ)⁻¹ ∈ L (I.map σ.val.toEmbedding))
    (hdis : ∀ I J, Disjoint I J → ∀ x ∈ L I, ∀ y ∈ L J, Commute x y)
    (hF : ∀ i j, SmallSupported L (F i j))
    (hc : ∀ i, F i none=c.comp (universalProjection _))
    (j k : D → TrackStar α →* H)
    (hj : ∀ i d, (T i).sector (C i d)=j d)
    (hk : ∀ i d, (T i).sector (C i d)ᶜ=k d)
    (hjs : ∀ d, SmallSupported L (j d))
    (hcomm : ∀ d s t, Commute (j d s) (k d t)) :
    ∀ d i s, formalGridInput F T U i s ∈
      Subgroup.normalizer ((⨆ i, (formalGridPiece F T U C d i).range : Subgroup H) : Set H) := by
  intro d
  apply controlled_cell_normalizes L c hconj hdis h20
    (formalGridInput F T U) (formalGridPiece F T U C d)
    (formalGridPiece F T U (fun i d => (C i d)ᶜ) d) (j d) (k d)
  · exact formalGridPiece_supported F T U C L hF d
  · exact formalGridPiece_supported F T U (fun i d => (C i d)ᶜ) L hF d
  · exact hjs d
  · exact formalGridPiece_control F T U C c hc j hj d
  · exact formalGridPiece_control F T U (fun i d => (C i d)ᶜ) c hc k hk d
  · exact hcomm d
  · exact formalGridInput_split F T U C d

end FormalGridPieces

section PrimitiveRectangleMasks
namespace InitialCoverSystem.PatchAtlas
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    {B : InitialCoverSystem a r m hm M}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))] (A : B.PatchAtlas)
    {ι κ D : Type*} [Finite ι] [Finite κ] [Nonempty D]

theorem formalRectangleMasks (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing)) (T : FormalStarTable (A.starFamily hlarge P))
    (v : κ → ι)
    (h : ∀ I, I.card≤15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb (P ∘ v))
    (W : D → polygonAlgebra a)
    (hW : ∀ d, ResolvedBy (fun i => (primitiveTests (a := a) (r := r) (P ∘ v) i).val) (W d).val)
    (hcover : ∀ x, ∃ d, x ∈ (W d).val)
    (hd : Pairwise fun d e => Disjoint (W d).val (W e).val) :
    ∃ C : D → Set (ι → Bool),
      (Pairwise fun d e => Disjoint (C d) (C e)) ∧
      (∀ σ, ∃ d, σ ∈ C d) ∧
      (∀ d, T.sector (C d)=B.fullGeometricSector hlarge (P ∘ v) h (W d)) ∧
      (∀ d, T.sector (C d)ᶜ=B.fullGeometricSector hlarge (P ∘ v) h (W d)ᶜ) ∧
      (∀ x d, polygonAssignment (primitiveTests (a := a) (r := r) P) x ∈ C d ↔ x ∈ (W d).val) := by
  obtain ⟨χ,hχ⟩ := resolvedPartitionSelector (primitiveTests (a := a) (r := r) (P ∘ v)) W hW hcover hd
  let C (d : D) : Set (ι → Bool) := {σ | χ (σ ∘ v)=d}
  refine ⟨C,?_,?_,?_,?_,?_⟩
  · intro d e hde
    apply Set.disjoint_left.mpr
    intro σ hd he
    exact hde (hd.symm.trans he)
  · intro σ
    exact ⟨χ (σ ∘ v),rfl⟩
  · intro d
    exact A.formalSector_subfamily_eq hlarge P T v h {σ | χ σ=d} (W d) (hW d)
      (fun x => hχ x d)
  · intro d
    exact A.formalSector_subfamily_eq hlarge P T v h {σ | χ σ≠d} (W d)ᶜ
      (fun x y he => not_congr (hW d x y he)) (fun x => not_congr (hχ x d))
  · intro x d
    exact hχ x d

end InitialCoverSystem.PatchAtlas
end PrimitiveRectangleMasks

section SupportedAssignmentPatching
variable {α ι D H Ω : Type*} [Fintype α] [DecidableEq α] [Finite ι] [Finite Ω] [Group H]
    [Group.IsPerfect (alternatingGroup α)]

theorem supported_assignment_patching
    (U : ι → Set Ω) (hsep : ∀ ω ν, (∀ i, ω ∈ U i ↔ ν ∈ U i) → ω=ν)
    (F : Option ι → TrackStar α →* H)
    (f : (I : FiveAlphabet α) → Option ι → alternatingGroup I.val →* H)
    (hspec : ∀ I i, (F i).comp (universalMap (subtypeAlternatingHom I.val))=
      (f I i).comp (universalProjection (alternatingGroup I.val)))
    (P : D → Subgroup H)
    (hgen : (copyFamilyEval F).range ≤ ⨆ d, P d)
    (hinv : ∀ d i s, F i s ∈ Subgroup.normalizer (P d : Set H))
    (G : D → Option ι → TrackStar α →* H)
    (hact : ∀ d (I : FiveAlphabet α) i s,
      ∀ x ∈ P d,
        F i (universalMap (subtypeAlternatingHom I.val) s)*x*
          (F i (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
        G d i (universalMap (subtypeAlternatingHom I.val) s)*x*
          (G d i (universalMap (subtypeAlternatingHom I.val) s))⁻¹)
    (hlocal : ∀ d (S : Finset α), S.card ≤ 15 → ∀ w ∈ smallFamilyLocal (ι := ι) S,
      smallFamilyModel U w=1 →
      ∀ x ∈ P d, Commute (copyFamilyEval (G d) (smallFamilyStarWord w)) x)
    (hα : 5 ≤ Fintype.card α) :
    HasCentralLaw (smallFamilyModel U)
      (smallFamilyEval f).rangeRestrict := by
  classical
  let f₀ : SmallFamilyLabel α ι → H := fun l => f l.1 l.2.1 l.2.2
  have hfs (I : FiveAlphabet α) (i : Option ι) (s : alternatingGroup I.val) :
      f I i s=F i (alphabetStarLift I s) := by
    have hh := DFunLike.congr_fun (hspec I i)
      (Classical.choose (universalProjection_surjective (alternatingGroup I.val) s))
    simpa only [MonoidHom.comp_apply,alphabetStarLift,
      Classical.choose_spec (universalProjection_surjective (alternatingGroup I.val) s)] using hh.symm
  have hgen' : (FreeGroup.lift f₀).range ≤ ⨆ d, P d := by
    rintro x ⟨w,rfl⟩
    apply hgen
    refine ⟨smallFamilyStarWord w,?_⟩
    exact DFunLike.congr_fun (smallFamilyStarWord_eval F f hspec) w
  apply smallFamily_assignment_law U hsep f ?_ hα
  intro S hS w hw hrel v _hv
  have hc := patching_centrality f₀ P hgen' (fun d l => by
    rw [show f₀ l=F l.2.1 (alphabetStarLift l.1 l.2.2) from hfs _ _ _]
    exact hinv _ _ _) w ?_
  · exact hc _ ⟨v,rfl⟩
  · intro d
    let g : SmallFamilyLabel α ι → H := fun l => G d l.2.1 (alphabetStarLift l.1 l.2.2)
    have hg : (FreeGroup.lift g)=(copyFamilyEval (G d)).comp smallFamilyStarWord := by
      apply FreeGroup.ext_hom
      rintro ⟨I,i,s⟩
      simp [g,smallFamilyStarWord]
    refine ⟨g,?_,?_⟩
    · intro l x hx
      rw [show f₀ l=F l.2.1 (alphabetStarLift l.1 l.2.2) from hfs _ _ _]
      exact hact d l.1 l.2.1 _ x hx
    · rw [hg]
      intro x hx
      exact (hlocal d S hS w hw hrel x hx).eq.symm

end SupportedAssignmentPatching

end SimpleAmenable
end
end

end OAI
