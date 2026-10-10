import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.GeometricSectors
import OAI.GroupTheory.SimpleAmenable.RandomFields.PrimitiveCovariance

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ActualSectorControl

variable {E H Q Ω : Type*} [Group E] [Group H] [Group Q] [Group.IsPerfect E]

namespace ActualLawfulTable
variable {q : H →* Q} {v : (Ω → E) →* Q} (T : ActualLawfulTable q v)

theorem sector_control {U V : Set Ω} (hUV : U ⊆ V) :
    SameActionOn (T.sector V) (T.sector Set.univ) (T.sector U).range := by
  classical
  intro s x hx
  obtain ⟨t,rfl⟩ := hx
  have hd : Disjoint V Vᶜ := disjoint_compl_right_iff.mpr le_rfl
  have he := DFunLike.congr_fun (T.sector_union hd) s
  rw [Set.union_compl_self] at he
  rw [he]
  change _ = (T.sector V s*T.sector Vᶜ s) * _ * (T.sector V s*T.sector Vᶜ s)⁻¹
  exact (conj_mul_of_commute _ _ _
    (T.sector_commute (disjoint_compl_left_iff.mpr hUV) s t)).symm

end ActualLawfulTable

variable {a : ℕ} {ι : Type*}

theorem resolvedPolygonMask_univ (U : ι → polygonAlgebra a) :
    resolvedPolygonMask U Set.univ = Set.univ := by
  ext ω
  simp only [resolvedPolygonMask,Set.mem_ofPred_eq,Set.mem_univ,iff_true,and_true]
  exact ω.property

namespace InitialCoverSystem
variable {m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) [Finite ι]

theorem geometricSector_whole (I : Finset (Fin (m+1)))
    [Group.IsPerfect (alternatingGroup I)]
    (b : Fin (m+1)) (hb : b ∉ I) (P : ι → Fin 5 × (CutRing × CutRing))
    (h : B.PrimitiveFamilyLaw I b hb P) :
    B.geometricSector I b hb P h (wholePolygon a) =
      (B.initialAlphabet I 0).comp (universalProjection (alternatingGroup I)) := by
  apply CentralOn.lift_unique (coverMap M (alternatingGenerator a r m hm))
    (copyFamilyEval (B.primitiveFamily I b hb P)).range h
  · rintro x ⟨s,rfl⟩
    exact B.geometricSector_mem I b hb P h _ s
  · rintro x ⟨s,rfl⟩
    rw [copyFamilyEval_range]
    exact (le_iSup (fun z => (B.primitiveFamily I b hb P z).range) none)
      ⟨universalProjection (alternatingGroup I) s,rfl⟩
  · rw [B.geometricSector_projection I b hb P h _
      (show ResolvedBy _ (wholePolygon a).val from fun x y he => Iff.rfl)]
    rw [← MonoidHom.comp_assoc]
    congr 1
    rw [initialAlphabet,← MonoidHom.comp_assoc,B.initialConditional_projection]
    rfl

theorem geometricSector_control (I : Finset (Fin (m+1)))
    [Group.IsPerfect (alternatingGroup I)]
    (b : Fin (m+1)) (hb : b ∉ I) (P : ι → Fin 5 × (CutRing × CutRing))
    (h : B.PrimitiveFamilyLaw I b hb P) (V W : polygonAlgebra a) (hVW : V ≤ W) :
    SameActionOn (B.geometricSector I b hb P h W)
      ((B.initialAlphabet I 0).comp (universalProjection (alternatingGroup I)))
      (B.geometricSector I b hb P h V).range := by
  rw [← B.geometricSector_whole I b hb P h]
  unfold geometricSector
  change SameActionOn _ ((B.primitiveTable I b hb P h).sector
    (resolvedPolygonMask (primitiveTests (a := a) (r := r) P) Set.univ)) _
  rw [resolvedPolygonMask_univ]
  exact (B.primitiveTable I b hb P h).sector_control (resolvedPolygonMask_mono _ hVW)

theorem geometricSector_input (I : Finset (Fin (m+1)))
    [Group.IsPerfect (alternatingGroup I)]
    (b : Fin (m+1)) (hb : b ∉ I) (P : ι → Fin 5 × (CutRing × CutRing))
    (h : B.PrimitiveFamilyLaw I b hb P) (i : ι) :
    B.geometricSector I b hb P h (primitiveTests (a := a) (r := r) P i) =
      (B.primitiveCopy I b hb (P i)).comp (universalProjection (alternatingGroup I)) := by
  apply CentralOn.lift_unique (coverMap M (alternatingGenerator a r m hm))
    (copyFamilyEval (B.primitiveFamily I b hb P)).range h
  · rintro x ⟨s,rfl⟩
    exact B.geometricSector_mem I b hb P h _ s
  · rintro x ⟨s,rfl⟩
    rw [copyFamilyEval_range]
    exact (le_iSup (fun z => (B.primitiveFamily I b hb P z).range) (some i))
      ⟨universalProjection (alternatingGroup I) s,rfl⟩
  · rw [B.geometricSector_projection I b hb P h _ (resolved_test _ i)]
    rw [← MonoidHom.comp_assoc,B.primitiveCopy_projection]
    rfl

end InitialCoverSystem
end ActualSectorControl

section AlphabetInclusion

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem subtypeAlternatingHom_mem_range (I : Finset α) (s : alternatingGroup α) :
    s ∈ (subtypeAlternatingHom I).range ↔ s.val.support ⊆ I := by
  constructor
  · rintro ⟨t,rfl⟩
    exact Equiv.Perm.mem_range_ofSubtype_iff.mp ⟨t.val,rfl⟩
  · intro hs
    obtain ⟨t,ht⟩ := Equiv.Perm.mem_range_ofSubtype_iff.mpr hs
    have hat : t ∈ alternatingGroup I := by
      rw [Equiv.Perm.mem_alternatingGroup,← Equiv.Perm.sign_ofSubtype,ht]
      exact s.property
    exact ⟨⟨t,hat⟩,Subtype.ext ht⟩

noncomputable def subalphabetHom {I J : Finset α} (hIJ : I ⊆ J) :
    alternatingGroup I →* alternatingGroup J :=
  (MonoidHom.ofInjective (subtypeAlternatingHom_injective J)).symm.toMonoidHom.comp
    ((subtypeAlternatingHom I).codRestrict (subtypeAlternatingHom J).range
      (fun s => (subtypeAlternatingHom_mem_range J _).mpr
        ((subtypeAlternatingHom_mem_range I _).mp ⟨s,rfl⟩ |>.trans hIJ)))

@[simp] theorem subtypeAlternatingHom_comp {I J : Finset α} (hIJ : I ⊆ J) :
    (subtypeAlternatingHom J).comp (subalphabetHom hIJ) = subtypeAlternatingHom I := by
  apply MonoidHom.ext
  intro s
  exact MonoidHom.apply_ofInjective_symm (subtypeAlternatingHom_injective J) _

namespace CommonFrame
variable {a m : ℕ} {r : CutRing} {hm : 2 ≤ m}
    {I J : Finset (Fin (m+1))} {u : CutRing × CutRing}

noncomputable def restrict (F : CommonFrame a r m hm J u) (hIJ : I ⊆ J) :
    CommonFrame a r m hm I u where
  k := F.k
  d := F.d
  projection := F.projection
  common := fun i hi => F.common i (hIJ hi)

end CommonFrame

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)

theorem initialAlphabet_inclusion {I J : Finset (Fin (m+1))} (hIJ : I ⊆ J) (j : Fin 5) :
    (B.initialAlphabet J j).comp (subalphabetHom hIJ) = B.initialAlphabet I j := by
  rw [initialAlphabet,MonoidHom.comp_assoc,subtypeAlternatingHom_comp]
  rfl

theorem primitiveCopy_inclusion {I J : Finset (Fin (m+1))} (hIJ : I ⊆ J)
    (b c : Fin (m+1)) (hb : b ∉ I) (hc : c ∉ J) (p : Fin 5 × (CutRing × CutRing)) :
    (B.primitiveCopy J c hc p).comp (subalphabetHom hIJ) = B.primitiveCopy I b hb p := by
  let F := commonFrame a r m hm J c hc p.2
  rw [B.primitiveCopy_frame J c hc p F,B.primitiveCopy_frame I b hb p (F.restrict hIJ)]
  change ((MulAut.conj (B.t F.k)).toMonoidHom.comp (B.initialAlphabet J p.1)).comp _ =
    (MulAut.conj (B.t F.k)).toMonoidHom.comp (B.initialAlphabet I p.1)
  rw [MonoidHom.comp_assoc,B.initialAlphabet_inclusion hIJ]

theorem primitiveFamily_inclusion {ι : Type*} {I J : Finset (Fin (m+1))} (hIJ : I ⊆ J)
    (b c : Fin (m+1)) (hb : b ∉ I) (hc : c ∉ J)
    (P : ι → Fin 5 × (CutRing × CutRing)) (i : Option ι) :
    (B.primitiveFamily J c hc P i).comp (subalphabetHom hIJ) = B.primitiveFamily I b hb P i := by
  cases i with
  | none => exact B.initialAlphabet_inclusion hIJ 0
  | some i => exact B.primitiveCopy_inclusion hIJ b c hb hc (P i)

theorem primitiveFamily_range_inclusion {ι : Type*} {I J : Finset (Fin (m+1))} (hIJ : I ⊆ J)
    (b c : Fin (m+1)) (hb : b ∉ I) (hc : c ∉ J)
    (P : ι → Fin 5 × (CutRing × CutRing)) :
    (copyFamilyEval (B.primitiveFamily I b hb P)).range ≤
      (copyFamilyEval (B.primitiveFamily J c hc P)).range := by
  rw [copyFamilyEval_range,copyFamilyEval_range]
  apply iSup_le
  intro i x hx
  obtain ⟨s,rfl⟩ := hx
  apply le_iSup (fun z => (B.primitiveFamily J c hc P z).range) i
  exact ⟨subalphabetHom hIJ s,DFunLike.congr_fun (B.primitiveFamily_inclusion hIJ b c hb hc P i) s⟩

theorem geometricSector_inclusion {ι : Type*} [Finite ι]
    {I J : Finset (Fin (m+1))} [Group.IsPerfect (alternatingGroup I)]
    [Group.IsPerfect (alternatingGroup J)] (hIJ : I ⊆ J)
    (b c : Fin (m+1)) (hb : b ∉ I) (hc : c ∉ J)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : B.PrimitiveFamilyLaw I b hb P) (g : B.PrimitiveFamilyLaw J c hc P)
    (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) V.val) :
    (B.geometricSector J c hc P g V).comp (universalMap (subalphabetHom hIJ)) =
      B.geometricSector I b hb P h V := by
  apply CentralOn.lift_unique (coverMap M (alternatingGenerator a r m hm))
    (copyFamilyEval (B.primitiveFamily J c hc P)).range g
  · rintro x ⟨s,rfl⟩
    exact B.geometricSector_mem J c hc P g V _
  · rintro x ⟨s,rfl⟩
    exact B.primitiveFamily_range_inclusion hIJ b c hb hc P
      (B.geometricSector_mem I b hb P h V s)
  · rw [← MonoidHom.comp_assoc,B.geometricSector_projection J c hc P g V hV,
      B.geometricSector_projection I b hb P h V hV,MonoidHom.comp_assoc,universalMap_spec]
    rw [← MonoidHom.comp_assoc]
    congr 1
    rw [MonoidHom.comp_assoc,subtypeAlternatingHom_comp]

end InitialCoverSystem
end AlphabetInclusion

end SimpleAmenable
end
end

end OAI
