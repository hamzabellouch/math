import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.PairLawAssembly
import OAI.GroupTheory.SimpleAmenable.CentralCovers.GrowthAnchorLaw
import OAI.GroupTheory.SimpleAmenable.CentralCovers.GrowthGeneration

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section GrowthAxisUniform
namespace InitialCoverSystem
variable {a m : ℕ} {r : CutRing} {hm : 2 ≤ m}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem growth_axis_law (hlarge : 20 ≤ m+1)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (s w z : CutRing) (hs : 0 < ordinary s) (hsr : ordinary s < ordinary r/2)
    (hwz : w*z=1)
    (hshort : (1+|ordinary (cutTau^a)|)*(|ordinary w|+|ordinary (cutTau*w)|) < ordinary s/4)
    {C : ℝ} (hC : 1000 ≤ C) (hSlope : 8*C < ordinary (cutTau^a))
    (hconj : |conjugate (cutTau^a)| < 1/1000) :
    ∃ N : ℕ, 1005 ≤ N ∧ ∀ (M : ℕ) (B : InitialCoverSystem a r m hm M)
      (_h : B.TangentChartLaws (symmetricWindowLength s) (symmetricWindowStart s) w),
      ∀ n : ℕ, N ≤ n → B.CoordinateWindowLaw n →
      ∀ (d : Fin 2) (p : ℤ) (I : Finset (Fin (m+1))) (b : Fin (m+1)) (hb : b ∉ I),
        B.PrimitiveFamilyLaw I b hb (axisWindowPrimitives d (growthNewLength n) p) := by
  obtain ⟨N,hN,h⟩ := growth_anchor_law (a := a) (hm := hm) hlarge hr s w z hs hsr hwz hshort hC hSlope hconj
  refine ⟨N,hN,?_⟩
  intro M B hB n hn g d p I b hb
  exact B.growth_axis_law_of_anchor (by omega) n (by omega) g d p
    (h M B hB n hn g d p) I b hb

end InitialCoverSystem
end GrowthAxisUniform

section SplitAssignment
variable {E S G ι κ : Type*} [Group E] [Group S] [Group G]

theorem iSup_ranges_commute (f : ι → E →* G) (g : κ → S →* G)
    (h : ∀ i j s t, Commute (f i s) (g j t)) :
    ∀ x ∈ ⨆ i, (f i).range, ∀ y ∈ ⨆ j, (g j).range, Commute x y := by
  intro x hx
  let C := Subgroup.centralizer ((⨆ j, (g j).range : Subgroup G) : Set G)
  have hf : (⨆ i, (f i).range : Subgroup G) ≤ C := by
    apply iSup_le
    intro i z hz
    obtain ⟨s,rfl⟩ := hz
    have hg : (⨆ j, (g j).range : Subgroup G) ≤ Subgroup.centralizer ({f i s} : Set G) := by
      apply iSup_le
      rintro j y ⟨t,rfl⟩ z hz
      obtain rfl := Set.mem_singleton_iff.mp hz
      exact (h i j s t).eq
    intro y hy
    exact (hg hy _ (Set.mem_singleton _)).symm
  intro y hy
  exact (show Commute y x from hf hx y hy).symm

def splitFactorProduct (A B : Subgroup G)
    (h : ∀ x ∈ A, ∀ y ∈ B, Commute x y) : A × B →* G where
  toFun x := x.1.1*x.2.1
  map_one' := one_mul _
  map_mul' x y := by
    change (x.1.1*y.1.1)*(x.2.1*y.2.1) = (x.1.1*x.2.1)*(y.1.1*y.2.1)
    calc
      _ = x.1.1*(y.1.1*x.2.1)*y.2.1 := by group
      _ = x.1.1*(x.2.1*y.1.1)*y.2.1 := by rw [(h _ y.1.2 _ x.2.2).eq]
      _ = _ := by group

theorem commutingFactors_of_generate (F L R : ι → E →* G)
    (hgen : (⨆ i, (F i).range : Subgroup G) = ⊤)
    (hsplit : ∀ i s, F i s = L i s*R i s)
    (hcomm : ∀ i j s t, Commute (L i s) (R j t)) :
    CommutingFactors (⨆ i, (L i).range) (⨆ i, (R i).range) := by
  have hLR := iSup_ranges_commute L R hcomm
  let p := splitFactorProduct (⨆ i, (L i).range) (⨆ i, (R i).range) hLR
  have hp : p.range = ⊤ := by
    apply top_unique
    rw [← hgen]
    apply iSup_le
    rintro i x ⟨s,rfl⟩
    exact ⟨(⟨L i s,le_iSup (fun i => (L i).range) i ⟨s,rfl⟩⟩,
      ⟨R i s,le_iSup (fun i => (R i).range) i ⟨s,rfl⟩⟩),(hsplit i s).symm⟩
  refine ⟨hLR,?_⟩
  intro x
  obtain ⟨⟨u,v⟩,huv⟩ := MonoidHom.range_eq_top.mp hp x
  exact ⟨u,u.property,v,v.property,huv.symm⟩

theorem star_split_assignment [Fintype ι] [Group.IsPerfect G]
    (π : E →* S) (_hπ : Function.Surjective π) (c : S →* G)
    (F : Option ι → E →* G) (hc : F none = c.comp π)
    (hgen : (⨆ i, (F i).range : Subgroup G) = ⊤)
    (L R : ι → Option ι → E →* G)
    (hsplit : ∀ i j s, F j s = L i j s*R i j s)
    (hcomm : ∀ i j k s t, Commute (L i j s) (R i k t))
    (hleft : ∀ i, L i none = F (some i)) :
    ∃ φ : ((ι → Bool) → S) →* (G ⧸ Subgroup.center G),
      Function.Surjective φ ∧
      φ.comp (sectorMask Set.univ) = (QuotientGroup.mk' _).comp c ∧
      ∀ i, (φ.comp (sectorMask {σ | σ i = true})).comp π =
        (QuotientGroup.mk' _).comp (F (some i)) := by
  let q : G →* G ⧸ Subgroup.center G := QuotientGroup.mk' _
  let F' := fun i => q.comp (F i)
  let L' := fun i j => q.comp (L i j)
  let R' := fun i j => q.comp (R i j)
  have hgen' : (⨆ i, (F' i).range : Subgroup (G ⧸ Subgroup.center G)) = ⊤ := by
    simp only [F',MonoidHom.range_comp]
    rw [← Subgroup.map_iSup,hgen,← MonoidHom.range_eq_map,MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
  have hs' i j s : F' j s = L' i j s*R' i j s := by
    dsimp [F',L',R']; rw [hsplit,map_mul]
  have hm' i j k s t : Commute (L' i j s) (R' i k t) := (hcomm i j k s t).map q
  let A := fun i => ⨆ j, (L' i j).range
  let B := fun i => ⨆ j, (R' i j).range
  have hAB i : CommutingFactors (A i) (B i) :=
    commutingFactors_of_generate F' (L' i) (R' i) hgen' (hs' i) (hm' i)
  have hz : Subgroup.center (G ⧸ Subgroup.center G) = ⊥ := perfect_center_quotient
  let g := fun i => ((hAB i).projectLeft hz).comp (q.comp c)
  have hg i : (g i).comp π = F' (some i) := by
    ext s
    change (hAB i).projectLeft hz (q (c (π s))) = q (F (some i) s)
    rw [← show F none s = c (π s) from DFunLike.congr_fun hc s]
    change (hAB i).projectLeft hz (F' none s) = F' (some i) s
    rw [hs' i none s,(hAB i).projectLeft_factors hz
      (le_iSup (fun j => (L' i j).range) none ⟨s,rfl⟩)
      (le_iSup (fun j => (R' i j).range) none ⟨s,rfl⟩)]
    exact congrArg (fun f : E →* G => q (f s)) (hleft i)
  have hggen : (q.comp c).range ⊔ ⨆ i, (g i).range = ⊤ := by
    apply top_unique
    rw [← hgen']
    apply iSup_le
    intro i
    cases i with
    | none =>
      have h : F' none = (q.comp c).comp π := by dsimp [F']; rw [hc,MonoidHom.comp_assoc]
      rw [h]
      exact (range_comp_subset _ _).trans le_sup_left
    | some i =>
      rw [← hg i]
      exact (range_comp_subset _ _).trans ((le_iSup (fun i => (g i).range) i).trans le_sup_right)
  obtain ⟨φ,hφ,hφc,hφg⟩ := simultaneous_assignment_surjection A B hAB hz (q.comp c) g (fun _ => rfl) hggen
  exact ⟨φ,hφ,hφc,fun i => by rw [hφg]; exact hg i⟩

end SplitAssignment

section PairSectors
noncomputable def primitivePair {ι : Type*}
    (P : ι → Fin 5 × (CutRing × CutRing)) (i j : ι) : Bool → Fin 5 × (CutRing × CutRing) :=
  fun b => if b then P j else P i

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι κ : Type*} [Finite ι] [Finite κ]

omit [Finite ι] [Finite κ] in

theorem smallPrimitive_range_reindex (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing)) (v : κ → ι) :
    (smallFamilyEval (B.smallPrimitiveInputs hlarge (P ∘ v))).range ≤
      (smallFamilyEval (B.smallPrimitiveInputs hlarge P)).range := by
  rw [smallFamilyEval_range,smallFamilyEval_range]
  apply iSup_le
  intro I
  apply iSup_le
  intro j
  have he : B.smallPrimitiveInputs hlarge (P ∘ v) I j =
      B.smallPrimitiveInputs hlarge P I (j.map v) := by cases j <;> rfl
  rw [he]
  exact (le_iSup (fun j => (B.smallPrimitiveInputs hlarge P I j).range) (j.map v)).trans
    (le_iSup (fun I => ⨆ j, (B.smallPrimitiveInputs hlarge P I j).range) I)

variable [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ i j I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb (primitivePair P i j))

noncomputable def pairStar : Option ι → TrackStar (Fin (m+1)) →*
    BoundedRelationCover M (alternatingGenerator a r m hm)
  | none => B.c.comp (universalProjection (alternatingGroup (Fin (m+1))))
  | some i => B.fullGeometricSector hlarge (primitivePair P i i) (h i i)
      (primitiveTests (a := a) (r := r) P i)

noncomputable def pairSplit (i : ι) (j : Option ι) (positive : Bool) :
    TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm) :=
  B.fullGeometricSector hlarge (primitivePair P i (j.getD i)) (h i (j.getD i))
    (primitiveFamilyTests (a := a) (r := r) P j ⊓
      (if positive then primitiveTests (a := a) (r := r) P i
        else (primitiveTests (a := a) (r := r) P i)ᶜ))

omit [Finite ι] [Group.IsPerfect (alternatingGroup (Fin (m+1)))] in
theorem primitivePair_left_resolved (i j : ι) :
    ResolvedBy (fun b => (primitiveTests (a := a) (r := r) (primitivePair P i j) b).val)
      (primitiveTests (a := a) (r := r) P i).val :=
  resolved_test _ false

omit [Finite ι] [Group.IsPerfect (alternatingGroup (Fin (m+1)))] in
theorem primitivePair_right_resolved (i : ι) (j : Option ι) :
    ResolvedBy (fun b => (primitiveTests (a := a) (r := r) (primitivePair P i (j.getD i)) b).val)
      (primitiveFamilyTests (a := a) (r := r) P j).val := by
  cases j with
  | none => exact fun _ _ _ => Iff.rfl
  | some j => exact resolved_test _ true

omit [Finite ι] in
theorem pairSplit_supported (i : ι) (j : Option ι) (positive : Bool) :
    B.AlignedSmallSupported (B.pairSplit hlarge P h i j positive) := by
  apply B.fullGeometricSector_supported
  intro x y he
  apply and_congr (primitivePair_right_resolved P i j x y he)
  cases positive with
  | false => exact not_congr (primitivePair_left_resolved P i (j.getD i) x y he)
  | true => exact primitivePair_left_resolved P i (j.getD i) x y he

omit [Finite ι] in
theorem pair_selected_star (i : ι) (j : Option ι) :
    B.fullGeometricSector hlarge (primitivePair P i (j.getD i)) (h i (j.getD i))
      (primitiveFamilyTests (a := a) (r := r) P j) = B.pairStar hlarge P h j := by
  cases j with
  | none => exact B.fullGeometricSector_whole hlarge _ _
  | some j =>
    apply B.fullGeometricSector_shared_primitive hlarge (primitivePair P i j) (primitivePair P j j)
      true false rfl _ _ _
    exact resolved_test _ ()

omit [Finite ι] in
theorem pairStar_split (i : ι) (j : Option ι) (s : TrackStar (Fin (m+1))) :
    B.pairStar hlarge P h j s =
      B.pairSplit hlarge P h i j true s * B.pairSplit hlarge P h i j false s := by
  rw [← B.pair_selected_star hlarge P h i j]
  unfold pairSplit
  simp only [Bool.false_eq_true,↓reduceIte]
  rw [← B.fullGeometricSector_union hlarge _ _
    (primitiveFamilyTests (a := a) (r := r) P j ⊓ primitiveTests (a := a) (r := r) P i)
    (primitiveFamilyTests (a := a) (r := r) P j ⊓ (primitiveTests (a := a) (r := r) P i)ᶜ)
    (fun x y he => and_congr (primitivePair_right_resolved P i j x y he)
      (primitivePair_left_resolved P i (j.getD i) x y he))
    (Set.disjoint_left.mpr (by intro x hx hy; exact hy.2 hx.2))]
  congr 2
  ext x
  change (x ∈ (primitiveFamilyTests (a := a) (r := r) P j).val) ↔
    (x ∈ (primitiveFamilyTests (a := a) (r := r) P j).val ∧ x ∈ (primitiveTests (a := a) (r := r) P i).val) ∨
    (x ∈ (primitiveFamilyTests (a := a) (r := r) P j).val ∧ x ∉ (primitiveTests (a := a) (r := r) P i).val)
  tauto

omit [Finite ι] in
theorem pairSplit_whole_left (i : ι) :
    B.pairSplit hlarge P h i none true = B.pairStar hlarge P h (some i) := by
  unfold pairSplit pairStar
  congr 1
  ext x
  change (x ∈ Set.univ ∧ x ∈ (primitiveTests (a := a) (r := r) P i).val) ↔ _
  simp

omit [Finite ι] in
theorem pairSplit_mem (i : ι) (j : Option ι) (positive : Bool) (s : TrackStar (Fin (m+1))) :
    B.pairSplit hlarge P h i j positive s ∈
      (smallFamilyEval (B.smallPrimitiveInputs hlarge P)).range := by
  have hi := B.smallPrimitive_range_reindex hlarge P (fun b : Bool => if b then j.getD i else i)
  have he : P ∘ (fun b : Bool => if b then j.getD i else i) = primitivePair P i (j.getD i) := by
    funext b; cases b <;> rfl
  rw [he] at hi
  apply hi
  exact B.fullGeometricSector_mem hlarge _ _ _ s

omit [Finite ι] in
theorem pairStar_mem (j : Option ι) (s : TrackStar (Fin (m+1))) :
    B.pairStar hlarge P h j s ∈ (smallFamilyEval (B.smallPrimitiveInputs hlarge P)).range := by
  cases j with
  | none => exact B.constant_range_full hlarge P ⟨_,rfl⟩
  | some i =>
    rw [← B.pairSplit_whole_left hlarge P h i]
    exact B.pairSplit_mem hlarge P h i none true s

end InitialCoverSystem
end PairSectors

end SimpleAmenable
end
end

end OAI
