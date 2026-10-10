import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.CellGeometry

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FiniteSectorPartition
namespace ActualLawfulTable
variable {E H Q Ω κ : Type*} [Group E] [Group H] [Group Q] [Group.IsPerfect E]
    {q : H →* Q} {v : (Ω → E) →* Q} (T : ActualLawfulTable q v)

theorem sector_range_le_biUnion (W : κ → Set Ω) (S : Finset κ)
    (hdisjoint : Pairwise fun i j => Disjoint (W i) (W j)) (K : Subgroup H)
    (hK : ∀ i ∈ S, (T.sector (W i)).range ≤ K) :
    (T.sector (⋃ i ∈ S, W i)).range ≤ K := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hd : Disjoint (W i) (⋃ j ∈ S, W j) := by
      apply Set.disjoint_iUnion_right.mpr
      intro j
      apply Set.disjoint_iUnion_right.mpr
      intro hj
      exact hdisjoint (by intro he; subst j; exact hi hj)
    have he : (⋃ j ∈ insert i S, W j) = W i ∪ ⋃ j ∈ S, W j := by
      ext x
      simp only [Set.mem_iUnion,Finset.mem_insert,Set.mem_union]
      constructor
      · rintro ⟨j,(rfl|hj),hx⟩
        · exact Or.inl hx
        · exact Or.inr ⟨j,hj,hx⟩
      · rintro (hx|⟨j,hj,hx⟩)
        · exact ⟨i,Or.inl rfl,hx⟩
        · exact ⟨j,Or.inr hj,hx⟩
    rw [he,T.sector_union hd]
    rintro x ⟨s,rfl⟩
    exact K.mul_mem (hK i (Finset.mem_insert_self i S) ⟨s,rfl⟩)
      (ih (fun j hj => hK j (Finset.mem_insert_of_mem hj)) ⟨s,rfl⟩)

theorem sector_range_le_partition [Fintype κ] (W : κ → Set Ω) (V : Set Ω)
    (hdisjoint : Pairwise fun i j => Disjoint (W i) (W j))
    (hcover : ∀ ω, ω ∈ V ↔ ∃ i, ω ∈ W i) :
    (T.sector V).range ≤ ⨆ i, (T.sector (W i)).range := by
  have he : V = ⋃ i ∈ (Finset.univ : Finset κ), W i := by
    ext ω
    simpa only [Set.mem_iUnion,Finset.mem_univ,exists_true_left] using hcover ω
  rw [he]
  exact T.sector_range_le_biUnion W Finset.univ hdisjoint _
    (fun i _ => le_iSup (fun j => (T.sector (W j)).range) i)

end ActualLawfulTable

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι κ : Type*} [Finite ι] [Fintype κ]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem fullGeometricSector_union (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (V W : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) V.val)
    (hd : Disjoint V.val W.val) (s : TrackStar (Fin (m+1))) :
    B.fullGeometricSector hlarge P h (V ⊔ W) s =
      B.fullGeometricSector hlarge P h V s * B.fullGeometricSector hlarge P h W s := by
  unfold fullGeometricSector
  change (B.fullPrimitiveTable hlarge P h).sector (resolvedPolygonMask _ (V.val ∪ W.val)) s = _
  rw [resolvedPolygonMask_union]
  exact DFunLike.congr_fun ((B.fullPrimitiveTable hlarge P h).sector_union
    (resolvedPolygonMask_disjoint _ hV hd)) s

theorem fullGeometricSector_partition_range (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (V : polygonAlgebra a) (W : κ → polygonAlgebra a)
    (hW : ∀ i, ResolvedBy (fun z => (primitiveTests (a := a) (r := r) P z).val) (W i).val)
    (hdisjoint : Pairwise fun i j => Disjoint (W i).val (W j).val)
    (hcover : ∀ p, p ∈ V.val ↔ ∃ i, p ∈ (W i).val) :
    (B.fullGeometricSector hlarge P h V).range ≤
      ⨆ i, (B.fullGeometricSector hlarge P h (W i)).range := by
  apply (B.fullPrimitiveTable hlarge P h).sector_range_le_partition
  · intro i j hij
    exact resolvedPolygonMask_disjoint _ (hW i) (hdisjoint hij)
  · intro ω
    constructor
    · rintro ⟨p,hp,hpV⟩
      obtain ⟨i,hi⟩ := (hcover p).mp hpV
      exact ⟨i,p,hp,hi⟩
    · rintro ⟨i,p,hp,hi⟩
      exact ⟨p,hp,(hcover p).mpr ⟨i,hi⟩⟩

end InitialCoverSystem

theorem commute_of_range_iSup {G X Y : Type*} [Group G] [Group X] [Group Y]
    {ι κ : Type*} (f : ι → X →* G) (g : κ → Y →* G)
    (hc : ∀ i j s t, Commute (f i s) (g j t))
    {x y : G} (hx : x ∈ ⨆ i, (f i).range) (hy : y ∈ ⨆ j, (g j).range) : Commute x y := by
  have hleft (j : κ) (t : Y) : (⨆ i, (f i).range) ≤ Subgroup.centralizer {g j t} := by
    apply iSup_le
    intro i z hz w hw
    obtain ⟨s,rfl⟩ := hz
    obtain rfl := Set.mem_singleton_iff.mp hw
    exact (hc i j s t).eq.symm
  have hright : (⨆ j, (g j).range) ≤ Subgroup.centralizer {x} := by
    apply iSup_le
    intro j z hz w hw
    obtain ⟨t,rfl⟩ := hz
    obtain rfl := Set.mem_singleton_iff.mp hw
    exact (hleft j t hx _ (Set.mem_singleton _)).symm
  exact hright hy _ (Set.mem_singleton _)

end FiniteSectorPartition

section AxisCellSplitting

def otherAxis (d : Fin 2) : Fin 2 := if d=0 then 1 else 0
@[simp] theorem otherAxis_ne (d : Fin 2) : otherAxis d ≠ d := by fin_cases d <;> decide

noncomputable def axisCellRectangle {n : ℕ} (d : Fin 2)
    (k l : ℕ) (hk : k ≤ n) (hl : l ≤ n) (hlpos : 0 < l)
    (p q : ℤ) (u v : CutRing) (huv : ordinary u ≤ ordinary v)
    (hu : p ≤ endpointLabel u ∧ endpointLabel u < p+k)
    (hv : p ≤ endpointLabel v ∧ endpointLabel v < p+k) (i : Fin l) : LabelledRectangle n where
  length j := if j=d then k else l
  length_le j := by split <;> assumption
  start j := if j=d then p else q
  lower j := if j=d then u else windowCut l q i.castSucc
  upper j := if j=d then v else windowCut l q i.succ
  ordered j := by
    split
    · exact huv
    · exact (windowCut_strictMono l q (Fin.castSucc_lt_succ (i := i))).le
  lower_label j := by
    split_ifs
    · exact hu
    · exact windowCut_label l q hlpos i.castSucc
  upper_label j := by
    split_ifs
    · exact hv
    · exact windowCut_label l q hlpos i.succ

theorem axisCellRectangle_polygon {a n : ℕ} (d : Fin 2)
    (k l : ℕ) (hk : k ≤ n) (hl : l ≤ n) (hlpos : 0 < l)
    (p q : ℤ) (u v : CutRing) (huv : ordinary u ≤ ordinary v)
    (hu : p ≤ endpointLabel u ∧ endpointLabel u < p+k)
    (hv : p ≤ endpointLabel v ∧ endpointLabel v < p+k) (i : Fin l) :
    (axisCellRectangle d k l hk hl hlpos p q u v huv hu hv i).polygon a =
      coordinateInterval a d u v ⊓ windowCell a (otherAxis d) l q i := by
  fin_cases d
  · rfl
  · change coordinateInterval a 0 _ _ ⊓ coordinateInterval a 1 u v =
      coordinateInterval a 1 u v ⊓ coordinateInterval a 0 _ _
    exact inf_comm _ _

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem axisSector_range_cells (hlarge : 15 < m+1) (n : ℕ) (g : B.CoordinateWindowLaw n)
    (d : Fin 2) (k l : ℕ) (hk : k ≤ n) (hl : l ≤ n) (hlpos : 201 ≤ l)
    (p q : ℤ) (u v : CutRing) (huv : ordinary u ≤ ordinary v)
    (hu : p ≤ endpointLabel u ∧ endpointLabel u < p+k)
    (hv : p ≤ endpointLabel v ∧ endpointLabel v < p+k) :
    (B.axisSector hlarge n g d k hk p (coordinateInterval a d u v)).range ≤
      ⨆ i : Fin l, (B.rectangleCopy hlarge g
        (axisCellRectangle d k l hk hl (by omega) p q u v huv hu hv i)).range := by
  let R := axisCellRectangle d k l hk hl (by omega) p q u v huv hu hv
  let z : Fin 2 → ℤ := fun j => if j=d then p else q
  rw [B.axisSector_in_window hlarge n g d k hk p z
    (by simp [z]) (by simp [z]; omega) _ (axisInterval_resolved d k p u v hu hv)]
  change (B.fullGeometricSector hlarge (coordinateWindowPrimitives n z) _ _).range ≤ _
  apply B.fullGeometricSector_partition_range hlarge (coordinateWindowPrimitives n z)
    (fun I _ b hb => g I b hb z) (coordinateInterval a d u v) (fun i => (R i).polygon a)
  · intro i
    exact (R i).resolved a r
  · intro i j hij
    rw [axisCellRectangle_polygon,axisCellRectangle_polygon]
    exact (windowCell_pairwise_disjoint (a := a) (otherAxis d) l hlpos q hij).mono
      (Set.inter_subset_right) (Set.inter_subset_right)
  · intro x
    constructor
    · intro hx
      obtain ⟨i,hi⟩ := windowCell_cover (a := a) (otherAxis d) l hlpos q x
      refine ⟨i,?_⟩
      rw [axisCellRectangle_polygon]
      exact ⟨hx,hi⟩
    · rintro ⟨i,hi⟩
      rw [axisCellRectangle_polygon] at hi
      exact hi.1

theorem axisCellRectangle_grid_control (hlarge : 15 < m+1) (n : ℕ) (g : B.CoordinateWindowLaw n)
    (d : Fin 2) (k l : ℕ) (hk : k ≤ n) (hl : l ≤ n) (hlpos : 0 < l)
    (p q : ℤ) (u v : CutRing) (huv : ordinary u ≤ ordinary v)
    (hu : p ≤ endpointLabel u ∧ endpointLabel u < p+k)
    (hv : p ≤ endpointLabel v ∧ endpointLabel v < p+k) (i : Fin l) :
    SmallControlled B.c (B.rectangleCopy hlarge g
      (axisCellRectangle d k l hk hl hlpos p q u v huv hu hv i))
      (B.axisSector hlarge n g (otherAxis d) l hl q (windowCell a (otherAxis d) l q i)) := by
  simpa only [axisCellRectangle,otherAxis_ne,ite_false,windowCell] using
    B.rectangleCopy_axes_control hlarge g
      (axisCellRectangle d k l hk hl hlpos p q u v huv hu hv i) (otherAxis d)

theorem axisCellRectangle_distinct_commute (hlarge : 20 ≤ m+1) (n : ℕ) (g : B.CoordinateWindowLaw n)
    (d : Fin 2) (k k' l : ℕ) (hk : k ≤ n) (hk' : k' ≤ n) (hl : l ≤ n) (hlpos : 201 ≤ l)
    (p p' q : ℤ) (u v u' v' : CutRing)
    (huv : ordinary u ≤ ordinary v) (huv' : ordinary u' ≤ ordinary v')
    (hu : p ≤ endpointLabel u ∧ endpointLabel u < p+k)
    (hv : p ≤ endpointLabel v ∧ endpointLabel v < p+k)
    (hu' : p' ≤ endpointLabel u' ∧ endpointLabel u' < p'+k')
    (hv' : p' ≤ endpointLabel v' ∧ endpointLabel v' < p'+k')
    (i j : Fin l) (hij : i ≠ j) (s t : TrackStar (Fin (m+1))) :
    Commute (B.rectangleCopy (by omega) g (axisCellRectangle d k l hk hl (by omega) p q u v huv hu hv i) s)
      (B.rectangleCopy (by omega) g (axisCellRectangle d k' l hk' hl (by omega) p' q u' v' huv' hu' hv' j) t) := by
  let R := axisCellRectangle d k l hk hl (by omega) p q u v huv hu hv i
  let R' := axisCellRectangle d k' l hk' hl (by omega) p' q u' v' huv' hu' hv' j
  refine (small_control_disjoint _ B.c B.constant_aligned B.disjoint_aligned
    (by simpa using hlarge) (B.rectangleCopy (by omega) g R) (B.rectangleCopy (by omega) g R')
    (B.axisSector (by omega) n g (otherAxis d) l hl q (windowCell a (otherAxis d) l q i))
    (B.axisSector (by omega) n g (otherAxis d) l hl q (windowCell a (otherAxis d) l q j))
    (B.rectangleCopy_supported (by omega) g R) (B.rectangleCopy_supported (by omega) g R')
    (B.axisSector_supported (by omega) n g (otherAxis d) l hl q _
      (windowCell_axis_resolved _ _ (by omega) _ _))
    (B.axisCellRectangle_grid_control (by omega) n g d k l hk hl (by omega) p q u v huv hu hv i)
    (B.axisCellRectangle_grid_control (by omega) n g d k' l hk' hl (by omega) p' q u' v' huv' hu' hv' j) ?_) s t
  intro x y
  exact B.fullGeometricSector_commute (by omega) (axisWindowPrimitives (otherAxis d) l q) _ _ _
    (windowCell_axis_resolved _ _ (by omega) _ _)
    (windowCell_pairwise_disjoint (otherAxis d) l hlpos q hij) x y

end InitialCoverSystem
end AxisCellSplitting

end SimpleAmenable
end
end

end OAI
