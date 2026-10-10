import Mathlib
import OAI.GroupTheory.SimpleAmenable.Amenability.ComponentChartContainment
import OAI.GroupTheory.SimpleAmenable.Amenability.BarrierFiniteMenu
import OAI.GroupTheory.SimpleAmenable.Amenability.PartitionArrows
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.ShapeTranslationUnique

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FinitePartitionArrows
open Classical Set
namespace PartitionArrow
variable {a m : ℕ} {P Q : TrackPolygonPartition a m} {g h : polygonFullGroup a m}

noncomputable def cellMap (hg : PartitionArrow P Q g) (c : PartitionCell P) : PartitionCell Q :=
  (hg c).choose

theorem cellMap_image (hg : PartitionArrow P Q g) (c : PartitionCell P) :
    g.val '' partitionCellSet c=partitionCellSet (hg.cellMap c) := (hg c).choose_spec.1

theorem eq_of_cellMap (hg : PartitionArrow P Q g) (hh : PartitionArrow P Q h)
    (he : hg.cellMap=hh.cellMap) : g=h := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  obtain ⟨c,hc,-⟩ := partitionCellSet_cover P x
  obtain ⟨u,hu⟩ := (hg c).choose_spec.2
  obtain ⟨v,hv⟩ := (hh c).choose_spec.2
  have him : g.val '' partitionCellSet c=h.val '' partitionCellSet c := by
    rw [hg.cellMap_image,hh.cellMap_image,he]
  have hne := partitionCellSet_nonempty c
  have hxshift : ordinary u.1=ordinary v.1 := by
    refine bounded_coordinate_shift_unique (partitionCellSet c) (fun t => t.2.val.1)
      (fun t => t.2.val.1) hne (show BddAbove ((fun t => t.2.val.1) '' partitionCellSet c) from ?_)
      g.val h.val him (ordinary u.1) (ordinary v.1) ?_ ?_
    · exact ⟨1,by rintro y ⟨z,hz,rfl⟩; exact z.2.property.1.2.le⟩
    · intro z hz
      exact congrArg Prod.fst (hu z hz)
    · intro z hz
      exact congrArg Prod.fst (hv z hz)
  have hyshift : ordinary u.2=ordinary v.2 := by
    refine bounded_coordinate_shift_unique (partitionCellSet c) (fun t => t.2.val.2)
      (fun t => t.2.val.2) hne (show BddAbove ((fun t => t.2.val.2) '' partitionCellSet c) from ?_)
      g.val h.val him (ordinary u.2) (ordinary v.2) ?_ ?_
    · exact ⟨1,by rintro y ⟨z,hz,rfl⟩; exact z.2.property.2.1.2.le⟩
    · intro z hz
      exact congrArg Prod.snd (hu z hz)
    · intro z hz
      exact congrArg Prod.snd (hv z hz)
  apply Prod.ext
  · have hgc : g.val x∈partitionCellSet (hg.cellMap c) := by rw [←hg.cellMap_image]; exact ⟨x,hc,rfl⟩
    have hhc : h.val x∈partitionCellSet (hh.cellMap c) := by rw [←hh.cellMap_image]; exact ⟨x,hc,rfl⟩
    rw [he] at hgc
    exact hgc.1.trans hhc.1.symm
  · apply Subtype.ext
    rw [hu x hc,hv x hc,hxshift,hyshift]

instance arrows_finite (P Q : TrackPolygonPartition a m) :
    Finite {g : polygonFullGroup a m // PartitionArrow P Q g} := by
  apply Finite.of_injective (fun g : {g : polygonFullGroup a m // PartitionArrow P Q g} => g.property.cellMap)
  intro g h he
  apply Subtype.ext
  exact eq_of_cellMap g.property h.property he

end PartitionArrow
end FinitePartitionArrows

section SampledPartitionMotion
open Classical Set

noncomputable def BarrierSignalSystem.sampledPartition {a m : ℕ} {ha : 0 < a} {Q B : ℝ}
    (S : BarrierSignalSystem a ha Q B) (n : ℕ) (b : BarrierBits a m ha) : TrackPolygonPartition a m :=
  fun i => sampledPolygonPartition ha i (sourceDyadicN_pos n)
    (fun j => S.marks (sourceDyadicN_pos n) j (barrierFirstBits b j)) (barrierSecondBits b)

theorem generic_component_image {a m : ℕ} (g : polygonFullGroup a m) (i k : Fin m)
    (u : CutRing×CutRing) (C D : Set (ℝ×ℝ)) (hC : C ⊆ squareInterior)
    (he : (fun x => x+(ordinary u.1,ordinary u.2)) '' C=D)
    (haff : ∀p : GenericSquare a,p.val∈C → fullGroupAffineData g i p=(k,u)) :
    g.val '' {x : TrackPoint a m | x.1=i ∧ x.2.val∈C}=
      {x : TrackPoint a m | x.1=k ∧ x.2.val∈D} := by
  apply Set.Subset.antisymm
  · rintro x ⟨⟨j,p⟩,⟨hji,hp⟩,rfl⟩
    dsimp at hji
    subst j
    have hd := haff p hp
    have ht := congrArg Prod.fst hd
    have hu := congrArg Prod.snd hd
    have hv := fullGroupSquareShift_spec g i p
    change fullGroupSquareShift g i p=u at hu
    rw [hu] at hv
    exact ⟨ht,by rw [hv,←he]; exact ⟨p.val,hp,rfl⟩⟩
  · rintro ⟨j,q⟩ ⟨hjk,hq⟩
    dsimp at hjk
    subst j
    obtain ⟨x,hx,hxq⟩ := (Set.mem_image _ _ _).mp (he.symm ▸ hq)
    have hxg : AvoidsCuts a x := by
      have hh := avoidsCuts_translate q.property.2.2 (-u)
      rw [←hxq] at hh
      simpa [map_neg,←Prod.neg_mk] using hh
    let p : GenericSquare a := ⟨x,⟨⟨(hC hx).1.1.le,(hC hx).1.2⟩,
      ⟨(hC hx).2.1.le,(hC hx).2.2⟩,hxg⟩⟩
    have hd := haff p hx
    have ht := congrArg Prod.fst hd
    have hu := congrArg Prod.snd hd
    have hv := fullGroupSquareShift_spec g i p
    change fullGroupSquareShift g i p=u at hu
    rw [hu] at hv
    refine ⟨(i,p),⟨rfl,hx⟩,?_⟩
    exact Prod.ext ht (Subtype.ext (hv.trans hxq))

namespace BarrierMenu
variable {a m : ℕ} {ha : 0 < a} {F : Finset (polygonFullGroup a m)} (M : BarrierMenu a m ha F)

theorem component_chart {n : ℕ} (hN : 1 ≤ sourceDyadicN n) (hB : M.B ≤ sourceDyadicN n)
    {b : BarrierBits a m ha} (hs : jointFieldSuccess (barrierEightDirections ha) M.signals.eight n b)
    (g : polygonFullGroup a m) (hg : g∈F) (i : Fin m) (p : GenericSquare a) :
    connectedComponentIn (barrierRegion (sampledBarriers ha i (sourceDyadicN n)
      (fun j => M.signals.marks (sourceDyadicN_pos n) j (barrierFirstBits b j))
      (barrierSecondBits b))) p.val ⊆ openSquareChart (barrierChartCuts g i) p := by
  obtain ⟨hs₁,hs₂⟩ := M.signals.eight_success hs
  apply barrier_component_openChart (barrierChartCuts g i) p
    (generic_mem_barrierRegion (sampledBarriers_supported ha i _ _ _) p)
  intro l hl x hx hxc
  have hb := ((M.chart_bound g hg i p l (Finset.mem_union_left _ hl)).1).trans hB
  exact M.signals.central_line_barrier i hN (barrierFirstBits b) (barrierSecondBits b) hs₁ hs₂
    ⟨by linarith,x,hx,hxc⟩ hb x hx hxc

theorem sampledPartition_arrow {n : ℕ} (hN : 1 ≤ sourceDyadicN n)
    (hQ : M.Q < sourceDyadicN n) (hB : M.B ≤ sourceDyadicN n)
    (g : polygonFullGroup a m) (hg : g∈F) (b : BarrierBits a m ha)
    (hs : jointFieldSuccess (barrierEightDirections ha) M.signals.eight n b)
    (hs' : jointFieldSuccess (barrierEightDirections ha) M.signals.eight n (barrierBitsTransport g b)) :
    PartitionArrow (M.signals.sampledPartition n b)
      (M.signals.sampledPartition n (barrierBitsTransport g b)) g := by
  let := barrierLineIndexFintype a (sourceDyadicN_pos n)
  obtain ⟨hs₁,hs₂⟩ := M.signals.eight_success hs
  obtain ⟨hs₁',hs₂'⟩ := M.signals.eight_success hs'
  intro c
  have hc := c.2.property
  change c.2.val∈(sampledPolygonPartition ha c.1 (sourceDyadicN_pos n) _ _).cells at hc
  obtain ⟨p,hpc⟩ := (mem_finiteBarrierPartition _ c.2.val).mp hc
  let k := (g.val (c.1,p)).1
  let q := (g.val (c.1,p)).2
  let u := fullGroupSquareShift g c.1 p
  let B₀ := sampledBarriers ha c.1 (sourceDyadicN n)
    (fun j => M.signals.marks (sourceDyadicN_pos n) j (barrierFirstBits b j)) (barrierSecondBits b)
  let B₁ := sampledBarriers ha k (sourceDyadicN n)
    (fun j => M.signals.marks (sourceDyadicN_pos n) j (barrierFirstBits (barrierBitsTransport g b) j))
    (barrierSecondBits (barrierBitsTransport g b))
  let d₀ : polygonAlgebra a := ⟨barrierComponentCell B₁ q.val,
    barrierComponentCell_polygon (sampledBarriers_supported ha k _ _ _) q.val⟩
  have hd₀ : d₀∈(M.signals.sampledPartition n (barrierBitsTransport g b) k).cells :=
    (mem_finiteBarrierPartition _ d₀).mpr ⟨q,rfl⟩
  let d : PartitionCell (M.signals.sampledPartition n (barrierBitsTransport g b)) := ⟨k,⟨d₀,hd₀⟩⟩
  have hdata : fullGroupAffineData g c.1 p=(k,u) := rfl
  have haff (r : GenericSquare a) (hr : r.val∈connectedComponentIn (barrierRegion B₀) p.val) :
      fullGroupAffineData g c.1 r=(k,u) := by
    exact (squareArrangement_on_openChart (fullGroupAffineData g c.1) (barrierChartCuts g c.1)
      (barrierChartCuts_spec g c.1) p r (M.component_chart hN hB hs g hg c.1 p hr)).trans hdata
  have he := M.signals.component_transport g c.1 k (barrierChartCuts g c.1)
    (barrierChartCuts_spec g c.1) p q u hdata (fullGroupSquareShift_spec g c.1 p)
    M.Q_nonneg (M.shift_bound g hg c.1 p) (M.chart_bound g hg c.1 p)
    hN hQ hB (barrierFirstBits b) (barrierSecondBits b)
    (barrierFirstBits (barrierBitsTransport g b)) (barrierSecondBits (barrierBitsTransport g b))
    hs₁ hs₁' hs₂ hs₂' (barrierBitsTransport_first g b) (barrierBitsTransport_second g b)
  have hcs : partitionCellSet c={x : TrackPoint a m | x.1=c.1 ∧
      x.2.val∈connectedComponentIn (barrierRegion B₀) p.val} := by
    ext x
    change (x.1=c.1 ∧ x.2∈c.2.val.val) ↔ _
    rw [hpc]
    rfl
  refine ⟨d,?_,u,?_⟩
  · rw [hcs]
    exact generic_component_image g c.1 k u _ _
      (fun _ hx => (connectedComponentIn_subset (barrierRegion B₀) p.val hx).1) he haff
  · intro x hx
    rw [hcs] at hx
    have hi := hx.1
    have hd := congrArg Prod.snd (haff x.2 hx.2)
    have hv := fullGroupSquareShift_spec g c.1 x.2
    change fullGroupSquareShift g c.1 x.2=u at hd
    rw [hd] at hv
    have hxpair : x=(c.1,x.2) := Prod.ext hi rfl
    rw [hxpair]
    exact hv

end BarrierMenu
end SampledPartitionMotion

end SimpleAmenable
end
end

end OAI
