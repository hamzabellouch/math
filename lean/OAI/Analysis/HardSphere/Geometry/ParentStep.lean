import Mathlib
import OAI.Analysis.HardSphere.Geometry.AnimalFamily

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators Classical
noncomputable section
open scoped BigOperators Classical
noncomputable section
open scoped BigOperators Classical ENNReal
namespace HardSphere.BathSlice
open HardSphere.Lattice

lemma parent_step {q : ℕ} (hq : 0 < q) {z w : Vertex} (hzw : starStep z w) :
    parent q z = parent q w ∨ rangeStep 1 (parent q z) (parent q w) := by
  by_cases he : parent q z = parent q w
  · exact Or.inl he
  right
  refine ⟨he,fun i ↦ ?_⟩
  have hqz : (0:ℤ)<q := by exact_mod_cast hq
  have hb := abs_le.mp (hzw.2 i)
  have hu : z i ≤ w i+q := by omega
  have hv : w i ≤ z i+q := by omega
  have hdu := Int.ediv_le_ediv hqz hu
  have hdv := Int.ediv_le_ediv hqz hv
  rw [Int.add_ediv_of_dvd_right (dvd_refl (q:ℤ)), Int.ediv_self hqz.ne'] at hdu hdv
  exact abs_le.mpr ⟨by change -(1:ℤ) ≤ z i/(q:ℤ)-w i/(q:ℤ); omega,
    by change z i/(q:ℤ)-w i/(q:ℤ) ≤ (1:ℤ); omega⟩

lemma parent_fiber_finite {q : ℕ} (hq : 0 < q) (v : Vertex) :
    {z | parent q z=v}.Finite := by
  have hqz : (0:ℤ)<q := by exact_mod_cast hq
  apply (Set.finite_Icc (fun i ↦ (q:ℤ)*v i) (fun i ↦ (q:ℤ)*v i+q)).subset
  intro z hz
  constructor <;> intro i
  · change (q:ℤ)*v i ≤ z i
    have he := Int.mul_ediv_add_emod (z i) q
    have hi : z i/(q:ℤ)=v i := congrFun hz i
    have hn := Int.emod_nonneg (z i) hqz.ne'
    rw [hi] at he
    omega
  · change z i ≤ (q:ℤ)*v i+q
    have he := Int.mul_ediv_add_emod (z i) q
    have hi : z i/(q:ℤ)=v i := congrFun hz i
    have hn := Int.emod_lt_of_pos (z i) hqz
    rw [hi] at he
    omega

lemma parent_preimage_finite {q : ℕ} (hq : 0 < q) (C : Finset Vertex) :
    ((parent q) ⁻¹' (↑C : Set Vertex)).Finite := by
  have hf : (⋃ v ∈ (↑C : Set Vertex), {z | parent q z=v}).Finite :=
    C.finite_toSet.biUnion (fun v _ ↦ parent_fiber_finite hq v)
  apply hf.subset
  intro z hz
  exact Set.mem_iUnion.mpr ⟨parent q z,Set.mem_iUnion.mpr ⟨hz,rfl⟩⟩

lemma parent_reach {q : ℕ} (hq : 0 < q) {D E : Set Vertex}
    (hDE : ∀ z ∈ D, parent q z ∈ E) {z w : Vertex}
    (hp : withinReach starStep D z w) :
    withinReach (rangeStep 1) E (parent q z) (parent q w) := by
  induction hp with
  | refl => exact .refl
  | @tail u v _ huv ih =>
    rcases parent_step hq huv.2.2 with he | he
    · simpa only [←he] using ih
    · exact ih.tail ⟨hDE u huv.1,hDE v huv.2.1,he⟩

lemma parent_projection_reachable {q K : ℕ} (hq : 0 < q) (hK : 2 < K)
    {D : Set Vertex} {B : Finset (DiscreteTorus K)}
    (hDB : ∀ z ∈ D, torusProjection K (parent q z) ∈ B) {z w : Vertex}
    (hp : withinReach starStep D z w) :
    (badGraph (torusRangeGraph K 1) B).Reachable
      (torusProjection K (parent q z)) (torusProjection K (parent q w)) := by
  rw [SimpleGraph.reachable_iff_reflTransGen]
  induction hp with
  | refl => exact .refl
  | @tail u v _ huv ih =>
    rcases parent_step hq huv.2.2 with he | he
    · simpa only [←he] using ih
    · exact ih.tail ⟨hDB u huv.1,hDB v huv.2.1,
        rangeStep_projection (by simpa only [mul_one] using hK) he⟩
end HardSphere.BathSlice

namespace HardSphere.Lattice
universe v
variable {V : Type v} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
lemma badGraph_reachable_induce {G : SimpleGraph V} {B : Finset V} {x y : V}
    (hp : (badGraph G B).Reachable x y) (hx : x ∈ B) (hy : y ∈ B) :
    (G.induce (↑B : Set V)).Reachable ⟨x,hx⟩ ⟨y,hy⟩ := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hp ⊢
  induction hp with
  | refl => exact .refl
  | @tail u v _ huv ih => exact (ih huv.1).tail huv.2.2

lemma badComponent_preconnected (G : SimpleGraph V) (B : Finset V) (x : V) :
    (G.induce (↑(badComponent G B x) : Set V)).Preconnected := by
  intro u v
  have hu := (mem_badComponent G B x u).mp u.property
  have hv := (mem_badComponent G B x v).mp v.property
  have hp := (reachable_inside_component G B hu.2).symm.trans
    (reachable_inside_component G B hv.2)
  exact badGraph_reachable_induce hp u.property v.property
end HardSphere.Lattice

namespace HardSphere.BathSlice
open HardSphere.Lattice

theorem parent_component_lift {q K : ℕ} [NeZero K] (hq : 0 < q) (hK : 2 < K)
    {D : Set Vertex} (hD : starConnected D) {z : Vertex} (hz : z ∈ D)
    (B : Finset (DiscreteTorus K)) (hDB : ∀ w ∈ D, torusProjection K (parent q w) ∈ B)
    (hsmall : (badComponent (torusRangeGraph K 1) B (torusProjection K (parent q z))).card < K) :
    ∃ C : Finset Vertex,
      (∀ w ∈ D, parent q w ∈ C) ∧
      Set.BijOn (torusProjection K) (↑C)
        (↑(badComponent (torusRangeGraph K 1) B (torusProjection K (parent q z)))) ∧
      (∀ u∈C, ∀ v∈C, ∀ i, |u i-v i| ≤
        ((badComponent (torusRangeGraph K 1) B (torusProjection K (parent q z))).card:ℤ)-1) := by
  classical
  let S := badComponent (torusRangeGraph K 1) B (torusProjection K (parent q z))
  have hmem : ∀ w ∈ D, torusProjection K (parent q w) ∈ S := by
    intro w hw
    apply (mem_badComponent _ _ _ _).mpr
    exact ⟨hDB w hw,parent_projection_reachable hq hK hDB (hD z hz w hw)⟩
  obtain ⟨C,hC,hbij,hspan⟩ := small_periodic_lifts (a := 1)
    (by simpa only [mul_one] using hK) S (by simpa only [one_mul] using hsmall)
    (badComponent_preconnected _ _ _) (parent q z) (hmem z hz)
  refine ⟨C,?_,hbij,?_⟩
  · intro w hw
    change parent q w ∈ (↑C : Set Vertex)
    rw [hC]
    exact ⟨hmem w hw,parent_reach hq (fun u hu ↦ hmem u hu) (hD z hz w hw)⟩
  · simpa only [Nat.cast_one,one_mul] using hspan

theorem finite_of_parent_component_small {q K : ℕ} [NeZero K] (hq : 0 < q) (hK : 2 < K)
    {D : Set Vertex} (hD : starConnected D) {z : Vertex} (hz : z ∈ D)
    (B : Finset (DiscreteTorus K)) (hDB : ∀ w ∈ D, torusProjection K (parent q w) ∈ B)
    (hsmall : (badComponent (torusRangeGraph K 1) B (torusProjection K (parent q z))).card < K) :
    D.Finite := by
  obtain ⟨C,hC,_,_⟩ := parent_component_lift hq hK hD hz B hDB hsmall
  exact (parent_preimage_finite hq C).subset hC

end HardSphere.BathSlice

namespace HardSphere.Lattice
lemma liftedBadComponent_eq_of_mem {B : Set Vertex} {z w : Vertex}
    (hw : w ∈ liftedBadComponent B z) : liftedBadComponent B w = liftedBadComponent B z := by
  ext v
  constructor
  · intro hv
    exact ⟨hw.1,hv.2.1,hw.2.2.trans hv.2.2⟩
  · intro hv
    exact ⟨hw.2.1,hv.2.1,(withinReach_symm (fun _ _ ↦ starStep_symm) hw.2.2).trans hv.2.2⟩

lemma own_badComponent_card_lt {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (B : Finset V) {M : ℕ} (he : ¬LargeBadComponent G B M)
    {v : V} (hv : v ∈ B) : (badComponent G B v).card < M := by
  apply lt_of_not_ge
  intro h
  exact he ⟨_,Finset.mem_image.mpr ⟨v,hv,rfl⟩,h⟩
end HardSphere.Lattice

end
end
end
end
end
end

end OAI
