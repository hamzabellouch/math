import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.BitWeight
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Topology

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter

namespace OrdinaryCorrelations.NumericalSubtrees
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.GraphKernel.PrimeSystem
open Finset Classical
variable {h ℓ r : ℕ} {w v : ClosedLine h ℓ}

lemma topology_treeSteps (hw : (returnSteps w).card=r) (hv : (returnSteps v).card=r)
    (ht : encodeTopology w r hw=encodeTopology v r hv) : w.treeSteps=v.treeSteps := by
  have hr : returnSteps w=returnSteps v := congrArg (fun t : Topology ℓ r => t.1.val) ht
  ext e
  have he := congrArg (fun E => e ∈ E) hr
  simp only [returnSteps,Finset.mem_sdiff,mem_univ,true_and] at he
  tauto

lemma topology_target_eq (hw : (returnSteps w).card=r) (hv : (returnSteps v).card=r)
    (ht : encodeTopology w r hw=encodeTopology v r hv)
    (e : Fin ℓ) (hew : e ∈ returnSteps w) (hev : e ∈ returnSteps v) :
    returnTarget w e hew = returnTarget v e hev := by
  have hte := congrArg (fun t : Topology ℓ r => topologyTarget t e) ht
  simpa only [topologyTarget_encode w r hw e hew,
    topologyTarget_encode v r hv e hev] using hte

theorem topology_offset_pattern (hw : (returnSteps w).card=r) (hv : (returnSteps v).card=r)
    (ht : encodeTopology w r hw=encodeTopology v r hv) (i j : Fin (ℓ+1)) :
    w.offset i=w.offset j ↔ v.offset i=v.offset j := by
  have htree := topology_treeSteps hw hv ht
  have H : ∀ k : ℕ, ∀ i j : Fin (ℓ+1), i.val≤k → j.val≤k →
      (w.offset i=w.offset j ↔ v.offset i=v.offset j) := by
    intro k
    induction k with
    | zero =>
      intro i j hi hj
      have hij : i=j := Fin.ext (by omega)
      subst j
      simp
    | succ k ih =>
      intro i j hi hj
      by_cases hik : i.val≤k
      · by_cases hjk : j.val≤k
        · exact ih i j hik hjk
        · have hjev : j.val=k+1 := by omega
          let e : Fin ℓ := ⟨k,by omega⟩
          have hje : j=e.succ := Fin.ext hjev
          rw [hje]
          by_cases het : e ∈ w.treeSteps
          · have hevt : e ∈ v.treeSteps := htree ▸ het
            have hwn : w.offset i≠w.offset e.succ := (mem_filter.mp het).2 i hik
            have hvn : v.offset i≠v.offset e.succ := (mem_filter.mp hevt).2 i hik
            simp [hwn,hvn]
          · have hew : e ∈ returnSteps w := Finset.mem_sdiff.mpr ⟨mem_univ _,het⟩
            have hev : e ∈ returnSteps v := by
              apply Finset.mem_sdiff.mpr
              exact ⟨mem_univ _,by simpa only [← htree] using het⟩
            have hetar := topology_target_eq hw hv ht e hew hev
            have hs := returnTarget_spec w e hew
            have hs' := returnTarget_spec v e hev
            rw [← hs.2,← hs'.2,← hetar]
            exact ih i (returnTarget w e hew) hik hs.1
      · by_cases hjk : j.val≤k
        · have hie : i.val=k+1 := by omega
          let e : Fin ℓ := ⟨k,by omega⟩
          have hi' : i=e.succ := Fin.ext hie
          rw [hi']
          by_cases het : e ∈ w.treeSteps
          · have hevt : e ∈ v.treeSteps := htree ▸ het
            have hwn : w.offset e.succ≠w.offset j := Ne.symm ((mem_filter.mp het).2 j hjk)
            have hvn : v.offset e.succ≠v.offset j := Ne.symm ((mem_filter.mp hevt).2 j hjk)
            simp [hwn,hvn]
          · have hew : e ∈ returnSteps w := Finset.mem_sdiff.mpr ⟨mem_univ _,het⟩
            have hev : e ∈ returnSteps v := by
              apply Finset.mem_sdiff.mpr
              exact ⟨mem_univ _,by simpa only [← htree] using het⟩
            have hetar := topology_target_eq hw hv ht e hew hev
            have hs := returnTarget_spec w e hew
            have hs' := returnTarget_spec v e hev
            rw [← hs.2,← hs'.2,← hetar]
            exact ih (returnTarget w e hew) j hs.1 hjk
        · have hij : i=j := Fin.ext (by omega)
          subst j
          simp
  exact H ℓ i j (by omega) (by omega)

structure SameGeometry (w v : ClosedLine h ℓ) : Prop where
  trees : w.treeSteps=v.treeSteps
  pattern : ∀ i j, w.offset i=w.offset j ↔ v.offset i=v.offset j

lemma sameGeometry_of_topology (hw : (returnSteps w).card=r) (hv : (returnSteps v).card=r)
    (ht : encodeTopology w r hw=encodeTopology v r hv) : SameGeometry w v :=
  ⟨topology_treeSteps hw hv ht,topology_offset_pattern hw hv ht⟩

namespace SameGeometry
lemma symm (H : SameGeometry w v) : SameGeometry v w :=
  ⟨H.trees.symm,fun i j => (H.pattern i j).symm⟩

lemma children (H : SameGeometry w v) (i : Fin (ℓ+1)) :
    w.children (w.offset i)=v.children (v.offset i) := by
  unfold ClosedLine.children
  apply congrArg Finset.card
  ext e
  simp only [mem_filter,H.trees,H.pattern]

lemma root (H : SameGeometry w v) (i : Fin (ℓ+1)) : w.offset i=0 ↔ v.offset i=0 := by
  simpa only [w.start_zero,v.start_zero] using H.pattern i 0

lemma noReturn (H : SameGeometry w v) (i : Fin (ℓ+1)) :
    w.NoReturnIncidence (w.offset i) ↔ v.NoReturnIncidence (v.offset i) := by
  simp only [ClosedLine.NoReturnIncidence,ne_eq,H.trees,H.pattern]

lemma good (H : SameGeometry w v) (e : Fin ℓ) : w.Good e ↔ v.Good e := by
  simp only [ClosedLine.Good,ne_eq,H.trees,H.children,H.root,H.noReturn]

lemma grows (H : SameGeometry w v) (i : Fin (ℓ+1)) (E : Finset (Fin ℓ)) :
    Grows w (w.offset i) E ↔ Grows v (v.offset i) E := by
  simp only [Grows,H.trees,H.pattern]

end SameGeometry

end OrdinaryCorrelations.NumericalSubtrees

end

end OAI
