import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListOuter

namespace OAI

/-! The literal fork transformation preserves the ordinary degree bound,
isolated centers, and degree-one active ports. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorGraph
open scoped Classical

theorem next_degreeBounds (N : ℚ) (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (hb : SourceBondLists.bounded s.1 s.2.1) (hd : DegreeBounds s) :
    DegreeBounds (next N s) := by
  let left := (SourceBondLists.bonds s.1 s.2.1 hb).left
  let right := (SourceBondLists.bonds s.1 s.2.1 hb).right
  have hbase (v : Fin s.1) : qmaGraphDegree left right v ≤ 3 := by
    rw [← degree_eq_graph]
    exact hd.ordinary v
  have hport (e : Fin (pairCount s.2.2.2)) (b : Fin 2) :
      qmaGraphDegree left right (qmaForkOuter (actualSite hs) (e,b)) ≤ 1 := by
    rw [← degree_eq_graph,actual_outer_eq]
    exact hd.port (outerPort s.2.2.2 (e,b)).1 (outerPort s.2.2.2 (e,b)).2
  refine ⟨?_,?_,?_⟩
  · intro v
    have hv : v.val < s.1+pairCount s.2.2.2*2 := by have := v.isLt; change _<s.1+2*pairCount s.2.2.2 at this; omega
    rw [next_ordinary_degree N s hs hb ⟨v.val,hv⟩]
    exact qmaForkBackground_degree_le_three left right (actualSite hs)
      (actualSite_injective hs) (actual_outer_injective hs) hbase hport _
  · intro i hi
    have hi' : i<s.2.2.2.length := by simpa only [next_centers] using hi
    let v : Fin s.1 := ⟨i,lt_of_lt_of_le hi' hs.centers⟩
    have hv := next_ordinary_degree N s hs hb (old s.1 (pairCount s.2.2.2) v)
    simp only [MediatorIteration.old_val] at hv
    change degree (next N s).2.1 v.val=0
    rw [hv]
    rw [qmaForkBackground_away_degree left right (actualSite hs)
      (actualSite_injective hs) v (actual_outer_away_center hs ⟨i,hi'⟩)]
    rw [← degree_eq_graph]
    exact hd.center i hi'
  · intro i j
    have hj₀ := j.isLt
    generalize hkj : j.val=k at hj₀ ⊢
    clear hkj j
    have hi : i.val<s.2.2.2.length := by simpa only [next_centers] using i.isLt
    have hgroup : groupAt (next N s).2.2.2 i.val=nextGroup s.1 (scale N s) s.2.2.2 i.val :=
      next_groupAt s.1 (scale N s) s.2.2.2 i.val hi
    have hj : k<(groupAt s.2.2.2 i.val).length/2+(groupAt s.2.2.2 i.val).length%2 := by
      have h := hj₀
      rw [hgroup,nextGroup_length] at h
      exact h
    rw [hgroup]
    by_cases hf : k<(groupAt s.2.2.2 i.val).length/2
    · rw [nextGroup_portAt_fresh _ _ _ _ _ hf]
      let p : LocalPair s.2.2.2 := ⟨⟨i.val,hi⟩,⟨k,hf⟩⟩
      let e := pairEquiv s.2.2.2 p
      have he : e.val=pairStart s.2.2.2 i.val+k := pairEquiv_val _ p
      have hv : (fresh s.1 (pairCount s.2.2.2) e 0).val=
          s.1+2*(pairStart s.2.2.2 i.val+k) := by
        simp only [MediatorIteration.fresh_val,Fin.val_zero,Nat.add_zero,he]
      rw [← hv,next_ordinary_degree N s hs hb]
      rw [qmaForkBackground_new_degree left right (actualSite hs)]
      norm_num
    · rw [nextGroup_portAt_retained _ _ _ _ _ (by omega)]
      let t := 2*((groupAt s.2.2.2 i.val).length/2)+
        (k-(groupAt s.2.2.2 i.val).length/2)
      have ht : t<(groupAt s.2.2.2 i.val).length := retained_index_lt _ _ hj (by omega)
      let v : Fin s.1 := ⟨(portAt (groupAt s.2.2.2 i.val) t).1,hs.bounded ⟨i.val,hi⟩ ⟨t,ht⟩⟩
      have haway (e : Fin (pairCount s.2.2.2)) :
          actualSite hs e 1 ≠ v ∧ actualSite hs e 2 ≠ v := by
        constructor
        · exact actual_outer_away_retained hs ⟨i.val,hi⟩ ⟨t,ht⟩ (by dsimp [t]; omega) (e,0)
        · exact actual_outer_away_retained hs ⟨i.val,hi⟩ ⟨t,ht⟩ (by dsimp [t]; omega) (e,1)
      have hv := next_ordinary_degree N s hs hb (old s.1 (pairCount s.2.2.2) v)
      simp only [MediatorIteration.old_val] at hv
      change degree (next N s).2.1 v.val ≤ 1
      rw [hv]
      rw [qmaForkBackground_away_degree left right (actualSite hs) (actualSite_injective hs) v haway]
      rw [← degree_eq_graph]
      exact hd.port ⟨i.val,hi⟩ ⟨t,ht⟩

end ContinuumCoulomb.QuantumForkList

end

end OAI
