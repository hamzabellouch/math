import OAI.Analysis.PlanarPacking.HalfGapCore
import OAI.Analysis.PlanarPacking.TailEnvelope

namespace OAI

namespace SharpPlanar
noncomputable def headData (a : Bool) : CardinalData :=
  let p:=exactData a
  ⟨p.C,p.c₀,p.d₀,p.x-tailList p.x 40⟩
lemma headData_zero (a : Bool) (n : Node) (hn : 40<n.val) (d : Bool) :
    (headData a).x (n,d)=0 := by
  simp only [headData,lp.coeFn_sub,Pi.sub_apply,tailList_apply,hn,ite_true,sub_self]
lemma exactJet_split (a : Bool) (ell : ℕ) (s : ℝ) :
    exactJet a ell s=cardinalSeries (headData a) ell s+tailErrorJet a ell s := by
  have hh := cardinalSeries_sub (p := exactData a) (q := headData a) rfl rfl rfl ell s
  have he:(exactData a).x-(headData a).x=tailList (exactList a) 40 := by
    simp only [headData,exactData_x]; abel
  rw [he] at hh
  change cardinalSeries (exactData a) ell s-cardinalSeries (headData a) ell s=
    cardinalSeries (tailData a) ell s at hh
  unfold exactJet tailErrorJet
  linarith
lemma headData_jets (a : Bool) (n : Node) (hn : 40<n.val) :
    cardinalSeries (headData a) 0 n.val=0 ∧ cardinalSeries (headData a) 1 n.val=0 := by
  have hh:=cardinal_jets (headData a) n
  rw [headData_zero a n hn false,headData_zero a n hn true] at hh
  simp only [mul_zero,add_zero] at hh
  rw [cardinal_eq_cardinalSeries] at hh
  rw [(cardinal_hasDerivAt (headData a) n.val).deriv] at hh
  exact hh
lemma tailErrorJet_node (a : Bool) (n : Node) (hn : 40<n.val) :
    tailErrorJet a 0 n.val=0 ∧ tailErrorJet a 1 n.val=0 := by
  have hv:=exactJet_node_zero a n
  have hd:=exactJet_node_first a n (Or.inl (by omega))
  rw [exactJet_split,(headData_jets a n hn).1,zero_add] at hv
  rw [exactJet_split,(headData_jets a n hn).2,zero_add] at hd
  exact ⟨hv,hd⟩
lemma tailErrorJet_bound (a : Bool) (n : Node) (hn : 40<n.val)
    {s : ℝ} (hs : (83:ℝ)/2 ≤ s) (hm : (83:ℝ)/2 ≤ n.val) :
    |tailErrorJet a 0 s| ≤ (3:ℝ)/1000*(s-n.val)^2 := by
  have hh:=jetTaylor_error (tailErrorJet_deriv a) 1 (n.val:ℝ) (s-n.val) ((6:ℝ)/1000)
    (fun t ht => (tail_second_bound a (by
      have hlow: (83:ℝ)/2 ≤ min (n.val:ℝ) (n.val+(s-n.val)) := by
        apply le_min hm; simpa using hs
      exact hlow.trans ht.1)).le)
  simp only [jetTaylor,Finset.sum_range_succ,Finset.sum_range_zero,
    (tailErrorJet_node a n hn).1,(tailErrorJet_node a n hn).2,zero_div,
    zero_mul,zero_add,sub_zero,Nat.reduceAdd,Nat.factorial,Nat.cast_one,
    sq_abs] at hh
  have he : (n.val:ℝ)+(s-n.val)=s := by ring
  rw [he] at hh
  convert hh using 1
  ring
end SharpPlanar

end OAI
