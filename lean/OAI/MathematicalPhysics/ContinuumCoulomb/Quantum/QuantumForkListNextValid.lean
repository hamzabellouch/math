import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListNextPorts

namespace OAI

/-! Every literal fork round keeps the active ports distinct from one another
and from the original centers. Fresh ports use the injective prefix index;
retained ports inherit the preceding round's separation. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList

theorem nextGroup_bounded {n : ℕ} {gs : Groups} (h : ValidPorts n gs) (R : ℚ)
    (i j : ℕ) (hi : i < gs.length) (hj : j < (nextGroup n R gs i).length) :
    (portAt (nextGroup n R gs i) j).1 < n+2*pairCount gs := by
  rw [nextGroup_length] at hj
  by_cases hf : j < (groupAt gs i).length/2
  · rw [nextGroup_portAt_fresh n R gs i j hf]
    have := fresh_index_lt gs i j hi hf
    dsimp only
    omega
  · have ho := retained_index_lt (groupAt gs i).length j hj (by omega)
    rw [nextGroup_portAt_retained n R gs i j (by omega)]
    have := h.bounded ⟨i,hi⟩ ⟨_,ho⟩
    dsimp only at this
    omega

theorem nextGroup_disjoint {n : ℕ} {gs : Groups} (h : ValidPorts n gs) (R : ℚ)
    (k i j : ℕ) (hk : k < gs.length) (hi : i < gs.length)
    (hj : j < (nextGroup n R gs i).length) :
    k ≠ (portAt (nextGroup n R gs i) j).1 := by
  rw [nextGroup_length] at hj
  by_cases hf : j < (groupAt gs i).length/2
  · rw [nextGroup_portAt_fresh n R gs i j hf]
    have := h.centers
    dsimp only
    omega
  · have ho := retained_index_lt (groupAt gs i).length j hj (by omega)
    rw [nextGroup_portAt_retained n R gs i j (by omega)]
    exact h.disjoint ⟨k,hk⟩ ⟨i,hi⟩ ⟨_,ho⟩

theorem nextGroup_injective {n : ℕ} {gs : Groups} (h : ValidPorts n gs) (R : ℚ)
    (i k j l : ℕ) (hi : i < gs.length) (hk : k < gs.length)
    (hj : j < (nextGroup n R gs i).length)
    (hl : l < (nextGroup n R gs k).length)
    (he : (portAt (nextGroup n R gs i) j).1=
      (portAt (nextGroup n R gs k) l).1) : i=k ∧ j=l := by
  rw [nextGroup_length] at hj hl
  by_cases hf : j < (groupAt gs i).length/2
  · rw [nextGroup_portAt_fresh n R gs i j hf] at he
    by_cases hg : l < (groupAt gs k).length/2
    · rw [nextGroup_portAt_fresh n R gs k l hg] at he
      have hp : pairIndex gs ⟨⟨i,hi⟩,⟨j,hf⟩⟩=
          pairIndex gs ⟨⟨k,hk⟩,⟨l,hg⟩⟩ := by
        apply Fin.ext
        dsimp only [pairIndex]
        dsimp only at he
        omega
      have hv := congrArg (fun p : LocalPair gs => (p.1.val,p.2.val))
        (pairIndex_injective gs hp)
      exact Prod.mk.inj hv
    · have ho := retained_index_lt (groupAt gs k).length l hl (by omega)
      rw [nextGroup_portAt_retained n R gs k l (by omega)] at he
      have hb := h.bounded ⟨k,hk⟩ ⟨_,ho⟩
      dsimp only at he hb
      omega
  · have ho := retained_index_lt (groupAt gs i).length j hj (by omega)
    rw [nextGroup_portAt_retained n R gs i j (by omega)] at he
    by_cases hg : l < (groupAt gs k).length/2
    · rw [nextGroup_portAt_fresh n R gs k l hg] at he
      have hb := h.bounded ⟨i,hi⟩ ⟨_,ho⟩
      dsimp only at he hb
      omega
    · have hp := retained_index_lt (groupAt gs k).length l hl (by omega)
      rw [nextGroup_portAt_retained n R gs k l (by omega)] at he
      have hh := h.injective ⟨i,hi⟩ ⟨k,hk⟩ ⟨_,ho⟩ ⟨_,hp⟩ he
      have hik : i=k := congrArg Fin.val hh.1
      refine ⟨hik,?_⟩
      subst k
      dsimp only at hh
      omega

theorem next_validPorts (N : ℚ) (s : State) (h : ValidPorts s.1 s.2.2.2) :
    ValidPorts (next N s).1 (next N s).2.2.2 := by
  constructor
  · rw [next_centers,next_count]
    exact le_trans h.centers (Nat.le_add_right _ _)
  · intro i j
    have hi : i.val < s.2.2.2.length := by simpa only [next_centers] using i.isLt
    have hj : j.val < (nextGroup s.1 (scale N s) s.2.2.2 i.val).length := by
      simpa only [next,next_groupAt _ _ _ _ hi] using j.isLt
    change (portAt (groupAt ((List.range s.2.2.2.length).map
      (nextGroup s.1 (scale N s) s.2.2.2)) i.val) j.val).1 < _
    rw [next_groupAt _ _ _ _ hi]
    exact nextGroup_bounded h (scale N s) i.val j.val hi hj
  · intro i k j
    have hi : i.val < s.2.2.2.length := by simpa only [next_centers] using i.isLt
    have hk : k.val < s.2.2.2.length := by simpa only [next_centers] using k.isLt
    have hj : j.val < (nextGroup s.1 (scale N s) s.2.2.2 k.val).length := by
      simpa only [next,next_groupAt _ _ _ _ hk] using j.isLt
    change i.val ≠ (portAt (groupAt ((List.range s.2.2.2.length).map
      (nextGroup s.1 (scale N s) s.2.2.2)) k.val) j.val).1
    rw [next_groupAt _ _ _ _ hk]
    exact nextGroup_disjoint h (scale N s) i.val k.val j.val hi hk hj
  · intro i k j l he
    have hi : i.val < s.2.2.2.length := by simpa only [next_centers] using i.isLt
    have hk : k.val < s.2.2.2.length := by simpa only [next_centers] using k.isLt
    have hj : j.val < (nextGroup s.1 (scale N s) s.2.2.2 i.val).length := by
      simpa only [next,next_groupAt _ _ _ _ hi] using j.isLt
    have hl : l.val < (nextGroup s.1 (scale N s) s.2.2.2 k.val).length := by
      simpa only [next,next_groupAt _ _ _ _ hk] using l.isLt
    change (portAt (groupAt ((List.range s.2.2.2.length).map
      (nextGroup s.1 (scale N s) s.2.2.2)) i.val) j.val).1=
      (portAt (groupAt ((List.range s.2.2.2.length).map
      (nextGroup s.1 (scale N s) s.2.2.2)) k.val) l.val).1 at he
    rw [next_groupAt _ _ _ _ hi,next_groupAt _ _ _ _ hk] at he
    obtain ⟨hik,hjl⟩ := nextGroup_injective h (scale N s) i.val k.val j.val l.val
      hi hk hj hl he
    exact ⟨Fin.ext hik,hjl⟩

theorem iterate_validPorts (N : ℚ) (s : State) (h : ValidPorts s.1 s.2.2.2)
    (k : ℕ) : ValidPorts (iterate N k s).1 (iterate N k s).2.2.2 := by
  induction k with
  | zero => exact h
  | succ k ih => exact next_validPorts N _ ih

end ContinuumCoulomb.QuantumForkList

end

end OAI
