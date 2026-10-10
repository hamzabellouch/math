import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.RegularMap
import OAI.Combinatorics.KMedianRecovery.Sampling.PrefixData

namespace OAI

namespace MetricKMedianRecovery.PhaseCoupledMerge
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseCountCrossing PhaseMergeInvariant
universe uD uX
variable {D : Type uD} {X : Type uX} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

structure Coupled (loc : D → X) (F : Finset X) (v eta lo hi : ℝ) (q n k : ℕ) where
  B : Finset X
  P : List (List X)
  r : X → X
  lam : ℝ
  lam' : ℝ
  eps : ℝ
  a : ℕ
  b : ℕ
  disjoint : Disjoint F B
  low : lo ≤ lam
  high : lam' ≤ hi
  price : lam ≤ lam'
  eps_nonneg : 0 ≤ eps
  error : lam'-lam+(Fintype.card D:ℝ)*((1-3*v)*eps) ≤ (Fintype.card D:ℝ)*eta
  inj : Function.Injective r
  fixed : ∀ i ∈ F, r i = i
  shrink : ∀ j, ∀ x ∈ F ∪ B, dist (loc j) (r x) ≤ dist (loc j) x
  loss : ∀ j, ∀ x ∈ F ∪ B, dist (loc j) x ≤ dist (loc j) (r x)+eps
  old_prefix : PrefixData loc F B v lam eta q P
  new_prefix : PrefixData loc F (B.image r) v lam' eta q (P.map (List.map r))
  sandwich : Sandwich k a b
  new_tail : Attains loc F (B.image r) (after ∅ (P.map (List.map r))) v lam' q n a
  old_tail : Attains loc F B (after ∅ P) v lam q n b

omit [Fintype D] [PseudoMetricSpace X] in
lemma disjoint_map {F B : Finset X} {r : X → X} (hd : Disjoint F B)
    (hi : Function.Injective r) (hf : ∀ i ∈ F, r i = i) : Disjoint F (B.image r) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hy
  have hyx : y = x := hi (he.trans (hf x hx).symm)
  exact Finset.disjoint_left.mp hd hx (hyx ▸ hy)

lemma Coupled.zero_false {loc : D → X} {F : Finset X} {v eta lo hi : ℝ} {q k : ℕ}
    (h : Coupled loc F v eta lo hi q 0 k) : False := by
  have ha := attains_zero h.new_tail
  have hb := attains_zero h.old_tail
  have he := PhaseHistoryTransfer.after_map ∅ h.P h.r
  simp only [Finset.image_empty] at he
  rw [he,paid_image F (after ∅ h.P) h.r h.inj h.fixed] at ha
  have hab : h.a = h.b := ha.trans hb.symm
  have hs := h.sandwich
  unfold Sandwich at hs
  omega

noncomputable def same {loc : D → X} {F B : Finset X} {v lam eta lo hi : ℝ}
    {q n k a b : ℕ} {P : List (List X)} (heta : 0 ≤ eta)
    (hd : Disjoint F B) (hl : lo ≤ lam) (hu : lam ≤ hi)
    (hp : PrefixData loc F B v lam eta q P) (hs : Sandwich k a b)
    (ha : Attains loc F B (after ∅ P) v lam q n a)
    (hb : Attains loc F B (after ∅ P) v lam q n b) : Coupled loc F v eta lo hi q n k where
  B := B
  P := P
  r := id
  lam := lam
  lam' := lam
  eps := 0
  a := a
  b := b
  disjoint := hd
  low := hl
  high := hu
  price := le_rfl
  eps_nonneg := le_rfl
  error := by simp only [sub_self,mul_zero,add_zero]; positivity
  inj := Function.injective_id
  fixed := fun _ _ => rfl
  shrink := fun _ _ _ => le_rfl
  loss := fun _ _ _ => by simp only [id_eq,add_zero,le_refl]
  old_prefix := hp
  new_prefix := by simpa only [Finset.image_id,List.map_id_fun,List.map_id] using hp
  sandwich := hs
  new_tail := by simpa only [Finset.image_id,List.map_id_fun,List.map_id] using ha
  old_tail := hb

theorem advance {loc : D → X} {F : Finset X} {v eta lo hi : ℝ} {q n k : ℕ}
    (hv : 0 < v) (hvsmall : v < 1/6) (hlo : 0 < lo) (heta : 0 ≤ eta)
    (h : Coupled loc F v eta lo hi q (n+1) k) :
    Solved loc F v eta lo hi (q+(n+1)) k ∨
      Nonempty (Coupled loc F v eta lo hi (q+1) n k) ∨
      ∃ H G : List X,
        Valid loc F (h.B.image h.r) (after ∅ (h.P.map (List.map h.r)))
          v ((1+v^2)^q) h.lam' eta H ∧
        Valid loc F (h.B.image h.r) (after ∅ (h.P.map (List.map h.r)))
          v ((1+v^2)^q) h.lam' eta G ∧
        (∀ i ∈ H, i ∈ F) ∧ (∀ i ∈ G, i ∈ F) ∧
        ∃ c, Sandwich k h.a c ∧
          Attains loc F (h.B.image h.r)
            (after ∅ (h.P.map (List.map h.r)) ∪ H.toFinset) v h.lam' (q+1) n h.a ∧
          Attains loc F (h.B.image h.r)
            (after ∅ (h.P.map (List.map h.r)) ∪ G.toFinset) v h.lam' (q+1) n c := by
  have hlam : 0 < h.lam := hlo.trans_le h.low
  have hlam' : 0 < h.lam' := hlam.trans_le h.price
  have hd := disjoint_map h.disjoint h.inj h.fixed
  obtain ⟨H,hH,hHr,ha⟩ := PhaseMergeInvariant.Attains.split h.new_tail
  obtain ⟨G,hG,hGr,hb⟩ := PhaseMergeInvariant.Attains.split h.old_tail
  obtain ⟨hG',c,hc,hcases⟩ := PhaseParameterAlignment.align loc F h.B (after ∅ h.P)
    G h.r v h.lam h.lam' eta h.eps q n k h.a h.b hv hvsmall hlam h.eps_nonneg
    h.price h.error h.inj h.fixed h.old_prefix.after_subset h.shrink h.loss
    h.old_prefix.row hG hGr h.sandwich
  have hafter : (after ∅ h.P).image h.r = after ∅ (h.P.map (List.map h.r)) := by
    simpa only [Finset.image_empty] using (PhaseHistoryTransfer.after_map ∅ h.P h.r).symm
  rw [hafter] at hG' hc
  have hfree : (G.toFinset \ F).card ≤ 3 := by
    have hh : G.toFinset ⊆ F := fun i hi => hGr i (List.mem_toFinset.mp hi)
    simp only [Finset.sdiff_eq_empty_iff_subset.mpr hh,Finset.card_empty,Nat.zero_le]
  have hpn := h.new_prefix.append_phase hv hvsmall hlam' G hG' hfree
  rcases hcases with hck | hac | hcb
  · apply Or.inl
    have hf := hpn.finish hv hvsmall hlam' heta hd (h.low.trans h.price) h.high
      (n := n) (by simpa only [after_append,after] using hck ▸ hc)
    simpa only [Nat.add_assoc,Nat.add_comm 1 n] using hf
  · exact Or.inr (Or.inr ⟨H,G,⟨PhaseMergeSurgery.prefix_exact_eta hH.1 heta,hH.2⟩,
      hG',hHr,hGr,c,hac,ha,hc⟩)
  · apply Or.inr ∘ Or.inl
    have hpo := h.old_prefix.append_phase hv hvsmall hlam G
      ⟨PhaseMergeSurgery.prefix_exact_eta hG.1 heta,hG.2⟩ hfree
    have he : (h.P++[G]).map (List.map h.r) = h.P.map (List.map h.r)++[G] := by
      simp only [List.map_append,List.map_cons,List.map_nil,
        PhaseParameterAlignment.regular_map_eq F G h.r h.fixed hGr]
    refine ⟨{ h with
      P := h.P++[G]
      a := c
      old_prefix := hpo
      new_prefix := ?_
      sandwich := hcb
      new_tail := ?_
      old_tail := ?_ }⟩
    · simpa only [he] using hpn
    · simpa only [he,after_append,after] using hc
    · simpa only [after_append,after] using hb

end MetricKMedianRecovery.PhaseCoupledMerge

end OAI
