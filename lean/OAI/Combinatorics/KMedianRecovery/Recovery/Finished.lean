import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Coupled
import OAI.Combinatorics.KMedianRecovery.Recovery.Data

namespace OAI

namespace MetricKMedianRecovery.PhaseGeometricMerge
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseCountCrossing PhaseMergeInvariant
  PhaseMergeRefinement
universe uD uX uY
variable {D : Type uD} {X : Type uX} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

def Finished (loc : D → X) (F : Finset X) (v eta lo hi : ℝ) (total k : ℕ) (U : ℝ) : Prop :=
  ∃ B lam P, Nonempty (PhaseLeafGeometry.Data loc F B U) ∧ Disjoint F B ∧ lo ≤ lam ∧ lam ≤ hi ∧
    PrefixData loc F B v lam eta total P ∧ ((after ∅ P) ∩ F).card = k

def Solved (loc : D → X) (F : Finset X) (v eta lo hi : ℝ) (total k : ℕ) (U : ℝ) : Prop :=
  ∃ (Y : Type uX) (m : PseudoMetricSpace Y) (d : DecidableEq Y) (e : X ↪ Y),
    letI := m
    letI := d
    (∀ x y, dist (e x) (e y) = dist x y) ∧
      Finished (fun j => e (loc j)) (F.image e) v eta lo hi total k U

lemma Solved.of_finished {loc : D → X} {F : Finset X} {v eta lo hi U : ℝ} {total k : ℕ}
    (h : Finished loc F v eta lo hi total k U) : Solved loc F v eta lo hi total k U := by
  refine ⟨X,inferInstance,inferInstance,Function.Embedding.refl X,fun _ _ => rfl,?_⟩
  change Finished loc (F.image (fun x => x)) v eta lo hi total k U
  have he : F.image (fun x => x) = F := by ext x; simp
  rw [he]
  exact h

omit [DecidableEq X] in
lemma Solved.pullback {Y : Type uX} [PseudoMetricSpace Y] [DecidableEq Y]
    {loc : D → X} {F : Finset X} {v eta lo hi U : ℝ} {total k : ℕ}
    (e : X ↪ Y) (he : ∀ x y, dist (e x) (e y) = dist x y)
    (h : Solved (fun j => e (loc j)) (F.image e) v eta lo hi total k U) :
    Solved loc F v eta lo hi total k U := by
  obtain ⟨Z,m,d,g,hg,hf⟩ := h
  let : PseudoMetricSpace Z := m
  let : DecidableEq Z := d
  refine ⟨Z,m,d,e.trans g,?_,?_⟩
  · intro x y
    exact (hg (e x) (e y)).trans (he x y)
  · change Finished (fun j => g (e (loc j))) (F.image (fun x => g (e x)))
      v eta lo hi total k U
    simpa only [Finset.image_image,Function.comp_def] using hf

lemma finish {loc : D → X} {F B : Finset X} {v lam eta lo hi U : ℝ}
    {q n k : ℕ} {P : List (List X)} (h : PrefixData loc F B v lam eta q P)
    (hv : 0 < v) (hvsmall : v < 1/6) (hlam : 0 < lam) (heta : 0 ≤ eta)
    (hdis : Disjoint F B) (hlow : lo ≤ lam) (hupp : lam ≤ hi)
    (d : PhaseLeafGeometry.Data loc F B U)
    (hk : Attains loc F B (after ∅ P) v lam q n k) :
    Solved loc F v eta lo hi (q+n) k U := by
  obtain ⟨T,hT,hh,hr,hc⟩ := hk
  apply Solved.of_finished
  refine ⟨B,lam,P++T,⟨d⟩,hdis,hlow,hupp,?_,?_⟩
  · simpa only [hT] using h.append_exact hv hvsmall hlam heta T hh hr
  · simpa only [after_append] using hc

structure Coupled (loc : D → X) (F : Finset X) (v eta lo hi : ℝ) (q n k : ℕ) (U : ℝ)
    extends PhaseCoupledMerge.Coupled loc F v eta lo hi q n k where
  old_geometry : PhaseLeafGeometry.Data loc F B U
  new_geometry : PhaseLeafGeometry.Data loc F (B.image r) U

noncomputable def same {loc : D → X} {F B : Finset X} {v lam eta lo hi U : ℝ}
    {q n k a b : ℕ} {P : List (List X)} (heta : 0 ≤ eta)
    (hd : Disjoint F B) (hl : lo ≤ lam) (hu : lam ≤ hi)
    (hp : PrefixData loc F B v lam eta q P) (d : PhaseLeafGeometry.Data loc F B U)
    (hs : Sandwich k a b)
    (ha : Attains loc F B (after ∅ P) v lam q n a)
    (hb : Attains loc F B (after ∅ P) v lam q n b) : Coupled loc F v eta lo hi q n k U where
  toCoupled := PhaseCoupledMerge.same heta hd hl hu hp hs ha hb
  old_geometry := d
  new_geometry := by simpa only [PhaseCoupledMerge.same,Finset.image_id] using d

theorem advance {loc : D → X} {F : Finset X} {v eta lo hi U : ℝ} {q n k : ℕ}
    (hv : 0 < v) (hvsmall : v < 1/6) (hlo : 0 < lo) (heta : 0 ≤ eta)
    (h : Coupled loc F v eta lo hi q (n+1) k U) :
    Solved loc F v eta lo hi (q+(n+1)) k U ∨
      Nonempty (Coupled loc F v eta lo hi (q+1) n k U) ∨
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
  have hd := PhaseCoupledMerge.disjoint_map h.disjoint h.inj h.fixed
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
    have hf := finish hpn hv hvsmall hlam' heta hd (h.low.trans h.price) h.high h.new_geometry
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

end MetricKMedianRecovery.PhaseGeometricMerge

end OAI
