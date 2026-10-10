import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.LeafBracket

namespace OAI

namespace MetricKMedianRecovery.PhaseMergeIteration
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseCountCrossing PhaseMergeInvariant
  PhaseMergeRefinement PhaseCoupledMerge PhaseLeafCoupling
universe uD uX

def Claim (D : Type uD) [Fintype D] (v eta lo hi : ℝ) (M : ℚ) (k n : ℕ) : Prop :=
  ∀ (X : Type uX) [PseudoMetricSpace X] [DecidableEq X] (loc : D → X) (F : Finset X) (q : ℕ),
    F.Nonempty → (∀ i ∈ F, ∀ j, dist i (loc j) ≤ (M:ℝ)) →
    Coupled loc F v eta lo hi q n k → Solved loc F v eta lo hi (q+n) k

variable {D : Type uD} {X : Type uX} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

omit [Fintype D] [DecidableEq X] in
lemma diameter_map {Y : Type uX} [PseudoMetricSpace Y] [DecidableEq Y]
    (e : X ↪ Y) (he : ∀ x y, dist (e x) (e y) = dist x y)
    {loc : D → X} {F : Finset X} {M : ℝ}
    (hd : ∀ i ∈ F, ∀ j, dist i (loc j) ≤ M) :
    ∀ i ∈ F.image e, ∀ j, dist i (e (loc j)) ≤ M := by
  intro i hi j
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hi
  rw [he]
  exact hd x hx j

theorem outcome_solved {loc : D → X} {F B : Finset X} {v lam eta lo hi : ℝ}
    {M : ℚ} {q n k N : ℕ} {P : List (List X)}
    (ih : Claim.{uD,uX} D v eta lo hi M k n)
    (hv : 0 < v) (hvsmall : v < 1/6) (hlam : 0 < lam) (heta : 0 ≤ eta)
    (hprec : (1:ℝ)/2^(N+1) ≤ eta) (hM : 0 < M) (hN : 3 ≤ N)
    (hhi : hi ≤ 8*N*(M:ℝ)) (hF : F.Nonempty)
    (hdiam : ∀ i ∈ F, ∀ j, dist i (loc j) ≤ (M:ℝ))
    (hd : Disjoint F B) (hl : lo ≤ lam) (hu : lam ≤ hi)
    (hp : PrefixData loc F B v lam eta q P)
    (ho : Outcome loc F B (after ∅ P) v lam eta q n k) :
    Solved loc F v eta lo hi (q+(n+1)) k := by
  rcases ho with hsuccess | hcommon | hsensitive
  · obtain ⟨H,hH,hk⟩ := hsuccess
    have hp' := hp.append_phase hv hvsmall hlam H hH.1 (by have hf := hH.2; omega)
    have hs := hp'.finish hv hvsmall hlam heta hd hl hu
      (n := n) (by simpa only [after_append,after] using hk)
    simpa only [Nat.add_assoc,Nat.add_comm 1 n] using hs
  · obtain ⟨H,hH,a,b,hs,ha,hb⟩ := hcommon
    have hp' := hp.append_phase hv hvsmall hlam H hH.1 (by have hf := hH.2; omega)
    have hc := same heta hd hl hu hp' hs
      (n := n) (by simpa only [after_append,after] using ha)
      (by simpa only [after_append,after] using hb)
    simpa only [Nat.add_assoc,Nat.add_comm 1 n] using ih X loc F (q+1) hF hdiam hc
  · obtain ⟨root,_,H,hH,hcases⟩ := PhaseSensitiveCrossing.sensitive_search loc F B (after ∅ P)
      v lam eta q n k N M hF hM hN hv hvsmall hlam (hu.trans hhi) hp.after_subset
      hd hdiam hp.row hsensitive
    rcases hcases with ⟨s,_,_,hc⟩ | ⟨l,u,hl0,hlu,_,hw,a,b,hs,ha,hb⟩
    · exact leaf_success hp hv hvsmall hlam heta hd hl hu root H hH s hc
    · classical
      let : PseudoMetricSpace (X ⊕ ℝ) := FreshCopyEndpoints.familyMetric root
      have hcast : ((u-l:ℚ):ℝ) ≤ ((1/(2:ℚ)^(N+1):ℚ):ℝ) := Rat.cast_le.mpr hw
      have hwr : (u:ℝ)-(l:ℝ) ≤ (1:ℝ)/2^(N+1) := by
        push_cast at hcast
        exact hcast
      let hc := leaf_bracket hp hv hvsmall hlam hd hl hu root H hH l u hl0 hlu
        (hwr.trans hprec) hs ha hb
      have hx := ih (X ⊕ ℝ) (fun j => FreshCopyEndpoints.incl (loc j))
        (F.image FreshCopyEndpoints.incl) (q+1) (hF.image _)
        (diameter_map FreshCopyEndpoints.incl (FreshCopyEndpoints.original_dist root) hdiam) hc
      have hx' := Solved.pullback FreshCopyEndpoints.incl (FreshCopyEndpoints.original_dist root) hx
      simpa only [Nat.add_assoc,Nat.add_comm 1 n] using hx'

theorem crossing_solved {loc : D → X} {F B : Finset X} {v lam eta lo hi : ℝ}
    {M : ℚ} {q n k N a b : ℕ} {P : List (List X)}
    (ih : Claim.{uD,uX} D v eta lo hi M k n)
    (hv : 0 < v) (hvsmall : v < 1/6) (hlam : 0 < lam) (heta : 0 ≤ eta)
    (hprec : (1:ℝ)/2^(N+1) ≤ eta) (hM : 0 < M) (hN : 3 ≤ N)
    (hhi : hi ≤ 8*N*(M:ℝ)) (hF : F.Nonempty)
    (hdiam : ∀ i ∈ F, ∀ j, dist i (loc j) ≤ (M:ℝ))
    (hd : Disjoint F B) (hl : lo ≤ lam) (hu : lam ≤ hi)
    (hp : PrefixData loc F B v lam eta q P)
    (H G : List X) (hH : Valid loc F B (after ∅ P) v ((1+v^2)^q) lam eta H)
    (hG : Valid loc F B (after ∅ P) v ((1+v^2)^q) lam eta G)
    (hHr : ∀ i ∈ H, i ∈ F) (hGr : ∀ i ∈ G, i ∈ F) (hs : Sandwich k a b)
    (ha : Attains loc F B (after ∅ P ∪ H.toFinset) v lam (q+1) n a)
    (hb : Attains loc F B (after ∅ P ∪ G.toFinset) v lam (q+1) n b) :
    Solved loc F v eta lo hi (q+(n+1)) k := by
  classical
  let : PseudoMetricSpace (X ⊕ (X × Bool)) := PhaseFreshAllocation.enlargedMetric
  let e : X ↪ X ⊕ (X × Bool) := PhaseFreshAllocation.incl
  let Fc := F.image e
  let Bc := PhaseMergePath.pool Fc
    (PhaseMergePath.pool Fc (B.image e) (PhaseFreshAllocation.copy false)) (PhaseFreshAllocation.copy true)
  have hBs : B.image e ⊆ Bc :=
    (PhaseMergePath.subset_pool Fc (B.image e) (PhaseFreshAllocation.copy false)).trans
      (PhaseMergePath.subset_pool Fc _ (PhaseFreshAllocation.copy true))
  have hdc : Disjoint Fc Bc := PhaseCountCrossing.disjoint_pool _ _ _
    (PhaseCountCrossing.disjoint_pool _ _ _ (PhaseFreshAllocation.disjoint_image F B hd)
      (fun i hi => PhaseFreshAllocation.copy_fresh F B i hi false))
    (PhaseFreshAllocation.spare_fresh F B)
  have hp' := (hp.map e PhaseFreshAllocation.original_dist).mono_free hBs
  have ho := PhaseFreshAllocation.allocated_crossing loc F B (after ∅ P) v lam eta q n k a b
    hv hvsmall hlam heta hp.after_subset hd hp.row H G hH hG hHr hGr hs ha hb
  have he := HistoryIsometry.after_map e (∅ : Finset X) P
  simp only [Finset.image_empty] at he
  have ho' : Outcome (fun j => e (loc j)) Fc Bc (after ∅ (P.map (List.map e)))
      v lam eta q n k := by rw [he]; exact ho
  have hx := outcome_solved ih hv hvsmall hlam heta hprec hM hN hhi (hF.image e)
    (diameter_map e PhaseFreshAllocation.original_dist hdiam) hdc hl hu hp' ho'
  exact Solved.pullback e PhaseFreshAllocation.original_dist hx

theorem solve (v eta lo hi : ℝ) (M : ℚ) (k N : ℕ)
    (hv : 0 < v) (hvsmall : v < 1/6) (hlo : 0 < lo) (heta : 0 ≤ eta)
    (hprec : (1:ℝ)/2^(N+1) ≤ eta) (hM : 0 < M) (hN : 3 ≤ N)
    (hhi : hi ≤ 8*N*(M:ℝ)) (n : ℕ) : Claim.{uD,uX} D v eta lo hi M k n := by
  induction n with
  | zero =>
    intro Y m d loc F q hF hdiam hc
    exact hc.zero_false.elim
  | succ n ih =>
    intro Y m d loc F q hF hdiam hc
    rcases advance hv hvsmall hlo heta hc with hs | ⟨hc'⟩ | ⟨H,G,hH,hG,hHr,hGr,c,hs,ha,hb⟩
    · exact hs
    · obtain ⟨hc'⟩ := hc'
      simpa only [Nat.add_assoc,Nat.add_comm 1 n] using ih Y loc F (q+1) hF hdiam hc'
    · exact crossing_solved ih hv hvsmall ((hlo.trans_le hc.low).trans_le hc.price) heta
        hprec hM hN hhi hF hdiam (disjoint_map hc.disjoint hc.inj hc.fixed)
        (hc.low.trans hc.price) hc.high hc.new_prefix H G hH hG hHr hGr hs ha hb

end MetricKMedianRecovery.PhaseMergeIteration

end OAI
