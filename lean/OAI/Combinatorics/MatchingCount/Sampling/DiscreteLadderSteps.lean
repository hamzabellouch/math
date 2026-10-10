import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.Sym2Order

namespace OAI

namespace MatchingFPRAS.Transport

open Finset Replica Replica.Ladder Variation

def discreteLadderSteps (N D K T m : ℕ) : ℕ :=
  20*ladderL N D*ladderM N D T*(ladderLambda N D K T+Nat.clog 2 m+1)

lemma discreteLadderSteps_eq (N D K T m : ℕ) :
    discreteLadderSteps N D K T m=ladderSteps N D K T ((m:ℝ)⁻¹) := by
  simp only [discreteLadderSteps,ladderSteps,inv_inv]
  rw [show (2:ℝ)=(2:ℕ) by norm_cast,Real.natCeil_logb_natCast]

variable {V L : Type*} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]

variable {bags : V → Finset L} {G : SimpleGraph L}

attribute [local instance] sym2Order bagEdgeOrder bagEdgeFintype UnitRefresh.Computable.allowedDec

noncomputable local instance : DecidableEq (BagPM bags) := Classical.decEq _

attribute [local instance] prodOrder sumOrder

variable (hbags : ∀ v,∀ a∈bags v,∀ b∈bags v,a=b ∨ G.Adj a b) (hG : G.IsAcyclic)

variable (rank : L → ℕ) (parent : L → Option L)

variable (hb : UnitRefresh.RankedBags bags rank parent) (hne : ∀ v,(bags v).Nonempty)

variable (hp : ∀ l p,parent l=some p → rank p<rank l)

def finiteLadder (D K T m : ℕ) (hq : 0<ladderQ (Fintype.card V) D)
    (w : BagEdge bags → ℚ) (M : BagPM bags) (η : ℚ)
    (s : Slot T (ladderQ (Fintype.card V) D) → BagPM bags) :
    (Fin (discreteLadderSteps (Fintype.card V) D K T m * scanBitCount (Fintype.card V)
      (bitPrecision (discreteLadderSteps (Fintype.card V) D K T m *
        scanErrorNumerator V L bags T (ladderQ (Fintype.card V) D)) η)) → Bool) →
        Slot T (ladderQ (Fintype.card V) D) → BagPM bags :=
  ladderBitRun hbags hG rank parent hb hne hp hq w M
    (bitPrecision (discreteLadderSteps (Fintype.card V) D K T m *
      scanErrorNumerator V L bags T (ladderQ (Fintype.card V) D)) η)
    (discreteLadderSteps (Fintype.card V) D K T m) s

lemma finiteLadder_tv (height : L → ℝ) (hheight : ∀ l,0<height l)
    (hstep : ∀ a b,G.Adj a b → height a≤2*height b)
    (D K : ℕ) (hD : 1≤D) (hN : 2≤Fintype.card V) (w : BagEdge bags → ℚ)
    (hw : ∀ e,height e.color / D ≤ (w e:ℝ) ∧ (w e:ℝ)≤3*height e.color)
    (hglobal : ∀ e,(D:ℝ)⁻¹≤(w e:ℝ) ∧ (w e:ℝ)≤3*4^K)
    (M : BagPM bags) (T m : ℕ) (hm : 1 < m) (η : ℚ) (hη : 0<η)
    (hq : 0<ladderQ (Fintype.card V) D)
    (s : Slot T (ladderQ (Fintype.card V) D) → BagPM bags) :
    tv (imageLaw (finiteLadder hbags hG rank parent hb hne hp D K T m hq w M η s))
      (ladderLaw (fun e=>(w e:ℝ)) T (ladderQ (Fintype.card V) D)) ≤ (η:ℝ)+(m:ℝ)⁻¹ := by
  have hm' : (1:ℝ)<(m:ℝ) := by exact_mod_cast hm
  have hi:=ideal_ladder_sampling hbags hG height hheight hstep D K hD hN
    (fun e=>(w e:ℝ)) hw hglobal M T s ((m:ℝ)⁻¹) (by positivity) (by exact inv_lt_one_of_one_lt₀ hm')
  rw [←discreteLadderSteps_eq] at hi
  have hb:=ladderBitRun_walk_tv hbags hG rank parent hb hne hp hq w M
    (discreteLadderSteps (Fintype.card V) D K T m) η hη s
  exact (tv_triangle _ _ _).trans (add_le_add hb hi)

end MatchingFPRAS.Transport

namespace MatchingFPRAS.BottleneckAlgorithm

open Finset MatchingFPRAS.Switching

variable {V : Type*} [Fintype V] [LinearOrder V]

variable {α : Type*} [LinearOrder α] [OfNat α 1]

def edge (w : V → V → α) (a b : V) : α := if a<b then w a b else w b a

def seed (w : V → V → α) (a b : V) : α := if a=b then 1 else max 1 (edge w a b)

def advance (w : V → V → α) (a b : V) : α :=
  if a=b then 1 else max (w a b)
    (univ.sup' ⟨a,mem_univ a⟩ fun c => min (w a c) (w c b))

def close (w : V → V → α) : ℕ → V → V → α
  | 0 => seed w
  | k+1 => advance (close w k)

@[simp] lemma close_diag (w : V → V → α) (k : ℕ) (a : V) : close w k a a=1 := by
  cases k <;> simp [close,seed,advance]

lemma close_one (w : V → V → α) (k : ℕ) (a b : V) : 1≤close w k a b := by
  induction k with
  | zero =>
    by_cases hab : a=b
    · simp [close,seed,hab]
    · simp [close,seed,hab]
  | succ k ih =>
    by_cases h : a=b
    · subst b; simp
    · exact ih.trans (by simp [close,advance,h])

lemma close_mono_step (w : V → V → α) (k : ℕ) (a b : V) :
    close w k a b≤close w (k+1) a b := by
  by_cases h : a=b
  · subst b; simp
  · simp [close,advance,h]

lemma close_mono (w : V → V → α) (a b : V) : Monotone (fun k=>close w k a b) :=
  monotone_nat_of_le_succ (fun k=>close_mono_step w k a b)

lemma edge_le_close (w : V → V → α) (k : ℕ) (a b : V) (hab : a≠b) :
    edge w a b≤close w k a b := by
  have h : edge w a b≤close w 0 a b := by
    simp [close,seed,hab]
  exact h.trans (close_mono w a b (Nat.zero_le k))

lemma via_le_close (w : V → V → α) (k : ℕ) (a b c : V) (hab : a≠b) :
    min (close w k a c) (close w k c b)≤close w (k+1) a b := by
  exact (le_sup' (fun c=>min (close w k a c) (close w k c b)) (mem_univ c)).trans
    (by simp [close,advance,hab])

lemma chain_le_close (w : V → V → α) (t : α) (a b : V) (L : List V)
    (hab : a≠b) (hc : List.IsChain (fun x y=>t≤edge w x y) (a::L))
    (hn : (a::L).Nodup) (hb : b∈L) : t≤close w L.length a b := by
  induction L generalizing a with
  | nil => simp at hb
  | cons c cs ih =>
    rcases List.isChain_cons_cons.mp hc with ⟨hac,hc⟩
    have han := List.nodup_cons.mp hn
    have hne : a≠c := by intro h; apply han.1; simp [h]
    rcases List.mem_cons.mp hb with rfl|hb
    · exact hac.trans (edge_le_close w _ _ _ hne)
    · have hcb : c≠b := by
        intro he
        exact (List.nodup_cons.mp han.2).1 (he ▸ hb)
      have hh := ih c hcb hc han.2 hb
      change t≤close w (cs.length+1) a b
      exact (le_min (hac.trans (edge_le_close w cs.length a c hne)) hh).trans
        (via_le_close w cs.length a b c hab)

lemma close_le (w B : V → V → α) (_hdiag : ∀ a,B a a=1) (hone : ∀ a b,1≤B a b)
    (hedge : ∀ a b,a≠b → edge w a b≤B a b)
    (htri : ∀ a b c,a≠b → a≠c → b≠c → min (B a c) (B c b)≤B a b)
    (k : ℕ) (a b : V) : close w k a b≤B a b := by
  induction k generalizing a b with
  | zero =>
    by_cases hab : a=b
    · subst b; simpa [close,seed] using hone a a
    · simpa [close,seed,hab] using max_le (hone a b) (hedge a b hab)
  | succ k ih =>
    by_cases hab : a=b
    · subst b; simpa using hone a a
    · change (if a=b then 1 else _)≤_
      rw [ite_eq_right hab]
      apply max_le (ih a b)
      apply sup'_le
      intro c _
      by_cases hac : a=c
      · subst c
        rw [close_diag]
        exact (min_le_left _ _).trans (hone a b)
      by_cases hbc : b=c
      · subst c
        rw [close_diag]
        exact (min_le_right _ _).trans (hone a b)
      exact (min_le_min (ih a c) (ih c b)).trans (htri a b c hab hac hbc)

theorem real_close_eq (w : V → V → ℝ) (a b : V) :
    close w (Fintype.card V) a b=bottleneck w a b := by
  apply le_antisymm
  · exact close_le w (bottleneck w) (by intro a; simp [bottleneck])
      (one_le_bottleneck w) (edgeActivity_le_bottleneck w) (bottleneck_ultrametric w) _ _ _
  · by_cases hab : a=b
    · subst b; simp [bottleneck]
    by_cases ht : 1<bottleneck w a b
    · obtain ⟨L,hL,hnd,hb⟩ := bottleneck_path w a b hab ht
      have hlen := hnd.length_le_card
      have h := chain_le_close w (bottleneck w a b) a b L hab hL hnd hb
      exact h.trans (close_mono w a b (by simpa using (show L.length≤Fintype.card V from by simpa using (Nat.le_of_succ_le hlen))))
    · exact (le_of_not_gt ht).trans (close_one w _ _ _)

lemma cast_close (w : V → V → ℚ) (k : ℕ) (a b : V) :
    ((close w k a b : ℚ) : ℝ)=close (fun x y => (w x y : ℝ)) k a b := by
  induction k generalizing a b with
  | zero =>
    unfold close seed edge
    split_ifs <;> simp [Rat.cast_max]
  | succ k ih =>
    simp only [close,advance]
    split_ifs with hab
    · simp
    · have hh := Finset.apply_sup'_eq_sup'_comp (s:=(univ:Finset V))
        (f:=fun c=>min (close w k a c) (close w k c b)) ⟨a,mem_univ a⟩
        (fun x : ℚ => (x : ℝ)) (by intro x y; exact Rat.cast_max x y)
      rw [Rat.cast_max]
      apply congrArg₂ max (ih a b)
      calc
        _ = _ := hh
        _ = _ := by
          apply Finset.sup'_congr _ rfl
          intro c _
          simp [Rat.cast_min,ih]

theorem rational_close_eq (w : V → V → ℚ) (a b : V) :
    ((close w (Fintype.card V) a b : ℚ) : ℝ)=bottleneck (fun x y=>(w x y:ℝ)) a b := by
  rw [cast_close,real_close_eq]

end MatchingFPRAS.BottleneckAlgorithm

end OAI
