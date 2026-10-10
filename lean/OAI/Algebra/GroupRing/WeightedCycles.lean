import Mathlib

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.WeightedCycles
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} {u v : V}

/-- Expanded length, attached to undirected edges. -/
def weight (w : Sym2 V → ℝ) (p : G.Walk u v) : ℝ := (p.edges.map w).sum

@[simp] theorem weight_nil (w : Sym2 V → ℝ) (u : V) : weight w (G := G) (Walk.nil : G.Walk u u) = 0 := rfl
@[simp] theorem weight_cons (w : Sym2 V → ℝ) {a b c : V} (h : G.Adj a b)
    (p : G.Walk b c) : weight w (Walk.cons h p) = w s(a,b) + weight w p := rfl
@[simp] theorem weight_append (w : Sym2 V → ℝ) {a b c : V}
    (p : G.Walk a b) (q : G.Walk b c) : weight w (p.append q) = weight w p + weight w q := by
  simp [weight]
@[simp] theorem weight_reverse (w : Sym2 V → ℝ) (p : G.Walk u v) :
    weight w p.reverse = weight w p := by simp [weight]

theorem weight_nonneg (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e) (p : G.Walk u v) :
    0 ≤ weight w p := by
  induction p with
  | nil => simp
  | cons h p ih => exact add_nonneg (hw _) ih

theorem weight_le_of_subwalk (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    {a b : V} {p : G.Walk u v} {q : G.Walk a b} (h : p.IsSubwalk q) :
    weight w p ≤ weight w q := by
  obtain ⟨l,r,rfl⟩ := h
  simp only [weight_append]
  linarith [weight_nonneg w hw l,weight_nonneg w hw r]

/-- A nonbacktracking walk with a repeated vertex contains a cycle of no
greater weight. Zero weights are permitted. -/
theorem reduced_not_path_cycle (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    (r : G.Walk u v) (hrr : r.edges.IsChain (· ≠ ·)) (hn : ¬r.IsPath) :
    ∃ (a : V) (c : G.Walk a a), c.IsCycle ∧ weight w c ≤ weight w r := by
  classical
  induction r with
  | nil => exact False.elim (hn (by simp))
  | @cons a b c h r ih =>
    have hcc := List.isChain_cons.mp (Walk.edges_cons _ _ ▸ hrr)
    by_cases hpath : r.IsPath
    · have hh : a ∈ r.support := by
        by_contra hh
        exact hn (Walk.cons_isPath_iff h r |>.mpr ⟨hpath,hh⟩)
      have hz : 0 < r.length := by
        by_contra hz
        have hrnil := Walk.length_eq_zero_iff.mp (by omega : r.length = 0)
        have he : a = b := by simpa [Walk.nil_iff_support_eq.mp hrnil] using hh
        exact h.ne he
      have hc : (Walk.cons h (r.takeUntil a hh)).IsCycle := by
        simp only [Walk.isCycle_def,Walk.isTrail_def,Walk.edges_cons,List.nodup_cons,
          ne_eq,reduceCtorEq,not_false_eq_true,Walk.support_cons,List.tail_cons,true_and]
        have ht : (Walk.cons h (r.takeUntil a hh)).support.tail.Nodup :=
          r.isPath_def.mp hpath |>.sublist <| List.IsInfix.sublist
            ⟨[],(r.dropUntil a hh).support.tail,by simp [← Walk.support_append]⟩
        refine ⟨⟨?_,Walk.edges_nodup_of_support_nodup ht⟩,ht⟩
        by_contra he
        refine hcc.1 s(a,b) ?_ rfl
        rw [← r.cons_tail_eq (by simp [Walk.not_nil_iff_lt_length,hz])]
        have hh' := Walk.IsPath.mk' ht |>.eq_snd_of_mem_edges (Sym2.eq_swap ▸ he)
        simp [hh',Walk.snd_takeUntil h.ne]
      refine ⟨a,_,hc,?_⟩
      simpa only [weight_cons] using
        (add_le_add (le_refl (w s(a,b))) (weight_le_of_subwalk w hw (r.isSubwalk_takeUntil hh)))
    · obtain ⟨a',c',hc',hle⟩ := ih hcc.2 hpath
      exact ⟨a',c',hc',by rw [weight_cons]; linarith [hw s(a,b)]⟩
  
/-- A nonbacktracking walk lighter than every cycle has no repeated vertex. -/
theorem reduced_isPath_of_weight_lt (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    (L : ℝ) (hG : ∀ a (c : G.Walk a a), c.IsCycle → L ≤ weight w c)
    (p : G.Walk u v) (hp : weight w p < L) (hred : p.edges.IsChain (· ≠ ·)) :
    p.IsPath := by
  by_contra hn
  obtain ⟨a,c,hc,hle⟩ := reduced_not_path_cycle w hw p hred hn
  exact hp.not_ge ((hG a c hc).trans hle)

/-- Two distinct immersed walks having the same endpoints contain a cycle
whose expanded length is no greater than their combined expanded length. -/
theorem distinct_reduced_cycle (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    (p q : G.Walk u v) (hne : p ≠ q)
    (hp : p.edges.IsChain (· ≠ ·)) (hq : q.edges.IsChain (· ≠ ·)) :
    ∃ (a : V) (c : G.Walk a a), c.IsCycle ∧ weight w c ≤ weight w p + weight w q := by
  classical
  by_cases hpp : p.IsPath
  · by_cases hqq : q.IsPath
    · obtain ⟨a,b,p',q',hsubp,hsubq,hc⟩ := hpp.exists_isCycle_of_ne hqq hne
      exact ⟨a,p'.append q'.reverse,hc,by
        simp only [weight_append,weight_reverse]
        exact add_le_add (weight_le_of_subwalk w hw hsubp) (weight_le_of_subwalk w hw hsubq)⟩
    · obtain ⟨a,c,hc,hle⟩ := reduced_not_path_cycle w hw q hq hqq
      exact ⟨a,c,hc,by linarith [weight_nonneg w hw p]⟩
  · obtain ⟨a,c,hc,hle⟩ := reduced_not_path_cycle w hw p hp hpp
    exact ⟨a,c,hc,by linarith [weight_nonneg w hw q]⟩

end TorsionFreeZeroDivisors.WeightedCycles
namespace TorsionFreeZeroDivisors.WeightedMoore
open scoped BigOperators

/-- A chain of `k+1` directed edges, including chains of zero probability. -/
@[reducible] def Chain (D : Type*) : ℕ → Type _
  | 0 => D
  | k+1 => D × Chain D k

instance {D : Type*} [Fintype D] (k : ℕ) : Fintype (Chain D k) := by
  induction k with
  | zero => exact inferInstanceAs (Fintype D)
  | succ k ih => exact inferInstanceAs (Fintype (D × Chain D k))

def head {D : Type*} : {k : ℕ} → Chain D k → D
  | 0, p => p
  | _+1, p => p.1

def last {D : Type*} : {k : ℕ} → Chain D k → D
  | 0, p => p
  | _+1, p => last p.2

def cost {D : Type*} (len : D → ℝ) : {k : ℕ} → Chain D k → ℝ
  | 0, p => len p
  | _+1, p => len p.1 + cost len p.2

def mass {D : Type*} [Fintype D] (T : D → D → ℝ) : {k : ℕ} → Chain D k → ℝ
  | 0, _ => 1 / Fintype.card D
  | _+1, p => T p.1 (head p.2) * mass T p.2

variable {D : Type*} [Fintype D] (T : D → D → ℝ)

/-- A doubly stochastic transition rule, with no entry exceeding one half. -/
structure Transition : Prop where
  nonneg : ∀ d e, 0 ≤ T d e
  row_sum : ∀ d, ∑ e, T d e = 1
  col_sum : ∀ e, ∑ d, T d e = 1
  half : ∀ d e, T d e ≤ 1/2

variable {T}

theorem mass_nonneg (ht : Transition T) {k : ℕ} (p : Chain D k) :
    0 ≤ mass T p := by
  induction k with
  | zero => exact one_div_nonneg.mpr (Nat.cast_nonneg _)
  | succ k ih => exact mul_nonneg (ht.nonneg _ _) (ih p.2)

/-- Stationarity of uniform directed-edge measure, proved by finite summation. -/
theorem head_expectation (ht : Transition T) (k : ℕ) (f : D → ℝ) :
    ∑ p : Chain D k, mass T p * f (head p) = (∑ d, f d) / Fintype.card D := by
  induction k generalizing f with
  | zero =>
    change (∑ p : D, (1 / Fintype.card D) * f p) = _
    rw [← Finset.mul_sum]
    ring
  | succ k ih =>
    change (∑ p : D × Chain D k, T p.1 (head p.2) * mass T p.2 * f p.1) = _
    rw [Fintype.sum_prod_type]
    have he (d : D) :
        (∑ q : Chain D k, T d (head q) * mass T q * f d) = f d / Fintype.card D := by
      have hi := ih (fun e => T d e)
      rw [ht.row_sum] at hi
      calc
        _ = (∑ q : Chain D k, mass T q * T d (head q)) * f d := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro q _
          ring
        _ = _ := by rw [hi]; ring
    simp_rw [he]
    exact (Finset.sum_div _ _ _).symm

theorem mass_sum [Nonempty D] (ht : Transition T) (k : ℕ) :
    ∑ p : Chain D k, mass T p = 1 := by
  simpa [Fintype.card_ne_zero] using head_expectation ht k (fun _ => (1:ℝ))

theorem cost_expectation (ht : Transition T) (k : ℕ) (len : D → ℝ) :
    ∑ p : Chain D k, mass T p * cost len p =
      (k+1:ℝ) * (∑ d, len d) / Fintype.card D := by
  induction k with
  | zero => simpa [cost,head] using head_expectation ht 0 len
  | succ k ih =>
    change (∑ p : D × Chain D k,
      (T p.1 (head p.2)*mass T p.2)*(len p.1+cost len p.2)) = _
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    have hf := head_expectation ht (k+1) len
    change (∑ p : D × Chain D k,
      T p.1 (head p.2)*mass T p.2*len p.1) = _ at hf
    rw [hf]
    have hs : (∑ p : D × Chain D k,
        T p.1 (head p.2)*mass T p.2*cost len p.2) =
        ∑ q : Chain D k, mass T q * cost len q := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q _
      calc
        _ = (∑ d, T d (head q)) * (mass T q * cost len q) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro d _
          ring
        _ = _ := by rw [ht.col_sum]; ring
    rw [hs,ih]
    push_cast
    ring

theorem mass_upper (ht : Transition T) {k : ℕ} (p : Chain D k) :
    mass T p ≤ (1 / Fintype.card D) * (1/2:ℝ)^k := by
  induction k with
  | zero => simp [mass]
  | succ k ih =>
    change T p.1 (head p.2)*mass T p.2 ≤ _
    calc
      _ ≤ (1/2:ℝ)*((1 / Fintype.card D)*(1/2:ℝ)^k) :=
        mul_le_mul (ht.half _ _) (ih p.2) (mass_nonneg ht p.2) (by norm_num)
      _ = _ := by rw [pow_succ]; ring

/-- Finite Markov without probability-space infrastructure: at least half the
mass has cost at most twice the expectation; zero-mass chains are irrelevant. -/
theorem short_mass {P : Type*} [Fintype P] (w c : P → ℝ)
    (hw : ∀ p, 0 ≤ w p) (hc : ∀ p, 0 ≤ c p)
    (hs : ∑ p, w p = 1) (B : ℝ) (hB : 0 < B)
    (hm : ∑ p, w p*c p ≤ B) :
    1/2 ≤ ∑ p ∈ Finset.univ.filter (fun p => c p ≤ 2*B ∧ 0 < w p), w p := by
  classical
  let S := Finset.univ.filter (fun p => c p ≤ 2*B ∧ 0 < w p)
  have hl : 2*B * (1 - ∑ p ∈ S, w p) ≤ B := by
    have hp : ∑ p ∈ Finset.univ \ S, w p = 1 - ∑ p ∈ S, w p := by
      have ht := Finset.sum_sdiff (f := w) (Finset.subset_univ S)
      rw [hs] at ht
      linarith
    rw [← hp, Finset.mul_sum]
    calc
      _ ≤ ∑ p ∈ Finset.univ \ S, w p*c p := by
        apply Finset.sum_le_sum
        intro p hp
        have hnot : ¬(c p ≤ 2*B ∧ 0 < w p) := by
          simpa [S] using (Finset.mem_sdiff.mp hp).2
        by_cases hz : w p = 0
        · simp [hz]
        · have hpos : 0 < w p := lt_of_le_of_ne (hw p) (Ne.symm hz)
          have hcp : 2*B < c p := lt_of_not_ge (fun h => hnot ⟨h,hpos⟩)
          nlinarith [mul_nonneg (hw p) (sub_nonneg.mpr hcp.le)]
      _ ≤ ∑ p, w p*c p := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.sdiff_subset) (fun p _ _ => mul_nonneg (hw p) (hc p))
      _ ≤ B := hm
  change 1/2 ≤ ∑ p ∈ S, w p
  nlinarith

omit [Fintype D] in
theorem cost_nonneg (len : D → ℝ) (hlen : ∀ d, 0 ≤ len d) {k : ℕ}
    (p : Chain D k) : 0 ≤ cost len p := by
  induction k with
  | zero => exact hlen p
  | succ k ih => exact add_nonneg (hlen p.1) (ih p.2)

/-- Entropy forces many short nonzero-probability nonbacktracking chains. -/
theorem many_short_chains [Nonempty D] (ht : Transition T) (k : ℕ)
    (len : D → ℝ) (hlen : ∀ d, 0 < len d) :
    ∃ S : Finset (Chain D k),
      (∀ p ∈ S, cost len p ≤ 2*(k+1:ℝ)*(∑ d, len d)/Fintype.card D ∧
        0 < mass T p) ∧
      (Fintype.card D : ℝ)*(2:ℝ)^k ≤ 2*S.card := by
  classical
  let B : ℝ := (k+1:ℝ)*(∑ d, len d)/Fintype.card D
  have hD : (0:ℝ) < Fintype.card D := Nat.cast_pos.mpr Fintype.card_pos
  have hs : 0 < ∑ d, len d := Finset.sum_pos (fun d _ => hlen d) Finset.univ_nonempty
  have hB : 0 < B := div_pos (mul_pos (by positivity) hs) hD
  have hc : ∀ p : Chain D k, 0 ≤ cost len p := cost_nonneg len (fun d => (hlen d).le)
  let S := Finset.univ.filter (fun p : Chain D k => cost len p ≤ 2*B ∧ 0 < mass T p)
  have hm : 1/2 ≤ ∑ p ∈ S, mass T p :=
    short_mass (mass T) (cost len) (mass_nonneg ht) hc (mass_sum ht k) B hB
      (cost_expectation ht k len).le
  refine ⟨S,?_,?_⟩
  · intro p hp
    have hp' := (Finset.mem_filter.mp hp).2
    refine ⟨?_,hp'.2⟩
    calc
      _ ≤ 2*B := hp'.1
      _ = _ := by dsimp [B]; ring
  · have hm' : (∑ p ∈ S, mass T p) ≤
        S.card*((1/Fintype.card D)*(1/2:ℝ)^k) := by
      calc
        _ ≤ ∑ _p ∈ S, (1/Fintype.card D)*(1/2:ℝ)^k :=
          Finset.sum_le_sum (fun p _ => mass_upper ht p)
        _ = _ := by simp
    have powpos : 0 < (2:ℝ)^k := pow_pos (by norm_num) _
    have hp : (1/2:ℝ)^k = 1/(2:ℝ)^k := by rw [one_div_pow]
    rw [hp] at hm'
    have he : (S.card:ℝ)*((1/Fintype.card D)*(1/(2:ℝ)^k)) =
        S.card/((Fintype.card D:ℝ)*(2:ℝ)^k) := by ring
    rw [he] at hm'
    have h := (le_div_iff₀ (mul_pos hD powpos)).mp (hm.trans hm')
    linarith

/-- More short chains than ordered endpoint pairs forces a collision. This uses
actual chains and their probabilities, not a hypothesis asserting path growth. -/
theorem short_collision [Nonempty D] (ht : Transition T) (k : ℕ)
    (len : D → ℝ) (hlen : ∀ d, 0 < len d)
    (hbig : 2*(Fintype.card D : ℝ) < (2:ℝ)^k) :
    ∃ p q : Chain D k, p ≠ q ∧ head p = head q ∧ last p = last q ∧
      0 < mass T p ∧ 0 < mass T q ∧
      cost len p + cost len q ≤ 4*(k+1:ℝ)*(∑ d, len d)/Fintype.card D := by
  classical
  obtain ⟨S,hS,hcard⟩ := many_short_chains ht k len hlen
  have hD : (0:ℝ) < Fintype.card D := Nat.cast_pos.mpr Fintype.card_pos
  have hlt : (Fintype.card D : ℝ)^2 < S.card := by
    have hmul := mul_lt_mul_of_pos_left hbig hD
    nlinarith
  have hn : (Finset.univ : Finset (D × D)).card < S.card := by
    simp only [Finset.card_univ,Fintype.card_prod]
    rw [pow_two] at hlt
    exact_mod_cast hlt
  obtain ⟨p,hp,q,hq,hne,he⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hn
    (f := fun p : Chain D k => (head p,last p)) (fun _ _ => Finset.mem_univ _)
  refine ⟨p,q,hne,(Prod.mk.inj he).1,(Prod.mk.inj he).2,(hS p hp).2,(hS q hq).2,?_⟩
  have hp' := (hS p hp).1
  have hq' := (hS q hq).1
  calc
    _ ≤ _ := add_le_add hp' hq'
    _ = _ := by ring

/-- An explicit logarithmic number of transitions suffices. -/
theorem logarithmic_short_collision [Nonempty D] (ht : Transition T)
    (len : D → ℝ) (hlen : ∀ d, 0 < len d) :
    let k := Nat.log 2 (Fintype.card D) + 2
    ∃ p q : Chain D k, p ≠ q ∧ head p = head q ∧ last p = last q ∧
      0 < mass T p ∧ 0 < mass T q ∧
      cost len p + cost len q ≤ 4*(k+1:ℝ)*(∑ d, len d)/Fintype.card D := by
  apply short_collision ht _ len hlen
  have hn := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (Fintype.card D)
  have hn' : (Fintype.card D : ℝ) < (2:ℝ)^(Nat.log 2 (Fintype.card D)+1) := by
    exact_mod_cast hn
  rw [show Nat.log 2 (Fintype.card D)+2 = (Nat.log 2 (Fintype.card D)+1)+1 by omega,
    pow_succ]
  linarith

namespace PortWalk

variable {V : Type*} (origin : D → V) (rev : D → D)
    (hinv : Function.Involutive rev)

open scoped Classical

def out (v : V) : Finset D := Finset.univ.filter (fun d => origin d = v)
def choices (v : V) : ℕ := (out origin v).card - 1

def step (d e : D) : Prop := origin (rev d) = origin e ∧ e ≠ rev d

def transition (d e : D) : ℝ :=
  if step origin rev d e then 1 / (choices origin (origin e) : ℝ) else 0

theorem succ_eq (d : D) :
    Finset.univ.filter (step origin rev d) = (out origin (origin (rev d))).erase (rev d) := by
  ext e
  simp [step,out,and_comm,eq_comm]

theorem succ_card (d : D) :
    (Finset.univ.filter (step origin rev d)).card = choices origin (origin (rev d)) := by
  rw [succ_eq,Finset.card_erase_of_mem (by simp [out])]
  rfl

include hinv

theorem pred_eq (e : D) :
    Finset.univ.filter (fun d => step origin rev d e) =
      ((out origin (origin e)).erase e).image rev := by
  ext d
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,
    Finset.mem_image,Finset.mem_erase]
  constructor
  · intro h
    refine ⟨rev d,⟨Ne.symm h.2,?_⟩,hinv d⟩
    simpa [out] using h.1
  · rintro ⟨a,⟨ha,hoa⟩,rfl⟩
    change origin (rev (rev a)) = origin e ∧ e ≠ rev (rev a)
    rw [hinv a]
    refine ⟨?_,Ne.symm ha⟩
    simpa [out] using hoa

theorem pred_card (e : D) :
    (Finset.univ.filter (fun d => step origin rev d e)).card = choices origin (origin e) := by
  rw [pred_eq origin rev hinv, Finset.card_image_of_injective _ hinv.injective,
    Finset.card_erase_of_mem (by simp [out])]
  rfl

/-- The actual nonbacktracking chain on ports of a multigraph is stationary
on uniformly chosen darts, including loops and parallel edges. -/
theorem transition_law (hdeg : ∀ d, 3 ≤ (out origin (origin d)).card) :
    Transition (transition origin rev) := by
  have hchoice (d : D) : (2:ℝ) ≤ choices origin (origin d) := by
    have h := hdeg d
    have : 2 ≤ choices origin (origin d) := by dsimp [choices]; omega
    exact_mod_cast this
  have hpos (d : D) : (0:ℝ) < choices origin (origin d) := lt_of_lt_of_le (by norm_num) (hchoice d)
  refine ⟨?_,?_,?_,?_⟩
  · intro d e
    unfold transition
    split <;> positivity
  · intro d
    have he : (∑ e, transition origin rev d e) =
        ∑ e ∈ Finset.univ.filter (step origin rev d),
          1 / (choices origin (origin (rev d)) : ℝ) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro e _
      unfold transition
      split_ifs with h
      · rw [h.1]
      · rfl
    rw [he]
    simp only [Finset.sum_const, nsmul_eq_mul, succ_card]
    exact mul_one_div_cancel (ne_of_gt (hpos (rev d)))
  · intro e
    change (∑ d, if step origin rev d e then _ else 0) = 1
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const,nsmul_eq_mul,pred_card origin rev hinv]
    exact mul_one_div_cancel (ne_of_gt (hpos e))
  · intro d e
    unfold transition
    split
    · exact one_div_le_one_div_of_le (by norm_num) (hchoice e)
    · norm_num

end PortWalk

end TorsionFreeZeroDivisors.WeightedMoore

end

end OAI
