import Mathlib
import OAI.Probability.Contingency.OuterAccuracy

namespace OAI

/-! Greedy Table. -/

noncomputable section


open scoped BigOperators
namespace Contingency

 
def marginPrefix {m : ℕ} (r : Fin m → ℕ) (t : ℕ) : ℕ :=
  ∑ i, if i.val < t then r i else 0

@[simp] theorem marginPrefix_zero {m : ℕ} (r : Fin m → ℕ) : marginPrefix r 0=0 := by
  simp [marginPrefix]

@[simp] theorem marginPrefix_total {m : ℕ} (r : Fin m → ℕ) : marginPrefix r m=∑ i,r i := by
  simp [marginPrefix]

theorem marginPrefix_mono {m : ℕ} (r : Fin m → ℕ) : Monotone (marginPrefix r) := by
  intro a b hab
  apply Finset.sum_le_sum
  intro i _
  by_cases ha : i.val < a
  · simp only [ite_eq_left ha,ite_eq_left (ha.trans_le hab)]
    exact le_rfl
  · simp only [ite_eq_right ha]
    exact Nat.zero_le _

theorem marginPrefix_succ {m : ℕ} (r : Fin m → ℕ) (i : Fin m) :
    marginPrefix r (i.val+1)=marginPrefix r i.val+r i := by
  have he : (fun j : Fin m => if j.val < i.val+1 then r j else 0)=
      fun j => (if j.val < i.val then r j else 0)+(if j=i then r i else 0) := by
    funext j
    by_cases h : j=i
    · subst j; simp
    · have hj : j.val≠i.val := fun hv => h (Fin.ext hv)
      by_cases hji : j.val < i.val
      · simp [h,hji,show j.val < i.val+1 by omega]
      · simp [h,hji,show ¬ j.val < i.val+1 by omega]
  unfold marginPrefix
  rw [he,Finset.sum_add_distrib]
  simp

 
def intervalOverlap (a b c d : ℕ) : ℕ := min b d-max a c

theorem intervalOverlap_symm (a b c d : ℕ) :
    intervalOverlap a b c d=intervalOverlap c d a b := by
  simp [intervalOverlap,min_comm,max_comm]

theorem intervalOverlap_increment (a b c d : ℕ) (hab : a≤b) (hcd : c≤d) :
    intervalOverlap a b c d+(min a d-min a c)=min b d-min b c := by
  unfold intervalOverlap
  omega

theorem prefix_increments_sum {n : ℕ} (c : Fin n → ℕ) (a : ℕ) :
    (∑ j : Fin n, (min a (marginPrefix c (j.val+1))-min a (marginPrefix c j.val)))=
      min a (∑ j,c j) := by
  rw [Fin.sum_univ_eq_sum_range (fun t => min a (marginPrefix c (t+1))-min a (marginPrefix c t)) n]
  have hm : Monotone (fun t => min a (marginPrefix c t)) := by
    intro x y hxy
    exact min_le_min_left a (marginPrefix_mono c hxy)
  simpa using Finset.sum_range_tsub hm n

 

def greedyEntries {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (i : Fin m) (j : Fin n) : ℕ :=
  intervalOverlap (marginPrefix r i.val) (marginPrefix r (i.val+1))
    (marginPrefix c j.val) (marginPrefix c (j.val+1))

theorem greedyEntries_row {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (hrc : (∑ i,r i)=∑ j,c j) (i : Fin m) : ∑ j,greedyEntries r c i j=r i := by
  have hs := Finset.sum_congr (s₁:=Finset.univ) (g:=fun j : Fin n =>
    min (marginPrefix r (i.val+1)) (marginPrefix c (j.val+1))-
      min (marginPrefix r (i.val+1)) (marginPrefix c j.val)) rfl
    (fun j _ => intervalOverlap_increment (marginPrefix r i.val)
      (marginPrefix r (i.val+1)) (marginPrefix c j.val) (marginPrefix c (j.val+1))
      (marginPrefix_mono r (Nat.le_succ _)) (marginPrefix_mono c (Nat.le_succ _)))
  rw [Finset.sum_add_distrib,prefix_increments_sum,prefix_increments_sum,← hrc] at hs
  have ha : marginPrefix r i.val ≤ ∑ i,r i := by
    rw [← marginPrefix_total r]
    exact marginPrefix_mono r i.isLt.le
  have hb : marginPrefix r (i.val+1) ≤ ∑ i,r i := by
    rw [← marginPrefix_total r]
    exact marginPrefix_mono r i.isLt
  rw [min_eq_left ha,min_eq_left hb] at hs
  change (∑ j,greedyEntries r c i j)+marginPrefix r i.val=marginPrefix r (i.val+1) at hs
  have hi := marginPrefix_succ r i
  omega

theorem greedyEntries_col {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (hrc : (∑ i,r i)=∑ j,c j) (j : Fin n) : ∑ i,greedyEntries r c i j=c j := by
  have he : (fun i => greedyEntries r c i j)=fun i => greedyEntries c r j i := by
    funext i
    exact intervalOverlap_symm _ _ _ _
  rw [he]
  exact greedyEntries_row c r hrc.symm j

def greedyTable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (hrc : (∑ i,r i)=∑ j,c j) : Tables r c :=
  ⟨greedyEntries r c,greedyEntries_row r c hrc,greedyEntries_col r c hrc⟩

end Contingency

 

 

open scoped BigOperators
namespace Contingency.PaddedGraph
noncomputable section
variable {m n : ℕ} (U L : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)

 

def greedyCompletion (hrc : (∑ i,r i)=∑ j,c j) (X : GraphState U r c) :
    Completion U L r c (graphUnderlying U r c X) := by
  have hf := graph_feasible U r c X
  have ht : (∑ i,rowNat U L r c (graphUnderlying U r c X) i)=
      ∑ j,colNat U L r c (graphUnderlying U r c X) j := by
    apply Int.ofNat_inj.mp
    push_cast
    simp only [rowNat_cast U L r c _ hf,colNat_cast U L r c _ hf]
    exact residual_totals U L r c X hrc
  exact tableCompletion U L r c _ hf (greedyTable _ _ ht)

 
def positiveLargeEquiv {m : ℕ} (U : ℕ) (r : Fin m → ℕ) (h : ∃ i,U≤r i) :
    Fin ((Fintype.card {i // U≤r i}-1)+1) ≃ {i // U≤r i} := by
  letI : Nonempty {i // U≤r i} := ⟨⟨h.choose,h.choose_spec⟩⟩
  have hp : 0 < Fintype.card {i // U≤r i} := Fintype.card_pos
  exact (Fintype.orderIsoFinOfCardEq _ (by omega)).toEquiv

section positive
variable (hm : 0 < m) (hn : 0 < n) (hrc : (∑ i,r i)=∑ j,c j) (k : ℕ)
local notation "d" => Parameters.dim m n
local notation "b" => Parameters.bits m n (∑ i,r i)
local notation "C" => Parameters.cap m n (∑ i,r i)
local instance greedyCanonicalTablesFintype : Fintype (Tables r c) := Fintype.ofFinite _
local notation "hdims" => Parameters.dimensions hm hn

 

def canonicalDraw : DyadicLaw (Tables r c) := by
  classical
  letI : Nonempty (GraphState (d^20) r c) := graph_nonempty _ r c hrc
  let Z := greedyTable r c hrc
  let X₀ : GraphState (d^20) r c := Sum.inl (initialTransversal _ r c Z)
  let fs := greedyCompletion (d^20) (d^12) r c hrc
  by_cases he : EmptyBlock (d^20) r c
  · exact emptyOuter d b k r c hdims.1 hdims.2.2.2 fs X₀ Z
  · have hlarge : ∃ w : Cell m n,IsLarge (d^20) r c w := by
      simpa only [EmptyBlock,IsSmall,not_forall,not_not] using he
    have hr : ∃ i,d^20≤r i := ⟨hlarge.choose.1,hlarge.choose_spec.1⟩
    have hc : ∃ j,d^20≤c j := ⟨hlarge.choose.2,hlarge.choose_spec.2⟩
    exact literalOuter d b k C r c (positiveLargeEquiv _ r hr) (positiveLargeEquiv _ c hc)
      hrc hdims.1 hdims.2.1 hdims.2.2.1 hdims.2.2.2
      (Parameters.paddedRow_le_cap r c) (by have := Parameters.cap_pow_bits m n (∑ i,r i); omega) fs X₀ Z

theorem canonicalDraw_bits : (canonicalDraw r c hm hn hrc k).bits=Schedule.R d b k := by
  classical
  let : Nonempty (GraphState (d^20) r c) := graph_nonempty _ r c hrc
  unfold canonicalDraw
  split_ifs
  · exact emptyOuter_bits _ _ _ _ _ _ _ _ _ _
  · exact literalOuter_bits _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem canonicalDraw_tv (hk : 1≤k) :
    letI := tables_nonempty r c hrc
    (canonicalDraw r c hm hn hrc k).toLaw.tv (Law.uniform (Tables r c)) ≤ (2:ℝ)^(-(k:ℤ)) := by
  classical
  let := tables_nonempty r c hrc
  let : Nonempty (GraphState (d^20) r c) := graph_nonempty _ r c hrc
  unfold canonicalDraw
  split_ifs with he
  · exact emptyOuter_tv d b k C r c he hrc hdims.1 hdims.2.1 hdims.2.2.1 hdims.2.2.2
      (Parameters.dimension_le_bits _ _ _) hk (Parameters.cap_pos _ _ _) (Parameters.threshold_le_cap _ _ _)
      (Parameters.paddedRow_le_cap r c) (Parameters.cap_pow_bits _ _ _) _ _ _
  · exact literalOuter_tv d b k C r c _ _ hrc hdims.1 hdims.2.1 hdims.2.2.1 hdims.2.2.2
      (Parameters.dimension_le_bits _ _ _) hk (Parameters.cap_pos _ _ _) (Parameters.threshold_le_cap _ _ _)
      (Parameters.paddedRow_le_cap r c) (Parameters.cap_pow_bits _ _ _) _ _ _

end positive
end
end Contingency.PaddedGraph

 

 

open scoped BigOperators
namespace Contingency
noncomputable section
namespace Law
variable {α : Type*} [Fintype α]

theorem point_tv (p q : Law α) (x : α) : |p.mass x-q.mass x|≤p.tv q := by
  classical
  let f := fun y => p.mass y-q.mass y
  have hz : (∑ y,f y)=0 := by simp [f,Finset.sum_sub_distrib,p.total,q.total]
  have he : (∑ y∈Finset.univ.erase x,f y)= -f x := by
    have hh := Finset.sum_erase_add (s:=Finset.univ) f (Finset.mem_univ x)
    rw [hz] at hh
    linarith
  have ha := Finset.abs_sum_le_sum_abs (s:=Finset.univ.erase x) (f:=f)
  rw [he,abs_neg] at ha
  have hh := Finset.sum_erase_add (s:=Finset.univ) (fun y => |f y|) (Finset.mem_univ x)
  change |f x|≤(∑ y,|f y|)/2
  linarith

 
theorem correction_domination [Nonempty α] (p : Law α) (δ : ℝ)
    (hδ0 : 0≤δ) (hδ1 : δ≤1) (hM : (Fintype.card α:ℝ)*δ≤1)
    (hTV : p.tv (uniform α)≤δ^2) (x : α) :
    (1-δ)*p.mass x≤1/(Fintype.card α:ℝ) := by
  have hN : (0:ℝ)<Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hp := (le_abs_self (p.mass x-(uniform α).mass x)).trans
    ((point_tv p (uniform α) x).trans hTV)
  change p.mass x-1/(Fintype.card α:ℝ)≤δ^2 at hp
  have hm : δ≤1/(Fintype.card α:ℝ) := (le_div_iff₀ hN).mpr (by nlinarith only [hM])
  have hh := mul_le_mul_of_nonneg_left hp (sub_nonneg.mpr hδ1)
  have hsq := sq_nonneg δ
  have hab := mul_le_mul_of_nonneg_left hm hδ0
  have hc := mul_nonneg hδ0 hsq
  nlinarith only [hh,hab,hc]

end Law

variable {α : Type*} [Fintype α] [Nonempty α]

def correctionCount (p : DyadicLaw α) (D : ℕ) (x : α) : ℕ :=
  (residualNumerator (Fintype.card α) p.bits D (p.count x)).toNat

theorem correction_integer_domination (p : DyadicLaw α) (D : ℕ)
    (hM : Fintype.card α≤2^D)
    (hTV : p.toLaw.tv (Law.uniform α)≤(2:ℝ)^(-((2*D:ℕ):ℤ))) (x : α) :
    (Fintype.card α:ℤ)*((2:ℤ)^D-1)*p.count x≤(2:ℤ)^(p.bits+D) := by
  have hδ0 : (0:ℝ)≤1/2^D := by positivity
  have hδ1 : (1:ℝ)/2^D≤1 := (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  have hm : (Fintype.card α:ℝ)*(1/2^D)≤1 := by
    rw [mul_one_div,div_le_one (by positivity)]
    exact_mod_cast hM
  have ht : p.toLaw.tv (Law.uniform α)≤((1:ℝ)/2^D)^2 := by
    convert hTV using 1
    rw [zpow_neg,zpow_natCast,show 2*D=D*2 by omega,pow_mul]
    simp [one_div,inv_pow]
  have hh := Law.correction_domination p.toLaw (1/2^D) hδ0 hδ1 hm ht x
  change (1-1/(2:ℝ)^D)*((p.count x:ℝ)/2^p.bits)≤1/(Fintype.card α:ℝ) at hh
  have hN : (0:ℝ)<Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hd : (0:ℝ)<2^D := by positivity
  have hr : (0:ℝ)<2^p.bits := by positivity
  have he : (1-1/(2:ℝ)^D)*((p.count x:ℝ)/2^p.bits)=
      (((2:ℝ)^D-1)*p.count x)/((2:ℝ)^D*2^p.bits) := by field_simp

  rw [he,div_le_div_iff₀ (mul_pos hd hr) hN] at hh
  have hh' : (Fintype.card α:ℝ)*((2:ℝ)^D-1)*p.count x≤(2:ℝ)^(p.bits+D) := by
    rw [pow_add]; nlinarith only [hh]
  exact_mod_cast hh'

theorem correction_counts (p : DyadicLaw α) (D : ℕ)
    (hM : Fintype.card α≤2^D)
    (hTV : p.toLaw.tv (Law.uniform α)≤(2:ℝ)^(-((2*D:ℕ):ℤ))) :
    (∀ x,(correctionCount p D x:ℤ)=residualNumerator (Fintype.card α) p.bits D (p.count x)) ∧
    (∑ x,correctionCount p D x)=Fintype.card α*2^p.bits := by
  have hh := residual_integers p.bits D p.count p.total
    (correction_integer_domination p D hM hTV)
  have hc : ∀ x,(correctionCount p D x:ℤ)=residualNumerator (Fintype.card α) p.bits D (p.count x) := by
    intro x; exact Int.toNat_of_nonneg (hh.1 x)
  refine ⟨hc,?_⟩
  have hs : (∑ x,(correctionCount p D x:ℤ))=(Fintype.card α:ℤ)*2^p.bits := by
    simp_rw [hc]; exact hh.2
  exact_mod_cast hs

def correctionLaw (p : DyadicLaw α) (D : ℕ)
    (hM : Fintype.card α≤2^D)
    (hTV : p.toLaw.tv (Law.uniform α)≤(2:ℝ)^(-((2*D:ℕ):ℤ))) : Law α where
  mass x := (correctionCount p D x:ℝ)/((Fintype.card α:ℝ)*2^p.bits)
  nonneg x := by positivity
  total := by
    rw [← Finset.sum_div]
    have hh : (∑ x,(correctionCount p D x:ℝ))=(Fintype.card α:ℝ)*2^p.bits := by
      exact_mod_cast (correction_counts p D hM hTV).2
    rw [hh]; exact div_self (by positivity)

 
theorem corrected_exact (p : DyadicLaw α) (D : ℕ)
    (hM : Fintype.card α≤2^D)
    (hTV : p.toLaw.tv (Law.uniform α)≤(2:ℝ)^(-((2*D:ℕ):ℤ))) (x : α) :
    (1-1/(2:ℝ)^D)*p.toLaw.mass x+
      (1/(2:ℝ)^D)*(correctionLaw p D hM hTV).mass x=
      (Law.uniform α).mass x := by
  have he : (correctionCount p D x:ℝ)=(2:ℝ)^(p.bits+D)-
      (Fintype.card α:ℝ)*((2:ℝ)^D-1)*p.count x := by
    exact_mod_cast (correction_counts p D hM hTV).1 x
  change (1-1/(2:ℝ)^D)*((p.count x:ℝ)/2^p.bits)+
    (1/(2:ℝ)^D)*((correctionCount p D x:ℝ)/((Fintype.card α:ℝ)*2^p.bits))=1/(Fintype.card α:ℝ)
  rw [he,pow_add]
  field_simp
  ring

end
end Contingency

 

 

open scoped BigOperators
namespace Contingency
namespace IntegerDraw
variable {α : Type*}

def total : List (α×ℕ) → ℕ
  | [] => 0
  | aw::xs => aw.2+total xs

 

def scan : List (α×ℕ) → ℕ → Option α
  | [], _ => none
  | aw::xs,z => if z<aw.2 then some aw.1 else scan xs (z-aw.2)

def weight [DecidableEq α] (xs : List (α×ℕ)) (a : α) : ℕ :=
  (xs.map (fun aw => if aw.1=a then aw.2 else 0)).sum

theorem scan_none_iff (xs : List (α×ℕ)) (z : ℕ) : scan xs z=none ↔ total xs≤z := by
  induction xs generalizing z with
  | nil => simp [scan,total]
  | cons aw xs ih =>
    simp only [scan,total]
    split_ifs with h
    · simp; omega
    · rw [ih]; omega

theorem scan_some_lt (xs : List (α×ℕ)) (z : ℕ) (a : α) (h : scan xs z=some a) :
    z<total xs := by
  by_contra hh
  have := (scan_none_iff xs z).mpr (by omega)
  rw [h] at this
  cases this

theorem scan_count [DecidableEq α] (xs : List (α×ℕ)) (a : α) :
    (∑ z∈Finset.range (total xs),if scan xs z=some a then 1 else 0)=weight xs a := by
  induction xs with
  | nil => simp [total,weight]
  | cons aw xs ih =>
    rw [total,Finset.sum_range_add]
    have hlo : (∑ z∈Finset.range aw.2,if scan (aw::xs) z=some a then 1 else 0)=
        if aw.1=a then aw.2 else 0 := by
      calc
        _ = ∑ _∈Finset.range aw.2,if aw.1=a then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro z hz
          have he : scan (aw::xs) z=some aw.1 := by simp [scan,Finset.mem_range.mp hz]
          rw [he]; simp
        _ = _ := by by_cases h : aw.1=a <;> simp [h]
    have hhi : (∑ z∈Finset.range (total xs),if scan (aw::xs) (aw.2+z)=some a then 1 else 0)=weight xs a := by
      simpa only [scan,show ∀ z,¬aw.2+z<aw.2 by omega,ite_false,Nat.add_sub_cancel_left] using ih
    rw [hlo,hhi]
    simp [weight]

theorem scan_count_padded [DecidableEq α] (xs : List (α×ℕ)) (a : α) (V : ℕ)
    (hV : total xs≤V) :
    (∑ z∈Finset.range V,if scan xs z=some a then 1 else 0)=weight xs a := by
  rw [← Nat.add_sub_of_le hV,Finset.sum_range_add,scan_count]
  have hz : (∑ z∈Finset.range (V-total xs),if scan xs (total xs+z)=some a then 1 else 0)=0 := by
    apply Finset.sum_eq_zero
    intro z _
    rw [(scan_none_iff xs _).mpr (by omega)]
    simp
  rw [hz,Nat.add_zero]

 
def trial [DecidableEq α] [Fintype α] (xs : List (α×ℕ)) (bits : ℕ) : DyadicLaw (Option α) :=
  (bitWordLaw bits).map (fun z => scan xs z.val)

theorem trial_count [DecidableEq α] [Fintype α] (xs : List (α×ℕ)) (bits : ℕ)
    (hb : total xs≤2^bits) (a : α) : (trial xs bits).count (some a)=weight xs a := by
  rw [trial,DyadicLaw.map_count]
  change (∑ z : Fin (2^bits),if scan xs z.val=some a then 1 else 0)=_
  rw [Fin.sum_univ_eq_sum_range (fun z : ℕ => if scan xs z=some a then 1 else 0) (2^bits)]
  exact scan_count_padded xs a _ hb

 
def visits : List (α×ℕ) → ℕ → ℕ
  | [],_ => 0
  | aw::xs,z => if z<aw.2 then 1 else 1+visits xs (z-aw.2)

theorem visits_le (xs : List (α×ℕ)) (z : ℕ) : visits xs z≤xs.length := by
  induction xs generalizing z with
  | nil => simp [visits]
  | cons aw xs ih =>
    simp only [visits,List.length_cons]
    split_ifs
    · omega
    · have := ih (z-aw.2); omega

 
theorem subtraction_bound (z w bits : ℕ) (hz : z<2^bits) : z-w<2^bits :=
  (Nat.sub_le z w).trans_lt hz

end IntegerDraw
end Contingency

 

 

open scoped BigOperators
namespace Contingency.IntegerDraw
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

def entries (v : α → ℕ) : List (α×ℕ) := Finset.univ.toList.map (fun a => (a,v a))

omit [Fintype α] [DecidableEq α] in
theorem total_eq_sum (xs : List (α×ℕ)) : total xs=(xs.map Prod.snd).sum := by
  induction xs with
  | nil => rfl
  | cons aw xs ih => simp [total,ih]

omit [DecidableEq α] in
theorem entries_total (v : α → ℕ) : total (entries v)=∑ a,v a := by
  rw [total_eq_sum]
  simp only [entries,List.map_map,Function.comp_def,Finset.sum_map_toList]

theorem entries_weight (v : α → ℕ) (a : α) : weight (entries v) a=v a := by
  simp [weight,entries,List.map_map,Finset.sum_map_toList]

theorem word_bound (V : ℕ) (hV : 0<V) : 2^(Nat.clog 2 V)<2*V := by
  by_cases h : V=1
  · subst V; norm_num
  · have hV1 : 1<V := by omega
    have hp : 2^(Nat.clog 2 V-1)<V := by simpa only [Nat.pred_eq_sub_one] using Nat.pow_pred_clog_lt_self (by omega : 1<2) hV1
    have hc := Nat.clog_pos (by omega : 1<2) hV1
    calc
      _ = 2^(Nat.clog 2 V-1)*2 := by rw [← pow_succ]; congr 1; omega
      _ < _ := by omega

variable (v : α → ℕ)
def bits : ℕ := Nat.clog 2 (∑ a,v a)
def drawTrial : DyadicLaw (Option α) := trial (entries v) (bits v)

theorem drawTrial_some (a : α) : (drawTrial v).count (some a)=v a := by
  rw [drawTrial,trial_count,entries_weight]
  rw [entries_total]
  exact Nat.le_pow_clog (by omega) _

theorem drawTrial_none : (drawTrial v).count none=2^(bits v)-(∑ a,v a) := by
  have ht := (drawTrial v).total
  rw [Fintype.sum_option] at ht
  simp only [drawTrial_some] at ht
  change _+_=2^(bits v) at ht
  omega

def failure : ℝ := (drawTrial v).toLaw.mass none

theorem failure_bounds (hv : 0<∑ a,v a) : 0≤failure v ∧ failure v<1/2 := by
  have hle : (∑ a,v a)≤2^(bits v) := Nat.le_pow_clog (by omega) _
  have hlt := word_bound (∑ a,v a) hv
  change 0≤((drawTrial v).count none:ℝ)/(2:ℝ)^bits v ∧ ((drawTrial v).count none:ℝ)/(2:ℝ)^bits v<1/2
  rw [drawTrial_none]
  rw [Nat.cast_sub hle,Nat.cast_pow,Nat.cast_ofNat]
  constructor
  · apply div_nonneg _ (by positivity)
    apply sub_nonneg.mpr
    exact_mod_cast hle
  · apply (div_lt_iff₀ (by positivity : 0<(2:ℝ)^bits v)).mpr
    have hh : (2:ℝ)^bits v<2*(∑ a,v a:ℕ) := by exact_mod_cast hlt
    linarith

 

def stoppingMass (j : ℕ) (a : α) : ℝ := (failure v)^j*(drawTrial v).toLaw.mass (some a)

theorem rejection_tail (hv : 0<∑ a,v a) :
    Filter.Tendsto (fun j : ℕ => (failure v)^j) Filter.atTop (nhds 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (failure_bounds v hv).1 (by linarith [(failure_bounds v hv).2])

theorem rejection_summable (hv : 0<∑ a,v a) : Summable (fun j : ℕ => (failure v)^j) := by
  apply summable_geometric_of_abs_lt_one
  rw [abs_of_nonneg (failure_bounds v hv).1]
  linarith [(failure_bounds v hv).2]

theorem expected_words (hv : 0<∑ a,v a) : (∑' j : ℕ,(failure v)^j)<2 := by
  have hf := failure_bounds v hv
  rw [tsum_geometric_of_abs_lt_one (by rw [abs_of_nonneg hf.1]; linarith : |failure v|<1)]
  rw [← one_div,div_lt_iff₀ (by linarith : 0<1-failure v)]
  linarith

theorem rejection_exact (hv : 0<∑ a,v a) (a : α) :
    (∑' j : ℕ,stoppingMass v j a)=(v a:ℝ)/(∑ a,v a:ℕ) := by
  have hf := failure_bounds v hv
  have hsum : (0:ℝ)<(∑ a,v a:ℕ) := by exact_mod_cast hv
  simp only [stoppingMass,tsum_mul_right]
  rw [tsum_geometric_of_abs_lt_one (by rw [abs_of_nonneg hf.1]; linarith : |failure v|<1)]
  simp only [failure,DyadicLaw.toLaw,drawTrial_none,drawTrial_some]
  have hle : (∑ a,v a)≤2^bits v := Nat.le_pow_clog (by omega) _
  change (1-((2^bits v-(∑ a,v a):ℕ):ℝ)/(2:ℝ)^bits v)⁻¹*((v a:ℝ)/(2:ℝ)^bits v)=_
  rw [Nat.cast_sub hle,Nat.cast_pow,Nat.cast_ofNat]
  field_simp [hsum.ne']
  ring_nf
  field_simp [hsum.ne']

end
end Contingency.IntegerDraw

 

 

open scoped BigOperators
namespace Contingency
noncomputable section

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)

theorem table_entry_le_total (X : Tables r c) (i : Fin m) (j : Fin n) : X.val i j≤∑ i,r i := by
  have hx := Finset.single_le_sum (fun j _ => Nat.zero_le (X.val i j)) (Finset.mem_univ j)
  rw [X.property.1 i] at hx
  exact hx.trans (Finset.single_le_sum (fun i _ => Nat.zero_le (r i)) (Finset.mem_univ i))

theorem table_card_cap (C : ℕ) (hN : (∑ i,r i)≤C) : Nat.card (Tables r c)≤(C+1)^(m*n) := by
  let : Fintype (Tables r c) := Fintype.ofFinite _
  let f : Tables r c → (Fin m×Fin n → Fin (C+1)) :=
    fun X w => ⟨X.val w.1 w.2,by have := (table_entry_le_total r c X w.1 w.2).trans hN; omega⟩
  have hinj : Function.Injective f := by
    intro X Y h
    apply Subtype.ext
    funext i j
    exact congrArg Fin.val (congrFun h (i,j))
  have hh := Fintype.card_le_of_injective f hinj
  rw [Nat.card_eq_fintype_card]
  simpa using hh

theorem table_card_dyadic {d b C : ℕ} (hmn : m*n≤d) (hN : (∑ i,r i)≤C) (hCb : C+1≤2^b) :
    Nat.card (Tables r c)≤2^(d*b) := by
  calc
    _ ≤ (C+1)^(m*n) := table_card_cap r c C hN
    _ ≤ (C+1)^d := Nat.pow_le_pow_right (by omega) hmn
    _ ≤ (2^b)^d := Nat.pow_le_pow_left hCb _
    _ = _ := by rw [← pow_mul]; congr 1; ring

namespace Parameters

def D (m n N : ℕ) : ℕ := dim m n^6*bits m n N^2

theorem rare_exponent {d b : ℕ} (hd : 14≤d) (hb : d≤b) : 500*(d*b)≤d^6*b^2 := by
  have hp : 14^5≤d^5 := Nat.pow_le_pow_left hd _
  have hb1 : 1≤b := by omega
  have hh : 500≤d^5*b := by nlinarith
  have hmul := Nat.mul_le_mul_left (d*b) hh
  calc
    _ = (d*b)*500 := by ring
    _ ≤ (d*b)*(d^5*b) := hmul
    _ = _ := by ring

theorem rare_weight {d b : ℕ} (hd : 14≤d) (hb : d≤b) :
    (2:ℝ)^(-((d^6*b^2:ℕ):ℤ))*(2:ℝ)^(500*(d*b))≤1 := by
  rw [zpow_neg,zpow_natCast,← div_eq_inv_mul]
  apply (div_le_one (by positivity)).mpr
  exact pow_le_pow_right₀ (by norm_num) (rare_exponent hd hb)

theorem table_card_D (hm : 0 < m) (hn : 0 < n) :
    Nat.card (Tables r c)≤2^D m n (∑ i,r i) := by
  have dims := dimensions hm hn
  have hN : (∑ i,r i)≤cap m n (∑ i,r i) := by unfold cap; omega
  apply (table_card_dyadic r c dims.2.2.2 hN (cap_pow_bits _ _ _)).trans
  apply Nat.pow_le_pow_right (by norm_num)
  have h := rare_exponent dims.1 (dimension_le_bits m n (∑ i,r i))
  unfold D
  omega

end Parameters
end
end Contingency

 

 

open scoped BigOperators
namespace Contingency
noncomputable section
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (hm : 0 < m) (hn : 0 < n) (hrc : (∑ i,r i)=∑ j,c j)
local instance greedyResidualTablesFintype : Fintype (Tables r c) := Fintype.ofFinite _
local notation "D" => Parameters.D m n (∑ i,r i)
local notation "p" => PaddedGraph.canonicalDraw r c hm hn hrc (2*D)

include hm hn in
theorem correction_accuracy_positive : 1≤2*D := by
  have hd := (Parameters.dimensions hm hn).1
  have hb := Parameters.dimension_le_bits m n (∑ i,r i)
  have hD : 0<D := by
    unfold Parameters.D
    exact Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (by omega))
  omega

 
def canonicalResidual (X : Tables r c) : ℕ := correctionCount p D X

theorem canonicalResidual_sum : (∑ X,canonicalResidual r c hm hn hrc X)=Fintype.card (Tables r c)*2^(p).bits := by
  let := tables_nonempty r c hrc
  apply (correction_counts p D _ _).2
  · simpa only [Nat.card_eq_fintype_card] using Parameters.table_card_D r c hm hn
  · exact PaddedGraph.canonicalDraw_tv r c hm hn hrc (2*D) (correction_accuracy_positive r hm hn)

theorem canonicalResidual_formula (X : Tables r c) :
    (canonicalResidual r c hm hn hrc X:ℤ)=
      (2:ℤ)^((p).bits+D)-(Fintype.card (Tables r c):ℤ)*((2:ℤ)^D-1)*(p).count X := by
  let := tables_nonempty r c hrc
  apply (correction_counts p D _ _).1
  · simpa only [Nat.card_eq_fintype_card] using Parameters.table_card_D r c hm hn
  · exact PaddedGraph.canonicalDraw_tv r c hm hn hrc (2*D) (correction_accuracy_positive r hm hn)

theorem canonicalResidual_pos_total : 0<∑ X,canonicalResidual r c hm hn hrc X := by
  let := tables_nonempty r c hrc
  rw [canonicalResidual_sum]
  exact Nat.mul_pos Fintype.card_pos (by positivity)

 

theorem canonical_corrected_exact (X : Tables r c) :
    letI := Classical.decEq (Tables r c)
    (1-1/(2:ℝ)^D)*(p).toLaw.mass X+(1/(2:ℝ)^D)*
      (∑' j : ℕ, IntegerDraw.stoppingMass (canonicalResidual r c hm hn hrc) j X)=
        1/(Fintype.card (Tables r c):ℝ) := by
  classical
  let := tables_nonempty r c hrc
  have hM : Fintype.card (Tables r c)≤2^D := by
    simpa only [Nat.card_eq_fintype_card] using Parameters.table_card_D r c hm hn
  have ht := PaddedGraph.canonicalDraw_tv r c hm hn hrc (2*D) (correction_accuracy_positive r hm hn)
  rw [IntegerDraw.rejection_exact _ (canonicalResidual_pos_total r c hm hn hrc) X,canonicalResidual_sum]
  push_cast
  exact corrected_exact p D hM ht X

 

theorem canonical_rejection_termination :
    letI := Classical.decEq (Tables r c)
    Filter.Tendsto (fun j : ℕ => (IntegerDraw.failure (canonicalResidual r c hm hn hrc))^j)
      Filter.atTop (nhds 0) ∧
    Summable (fun j : ℕ => (IntegerDraw.failure (canonicalResidual r c hm hn hrc))^j) ∧
    (∑' j : ℕ,(IntegerDraw.failure (canonicalResidual r c hm hn hrc))^j)<2 := by
  classical
  exact ⟨IntegerDraw.rejection_tail _ (canonicalResidual_pos_total r c hm hn hrc),
    IntegerDraw.rejection_summable _ (canonicalResidual_pos_total r c hm hn hrc),
    IntegerDraw.expected_words _ (canonicalResidual_pos_total r c hm hn hrc)⟩

end
end Contingency

end

end OAI
