import OAI.Probability.TraceReconstruction.Shapes

namespace OAI

/-!
# Layout

Multiwindow and paired layouts, coordinate simulations, and literal source types and trees.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Literal unmarked concatenation of fixed windows with separately reported
pure pre/post regions. Counts are in atoms, not surviving trace symbols. -/
def framedConcat {α : Type*} (e : α) {k : ℕ}
    (pre post : Fin k → ℕ) (W : Fin k → List α) : List α :=
  (List.ofFn (fun i => List.replicate (pre i) e ++ W i ++
    List.replicate (post i) e)).flatten

theorem framedConcat_succ {α : Type*} (e : α) {k : ℕ}
    (pre post : Fin (k+1) → ℕ) (W : Fin (k+1) → List α) :
    framedConcat e pre post W = List.replicate (pre 0) e ++ W 0 ++
      List.replicate (post 0) e ++
      framedConcat e (fun i => pre i.succ) (fun i => post i.succ) (fun i => W i.succ) := by
  simp [framedConcat,List.ofFn_succ,List.append_assoc]

/-- Only the first, last, and intervening pure lengths are observable in an
unmarked word. In particular boundaries may jitter across nominal units. -/
theorem framedConcat_eq_of_gaps {α : Type*} (e : α) (k : ℕ)
    (pre post pre' post' : Fin (k+1) → ℕ) (W : Fin (k+1) → List α)
    (u u' : ℕ) (hfirst : u+pre 0=u'+pre' 0)
    (hgap : ∀i : Fin k, post i.castSucc+pre i.succ=post' i.castSucc+pre' i.succ)
    (hlast : post (Fin.last k)=post' (Fin.last k)) :
    List.replicate u e ++ framedConcat e pre post W =
      List.replicate u' e ++ framedConcat e pre' post' W := by
  induction k generalizing u u' with
  | zero =>
    have hl : post 0=post' 0 := hlast
    simp only [framedConcat,List.ofFn_succ,List.ofFn_zero,List.flatten_cons,
      List.flatten_nil,List.append_nil]
    calc
      _ = List.replicate (u+pre 0) e ++ W 0 ++ List.replicate (post 0) e := by
        simp only [List.replicate_add,List.append_assoc]
      _ = List.replicate (u'+pre' 0) e ++ W 0 ++ List.replicate (post' 0) e := by rw [hfirst,hl]
      _ = _ := by simp only [List.replicate_add,List.append_assoc]
  | succ k ih =>
    rw [framedConcat_succ e pre post W,framedConcat_succ e pre' post' W]
    have ht := ih (fun i => pre i.succ) (fun i => post i.succ)
      (fun i => pre' i.succ) (fun i => post' i.succ) (fun i => W i.succ)
      (post 0) (post' 0) (hgap 0) (fun i => hgap i.succ) hlast
    calc
      _ = List.replicate (u+pre 0) e ++ W 0 ++
          (List.replicate (post 0) e ++ framedConcat e
            (fun i => pre i.succ) (fun i => post i.succ) (fun i => W i.succ)) := by
        simp only [List.replicate_add,List.append_assoc]
      _ = List.replicate (u'+pre' 0) e ++ W 0 ++
          (List.replicate (post' 0) e ++ framedConcat e
            (fun i => pre' i.succ) (fun i => post' i.succ) (fun i => W i.succ)) := by rw [hfirst,ht]
      _ = _ := by simp only [List.replicate_add,List.append_assoc]

/-- Number of atoms strictly before the indicated padded unit. -/
def framePrefix {k : ℕ} (pre post : Fin k → ℕ) (len : Fin k → ℕ) (i : ℕ) : ℕ :=
  ∑j : Fin k, if j.val < i then pre j+len j+post j else 0

theorem framePrefix_zero {k : ℕ} (pre post len : Fin k → ℕ) :
    framePrefix pre post len 0=0 := by simp [framePrefix]

theorem framePrefix_step {k : ℕ} (pre post len : Fin k → ℕ) (i : Fin k) :
    framePrefix pre post len (i.val+1)=framePrefix pre post len i.val+pre i+len i+post i := by
  have he : (fun j : Fin k => if j.val < i.val+1 then pre j+len j+post j else 0)=
      fun j => (if j.val < i.val then pre j+len j+post j else 0)+
        (if j=i then pre i+len i+post i else 0) := by
    funext j
    by_cases h : j=i
    · subst j; simp
    · have hn : j.val ≠ i.val := fun h' => h (Fin.ext h')
      by_cases hlt : j.val < i.val
      · simp [hlt,show j.val < i.val+1 by omega,h]
      · simp [hlt,show ¬j.val < i.val+1 by omega,h]
  simp only [framePrefix,he,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  omega

/-- Equal actual starting positions and equal total counts are enough:
there is no requirement that a part coincide with its nominal unit. -/
theorem framedConcat_eq_of_starts {α : Type*} (e : α) (k : ℕ)
    (pre post pre' post' : Fin (k+1) → ℕ) (W : Fin (k+1) → List α)
    (hstart : ∀i : Fin (k+1),
      framePrefix pre post (fun j => (W j).length) i.val+pre i=
      framePrefix pre' post' (fun j => (W j).length) i.val+pre' i)
    (htotal : framePrefix pre post (fun j => (W j).length) (k+1)=
      framePrefix pre' post' (fun j => (W j).length) (k+1)) :
    framedConcat e pre post W=framedConcat e pre' post' W := by
  have H := framedConcat_eq_of_gaps e k pre post pre' post' W 0 0
  simp only [List.replicate_zero,List.nil_append] at H
  apply H
  · simpa only [Fin.val_zero,framePrefix_zero,zero_add] using hstart 0
  · intro i
    have h₁ := hstart i.castSucc
    have h₂ := hstart i.succ
    have h₃ := framePrefix_step pre post (fun j => (W j).length) i.castSucc
    have h₄ := framePrefix_step pre' post' (fun j => (W j).length) i.castSucc
    simp only [Fin.val_castSucc,Fin.val_succ] at *
    omega
  · have h₁ := hstart (Fin.last k)
    have h₂ := framePrefix_step pre post (fun j => (W j).length) (Fin.last k)
    have h₃ := framePrefix_step pre' post' (fun j => (W j).length) (Fin.last k)
    simp only [Fin.val_last] at *
    omega

end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem framePrefix_constant {k : ℕ} (pre post len : Fin k → ℕ) (P i : ℕ)
    (hc : ∀j,pre j+len j+post j=P) (hi : i ≤ k) :
    framePrefix pre post len i=i*P := by
  induction i with
  | zero => simp [framePrefix_zero]
  | succ i ih =>
    have h := framePrefix_step pre post len ⟨i,by omega⟩
    have hh := hc ⟨i,by omega⟩
    rw [h,ih (by omega),Nat.add_mul,Nat.one_mul]
    omega

theorem flatten_framedConcat (w : List Bool) {k : ℕ}
    (pre post : Fin k → ℕ) (W : Fin k → List (List Bool)) :
    (framedConcat w pre post W).flatten=
      (List.ofFn (fun i => pureAtomRun w (pre i) ++ (W i).flatten ++
        pureAtomRun w (post i))).flatten := by
  rw [framedConcat,List.flatten_flatten,List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  simp [Function.comp_apply,List.flatten_append,pureAtomRun]

/-- The deterministic multiwindow identity used by the nested simulator.
Every motif is covered by its own window. Predetermined pure-region lengths
may move the boundaries of nominal units; only their exact cumulative counts
are required. Windows and chunks all remain literal unmarked binary words. -/
theorem template_group_windows (k P T a L : ℕ) (sign : Fin L → Bool)
    (w : Bool → List Bool) (τ : Fin (k+1) → Bool)
    (t pre post : Fin (k+1) → ℕ)
    (hleft : ∀u,t u ≤ a) (hfit : ∀u,a+L ≤ t u+T)
    (hunit : ∀u,t u+T ≤ P)
    (hstart : ∀u,framePrefix pre post (fun _ => T) u.val+pre u=u.val*P+t u)
    (htotal : framePrefix pre post (fun _ => T) (k+1)=(k+1)*P) :
    (List.ofFn (fun u => complementaryWords P a L sign w (τ u))).flatten=
      (List.ofFn (fun u => pureAtomRun (w false) (pre u) ++
        complementaryWords T (a-t u) L sign w (τ u) ++
        pureAtomRun (w false) (post u))).flatten := by
  let W : Fin (k+1) → List (List Bool) := fun u =>
    List.ofFn (fun i => w (templateType T (a-t u) L sign (τ u) i))
  let z : Fin (k+1) → ℕ := fun u => P-(t u+T)
  have hz : ∀u,t u+T+z u=P := by intro u; dsimp [z]; have hu := hunit u; omega
  have hlen : ∀u,(W u).length=T := by intro u; simp [W]
  have hp : ∀i,i ≤ k+1 → framePrefix t z (fun u => (W u).length) i=i*P :=
    fun i hi => framePrefix_constant t z _ P i (fun u => by rw [hlen]; exact hz u) hi
  have he := framedConcat_eq_of_starts (w false) k t z pre post W
    (fun u => by simp only [hlen] at hp ⊢; rw [hp _ (by omega),hstart])
    (by simp only [hlen] at hp ⊢; rw [hp _ le_rfl,htotal])
  have he' := congrArg List.flatten he
  rw [flatten_framedConcat,flatten_framedConcat] at he'
  calc
    _ = (List.ofFn (fun u => pureAtomRun (w false) (t u) ++ (W u).flatten ++
          pureAtomRun (w false) (z u))).flatten := by
      congr 1
      apply congrArg List.ofFn
      funext u
      have hh := template_word_window (t u) T (z u) a L sign (τ u) w (hleft u) (hfit u)
      rw [hz] at hh
      simpa only [complementaryWords,atomString_constant,W,atomString,List.ofFn_const,pureAtomRun] using hh
    _ = _ := he'

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
variable {K : Type*} [Fintype K]

/-- Counts of literal side chunks, with one deterministic pure filler in
 each region. A bundle can contain any even number of paired chunks. -/
def pairedPreCount {N : ℕ} (left : K → Fin N) (filler : Fin N → ℕ)
    (first : K → ℕ) (u : Fin N) : ℕ :=
  filler u + ∑v, if left v=u then first v else 0

def pairedPostCount {N : ℕ} (right : K → Fin N) (filler : Fin N → ℕ)
    (reserve first : K → ℕ) (u : Fin N) : ℕ :=
  filler u + ∑v, if right v=u then 2*reserve v-first v else 0

theorem pairedPreCount_cast {N : ℕ} (left : K → Fin N) (filler : Fin N → ℕ)
    (reserve first : K → ℕ) (A : ℕ)
    (hfill : ∀u,filler u+(∑v,if left v=u then reserve v else 0)=A) (u : Fin N) :
    (pairedPreCount left filler first u : ℤ) = A+
      ∑v, if left v=u then (first v:ℤ)-reserve v else 0 := by
  have hf : (filler u:ℤ)+(∑v,if left v=u then (reserve v:ℤ) else 0)=A := by
    exact_mod_cast hfill u
  have he : (∑v,if left v=u then (first v:ℤ)-reserve v else 0)=
      (∑v,if left v=u then (first v:ℤ) else 0)-
        (∑v,if left v=u then (reserve v:ℤ) else 0) := by
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro v _
    split_ifs <;> ring
  simp only [pairedPreCount,Nat.cast_add,Nat.cast_sum,Nat.cast_ite,Nat.cast_zero]
  rw [he]
  omega

theorem pairedPostCount_cast {N : ℕ} (right : K → Fin N) (filler : Fin N → ℕ)
    (reserve first : K → ℕ) (A : ℕ) (hfirst : ∀v,first v ≤ 2*reserve v)
    (hfill : ∀u,filler u+(∑v,if right v=u then reserve v else 0)=A) (u : Fin N) :
    (pairedPostCount right filler reserve first u : ℤ) = A-
      ∑v, if right v=u then (first v:ℤ)-reserve v else 0 := by
  have hf : (filler u:ℤ)+(∑v,if right v=u then (reserve v:ℤ) else 0)=A := by
    exact_mod_cast hfill u
  have he : (∑v,if right v=u then ((2*reserve v-first v:ℕ):ℤ) else 0)=
      (∑v,if right v=u then (reserve v:ℤ) else 0)-
        (∑v,if right v=u then (first v:ℤ)-reserve v else 0) := by
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro v _
    rw [Nat.cast_sub (hfirst v)]
    push_cast
    split_ifs <;> ring
  simp only [pairedPostCount,Nat.cast_add,Nat.cast_sum,Nat.cast_ite,Nat.cast_zero]
  rw [he]
  omega

/-- Prefix sum of a delta at a prescribed label, with no loss from replacing
 its real finite support by an interval. -/
theorem fin_prefix_delta {N : ℕ} (a : Fin N) (i : ℕ) (x : ℤ) :
    (∑u : Fin N, if u.val < i then (if a=u then x else 0) else 0)=
      if a.val < i then x else 0 := by
  have he : (fun u : Fin N => if u.val < i then (if a=u then x else 0) else 0)=
      fun u => if u=a then (if a.val < i then x else 0) else 0 := by
    funext u
    by_cases h : u=a
    · subst u; simp
    · simp [h,Ne.symm h]
  rw [he]
  simp

/-- Exact paired-interval contribution to the position of a window. -/
theorem pair_activity_identity {N : ℕ} (l r u : Fin N) (hlr : l.val ≤ r.val) (x : ℤ) :
    (if l.val < u.val then x else 0)-(if r.val < u.val then x else 0)+
      (if l=u then x else 0) =
      if l.val ≤ u.val ∧ u.val ≤ r.val then x else 0 := by
  by_cases hlu : l.val < u.val
  · by_cases hru : r.val < u.val
    · simp [hlu,hru,show l≠u by intro h; subst u; omega,show ¬u.val ≤ r.val by omega]
    · simp [hlu,hru,show l≠u by intro h; subst u; omega,show l.val ≤ u.val by omega,show u.val ≤ r.val by omega]
  · by_cases hlu' : l=u
    · subst u; simp [hlr,show ¬r.val < l.val by omega]
    · have hn : l.val≠u.val := fun h => hlu' (Fin.ext h)
      simp [hlu,hlu',show ¬r.val < u.val by omega,show ¬l.val ≤ u.val by omega]

/-- Cumulative pure chunk counts have exactly the source's localBits-plus-active-
globalBits jitter. This identity uses the actual chronological pre/post schedule. -/
theorem pairedLayout_start {N : ℕ} (left right : K → Fin N)
    (horder : ∀v,(left v).val ≤ (right v).val)
    (fpre fpost : Fin N → ℕ) (reserve first : K → ℕ)
    (hfirst : ∀v,first v ≤ 2*reserve v) (A B T : ℕ)
    (hpre : ∀u,fpre u+(∑v,if left v=u then reserve v else 0)=A)
    (hpost : ∀u,fpost u+(∑v,if right v=u then reserve v else 0)=B)
    (u : Fin N) :
    ((framePrefix (pairedPreCount left fpre first)
      (pairedPostCount right fpost reserve first) (fun _ => T) u.val+
      pairedPreCount left fpre first u : ℕ):ℤ)=
      u.val*(A+T+B)+A+
        ∑v, if (left v).val ≤ u.val ∧ u.val ≤ (right v).val then
          (first v:ℤ)-reserve v else 0 := by
  let d : K → ℤ := fun v => (first v:ℤ)-reserve v
  have hpr := pairedPreCount_cast left fpre reserve first A hpre
  have hpo := pairedPostCount_cast right fpost reserve first B hfirst hpost
  have hsum : (∑j : Fin N, if j.val < u.val then (1:ℤ) else 0)=(u.val:ℤ) := by
    have hc := framePrefix_constant (fun _ : Fin N => 0) (fun _ => 0) (fun _ => 1) 1 u.val
      (by simp) (by omega)
    simpa [framePrefix] using congrArg (fun n : ℕ => (n:ℤ)) hc
  simp only [Nat.cast_add,framePrefix,Nat.cast_sum,Nat.cast_ite,Nat.cast_zero,hpr,hpo]
  have hex : (∑j : Fin N,if j.val < u.val then
        (A+(∑v,if left v=j then d v else 0))+T+
        (B-(∑v,if right v=j then d v else 0)) else 0)=
      (u.val:ℤ)*(A+T+B)+
        ∑v,((if (left v).val < u.val then d v else 0)-
          (if (right v).val < u.val then d v else 0)) := by
    calc
      _ = (∑j : Fin N,(if j.val < u.val then (1:ℤ) else 0)*(A+T+B))+
          ∑j : Fin N,∑v,
            ((if j.val < u.val then (if left v=j then d v else 0) else 0)-
             (if j.val < u.val then (if right v=j then d v else 0) else 0)) := by
        rw [←Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j.val < u.val
        · simp [hj,Finset.sum_sub_distrib]; ring
        · simp [hj]
      _ = _ := by
        rw [←Finset.sum_mul,hsum,Finset.sum_comm]
        simp_rw [Finset.sum_sub_distrib,fin_prefix_delta]
  change (∑j : Fin N,if j.val < u.val then
      (A+(∑v,if left v=j then d v else 0))+T+
      (B-(∑v,if right v=j then d v else 0)) else 0)+
      (A+∑v,if left v=u then d v else 0)=_
  rw [hex]
  have he : (∑v,((if (left v).val < u.val then d v else 0)-
      (if (right v).val < u.val then d v else 0)))+
      (∑v,if left v=u then d v else 0)=
      ∑v,if (left v).val ≤ u.val ∧ u.val ≤ (right v).val then d v else 0 := by
    rw [←Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun v _ => pair_activity_identity (left v) (right v) u (horder v) (d v))
  dsimp only [d] at *
  linarith only [he]

end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical
variable {K : Type*} [Fintype K]

theorem pairedLayout_total {N : ℕ} (left right : K → Fin N)
    (fpre fpost : Fin N → ℕ) (reserve first : K → ℕ)
    (hfirst : ∀v,first v ≤ 2*reserve v) (A B T : ℕ)
    (hpre : ∀u,fpre u+(∑v,if left v=u then reserve v else 0)=A)
    (hpost : ∀u,fpost u+(∑v,if right v=u then reserve v else 0)=B) :
    framePrefix (pairedPreCount left fpre first)
      (pairedPostCount right fpost reserve first) (fun _ => T) N=N*(A+T+B) := by
  have hpr := pairedPreCount_cast left fpre reserve first A hpre
  have hpo := pairedPostCount_cast right fpost reserve first B hfirst hpost
  have he : ∀f : K → Fin N,
      (∑u : Fin N,∑v,if f v=u then (first v:ℤ)-reserve v else 0)=
        ∑v,((first v:ℤ)-reserve v) := by
    intro f
    rw [Finset.sum_comm]
    simp
  apply Nat.cast_injective (R:=ℤ)
  simp only [framePrefix,Fin.isLt,ite_true,Nat.cast_sum,Nat.cast_add,hpr,hpo,
    Finset.sum_add_distrib,Finset.sum_sub_distrib,he,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul]
  push_cast
  ring

/-- One localBits bundle at each child, and one globalBits bundle at each vertex in
 the first quarter, paired with the reflected last-quarter post region. -/
abbrev SourceBundle (N : ℕ) := Fin N ⊕ Fin (N/4)

def sourceBundleLeft (N : ℕ) : SourceBundle N → Fin N
  | .inl u => u
  | .inr v => ⟨v.val,by have := v.isLt; omega⟩

def sourceBundleRight (N : ℕ) : SourceBundle N → Fin N
  | .inl u => u
  | .inr v => ⟨N-1-v.val,by have := v.isLt; omega⟩

theorem sourceBundle_order (N : ℕ) (v : SourceBundle N) :
    (sourceBundleLeft N v).val ≤ (sourceBundleRight N v).val := by
  cases v with
  | inl u => rfl
  | inr v => dsimp [sourceBundleLeft,sourceBundleRight]; have := v.isLt; omega

theorem sum_injective_delta_le {α β : Type*} [Fintype α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (u : β) (R : ℕ) :
    (∑v,if f v=u then R else 0) ≤ R := by
  by_cases h : ∃v,f v=u
  · obtain ⟨v,hv⟩ := h
    have he : ∀j,f j=u ↔ j=v := fun j => by rw [←hv]; exact hf.eq_iff
    simp [he]
  · push Not at h
    simp [h]

theorem sourceBundle_reserve_pre (N R : ℕ) (u : Fin N) :
    (∑v : SourceBundle N,if sourceBundleLeft N v=u then R else 0) ≤ 2*R := by
  rw [Fintype.sum_sum_type]
  change (∑v : Fin N, if v=u then R else 0)+(∑v : Fin (N/4),
    if (⟨v.val,by have := v.isLt; omega⟩ : Fin N)=u then R else 0) ≤ 2*R
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  have h := sum_injective_delta_le
    (fun v : Fin (N/4) => (⟨v.val,by have := v.isLt; omega⟩ : Fin N))
    (fun _ _ he => Fin.ext (congrArg (fun z : Fin N => z.val) he)) u R
  omega

theorem sourceBundle_reserve_post (N R : ℕ) (u : Fin N) :
    (∑v : SourceBundle N,if sourceBundleRight N v=u then R else 0) ≤ 2*R := by
  rw [Fintype.sum_sum_type]
  change (∑v : Fin N, if v=u then R else 0)+(∑v : Fin (N/4),
    if (⟨N-1-v.val,by have := v.isLt; omega⟩ : Fin N)=u then R else 0) ≤ 2*R
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  have hinj : Function.Injective (fun v : Fin (N/4) =>
      (⟨N-1-v.val,by have := v.isLt; omega⟩ : Fin N)) := by
    intro v w he
    have hv := v.isLt
    have hw := w.isLt
    have h := congrArg Fin.val he
    apply Fin.ext
    dsimp only at h
    omega
  have h := sum_injective_delta_le _ hinj u R
  omega

def sourceBundleCount (N t h : ℕ) (localBits : Fin N → Fin t → Bool)
    (globalBits : Fin ((N/4)*t) → Bool) : SourceBundle N → ℕ
  | .inl u => t*h+∑a,bitIndex (localBits u a)
  | .inr v => t*h+∑a : Fin t,bitIndex (globalBits (globalTrialIndex N t v a))

theorem sourceBundleCount_le (N t h : ℕ) (ht : Even t)
    (localBits : Fin N → Fin t → Bool) (globalBits : Fin ((N/4)*t) → Bool)
    (v : SourceBundle N) : sourceBundleCount N t h localBits globalBits v ≤ 2*(t*h+t/2) := by
  have hh : 2*(t/2)=t := Nat.mul_div_cancel' ((even_iff_two_dvd).mp ht)
  have hs (b : Fin t → Bool) : (∑a,bitIndex (b a)) ≤ t := by
    calc
      _ ≤ ∑_a : Fin t,1 := Finset.sum_le_sum (fun a _ => by cases b a <;> norm_num [bitIndex])
      _ = t := by simp
  cases v with
  | inl u => dsimp [sourceBundleCount]; have := hs (localBits u); omega
  | inr v => dsimp [sourceBundleCount]; have := hs (fun a => globalBits (globalTrialIndex N t v a)); omega

/-- The actual scheduled bits give precisely the arithmetic source displacement
 Y=H+V, including its common-globalBits plateau and outer-quarter behavior. -/
theorem sourceBundle_activity (N t h : ℕ)
    (localBits : Fin N → Fin t → Bool) (globalBits : Fin ((N/4)*t) → Bool) (u : Fin N) :
    (∑v : SourceBundle N, if (sourceBundleLeft N v).val ≤ u.val ∧
        u.val ≤ (sourceBundleRight N v).val then
      (sourceBundleCount N t h localBits globalBits v:ℤ)-(t*h+t/2:ℕ) else 0)=
      ((∑a : Fin t,(bitIndex (localBits u a):ℤ))-(t/2:ℕ))+
        scheduledGlobalShift N t globalBits u := by
  rw [Fintype.sum_sum_type]
  have he : (∑v : Fin N, if v.val ≤ u.val ∧ u.val ≤ v.val then
      (sourceBundleCount N t h localBits globalBits (.inl v):ℤ)-(t*h+t/2:ℕ) else 0)=
      (∑a : Fin t,(bitIndex (localBits u a):ℤ))-(t/2:ℕ) := by
    have hc : ∀v : Fin N,(v.val ≤ u.val ∧ u.val ≤ v.val) ↔ v=u := by
      intro v
      constructor
      · intro hv; exact Fin.ext (le_antisymm hv.1 hv.2)
      · intro hv; subst v; exact ⟨le_rfl,le_rfl⟩
    simp only [hc,Finset.sum_ite_eq',Finset.mem_univ,ite_true,sourceBundleCount,
      Nat.cast_add,Nat.cast_mul,Nat.cast_sum]
    ring
  change (∑v : Fin N, if v.val ≤ u.val ∧ u.val ≤ v.val then
      (sourceBundleCount N t h localBits globalBits (.inl v):ℤ)-(t*h+t/2:ℕ) else 0)+_=_
  rw [he]
  congr 1
  unfold scheduledGlobalShift
  apply Finset.sum_congr rfl
  intro v _
  have hv := v.isLt
  have hu := u.isLt
  have hc : (sourceBundleLeft N (.inr v)).val ≤ u.val ∧
      u.val ≤ (sourceBundleRight N (.inr v)).val ↔ v.val ≤ u.val ∧ u.val+v.val < N := by
    dsimp [sourceBundleLeft,sourceBundleRight]; omega
  simp only [hc]
  split_ifs
  · simp only [sourceBundleCount,Nat.cast_add,Nat.cast_mul,Nat.cast_sum]; ring
  · rfl

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- One-bundle reserved nominal count is integral because the number of
 paired trials is even. The actual filler reserves both local and global
 bundles when both are present in a region. -/
def sourceLayoutReserve (t h : ℕ) : ℕ := t*h+t/2

def sourcePreFiller (N A t h : ℕ) (u : Fin N) : ℕ :=
  A-∑v : SourceBundle N,if sourceBundleLeft N v=u then sourceLayoutReserve t h else 0

def sourcePostFiller (N B t h : ℕ) (u : Fin N) : ℕ :=
  B-∑v : SourceBundle N,if sourceBundleRight N v=u then sourceLayoutReserve t h else 0

def sourcePreCount (N A t h : ℕ) (loc : Fin N → Fin t → Bool)
    (glob : Fin ((N/4)*t) → Bool) : Fin N → ℕ :=
  pairedPreCount (sourceBundleLeft N) (sourcePreFiller N A t h)
    (sourceBundleCount N t h loc glob)

def sourcePostCount (N B t h : ℕ) (loc : Fin N → Fin t → Bool)
    (glob : Fin ((N/4)*t) → Bool) : Fin N → ℕ :=
  pairedPostCount (sourceBundleRight N) (sourcePostFiller N B t h)
    (fun _ => sourceLayoutReserve t h) (sourceBundleCount N t h loc glob)

def sourceDisplacement (N t : ℕ) (loc : Fin N → Fin t → Bool)
    (glob : Fin ((N/4)*t) → Bool) (u : Fin N) : ℤ :=
  (∑a : Fin t,(bitIndex (loc u a):ℤ))-(t/2:ℕ)+scheduledGlobalShift N t glob u

def sourceWindowStart (N A t : ℕ) (loc : Fin N → Fin t → Bool)
    (glob : Fin ((N/4)*t) → Bool) (u : Fin N) : ℕ :=
  ((A:ℤ)+sourceDisplacement N t loc glob u).toNat

theorem sourcePreFiller_nominal (N A t h : ℕ)
    (hA : 2*sourceLayoutReserve t h ≤ A) (u : Fin N) :
    sourcePreFiller N A t h u+
      (∑v : SourceBundle N,if sourceBundleLeft N v=u then sourceLayoutReserve t h else 0)=A := by
  exact Nat.sub_add_cancel ((sourceBundle_reserve_pre N _ u).trans hA)

theorem sourcePostFiller_nominal (N B t h : ℕ)
    (hB : 2*sourceLayoutReserve t h ≤ B) (u : Fin N) :
    sourcePostFiller N B t h u+
      (∑v : SourceBundle N,if sourceBundleRight N v=u then sourceLayoutReserve t h else 0)=B := by
  exact Nat.sub_add_cancel ((sourceBundle_reserve_post N _ u).trans hB)

theorem sourceLayout_exact_start (N A T B t h : ℕ) (ht : Even t)
    (hA : 2*sourceLayoutReserve t h ≤ A) (hB : 2*sourceLayoutReserve t h ≤ B)
    (loc : Fin N → Fin t → Bool) (glob : Fin ((N/4)*t) → Bool) (u : Fin N) :
    ((framePrefix (sourcePreCount N A t h loc glob) (sourcePostCount N B t h loc glob)
      (fun _ => T) u.val+sourcePreCount N A t h loc glob u:ℕ):ℤ)=
      u.val*(A+T+B)+A+sourceDisplacement N t loc glob u := by
  have H := pairedLayout_start (sourceBundleLeft N) (sourceBundleRight N)
    (sourceBundle_order N) (sourcePreFiller N A t h) (sourcePostFiller N B t h)
    (fun _ => sourceLayoutReserve t h) (sourceBundleCount N t h loc glob)
    (sourceBundleCount_le N t h ht loc glob) A B T
    (sourcePreFiller_nominal N A t h hA) (sourcePostFiller_nominal N B t h hB) u
  simp only [sourceLayoutReserve] at H
  rw [sourceBundle_activity] at H
  exact H

theorem sourceLayout_exact_total (N A T B t h : ℕ) (ht : Even t)
    (hA : 2*sourceLayoutReserve t h ≤ A) (hB : 2*sourceLayoutReserve t h ≤ B)
    (loc : Fin N → Fin t → Bool) (glob : Fin ((N/4)*t) → Bool) :
    framePrefix (sourcePreCount N A t h loc glob) (sourcePostCount N B t h loc glob)
      (fun _ => T) N=N*(A+T+B) := by
  exact pairedLayout_total (sourceBundleLeft N) (sourceBundleRight N)
    (sourcePreFiller N A t h) (sourcePostFiller N B t h)
    (fun _ => sourceLayoutReserve t h) (sourceBundleCount N t h loc glob)
    (sourceBundleCount_le N t h ht loc glob) A B T
    (sourcePreFiller_nominal N A t h hA) (sourcePostFiller_nominal N B t h hB)

/-- The literal surrogate side chunks, after concatenation, are a correct
 partition of the actual parent word whenever the windows fit. This is
 an equality of unmarked binary strings, not an assumed channel identity. -/
theorem sourceLayout_literal_partition (k A T B t h a L : ℕ) (ht : Even t)
    (hA : 2*sourceLayoutReserve t h ≤ A) (hB : 2*sourceLayoutReserve t h ≤ B)
    (loc : Fin (k+1) → Fin t → Bool) (glob : Fin (((k+1)/4)*t) → Bool)
    (sign : Fin L → Bool) (w : Bool → List Bool) (τ : Fin (k+1) → Bool)
    (hzero : ∀u,0 ≤ (A:ℤ)+sourceDisplacement (k+1) t loc glob u)
    (hleft : ∀u,sourceWindowStart (k+1) A t loc glob u ≤ a)
    (hfit : ∀u,a+L ≤ sourceWindowStart (k+1) A t loc glob u+T)
    (hunit : ∀u,sourceWindowStart (k+1) A t loc glob u+T ≤ A+T+B) :
    (List.ofFn (fun u => complementaryWords (A+T+B) a L sign w (τ u))).flatten=
      (List.ofFn (fun u => pureAtomRun (w false) (sourcePreCount (k+1) A t h loc glob u) ++
        complementaryWords T (a-sourceWindowStart (k+1) A t loc glob u) L sign w (τ u) ++
        pureAtomRun (w false) (sourcePostCount (k+1) B t h loc glob u))).flatten := by
  apply template_group_windows k (A+T+B) T a L sign w τ
    (sourceWindowStart (k+1) A t loc glob)
    (sourcePreCount (k+1) A t h loc glob) (sourcePostCount (k+1) B t h loc glob)
    hleft hfit hunit
  · intro u
    apply Nat.cast_injective (R:=ℤ)
    rw [sourceLayout_exact_start (k+1) A T B t h ht hA hB]
    simp only [Nat.cast_add,Nat.cast_mul,sourceWindowStart,Int.toNat_of_nonneg (hzero u)]
    ring
  · exact sourceLayout_exact_total (k+1) A T B t h ht hA hB loc glob

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Independent emissions at all literal slots accumulate their actual
 approximation errors. The decoders may depend on the fixed slot ID. -/
theorem coordinateProduct_approximates {α : Type*} [Fintype α]
    {n : ℕ} {q : ℝ} (hq : q∈Set.Icc 0 1) (P : Fin n → FiniteLaw α)
    (f : Fin n → α → List Bool) (w : Fin n → List Bool) (E : Fin n → ℝ)
    (h : ∀i,ApproximatesTrace q (P i) (f i) (w i) (E i)) :
    ApproximatesTrace q (FiniteLaw.coordinateProduct P)
      (fun x => coordinateWord (fun i => f i (x i))) (coordinateWord w) (∑i,E i) := by
  induction n with
  | zero =>
    intro F hF
    change |(FiniteLaw.coordinateProduct P).expect (fun _ => F [])-F []|≤∑i : Fin 0,E i
    simp only [FiniteLaw.expect_const,sub_self,abs_zero,Finset.univ_eq_empty,Finset.sum_empty,le_refl]
  | succ n ih =>
    intro F hF
    have ht := ih (fun i => P i.succ) (fun i => f i.succ)
      (fun i => w i.succ) (fun i => E i.succ) (fun i => h i.succ)
    have hh := ApproximatesTrace.append hq (h 0) ht F hF
    rw [FiniteLaw.expect_prod] at hh
    rw [FiniteLaw.expect_coordinateProduct_succ,coordinateWord_succ,Fin.sum_univ_succ]
    have he (a : α) (x : Fin n → α) :
        coordinateWord (fun i => f i ((Fin.cons a x : Fin (n+1) → α) i))=
          f 0 a++coordinateWord (fun i => f i.succ (x i)) := by
      rw [coordinateWord_succ]
      simp only [Fin.cons_zero,Fin.cons_succ]
    simp_rw [he]
    exact hh

namespace FiniteLaw
variable {ι κ α : Type*} [Fintype ι] [Fintype κ] [Fintype α]

/-- Independent emissions indexed by the actual token IDs of the layout. -/
def indexedProduct (P : ι → FiniteLaw α) : FiniteLaw (ι → α) where
  mass x := ∏i,(P i).mass (x i)
  nonneg x := Finset.prod_nonneg (fun i _ => (P i).nonneg _)
  total := by
    rw [←Fintype.prod_sum]
    simp only [(P _).total,Finset.prod_const_one]

/-- Reorder independent emissions by the literal chronological slot order.
The order is a bijection, so no output is duplicated or silently discarded. -/
theorem indexedProduct_expect_equiv (P : ι → FiniteLaw α) (e : κ ≃ ι)
    (F : (ι → α) → ℝ) :
    (indexedProduct P).expect F=(indexedProduct (fun j => P (e j))).expect
      (fun x => F (fun i => x (e.symm i))) := by
  let E : (κ → α) ≃ (ι → α) :=
    { toFun := fun x i => x (e.symm i)
      invFun := fun x j => x (e j)
      left_inv := fun x => by funext j; simp
      right_inv := fun x => by funext i; simp }
  unfold expect indexedProduct
  rw [←E.sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  change (∏i,(P i).mass (x (e.symm i)))*F (fun i => x (e.symm i))=_
  congr 1
  rw [←e.prod_comp]
  simp only [Equiv.symm_apply_apply]

theorem indexedProduct_map (P : ι → FiniteLaw α) {β : Type*} [Fintype β]
    (f : ι → α → β) :
    (indexedProduct P).map (fun x i => f i (x i))=
      indexedProduct (fun i => (P i).map (f i)) := by
  apply FiniteLaw.ext
  funext y
  rw [map_mass]
  change (∑x : ι → α,if (fun i => f i (x i))=y then ∏i,(P i).mass (x i) else 0)=_
  simp only [indexedProduct,map_mass]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases he : (fun i => f i (x i))=y
  · rw [ite_eq_left he]
    exact Finset.prod_congr rfl (fun i _ => (ite_eq_left (congrFun he i)).symm)
  · rw [ite_eq_right he]
    symm
    have hi : ∃i,f i (x i)≠y i := by
      by_contra h
      push Not at h
      exact he (funext h)
    obtain ⟨i,hi⟩ := hi
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

end FiniteLaw

/-- An arbitrarily indexed actual layout has the same unconditional trace
 guarantee after its fixed, public chronological ordering is applied. -/
theorem indexedProduct_approximates {ι α : Type*} [Fintype ι] [Fintype α]
    {n : ℕ} {q : ℝ} (hq : q∈Set.Icc 0 1) (e : Fin n ≃ ι)
    (P : ι → FiniteLaw α) (f : ι → α → List Bool) (w : ι → List Bool) (E : ι → ℝ)
    (h : ∀i,ApproximatesTrace q (P i) (f i) (w i) (E i)) :
    ApproximatesTrace q (FiniteLaw.indexedProduct P)
      (fun x => coordinateWord (fun j => f (e j) (x (e j))))
      (coordinateWord (fun j => w (e j))) (∑i,E i) := by
  intro F hF
  rw [FiniteLaw.indexedProduct_expect_equiv P e]
  simp only [Equiv.symm_apply_apply]
  have H := coordinateProduct_approximates hq (fun j => P (e j))
    (fun j => f (e j)) (fun j => w (e j)) (fun j => E (e j)) (fun j => h (e j)) F hF
  rw [e.sum_comp] at H
  simp only [FiniteLaw.expect,FiniteLaw.indexedProduct,FiniteLaw.coordinateProduct] at H ⊢
  convert H using 1
  congr 3
  ext x
  simp

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- The Boolean representation of the source Prouhet signs; true denotes
 a negative type. No sign convention is changed in passing to literal words. -/
def boolTypeSign (b : Bool) : ℝ := if b then -1 else 1

def prouhetBool (s : ℕ) (i : Fin (2^s)) : Bool :=
  decide ((prouhetSeries s).coeff (i.val:ℤ)= -1)

theorem boolTypeSign_injective : Function.Injective boolTypeSign := by
  intro a b h
  cases a <;> cases b <;> norm_num [boolTypeSign] at *

theorem boolTypeSign_template (s P a : ℕ) (τ : Bool) (i : Fin P) :
    boolTypeSign (templateType P a (2^s) (prouhetBool s) τ i)=
      motifChildSign s (a:ℤ) i.val (boolTypeSign τ) := by
  by_cases hi : a ≤ i.val ∧ i.val < a+2^s
  · have hz : 0 ≤ (i.val:ℤ)-a ∧ (i.val:ℤ)-a < (2^s:ℕ) := by omega
    have he : ((i.val-a:ℕ):ℤ)=(i.val:ℤ)-a := by omega
    have hc := (abs_eq (by norm_num : (0:ℝ)≤1)).mp
      ((prouhetSeries_coeff_spec s).2 _ hz.1 hz.2)
    have hχ : motifIndicator s ((i.val:ℤ)-a)=1 := by simp only [motifIndicator,ite_eq_left hz]
    rcases hc with hc | hc <;> cases τ <;>
      norm_num [templateType,hi,prouhetBool,he,boolTypeSign,motifChildSign,hχ,hc]
  · have hz : ¬(0 ≤ (i.val:ℤ)-a ∧ (i.val:ℤ)-a < (2^s:ℕ)) := by omega
    have hc : (prouhetSeries s).coeff ((i.val:ℤ)-a)=0 :=
      (prouhetSeries_coeff_spec s).1 _ (by omega)
    have hχ : motifIndicator s ((i.val:ℤ)-a)=0 := by simp only [motifIndicator,ite_eq_right hz]
    simp [templateType,hi,boolTypeSign,motifChildSign,hχ,hc]

theorem sourceWindowStart_cast_of_fit (N P T t : ℕ)
    (loc : Fin N → Fin t → Bool) (glob : Fin ((N/4)*t) → Bool)
    (hP : 2*T ≤ P) (hT : 16 ≤ T) (u : Fin N)
    (hY : |8*sourceDisplacement N t loc glob u| ≤ (T:ℤ)) :
    (sourceWindowStart N ((P-T)/2) t loc glob u:ℤ)=
      (((P-T)/2:ℕ):ℤ)+sourceDisplacement N t loc glob u := by
  apply Int.toNat_of_nonneg
  have hy := abs_le.mp hY
  omega

/-- A zero-based centered version of the floor-fit calculation. -/
theorem sourceWindowStart_fit (N P T t L : ℕ)
    (loc : Fin N → Fin t → Bool) (glob : Fin ((N/4)*t) → Bool)
    (hP : 2*T ≤ P) (hT : 16 ≤ T) (heven : Even T) (hL : 8*L ≤ T)
    (u : Fin N) (hY : |8*sourceDisplacement N t loc glob u| ≤ (T:ℤ)) :
    sourceWindowStart N ((P-T)/2) t loc glob u+T ≤ P ∧
    sourceWindowStart N ((P-T)/2) t loc glob u ≤ P/2 ∧
    P/2+L ≤ sourceWindowStart N ((P-T)/2) t loc glob u+T :=
  centered_window_floor_fit P T L _ _ hP hT heven hL hY
    (sourceWindowStart_cast_of_fit N P T t loc glob hP hT u hY)

/-- The zero-based centered translated anchor, including both half-trial corrections. -/
theorem sourceWindowStart_anchor (N P T t L : ℕ)
    (loc : Fin N → Fin t → Bool) (glob : Fin ((N/4)*t) → Bool)
    (hP : 2*T ≤ P) (hT : 16 ≤ T) (heven : Even T) (hL : 8*L ≤ T)
    (u : Fin N) (hY : |8*sourceDisplacement N t loc glob u| ≤ (T:ℤ)) :
    ((P/2-sourceWindowStart N ((P-T)/2) t loc glob u:ℕ):ℤ)=
      (T/2:ℕ)+(t/2:ℕ)-(∑a : Fin t,(bitIndex (loc u a):ℤ))-
        scheduledGlobalShift N t glob u := by
  have hfit := sourceWindowStart_fit N P T t L loc glob hP hT heven hL u hY
  have hc := sourceWindowStart_cast_of_fit N P T t loc glob hP hT u hY
  have ha := centered_window_floor_anchor P T (by omega) heven
  have hA : (P-T)/2 ≤ P/2 := Nat.div_le_div_right (Nat.sub_le P T)
  have ha' : ((P/2:ℕ):ℤ)-((P-T)/2:ℕ)=(T/2:ℕ) := by omega
  rw [Nat.cast_sub hfit.2.1,hc]
  dsimp only [sourceDisplacement]
  linarith only [ha']

/-- The manuscript numbers motif slots from one. Thus its actual zero-based
 onset is P/2-1, not P/2. The strict margins include this endpoint correction. -/
theorem sourceWindowStart_oneBased_fit (N P T t L : ℕ)
    (loc : Fin N → Fin t → Bool) (glob : Fin ((N/4)*t) → Bool)
    (hP : 2*T ≤ P) (hT : 16 ≤ T) (heven : Even T) (hL : 8*L ≤ T)
    (u : Fin N) (hY : |8*sourceDisplacement N t loc glob u| ≤ (T:ℤ)) :
    sourceWindowStart N ((P-T)/2) t loc glob u+T ≤ P ∧
    sourceWindowStart N ((P-T)/2) t loc glob u ≤ P/2-1 ∧
    P/2-1+L ≤ sourceWindowStart N ((P-T)/2) t loc glob u+T := by
  have hc := sourceWindowStart_cast_of_fit N P T t loc glob hP hT u hY
  have ha := centered_window_floor_anchor P T (by omega) heven
  have hy := abs_le.mp hY
  omega

/-- The exact source anchor in zero-based coordinates. The minus one is
 forced by the one-based motif-label convention. -/
theorem sourceWindowStart_oneBased_anchor (N P T t L : ℕ)
    (loc : Fin N → Fin t → Bool) (glob : Fin ((N/4)*t) → Bool)
    (hP : 2*T ≤ P) (hT : 16 ≤ T) (heven : Even T) (hL : 8*L ≤ T)
    (u : Fin N) (hY : |8*sourceDisplacement N t loc glob u| ≤ (T:ℤ)) :
    ((P/2-1-sourceWindowStart N ((P-T)/2) t loc glob u:ℕ):ℤ)=
      (T/2:ℕ)-1+(t/2:ℕ)-(∑a : Fin t,(bitIndex (loc u a):ℤ))-
        scheduledGlobalShift N t glob u := by
  have hf := sourceWindowStart_oneBased_fit N P T t L loc glob hP hT heven hL u hY
  have ha := sourceWindowStart_anchor N P T t L loc glob hP hT heven hL u hY
  omega

/-- The actual recursively substituted source block words. Indices in P
 are shifted down by one, but physical binary strings are unchanged. -/
def sourceBlockWord (s : ℕ) (P : ℕ → ℕ) (atom : Bool → List Bool) : ℕ → Bool → List Bool
  | 0 => atom
  | j+1 => complementaryWords (P j) (P j/2-1) (2^s) (prouhetBool s)
      (sourceBlockWord s P atom j)

def sourceBlockLength (P : ℕ → ℕ) (S : ℕ) : ℕ → ℕ
  | 0 => S
  | j+1 => P j*sourceBlockLength P S j

theorem sourceBlockWord_length (s : ℕ) (P : ℕ → ℕ) (atom : Bool → List Bool) (S : ℕ)
    (hw : ∀τ,(atom τ).length=S) (j : ℕ) (τ : Bool) :
    (sourceBlockWord s P atom j τ).length=sourceBlockLength P S j := by
  induction j generalizing τ with
  | zero => exact hw τ
  | succ j ih => exact complementaryWords_length _ _ _ _ _ _ (fun τ => ih τ) τ

theorem sourceBlockWord_injective (s : ℕ) (P : ℕ → ℕ) (atom : Bool → List Bool) (S : ℕ)
    (hw : ∀τ,(atom τ).length=S) (hinj : Function.Injective atom) (j : ℕ)
    (hP : ∀k<j,0<P k) : Function.Injective (sourceBlockWord s P atom j) := by
  induction j with
  | zero => exact hinj
  | succ j ih =>
    apply complementaryWords_injective _ _ _ (sourceBlockLength P S j)
      _ _ (sourceBlockWord_length s P atom S hw j)
    · exact ih (fun k hk => hP k (by omega))
    · positivity
    · have h := hP j (Nat.lt_succ_self j); omega

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Total Boolean type, also on failed layouts; no conditioning is hidden
 in the definition. -/
def integerTemplateType (N s : ℕ) (X : ℤ) (τ : Bool) (u : Fin N) : Bool :=
  decide (motifChildSign s X u.val (boolTypeSign τ)= -1)

theorem boolTypeSign_integerTemplate (N s : ℕ) (X : ℤ) (τ : Bool) (u : Fin N) :
    boolTypeSign (integerTemplateType N s X τ u)=motifChildSign s X u.val (boolTypeSign τ) := by
  have hτ : IsTypeSign (boolTypeSign τ) := by cases τ <;> norm_num [IsTypeSign,boolTypeSign]
  rcases motifChildSign_isSign s X u.val hτ with h | h <;>
    (simp only [integerTemplateType,h]; norm_num [boolTypeSign])

theorem integerTemplateType_nat (N s a : ℕ) (τ : Bool) :
    integerTemplateType N s (a:ℤ) τ=templateType N a (2^s) (prouhetBool s) τ := by
  funext u
  apply boolTypeSign_injective
  rw [boolTypeSign_integerTemplate,boolTypeSign_template]

/-- Global trials at a parent use its children's local-trial count. This
 fixes the index shift between source level labels and zero-based arrays. -/
def sourceScheduledTrials (T n : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | b+1 => (T (b+1)/4)*n b

def sourceScheduledShift (T n : ℕ → ℕ) :
    (b : ℕ) → (Fin (sourceScheduledTrials T n b) → Bool) → Fin (T b) → ℤ
  | 0, _, _ => 0
  | b+1, glob, u => scheduledGlobalShift (T (b+1)) (n b) glob u

def sourceLocalCenter (T n : ℕ → ℕ) (b : ℕ) : ℤ :=
  (T b/2:ℕ)-1+(n b/2:ℕ)

def sourceNodeAnchor (T n : ℕ → ℕ) (center : ℕ → ℤ) (b : ℕ)
    (bits : WindowAssignments T n (sourceScheduledTrials T n) Bool (b+1)) (incoming : ℤ) : ℤ :=
  center b-(∑i,(bitIndex (bits.1 i):ℤ))-incoming

/-- All actual leaf Booleans on the complete deterministic window tree. -/
def sourceTreeLeafBool (T n : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ) :
    (b : ℕ) → WindowAssignments T n (sourceScheduledTrials T n) Bool b → ℤ → Bool → WindowLeaf T b → Bool
  | 0, _, _, τ, _ => τ
  | b+1, bits, incoming, τ, v =>
      sourceTreeLeafBool T n s center b (bits.2.2 v.1)
        (sourceScheduledShift T n b bits.2.1 v.1)
        (integerTemplateType (T b) s (sourceNodeAnchor T n center b bits incoming) τ v.1) v.2

theorem sourceTreeLeafBool_sign (T n : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (b : ℕ) (bits : WindowAssignments T n (sourceScheduledTrials T n) Bool b)
    (incoming : ℤ) (τ : Bool) (v : WindowLeaf T b) :
    boolTypeSign (sourceTreeLeafBool T n s center b bits incoming τ v)=
      sourceTreeLeafSign T n (sourceScheduledTrials T n) s center
        (sourceScheduledShift T n) b bits incoming (boolTypeSign τ) v := by
  induction b generalizing incoming τ with
  | zero => rfl
  | succ b ih =>
    change boolTypeSign (sourceTreeLeafBool T n s center b _ _ _ v.2)=_
    rw [ih,boolTypeSign_integerTemplate]
    rfl

def sourceNominalPre (P T : ℕ → ℕ) (b : ℕ) : ℕ := (P b-T b)/2
def sourceNominalPost (P T : ℕ → ℕ) (b : ℕ) : ℕ := P b-T b-sourceNominalPre P T b

theorem sourceNominal_total (P T : ℕ → ℕ) (b : ℕ) (h : T b ≤ P b) :
    sourceNominalPre P T b+T b+sourceNominalPost P T b=P b := by
  dsimp [sourceNominalPre,sourceNominalPost]
  omega

/-- The actual center before recursively cutting its pure side regions. -/
def sourceCenterWord (s : ℕ) (P T n : ℕ → ℕ) (center : ℕ → ℤ) (atom : Bool → List Bool) :
    (b : ℕ) → WindowAssignments T n (sourceScheduledTrials T n) Bool b → ℤ → Bool → List Bool
  | 0, _, _, τ => atom τ
  | b+1, bits, incoming, τ => atomString (T b) (sourceBlockWord s P atom b)
      (integerTemplateType (T b) s (sourceNodeAnchor T n center b bits incoming) τ)

/-- The unconditional literal surrogate partition: local and common-global
 pairs contribute their real selected pure lengths, on every bit assignment. -/
def sourceTreeWord (s : ℕ) (P T n h : ℕ → ℕ) (center : ℕ → ℤ) (atom : Bool → List Bool) :
    (b : ℕ) → WindowAssignments T n (sourceScheduledTrials T n) Bool b → ℤ → Bool → List Bool
  | 0, _, _, τ => atom τ
  | 1, bits, incoming, τ => sourceCenterWord s P T n center atom 1 bits incoming τ
  | b+2, bits, incoming, τ =>
      let loc := fun u => (bits.2.2 u).1
      let glob := bits.2.1
      coordinateWord (fun u : Fin (T (b+1)) =>
        pureAtomRun (sourceBlockWord s P atom b false)
          (sourcePreCount (T (b+1)) (sourceNominalPre P T b) (n b) (h b) loc glob u) ++
        sourceTreeWord s P T n h center atom (b+1) (bits.2.2 u)
          (sourceScheduledShift T n (b+1) glob u)
          (integerTemplateType (T (b+1)) s (sourceNodeAnchor T n center (b+1) bits incoming) τ u) ++
        pureAtomRun (sourceBlockWord s P atom b false)
          (sourcePostCount (T (b+1)) (sourceNominalPost P T b) (n b) (h b) loc glob u))

/-- The actual fit event uses a joint test of all displacements. It does not
 assert independence and will only be charged probabilistically afterwards. -/
def SourceTreeFit (T n : ℕ → ℕ) :
    (b : ℕ) → WindowAssignments T n (sourceScheduledTrials T n) Bool b → Prop
  | 0, _ => True
  | 1, _ => True
  | b+2, bits =>
      (∀u, |8*sourceDisplacement (T (b+1)) (n b) (fun v => (bits.2.2 v).1) bits.2.1 u| ≤ (T b:ℤ)) ∧
      ∀u, SourceTreeFit T n (b+1) (bits.2.2 u)

/-- Numerical layout conditions from the source. These contain no word or
 statistical conclusions, only the genuine integer margins. -/
structure SourceLayoutMargins (s : ℕ) (P T n h : ℕ → ℕ) (b : ℕ) : Prop where
  positive : ∀j<b, 0<T j
  large : ∀j<b, 16≤T j
  even_window : ∀j<b, Even (T j)
  ambient : ∀j<b, 2*T j≤P j
  motif : ∀j<b, 8*2^s≤T j
  even_trials : ∀j<b, Even (n j)
  pre_reserve : ∀j<b, 2*sourceLayoutReserve (n j) (h j)≤ sourceNominalPre P T j
  post_reserve : ∀j<b, 2*sourceLayoutReserve (n j) (h j)≤ sourceNominalPost P T j

theorem SourceLayoutMargins.restrict {s : ℕ} {P T n h : ℕ → ℕ} {b c : ℕ}
    (H : SourceLayoutMargins s P T n h b) (hc : c≤b) : SourceLayoutMargins s P T n h c := by
  constructor <;> intro j hj
  · exact H.positive j (lt_of_lt_of_le hj hc)
  · exact H.large j (lt_of_lt_of_le hj hc)
  · exact H.even_window j (lt_of_lt_of_le hj hc)
  · exact H.ambient j (lt_of_lt_of_le hj hc)
  · exact H.motif j (lt_of_lt_of_le hj hc)
  · exact H.even_trials j (lt_of_lt_of_le hj hc)
  · exact H.pre_reserve j (lt_of_lt_of_le hj hc)
  · exact H.post_reserve j (lt_of_lt_of_le hj hc)

/-- Every recursively cut surrogate center is literally the actual center on
 the joint fit event. The source type assignment is retained at all leaves. -/
theorem sourceTreeWord_eq_center (s : ℕ) (P T n h : ℕ → ℕ) (center : ℕ → ℤ)
    (atom : Bool → List Bool) (b : ℕ) (H : SourceLayoutMargins s P T n h b)
    (hc : ∀j, j+1<b → center j=sourceLocalCenter T n j)
    (bits : WindowAssignments T n (sourceScheduledTrials T n) Bool b)
    (incoming : ℤ) (τ : Bool) (hfit : SourceTreeFit T n b bits) :
    sourceTreeWord s P T n h center atom b bits incoming τ=
      sourceCenterWord s P T n center atom b bits incoming τ := by
  induction b using Nat.twoStepInduction generalizing incoming τ with
  | zero => rfl
  | one => rfl
  | more b ih₁ ih₂ =>
    change (Fin (n (b+1)) → Bool) × (Fin ((T (b+1)/4)*n b) → Bool) ×
      (Fin (T (b+1)) → WindowAssignments T n (sourceScheduledTrials T n) Bool (b+1)) at bits
    let loc : Fin (T (b+1)) → Fin (n b) → Bool := fun u => (bits.2.2 u).1
    let glob := bits.2.1
    let a := P b/2-1
    let A := sourceNominalPre P T b
    let B := sourceNominalPost P T b
    let start := sourceWindowStart (T (b+1)) A (n b) loc glob
    let θ := integerTemplateType (T (b+1)) s (sourceNodeAnchor T n center (b+1) bits incoming) τ
    have hb : b<b+2 := by omega
    have htotal := sourceNominal_total P T b (by have hh := H.ambient b hb; omega)
    have hf (u : Fin (T (b+1))) := sourceWindowStart_oneBased_fit (T (b+1)) (P b) (T b) (n b)
      (2^s) loc glob (H.ambient b hb) (H.large b hb) (H.even_window b hb) (H.motif b hb) u (hfit.1 u)
    have hx (u : Fin (T (b+1))) :
        sourceNodeAnchor T n center b (bits.2.2 u) (sourceScheduledShift T n (b+1) glob u)=((a-start u:ℕ):ℤ) := by
      change sourceNodeAnchor T n center b (bits.2.2 u) (sourceScheduledShift T n (b+1) glob u)=
        ((P b/2-1-sourceWindowStart (T (b+1)) ((P b-T b)/2) (n b) loc glob u:ℕ):ℤ)
      rw [sourceWindowStart_oneBased_anchor (T (b+1)) (P b) (T b) (n b) (2^s) loc glob
        (H.ambient b hb) (H.large b hb) (H.even_window b hb) (H.motif b hb) u (hfit.1 u)]
      simp only [sourceNodeAnchor,hc b (by omega),sourceLocalCenter,sourceScheduledShift,loc]
    have hchild (u : Fin (T (b+1))) :
        sourceTreeWord s P T n h center atom (b+1) (bits.2.2 u)
          (sourceScheduledShift T n (b+1) glob u) (θ u)=
        complementaryWords (T b) (a-start u) (2^s) (prouhetBool s) (sourceBlockWord s P atom b) (θ u) := by
      rw [ih₂ (H.restrict (by omega)) (fun j hj => hc j (by omega)) _ _ _ (hfit.2 u)]
      simp only [sourceCenterWord,hx,integerTemplateType_nat,complementaryWords]
    have hstartnonneg (u : Fin (T (b+1))) : 0≤(A:ℤ)+sourceDisplacement (T (b+1)) (n b) loc glob u := by
      have he := sourceWindowStart_cast_of_fit (T (b+1)) (P b) (T b) (n b) loc glob
        (H.ambient b hb) (H.large b hb) u (hfit.1 u)
      have hn : (0:ℤ)≤(start u:ℕ) := Int.natCast_nonneg _
      change (start u:ℤ)=(A:ℤ)+_ at he
      omega
    have hp := H.positive (b+1) (by omega)
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : T (b+1)≠0)
    have hpart : (List.ofFn (fun u => complementaryWords (P b) a (2^s) (prouhetBool s)
          (sourceBlockWord s P atom b) (θ u))).flatten=
        coordinateWord (fun u => pureAtomRun (sourceBlockWord s P atom b false)
          (sourcePreCount (T (b+1)) A (n b) (h b) loc glob u) ++
          complementaryWords (T b) (a-start u) (2^s) (prouhetBool s) (sourceBlockWord s P atom b) (θ u) ++
          pureAtomRun (sourceBlockWord s P atom b false) (sourcePostCount (T (b+1)) B (n b) (h b) loc glob u)) := by
      have hh := sourceLayout_literal_partition k A (T b) B (n b) (h b) a (2^s)
      have hk' : k+1=T (b+1) := hk.symm
      rw [hk'] at hh
      rw [show A+T b+B=P b from htotal] at hh
      exact hh (H.even_trials b hb) (H.pre_reserve b hb) (H.post_reserve b hb) loc glob
        (prouhetBool s) (sourceBlockWord s P atom b) θ hstartnonneg
        (fun u => (hf u).2.1) (fun u => (hf u).2.2) (fun u => (hf u).1)
    change coordinateWord (fun u : Fin (T (b+1)) =>
      pureAtomRun (sourceBlockWord s P atom b false) (sourcePreCount (T (b+1)) A (n b) (h b) loc glob u) ++
      sourceTreeWord s P T n h center atom (b+1) (bits.2.2 u)
        (sourceScheduledShift T n (b+1) glob u) (θ u) ++
      pureAtomRun (sourceBlockWord s P atom b false) (sourcePostCount (T (b+1)) B (n b) (h b) loc glob u))=
        atomString (T (b+1)) (sourceBlockWord s P atom (b+1)) θ
    calc
      _ = coordinateWord (fun u : Fin (T (b+1)) =>
        pureAtomRun (sourceBlockWord s P atom b false) (sourcePreCount (T (b+1)) A (n b) (h b) loc glob u) ++
        complementaryWords (T b) (a-start u) (2^s) (prouhetBool s) (sourceBlockWord s P atom b) (θ u) ++
        pureAtomRun (sourceBlockWord s P atom b false) (sourcePostCount (T (b+1)) B (n b) (h b) loc glob u)) := by
          apply congrArg coordinateWord
          funext u
          exact congrArg (fun w => pureAtomRun (sourceBlockWord s P atom b false)
            (sourcePreCount (T (b+1)) A (n b) (h b) loc glob u) ++ w ++
              pureAtomRun (sourceBlockWord s P atom b false)
                (sourcePostCount (T (b+1)) B (n b) (h b) loc glob u)) (hchild u)
      _ = _ := hpart.symm

end TraceReconstruction

end
end
end
end
end
end
end
end
end

end OAI
