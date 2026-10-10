import Mathlib
import OAI.Probability.Contingency.IntegerDrawMachine

namespace OAI

/-! Integer Draw Tail. -/

noncomputable section

open Filter
open scoped BigOperators
open Filter
namespace Contingency.BitModel.StackCode.IntegerDraw
open BinaryTrial
noncomputable section

instance (B : List Bool) (f : ℕ→Bool) (j : ℕ) : Decidable (accepted B f j) :=
  inferInstanceAs (Decidable (beValue (candidate B f j)≤beValue B))

def extend {t : ℕ} (f : Fin t→Bool) (i : ℕ) : Bool := if h:i<t then f ⟨i,h⟩ else false

@[simp] theorem trace_extend {t : ℕ} (f : Fin t→Bool) : trace (extend f) 0 t=List.ofFn f := by
  unfold trace
  congr 1
  funext i
  simp [extend]

def coord (B : List Bool) (k t : ℕ) (ht : startTime B k+successTime B≤t)
    (ji : Fin k×Fin B.length) : Fin t :=
  ⟨startTime B ji.1+ji.2*4+2,by
    have hj := Nat.mul_le_mul_right (retryTime B) (Nat.succ_le_of_lt ji.1.isLt)
    rw [Nat.succ_mul] at hj
    have hi := ji.2.isLt
    dsimp [startTime,retryTime,successTime] at *
    omega⟩

 theorem coord_injective (B : List Bool) (k t : ℕ) (ht : startTime B k+successTime B≤t) :
    Function.Injective (coord B k t ht) := by
  intro a b he
  have hv := congrArg Fin.val he
  change startTime B a.1+a.2*4+2=startTime B b.1+b.2*4+2 at hv
  have ha := a.2.isLt
  have hb := b.2.isLt
  have hj : a.1=b.1 := by
    by_contra hn
    have hn' : a.1.val≠b.1.val := fun h => hn (Fin.ext h)
    rcases lt_or_gt_of_ne hn' with hh|hh
    · have hm := Nat.mul_le_mul_right (retryTime B) (Nat.succ_le_of_lt hh)
      rw [Nat.succ_mul] at hm
      dsimp [startTime,retryTime] at hv hm
      omega
    · have hm := Nat.mul_le_mul_right (retryTime B) (Nat.succ_le_of_lt hh)
      rw [Nat.succ_mul] at hm
      dsimp [startTime,retryTime] at hv hm
      omega
  apply Prod.ext hj
  apply Fin.ext
  rw [hj] at hv
  omega

 theorem candidate_coord (B : List Bool) (k t : ℕ) (ht : startTime B k+successTime B≤t)
    (f : Fin t→Bool) (j : Fin k) :
    candidate B (extend f) j=List.ofFn (fun i => f (coord B k t ht (j,i))) := by
  unfold candidate streamDigits
  rw [digits_coin]
  congr 1
  funext i
  simp only [digitCoord,finProdFinEquiv]
  have hc := (coord B k t ht (j,i)).isLt
  dsimp [coord] at hc
  have hi : startTime B ↑j+(2+4*↑i)=startTime B ↑j+↑i*4+2 := by omega
  change extend f (startTime B ↑j+(2+4*↑i))=f (coord B k t ht (j,i))
  rw [hi]
  simp [extend,hc,coord]

 theorem bound_lt (B : List Bool) : beValue B<2^B.length := by
  simpa [wordValue] using wordValue_lt B.get

def badCount (B : List Bool) : ℕ := 2^B.length-(beValue B+1)

def rejectRate (B : List Bool) : ℝ := badCount B/2^B.length

 theorem bad_words (B : List Bool) :
    (Finset.univ.filter fun bs : Fin B.length→Bool => ¬wordValue bs≤beValue B).card=badCount B := by
  classical
  have h := Finset.card_filter_add_card_filter_not
    (s:=Finset.univ) (p:=fun bs : Fin B.length→Bool => wordValue bs≤beValue B)
  rw [bounded_words _ _ (bound_lt B)] at h
  simp only [Finset.card_univ,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin] at h
  unfold badCount
  omega

 theorem all_bad (B : List Bool) (k : ℕ) :
    (Finset.univ.filter fun f : (Fin k×Fin B.length)→Bool =>
      ∀ j,¬wordValue (fun i => f (j,i))≤beValue B).card=(badCount B)^k := by
  classical
  simp only [Finset.card_filter]
  change (∑ f,if (∀ j,¬wordValue ((Equiv.curry _ _ _ f) j)≤beValue B) then 1 else 0)=_
  rw [(Equiv.curry (Fin k) (Fin B.length) Bool).sum_comp
    (fun f => if (∀ j,¬wordValue (f j)≤beValue B) then (1:ℕ) else 0)]
  rw [← Finset.card_filter]
  calc
    _ = (Finset.univ.filter fun bs : Fin B.length→Bool => ¬wordValue bs≤beValue B).card^k :=
      CoordinateLaw.count_all k (fun bs : Fin B.length→Bool => ¬wordValue bs≤beValue B)
    _ = _ := by rw [bad_words]

 theorem bad_probability (B : List Bool) (k t : ℕ) (ht : startTime B k+successTime B≤t) :
    ((Finset.univ.filter fun f : Fin t→Bool => ∀ j : Fin k,¬accepted B (extend f) j).card:ℝ)/2^t=
      rejectRate B^k := by
  classical
  have he : (fun f : Fin t→Bool => ∀ j : Fin k,¬accepted B (extend f) j)=
      (fun f : Fin t→Bool => ∀ j : Fin k,¬wordValue (fun i => (f∘coord B k t ht) (j,i))≤beValue B) := by
    funext f
    simp only [accepted,candidate_coord B k t ht f,wordValue,Function.comp_def]
  simp only [he]
  have hh := CoordinateLaw.probability_restrict (coord B k t ht) (coord_injective B k t ht)
    (fun g : (Fin k×Fin B.length)→Bool => ∀ j,¬wordValue (fun i => g (j,i))≤beValue B)
  simp only [Fintype.card_fin,Fintype.card_prod] at hh
  rw [hh,all_bad]
  push_cast
  rw [show k*B.length=B.length*k from Nat.mul_comm _ _,pow_mul]
  exact (div_pow _ _ _).symm

 theorem tail_bound (B : List Bool) (k t : ℕ) (ht : startTime B k+successTime B≤t) :
    tail program B t≤rejectRate B^k := by
  classical
  rw [← bad_probability B k t ht]
  unfold tail
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card (show
    (Finset.univ.filter fun f : Fin t→Bool => (run program B f).state≠none) ⊆
      (Finset.univ.filter fun f : Fin t→Bool => ∀ j : Fin k,¬accepted B (extend f) j) from by
    intro f hf
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hf ⊢
    intro j hj
    apply hf
    have hh := accepts_halt B (extend f) k t ⟨j,j.isLt,hj⟩ ht
    simpa only [trace_extend,run] using hh)

end
end Contingency.BitModel.StackCode.IntegerDraw

 

 

namespace Contingency.BitModel.CoordinateLaw
open scoped BigOperators
noncomputable section

 theorem count_snoc {γ : Type*} [Fintype γ] (k : ℕ)
    (p : (Fin k→γ)→Prop) (q : γ→Prop) [DecidablePred p] [DecidablePred q] :
    (Finset.univ.filter fun f : Fin (k+1)→γ => p (fun i => f i.castSucc) ∧ q (f (Fin.last k))).card=
      (Finset.univ.filter q).card*(Finset.univ.filter p).card := by
  classical
  simp only [Finset.card_filter]
  rw [← (Fin.snocEquiv (fun _ : Fin (k+1) => γ)).sum_comp
    (fun f => if p (fun i => f i.castSucc) ∧ q (f (Fin.last k)) then (1:ℕ) else 0)]
  simp only [Fintype.sum_prod_type,Fin.snocEquiv_apply,Fin.snoc_castSucc,Fin.snoc_last]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hq : q v
  · simp [hq]
  · simp [hq]

end
end Contingency.BitModel.CoordinateLaw

 

 

 

open scoped BigOperators
namespace Contingency.BitModel.StackCode.IntegerDraw
open BinaryTrial
noncomputable section

def word (B : List Bool) (u : Fin (2^B.length)) : List Bool := List.ofFn ((wordEquiv B.length).symm u)

@[simp] theorem word_value (B : List Bool) (u : Fin (2^B.length)) : beValue (word B u)=u.val := by
  have hh := congrArg Fin.val ((wordEquiv B.length).apply_symm_apply u)
  exact hh

 theorem word_injective (B : List Bool) : Function.Injective (word B) := by
  intro u v he
  apply Fin.ext
  simpa only [word_value] using congrArg beValue he

def hit (B : List Bool) (f : ℕ→Bool) (j : ℕ) (u : Fin (2^B.length)) : Prop :=
  (∀ i : Fin j,¬accepted B f i) ∧ candidate B f j=word B u

instance (B : List Bool) (f : ℕ→Bool) (j : ℕ) (u : Fin (2^B.length)) : Decidable (hit B f j u) := by
  unfold hit
  infer_instance

 theorem hit_halts (B : List Bool) (f : ℕ→Bool) (j t : ℕ) (u : Fin (2^B.length))
    (hu : u.val≤beValue B) (hh : hit B f j u) (ht : startTime B j+successTime B≤t) :
    let result := (trace f 0 t).foldl (fun c b => step program b c) (initial program B)
    result.state=none ∧ result.memory.outputRev.reverse=word B u := by
  have ha : accepted B f j := by unfold accepted; rw [hh.2,word_value]; exact hu
  have hp : ∀ i<j,¬accepted B f i := fun i hi => hh.1 ⟨i,hi⟩
  simpa only [hh.2] using first_accept_later B f j t ha hp ht

 theorem hit_disjoint (B : List Bool) (f : ℕ→Bool) (i j : ℕ) (u : Fin (2^B.length))
    (hu : u.val≤beValue B) (hi : hit B f i u) (hj : hit B f j u) : i=j := by
  have hai : accepted B f i := by unfold accepted; rw [hi.2,word_value]; exact hu
  have haj : accepted B f j := by unfold accepted; rw [hj.2,word_value]; exact hu
  rcases lt_trichotomy i j with h|h|h
  · exact False.elim (hj.1 ⟨i,h⟩ hai)
  · exact h
  · exact False.elim (hi.1 ⟨j,h⟩ haj)

 theorem hit_coordinates_count (B : List Bool) (j : ℕ) (u : Fin (2^B.length)) :
    (Finset.univ.filter fun f : (Fin (j+1)×Fin B.length)→Bool =>
      (∀ i : Fin j,¬wordValue (fun a => f (i.castSucc,a))≤beValue B) ∧
      (fun a => f (Fin.last j,a))=(wordEquiv B.length).symm u).card=badCount B^j := by
  classical
  simp only [Finset.card_filter]
  change (∑ f,if (∀ i : Fin j,¬wordValue ((Equiv.curry _ _ _ f) i.castSucc)≤beValue B) ∧
    ((Equiv.curry _ _ _ f) (Fin.last j))=(wordEquiv B.length).symm u then 1 else 0)=_
  rw [(Equiv.curry (Fin (j+1)) (Fin B.length) Bool).sum_comp
    (fun f => if (∀ i : Fin j,¬wordValue (f i.castSucc)≤beValue B) ∧
      f (Fin.last j)=(wordEquiv B.length).symm u then (1:ℕ) else 0)]
  rw [← Finset.card_filter]
  rw [CoordinateLaw.count_snoc j (fun f : Fin j→Fin B.length→Bool => ∀ i,¬wordValue (f i)≤beValue B)
    (fun bs => bs=(wordEquiv B.length).symm u)]
  simp only [Finset.filter_eq',Finset.mem_univ,ite_true,Finset.card_singleton,one_mul]
  rw [CoordinateLaw.count_all j (fun bs : Fin B.length→Bool => ¬wordValue bs≤beValue B),bad_words]

 theorem hit_probability (B : List Bool) (j t : ℕ) (ht : startTime B (j+1)+successTime B≤t)
    (u : Fin (2^B.length)) :
    ((Finset.univ.filter fun f : Fin t→Bool => hit B (extend f) j u).card:ℝ)/2^t=
      rejectRate B^j/2^B.length := by
  classical
  let e := coord B (j+1) t ht
  let p : ((Fin (j+1)×Fin B.length)→Bool)→Prop := fun g =>
    (∀ i : Fin j,¬wordValue (fun a => g (i.castSucc,a))≤beValue B) ∧
      (fun a => g (Fin.last j,a))=(wordEquiv B.length).symm u
  have he : (Finset.univ.filter fun f : Fin t→Bool => hit B (extend f) j u)=
      (Finset.univ.filter fun f : Fin t→Bool => p (f∘e)) := by
    apply Finset.filter_congr
    intro f _
    dsimp only [hit,accepted,p,e,Function.comp_def]
    have hl := candidate_coord B (j+1) t ht f (Fin.last j)
    have hp := fun i : Fin j => candidate_coord B (j+1) t ht f i.castSucc
    simp only [Fin.val_last,Fin.val_castSucc] at hl hp
    simp only [hl,hp,word,List.ofFn_inj,wordValue]
  rw [he]
  have hh := CoordinateLaw.probability_restrict e (coord_injective B (j+1) t ht) p
  simp only [Fintype.card_fin,Fintype.card_prod] at hh
  rw [hh]
  change ((Finset.univ.filter _).card:ℝ)/2^((j+1)*B.length)=_
  rw [hit_coordinates_count]
  push_cast
  rw [Nat.add_mul,Nat.one_mul,pow_add,Nat.mul_comm j B.length,pow_mul]
  unfold rejectRate
  rw [div_pow]
  field_simp

end
end Contingency.BitModel.StackCode.IntegerDraw

 

 

 

open scoped BigOperators
open Filter
namespace Contingency.BitModel.StackCode.IntegerDraw
open BinaryTrial
noncomputable section

 theorem rate_nonneg (B : List Bool) : 0≤rejectRate B := by unfold rejectRate; positivity
 theorem rate_lt_one (B : List Bool) : rejectRate B<1 := by
  have hp : 0<2^B.length := by positivity
  have hb : badCount B<2^B.length := by unfold badCount; omega
  unfold rejectRate
  apply (div_lt_one (by positivity)).2
  exact_mod_cast hb

 theorem rate_le_half (B : List Bool) (h : 2^B.length≤2*(beValue B+1)) : rejectRate B≤1/2 := by
  have hb := Nat.sub_add_cancel (Nat.succ_le_of_lt (bound_lt B))
  change badCount B+(beValue B+1)=2^B.length at hb
  have hn : 2*badCount B≤2^B.length := by omega
  have hr : (2:ℝ)*(badCount B:ℝ)≤(2:ℝ)^B.length := by exact_mod_cast hn
  unfold rejectRate
  apply (div_le_iff₀ (by positivity : (0:ℝ)<2^B.length)).2
  nlinarith

 theorem grouped_geometric (C : ℕ) (hC : 0<C) (q : ℝ) (hq : 0≤q) (hq1 : q<1) :
    Summable (fun t : ℕ => q^(t/C)) ∧ (∑' t : ℕ,q^(t/C))=(C:ℝ)/(1-q) := by
  let : NeZero C := ⟨by omega⟩
  have hs : Summable (fun p : ℕ×Fin C => q^p.1) := by
    apply (summable_prod_of_nonneg (fun _ => pow_nonneg hq _)).2
    constructor
    · intro n; exact Summable.of_finite
    · simpa [tsum_fintype] using (summable_geometric_of_lt_one hq hq1).mul_left (C:ℝ)
  have hh : Summable (fun t : ℕ => q^(t/C)) := by
    simpa [Function.comp_def,Nat.divModEquiv_apply] using (Nat.divModEquiv C).summable_iff.mpr hs
  refine ⟨hh,?_⟩
  have he := (Nat.divModEquiv C).tsum_eq (fun p : ℕ×Fin C => q^p.1)
  simp only [Nat.divModEquiv_apply] at he
  rw [he,hs.tsum_prod]
  simp only [tsum_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [tsum_mul_left,tsum_geometric_of_lt_one hq hq1]
  rfl

 theorem tail_nonneg (P : Program) (xs : List Bool) (t : ℕ) : 0≤tail P xs t := by
  unfold tail
  positivity

 theorem tail_le_one (P : Program) (xs : List Bool) (t : ℕ) : tail P xs t≤1 := by
  classical
  unfold tail
  apply (div_le_one (by positivity)).2
  have hc := Finset.card_filter_le (Finset.univ : Finset (Fin t→Bool)) (fun f => (run P xs f).state≠none)
  simp only [Finset.card_univ,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin] at hc
  exact_mod_cast hc

 theorem shifted_tail_bound (B : List Bool) (t : ℕ) :
    tail program B (t+(prepTime B+successTime B))≤rejectRate B^(t/retryTime B) := by
  apply tail_bound
  have hh := Nat.div_mul_le_self t (retryTime B)
  dsimp [startTime]
  omega

 theorem stack_summable (B : List Bool) : Summable (tail program B) := by
  have hp : 0<retryTime B := by unfold retryTime; omega
  have hs := (grouped_geometric (retryTime B) hp (rejectRate B) (rate_nonneg B) (rate_lt_one B)).1
  apply (summable_nat_add_iff (prepTime B+successTime B)).1
  exact hs.of_nonneg_of_le (fun _ => tail_nonneg _ _ _) (shifted_tail_bound B)

 theorem stack_expected (B : List Bool) :
    (∑' t,tail program B t)≤(prepTime B+successTime B:ℕ)+(retryTime B:ℝ)/(1-rejectRate B) := by
  have hp : 0<retryTime B := by unfold retryTime; omega
  have hg := grouped_geometric (retryTime B) hp (rejectRate B) (rate_nonneg B) (rate_lt_one B)
  have hs := stack_summable B
  have hu := (summable_nat_add_iff (prepTime B+successTime B)).2 hs
  rw [← hs.sum_add_tsum_nat_add (prepTime B+successTime B)]
  apply add_le_add
  · calc
      _ ≤ ∑ _i∈Finset.range (prepTime B+successTime B),(1:ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        exact tail_le_one _ _ _
      _ = _ := by simp
  · exact (hu.tsum_le_tsum (shifted_tail_bound B) hg.1).trans_eq hg.2

 theorem stack_linear_expected (B : List Bool) (h : 2^B.length≤2*(beValue B+1)) :
    (∑' t,tail program B t)≤(26*B.length+15:ℕ) := by
  have hi := rate_le_half B h
  have hp : 0<1-rejectRate B := by linarith [rate_lt_one B]
  apply (stack_expected B).trans
  have hd : (retryTime B:ℝ)/(1-rejectRate B)≤2*retryTime B := by
    apply (div_le_iff₀ hp).2
    have hn : (0:ℝ)≤retryTime B := by positivity
    nlinarith
  dsimp [prepTime,successTime,retryTime] at hd ⊢
  push_cast at hd ⊢
  linarith

 theorem machine_summable (B : List Bool) : Summable (machine.tail B) :=
  tail_summable_compile program B (stack_summable B)

 theorem machine_halts_ae (B : List Bool) : Tendsto (machine.tail B) atTop (nhds 0) :=
  (machine_summable B).tendsto_atTop_zero

 theorem machine_linear_expected (B : List Bool) (h : 2^B.length≤2*(beValue B+1)) :
    (∑' t,machine.tail B t)≤(52*B.length+30:ℕ) := by
  rw [machine,expected_compile program B (stack_summable B)]
  have hh := stack_linear_expected B h
  push_cast at hh ⊢
  linarith

end
end Contingency.BitModel.StackCode.IntegerDraw

 

 

 

open scoped BigOperators
open Filter
namespace Contingency.BitModel.StackCode
open IntegerDraw
noncomputable section

 theorem run_prefix_halt (P : Program) (xs : List Bool) (s t : ℕ) (hst : s≤t) (f : Fin t→Bool)
    (hs : (run P xs (fun i : Fin s => f ⟨i,lt_of_lt_of_le i.isLt hst⟩)).state=none) :
    run P xs f=run P xs (fun i : Fin s => f ⟨i,lt_of_lt_of_le i.isLt hst⟩) := by
  have hp : trace (extend f) 0 s=List.ofFn (fun i : Fin s => f ⟨i,lt_of_lt_of_le i.isLt hst⟩) := by
    unfold trace
    congr 1
    funext i
    simp [extend,lt_of_lt_of_le i.isLt hst]
  have ht : List.ofFn f=trace (extend f) 0 s ++ trace (extend f) s (t-s) := by
    rw [← trace_extend f]
    have hh := trace_append (extend f) 0 s (t-s)
    simpa [Nat.add_sub_cancel' hst] using hh.symm
  unfold run
  rw [ht,List.foldl_append,hp]
  change (trace (extend f) s (t-s)).foldl (fun c b => step P b c) _=_
  generalize hc : run P xs (fun i : Fin s => f ⟨i,lt_of_lt_of_le i.isLt hst⟩)=c at hs
  change (trace (extend f) s (t-s)).foldl (fun c b => step P b c) (run P xs _)=run P xs _
  rw [hc]
  rcases c with ⟨state,m⟩
  change state=none at hs
  subst state
  exact halted_fold P _ m

 theorem mass_nonneg (P : Program) (xs out : List Bool) (t : ℕ) : 0 ≤ mass P xs out t := by
  unfold mass
  positivity

 theorem mass_le_one (P : Program) (xs out : List Bool) (t : ℕ) : mass P xs out t≤1 := by
  classical
  unfold mass
  apply (div_le_one (by positivity)).2
  have hh := Finset.card_filter_le (Finset.univ : Finset (Fin t→Bool))
    (fun f => (run P xs f).state=none ∧ (run P xs f).memory.outputRev.reverse=out)
  simp only [Finset.card_univ,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin] at hh
  exact_mod_cast hh

 theorem mass_mono (P : Program) (xs out : List Bool) : Monotone (mass P xs out) := by
  classical
  intro s t hst
  let e : Fin s→Fin t := fun i => ⟨i,lt_of_lt_of_le i.isLt hst⟩
  have hi : Function.Injective e := by
    intro i j h
    exact Fin.ext (congrArg (fun x : Fin t => x.val) h)
  let p : (Fin s→Bool)→Prop := fun f => (run P xs f).state=none ∧ (run P xs f).memory.outputRev.reverse=out
  have he := CoordinateLaw.probability_restrict e hi p
  simp only [Fintype.card_fin] at he
  unfold mass
  change ((Finset.univ.filter p).card:ℝ)/2^s≤_
  rw [← he]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card (show
    (Finset.univ.filter fun f : Fin t→Bool => p (f∘e)) ⊆
      (Finset.univ.filter fun f : Fin t→Bool => (run P xs f).state=none ∧ (run P xs f).memory.outputRev.reverse=out) from by
    intro f hf
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hf ⊢
    have hh := run_prefix_halt P xs s t hst f hf.1
    rw [hh]
    exact hf)

 theorem mass_limit_exists (P : Program) (xs out : List Bool) :
    ∃ r : ℝ,Tendsto (mass P xs out) atTop (nhds r) :=
  ⟨_,tendsto_atTop_ciSup (mass_mono P xs out) ⟨1,by
    rintro _ ⟨t,rfl⟩
    exact mass_le_one P xs out t⟩⟩

 theorem sum_mass_le_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Program) (xs : List Bool) (out : ι→List Bool) (ho : Function.Injective out) (t : ℕ) :
    ∑ i,mass P xs (out i) t≤1 := by
  classical
  simp only [mass,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [← Finset.sum_div,Finset.sum_comm]
  apply (div_le_one (by positivity)).2
  calc
    _ ≤ ∑ _f : Fin t→Bool,(1:ℝ) := by
      apply Finset.sum_le_sum
      intro f _
      have hc : (Finset.univ.filter fun i : ι => (run P xs f).state=none ∧
        (run P xs f).memory.outputRev.reverse=out i).card≤1 := by
        apply Finset.card_le_one.mpr
        intro i hi j hj
        simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hi hj
        exact ho (hi.2.symm.trans hj.2)
      have hcr : ((Finset.univ.filter fun i : ι => (run P xs f).state=none ∧
        (run P xs f).memory.outputRev.reverse=out i).card:ℝ)≤1 := by exact_mod_cast hc
      simpa only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero] using hcr
    _ = _ := by simp

end
end Contingency.BitModel.StackCode

 

 

 

open scoped BigOperators
open Filter
namespace Contingency.BitModel.StackCode.IntegerDraw
open BinaryTrial
noncomputable section

 theorem initial_mass_lower (B : List Bool) (k t : ℕ) (ht : startTime B k+successTime B≤t)
    (u : Fin (2^B.length)) (hu : u.val≤beValue B) :
    (∑ j∈Finset.range k,rejectRate B^j/2^B.length) ≤ mass program B (word B u) t := by
  classical
  let s : ℕ→Finset (Fin t→Bool) := fun j => Finset.univ.filter fun f => hit B (extend f) j u
  have hsub : (Finset.range k).biUnion s ⊆
      (Finset.univ.filter fun f : Fin t→Bool => (run program B f).state=none ∧
        (run program B f).memory.outputRev.reverse=word B u) := by
    intro f hf
    obtain ⟨j,hj,hf⟩ := Finset.mem_biUnion.mp hf
    have hhit : hit B (extend f) j u := (Finset.mem_filter.mp hf).2
    have hjk : j<k := Finset.mem_range.mp hj
    have hh := hit_halts B (extend f) j t u hu hhit (by
      have hm := Nat.mul_le_mul_right (retryTime B) (Nat.le_of_lt hjk)
      dsimp [startTime] at ht ⊢
      omega)
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    simpa only [trace_extend,run] using hh
  have hdis : (↑(Finset.range k) : Set ℕ).PairwiseDisjoint s := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro f hi hj
    exact hij (hit_disjoint B (extend f) i j u hu (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2)
  calc
    _ = ∑ j∈Finset.range k,((s j).card:ℝ)/2^t := by
      apply Finset.sum_congr rfl
      intro j hj
      apply (hit_probability B j t _ u).symm
      have hm := Nat.mul_le_mul_right (retryTime B) (Nat.succ_le_of_lt (Finset.mem_range.mp hj))
      simp only [Nat.succ_eq_add_one] at hm
      dsimp [startTime] at ht ⊢
      omega
    _ = (((Finset.range k).biUnion s).card:ℝ)/2^t := by
      rw [Finset.card_biUnion hdis,Nat.cast_sum,Finset.sum_div]
    _ ≤ _ := by
      unfold mass
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast Finset.card_le_card hsub

 theorem hit_series (B : List Bool) :
    HasSum (fun j : ℕ => rejectRate B^j/2^B.length) (1/(beValue B+1:ℝ)) := by
  have hh := (hasSum_geometric_of_lt_one (rate_nonneg B) (rate_lt_one B)).div_const ((2:ℝ)^B.length)
  have hb := Nat.sub_add_cancel (Nat.succ_le_of_lt (bound_lt B))
  change badCount B+(beValue B+1)=2^B.length at hb
  have hr : (badCount B:ℝ)+(beValue B+1:ℝ)=(2:ℝ)^B.length := by exact_mod_cast hb
  have hm : (beValue B+1:ℝ)≠0 := by positivity
  have he : (1 - rejectRate B)⁻¹ / (2:ℝ)^B.length = 1/(beValue B+1:ℝ) := by
    unfold rejectRate
    field_simp
    rw [show (2:ℝ)^B.length - badCount B = beValue B+1 by linarith]
    exact div_self hm
  simpa only [he] using hh

 theorem limit_lower (B : List Bool) (u : Fin (2^B.length)) (hu : u.val≤beValue B)
    (r : ℝ) (hr : Tendsto (mass program B (word B u)) atTop (nhds r)) : 1/(beValue B+1:ℝ)≤r := by
  apply le_of_tendsto' (hit_series B).tendsto_sum_nat
  intro k
  apply ge_of_tendsto hr
  filter_upwards [eventually_ge_atTop (startTime B k+successTime B)] with t ht
  exact initial_mass_lower B k t ht u hu

 def validWord (B : List Bool) (u : Fin (beValue B+1)) : List Bool :=
  word B ⟨u,Nat.lt_of_lt_of_le u.isLt (Nat.succ_le_of_lt (bound_lt B))⟩

 theorem validWord_injective (B : List Bool) : Function.Injective (validWord B) := by
  intro u v he
  have hh := word_injective B he
  exact Fin.ext (congrArg (fun x : Fin (2^B.length) => x.val) hh)

 theorem stack_uniform (B : List Bool) (u : Fin (beValue B+1)) :
    Tendsto (mass program B (validWord B u)) atTop (nhds (1/(beValue B+1:ℝ))) := by
  choose r hr using fun v : Fin (beValue B+1) => mass_limit_exists program B (validWord B v)
  have hlo : ∀ v,1/(beValue B+1:ℝ)≤r v := by
    intro v
    exact limit_lower B ⟨v,Nat.lt_of_lt_of_le v.isLt (Nat.succ_le_of_lt (bound_lt B))⟩ (Nat.le_of_lt_succ v.isLt) (r v) (hr v)
  have hsum : ∑ v,r v≤1 := by
    apply le_of_tendsto' (tendsto_finsetSum Finset.univ (fun v _ => hr v))
    intro t
    exact sum_mass_le_one program B (validWord B) (validWord_injective B) t
  have he : ∑ v : Fin (beValue B+1),(1/(beValue B+1:ℝ))=1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    field_simp
  have heach : ∀ v,r v=1/(beValue B+1:ℝ) := by
    intro v
    apply le_antisymm _ (hlo v)
    have hh := Finset.sum_le_sum (s:=Finset.univ.erase v) (fun i _ => hlo i)
    have h1 := Finset.sum_erase_add Finset.univ r (Finset.mem_univ v)
    have h2 := Finset.sum_erase_add Finset.univ (fun _ : Fin (beValue B+1) => 1/(beValue B+1:ℝ)) (Finset.mem_univ v)
    linarith
  simpa only [heach u] using hr u

 theorem machine_uniform (B : List Bool) (u : Fin (beValue B+1)) :
    Tendsto (machine.mass B (validWord B u)) atTop (nhds (1/(beValue B+1:ℝ))) :=
  mass_limit_compile program B (validWord B u) _ (stack_uniform B u)

end
end Contingency.BitModel.StackCode.IntegerDraw

 

 

 

namespace Contingency.BitModel.StackCode.IntegerDraw
open BinaryTrial
noncomputable section

def drawBits (B : List Bool) (f : ℕ→Bool) (j : ℕ) (i : Fin B.length) : Bool :=
  f (startTime B j+i*4+2)

theorem candidate_bits (B : List Bool) (f : ℕ→Bool) (j : ℕ) :
    candidate B f j=List.ofFn (drawBits B f j) := by
  unfold candidate streamDigits
  rw [digits_coin]
  congr 1
  funext i
  change f (startTime B j+(2+4*i.val))=f (startTime B j+i.val*4+2)
  congr 1
  omega

theorem wordValue_false (n : ℕ) : wordValue (fun _ : Fin n => false)=0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [wordValue_succ]; simp [ih]

theorem extend_accepts (B : List Bool) {t : ℕ} (f : Fin t→Bool) :
    accepted B (extend f) t := by
  have hg : drawBits B (extend f) t = fun _ => false := by
    funext i
    have hr : 1≤retryTime B := by unfold retryTime; omega
    have ht : t ≤ startTime B t := by
      unfold startTime
      have hm := Nat.mul_le_mul_left t hr
      omega
    simp [drawBits,extend,show ¬startTime B t+i*4+2<t by omega]
  unfold accepted
  rw [candidate_bits,hg]
  change wordValue (fun _ : Fin B.length => false)≤_
  rw [wordValue_false]
  exact Nat.zero_le _

theorem validWord_bits (B : List Bool) (f : Fin B.length→Bool) (hf : wordValue f≤beValue B) :
    validWord B ⟨wordValue f,Nat.lt_succ_of_le hf⟩=List.ofFn f := by
  unfold validWord word
  congr 1
  apply (wordEquiv B.length).injective
  rw [Equiv.apply_symm_apply]
  apply Fin.ext
  rfl

theorem halted_trace (P : Program) (B : List Bool) (f : ℕ→Bool) (t T : ℕ) (htT : t≤T)
    (hh : ((trace f 0 t).foldl (fun c b => step P b c) (initial P B)).state=none) :
    (trace f 0 T).foldl (fun c b => step P b c) (initial P B)=
      (trace f 0 t).foldl (fun c b => step P b c) (initial P B) := by
  have he : trace f 0 T=trace f 0 t ++ trace f t (T-t) := by
    simpa only [Nat.zero_add,Nat.add_sub_cancel' htT] using (trace_append f 0 t (T-t)).symm
  rw [he,List.foldl_append]
  generalize hc : (trace f 0 t).foldl (fun c b => step P b c) (initial P B)=c at hh ⊢
  rcases c with ⟨s,m⟩
  change s=none at hh
  subst s
  exact halted_fold P _ m

theorem stack_safe (B : List Bool) {t : ℕ} (f : Fin t→Bool) (hh : (run program B f).state=none) :
    ∃ u : Fin (beValue B+1),(run program B f).memory.outputRev.reverse=validWord B u := by
  classical
  have ha : ∃ j,accepted B (extend f) j := ⟨t,extend_accepts B f⟩
  let j := Nat.find ha
  have hj : accepted B (extend f) j := Nat.find_spec ha
  have hp : ∀ i<j,¬accepted B (extend f) i := fun i hi => Nat.find_min ha hi
  let T := max t (startTime B j+successTime B)
  have hr := first_accept_later B (extend f) j T hj hp (le_max_right _ _)
  have he := halted_trace program B (extend f) t T (le_max_left _ _) (by simpa only [trace_extend,run] using hh)
  rw [he] at hr
  simp only [trace_extend] at hr
  have hv : wordValue (drawBits B (extend f) j)≤beValue B := by
    simpa only [accepted,candidate_bits,wordValue] using hj
  refine ⟨⟨wordValue (drawBits B (extend f) j),Nat.lt_succ_of_le hv⟩,?_⟩
  rw [validWord_bits B _ hv]
  simpa only [candidate_bits,run] using hr.2

end
end Contingency.BitModel.StackCode.IntegerDraw

end

end OAI
