import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.RawCount
import OAI.Combinatorics.KMedianRecovery.Sampling.SamplingStateMachine

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
def config (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J : ℕ) : List Bool :=
  encode [n.bits,RationalMatrix.encode δ,BinaryFinSet.encode D,BinaryFinSet.encode F,BinaryFinSet.encode S,
    BinaryRational.encode Δ,BinaryRational.encode P,BinaryRational.encode κ,m.bits,BinaryMenu.weights M E J]
noncomputable def c (i : ℕ) (x : List Bool) : List Bool := field i (extractPrefix x)
noncomputable def c_computes (i : ℕ) : PolyComputes (c i) := extractPrefix_computes.comp (field_computes i)
noncomputable def deleted (x : List Bool) : List Bool := extractPrefix (discardPrefix x)
noncomputable def leaves (x : List Bool) : List Bool := discardPrefix (discardPrefix x)
noncomputable def deleted_computes : PolyComputes deleted := discardPrefix_computes.comp extractPrefix_computes
noncomputable def leaves_computes : PolyComputes leaves := discardPrefix_computes.comp discardPrefix_computes
noncomputable def undeleted (x : List Bool) : List Bool := BinaryNatSet.diff (pairBits (c 4 x,deleted x))
noncomputable def undeleted_computes : PolyComputes undeleted := ((c_computes 4).pair deleted_computes).comp BinaryNatSet.diff_computes
noncomputable def reference (x : List Bool) : List Bool := encode [c 0 x,c 5 x,undeleted x,leaves x]
noncomputable def reference_computes : PolyComputes reference := cons_computes (c_computes 0)
  (cons_computes (c_computes 5) (cons_computes undeleted_computes (cons_computes leaves_computes (const_computes []))))
noncomputable def oracle (x : List Bool) : List Bool := encode [c 1 x,c 2 x,reference x]
noncomputable def oracle_computes : PolyComputes oracle := cons_computes (c_computes 1)
  (cons_computes (c_computes 2) (cons_computes reference_computes (const_computes [])))
lemma reference_pair (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J : ℕ) (s : RationalSampling.State n) :
    reference (pairBits (config δ D F S Δ P κ m M E J,BinarySamplingState.encode s))=BinarySamplingState.context Δ S s := by
  simp only [reference,c,config,extractPrefix_pairBits,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,
    undeleted,deleted,BinarySamplingState.encode,discardPrefix_pairBits,BinaryFinSet.diff_pack,leaves,BinarySamplingState.context]
lemma oracle_pair (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J : ℕ) (s : RationalSampling.State n) :
    oracle (pairBits (config δ D F S Δ P κ m M E J,BinarySamplingState.encode s))=BinarySamplingOracle.pack δ D S Δ s := by
  rw [oracle,reference_pair]
  simp only [c,config,extractPrefix_pairBits,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,BinarySamplingOracle.pack]
end MetricKMedianRecovery.BitMachine.BinarySampler

namespace MetricKMedianRecovery.Dyadic.Canonical
open FiniteSampling
variable {A : Type*}
def select (default : A) : List (A×ℕ) → ℕ → A
  | [],_=>default
  | (a,w)::ws,v=>if v<w then a else select default ws (v-w)
lemma select_sum (d : A) (ws : List (A×ℕ)) (T : ℕ)
    (hT : (ws.map Prod.snd).sum≤T) (f : A→ℝ) :
    (∑ v∈Finset.range T, f (select d ws v))=
      (ws.map (fun aw=>(aw.2:ℝ)*f aw.1)).sum+(T-(ws.map Prod.snd).sum)*f d := by
  induction ws generalizing T with
  | nil=>simp [select]
  | cons aw ws ih=>
    rcases aw with ⟨a,w⟩
    simp only [List.map_cons,List.sum_cons] at hT ⊢
    have hw : w≤T := by omega
    have ht : (ws.map Prod.snd).sum≤T-w := by omega
    conv_lhs => rw [show T=w+(T-w) by omega,Finset.sum_range_add]
    have hh : (∑ v∈Finset.range w,f (select d ((a,w)::ws) v))=(w:ℝ)*f a := by
      simp only [select]
      rw [Finset.sum_congr rfl (fun v hv=>congrArg f (ite_eq_left (Finset.mem_range.mp hv)))]
      simp
    rw [hh]
    have he : (∑ v∈Finset.range (T-w),f (select d ((a,w)::ws) (w+v)))=
        ∑ v∈Finset.range (T-w),f (select d ws v) := by
      apply Finset.sum_congr rfl
      intro v _
      simp [select,show ¬w+v<w by omega]
    rw [he,ih (T-w) ht]
    rw [Nat.cast_sub hw,Nat.cast_add]
    ring
variable [Fintype A] [DecidableEq A]
noncomputable def list (p : A→ℝ) (b : ℕ) (as : List A) : List (A×ℕ) := as.map (fun a=>(a,rawCount p b a))
noncomputable def draw (p : A→ℝ) (b : ℕ) (default : A) (as : List A) (bits : Fin b→Bool) : A :=
  select default (list p b as) (Categorical.uniformBits b bits).val
omit [DecidableEq A] in
lemma list_sum (p : A→ℝ) (b : ℕ) (as : List A) (h : as.Perm (Finset.univ.toList)) :
    ((list p b as).map Prod.snd).sum=∑ a,rawCount p b a := by
  simp only [list,List.map_map,Function.comp_def]
  rw [(h.map (rawCount p b)).sum_eq]
  exact Finset.sum_map_toList _ _
lemma draw_average (p : A→ℝ) (hp : ∀ a,0≤p a) (ht : ∑ a,p a=1)
    (b : ℕ) (d : A) (as : List A) (ha : as.Perm (Finset.univ.toList)) (f : A→ℝ) :
    average (fun bits=>f (draw p b d as bits))=∑ a,weight p b d a*f a := by
  classical
  rw [average,Fintype.expect_eq_sum_div_card]
  have he := Fintype.sum_equiv (Categorical.uniformBits b)
    (fun bits=>f (draw p b d as bits)) (fun v=>f (select d (list p b as) v.val)) (fun _=>rfl)
  rw [he,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]
  rw [←Finset.sum_range (fun v=>f (select d (list p b as) v))]
  have hle : ((list p b as).map Prod.snd).sum≤2^b := by
    rw [list_sum _ _ _ ha]; exact rawCount_sum_le p hp ht b
  rw [select_sum d (list p b as) (2^b) hle f,list_sum _ _ _ ha]
  have hs : ((list p b as).map (fun aw=>(aw.2:ℝ)*f aw.1)).sum=∑ a,(rawCount p b a:ℝ)*f a := by
    simp only [list,List.map_map,Function.comp_def]
    rw [(ha.map (fun a=>(rawCount p b a:ℝ)*f a)).sum_eq]
    exact Finset.sum_map_toList _ _
  rw [hs]
  simp only [weight,count,Nat.cast_add,add_div,add_mul,Finset.sum_add_distrib]
  rw [Finset.sum_div]
  congr 1
  · apply Finset.sum_congr rfl
    intro a _
    ring
  · simp only [Nat.cast_ite,Nat.cast_zero,ite_div,zero_div,ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    rw [Nat.cast_sub (rawCount_sum_le p hp ht b),Nat.cast_pow,Nat.cast_ofNat]
    ring
end MetricKMedianRecovery.Dyadic.Canonical

namespace MetricKMedianRecovery.Dyadic.Canonical

def rank : List ℕ→ℕ→Option ℕ
  | [],_=>none
  | w::ws,v=>if v<w then some 0 else (rank ws (v-w)).map Nat.succ
def findRank (ws : List ℕ) (v : ℕ) : Option ℕ :=
  (List.range ws.length).find? (fun j=>decide (v<(ws.take (j+1)).sum))
lemma findRank_eq (ws : List ℕ) (v : ℕ) : findRank ws v=rank ws v := by
  induction ws generalizing v with
  | nil=>rfl
  | cons w ws ih=>
    by_cases h : v<w
    · simp [findRank,List.range_succ_eq_map,rank,h]
    · have hzero : decide (v<(List.take (0+1) (w::ws)).sum)=false := by
        simpa using h
      unfold findRank
      rw [List.length_cons,List.range_succ_eq_map,List.find?_cons,hzero]
      dsimp only
      rw [List.find?_map]
      have he : ((fun j=>decide (v<(List.take (j+1) (w::ws)).sum)) ∘ Nat.succ)=
          (fun j=>decide (v-w<(ws.take (j+1)).sum)) := by
        funext j
        apply decide_eq_decide.mpr
        change (v<w+(ws.take (j+1)).sum) ↔ _
        omega
      rw [he,rank,ite_eq_right h]
      exact congrArg (Option.map Nat.succ) (ih (v-w))
lemma select_relabel {A B : Type*} (g : A→B) (d : A) (ws : List (A×ℕ)) (v : ℕ) :
    select (g d) (ws.map (fun aw=>(g aw.1,aw.2))) v=g (select d ws v) := by
  induction ws generalizing v with
  | nil=>rfl
  | cons aw ws ih=>
    simp only [List.map_cons,select]
    split_ifs <;> simp only [ih]
lemma rank_select (ws : List ℕ) (v i : ℕ) :
    select none ((ws.zipIdx i).map (fun wi=>(some wi.2,wi.1))) v=
      (rank ws v).map (fun j=>i+j) := by
  induction ws generalizing v i with
  | nil=>rfl
  | cons w ws ih=>
    simp only [List.zipIdx_cons,List.map_cons,select,rank]
    split_ifs with h
    · simp
    · rw [ih]
      simp only [Option.map_map,Function.comp_def]
      congr 1
      funext j
      omega
lemma rank_select_zero (ws : List ℕ) (v : ℕ) :
    select none ((ws.zipIdx).map (fun wi=>(some wi.2,wi.1))) v=rank ws v := by
  simpa using rank_select ws v 0
lemma select_index (d : ℕ) (ws : List ℕ) (v : ℕ) :
    select d ((ws.zipIdx).map (fun wi=>(wi.2,wi.1))) v=(rank ws v).getD d := by
  have hh:=select_relabel (fun x : Option ℕ=>x.getD d) none
    ((ws.zipIdx).map (fun wi=>(some wi.2,wi.1))) v
  simpa only [List.map_map,Function.comp_def,Option.getD_none,Option.getD_some,rank_select_zero] using hh
end MetricKMedianRecovery.Dyadic.Canonical

end OAI
