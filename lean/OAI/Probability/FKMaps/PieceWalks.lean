import OAI.Probability.FKMaps.ExcursionKernel
import OAI.Probability.FKMaps.InventoryRenewal
import OAI.Probability.FKMaps.WordCoefficients

namespace OAI

noncomputable section
open List Equiv Equiv.Perm
open scoped BigOperators ENNReal
namespace FKCRT.Inventory
attribute [local instance] Classical.propDecidable

lemma wordSeries_substitution (t r : ℝ≥0∞) :
    wordSeries t r=1+∑' c : Core,t^flexibleCount c.val []*(r*wordSeries t r)^c.val.length := by
  let : DecidableEq EmptyTypedWord := fun _ _ => Classical.propDecidable _
  let e : EmptyTypedWord := ⟨[],rfl⟩
  have hne : (∑' w : EmptyTypedWord,if w=e then 0 else wordMonomial t r w.val)=
      ∑' w : NonemptyTypedWord,wordMonomial t r w.val.val := by
    calc
      _=∑' w : EmptyTypedWord,
          Set.indicator {w : EmptyTypedWord | w.val≠[]} (fun w => wordMonomial t r w.val) w := by
        apply tsum_congr
        intro w
        by_cases hw : w.val=[]
        · have hwe : w=e := Subtype.ext hw
          simp [hwe,e,Set.indicator]
        · have hwe : w≠e := fun h => hw (congrArg Subtype.val h)
          simp [hw,hwe,Set.indicator]
      _ = _ := (tsum_subtype {w : EmptyTypedWord | w.val≠[]} (fun w => wordMonomial t r w.val)).symm
  calc
    wordSeries t r=wordMonomial t r e.val+
        ∑' w : EmptyTypedWord,if w=e then 0 else wordMonomial t r w.val :=
      by simpa only [wordSeries] using (ENNReal.tsum_eq_add_tsum_ite
        (f := fun w : EmptyTypedWord => wordMonomial t r w.val) e)
    _=1+∑' w : NonemptyTypedWord,wordMonomial t r w.val.val :=
      congrArg₂ (·+·) (wordMonomial_nil t r) hne
    _ = _ := by rw [nonempty_word_series]

def emptyAtSizeEquiv (m : ℕ) :
    {w : EmptyTypedWord // w.val.length/2=m} ≃ {w // w∈typedEmptyWords (2*m)} where
  toFun w := ⟨w.val.val,Finset.mem_filter.mpr ⟨mem_wordsOfLength.mpr (by
      obtain ⟨k,hk⟩ := empty_length_even w.val
      have hm := w.property
      omega),w.val.property⟩⟩
  invFun w := ⟨⟨w.val,(Finset.mem_filter.mp w.property).2⟩,by
    have h := mem_wordsOfLength.mp (Finset.mem_filter.mp w.property).1
    change w.val.length/2=m
    omega⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Arbitrary nonnegative observables partition by the actual even length. -/
lemma empty_tsum_by_size (f : List TypedLetter→ℝ≥0∞) :
    (∑' w : EmptyTypedWord,f w.val)=∑' m : ℕ,∑ w∈typedEmptyWords (2*m),f w := by
  rw [← (Equiv.sigmaFiberEquiv (fun w : EmptyTypedWord => w.val.length/2)).tsum_eq]
  change (∑' d : Σ m : ℕ,{w : EmptyTypedWord // w.val.length/2=m},f d.2.val.val)=_
  rw [ENNReal.tsum_sigma (fun (m : ℕ) (w : {w : EmptyTypedWord // w.val.length/2=m}) => f w.val.val)]
  apply tsum_congr
  intro m
  rw [← (emptyAtSizeEquiv m).symm.tsum_eq]
  change (∑' w : {w // w∈typedEmptyWords (2*m)},f w.val)=_
  rw [tsum_fintype]
  exact (Finset.sum_subtype (typedEmptyWords (2*m)) (fun _ => Iff.rfl) f).symm

def typedCoefficient (t : ℝ≥0∞) (m : ℕ) : ℝ≥0∞ :=
  ∑ w∈typedEmptyWords (2*m),t^flexibleCount w []

lemma wordSeries_coefficients (t r : ℝ≥0∞) :
    wordSeries t r=∑' m : ℕ,typedCoefficient t m*(r^2)^m := by
  rw [wordSeries,empty_tsum_by_size]
  apply tsum_congr
  intro m
  rw [typedCoefficient,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro w hw
  have hl := mem_wordsOfLength.mp (Finset.mem_filter.mp hw).1
  rw [wordMonomial,hl,pow_mul]

def coreSubtypeEquiv : Core ≃ {w : EmptyTypedWord // CoreWord w.val} where
  toFun c := ⟨⟨c.val,coreWord_empty _ c.property⟩,c.property⟩
  invFun w := ⟨w.val.val,w.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma core_tsum_by_size (f : List TypedLetter→ℝ≥0∞) :
    (∑' c : Core,f c.val)=
      ∑' m : ℕ,∑ w∈(typedEmptyWords (2*m)).filter CoreWord,f w := by
  rw [← coreSubtypeEquiv.symm.tsum_eq]
  change (∑' c : {w : EmptyTypedWord // CoreWord w.val},f c.val.val)=_
  calc
    _=∑' w : EmptyTypedWord,Set.indicator {w : EmptyTypedWord | CoreWord w.val}
        (fun w => f w.val) w := tsum_subtype _ _
    _=∑' w : EmptyTypedWord,if CoreWord w.val then f w.val else 0 := rfl
    _=∑' m : ℕ,∑ w∈typedEmptyWords (2*m),if CoreWord w then f w else 0 :=
      empty_tsum_by_size (fun w => if CoreWord w then f w else 0)
    _=_ := by
      apply tsum_congr
      intro m
      simp only [Finset.sum_filter]

def coreCoefficient (t : ℝ≥0∞) (m : ℕ) : ℝ≥0∞ :=
  ∑ w∈(typedEmptyWords (2*m)).filter CoreWord,t^flexibleCount w []

lemma core_series_coefficients (t r : ℝ≥0∞) :
    (∑' c : Core,t^flexibleCount c.val []*r^c.val.length)=
      ∑' m : ℕ,coreCoefficient t m*(r^2)^m := by
  rw [core_tsum_by_size (fun w => t^flexibleCount w []*r^w.length)]
  apply tsum_congr
  intro m
  rw [coreCoefficient,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro w hw
  have hl := mem_wordsOfLength.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).1
  rw [hl,pow_mul]

/-- Exact source T=1+Phi_+(u*T²), now for the actual connected-core
coefficients extracted from the original inventory words. -/
theorem wordSeries_core_coefficients (t r : ℝ≥0∞) :
    wordSeries t r=1+∑' m : ℕ,coreCoefficient t m*(r^2*wordSeries t r^2)^m := by
  calc
    wordSeries t r=1+∑' c : Core,t^flexibleCount c.val []*(r*wordSeries t r)^c.val.length :=
      wordSeries_substitution t r
    _=_ := by rw [core_series_coefficients,mul_pow]

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk

lemma kernel_uniform_bound : ∃ C : ℝ,0<C ∧ ∀ n : ℕ,0<n → ∀ z : ℤ,
    kernel n z ≤ C/Real.sqrt n := by
  obtain ⟨E,hE,hEt,h⟩ := kernel_uniform_local_limit
  obtain ⟨A,hA⟩ := hEt.bddAbove_range
  let c := Real.sqrt (2*Real.pi)/Real.pi
  have hc : 0<c := div_pos (Real.sqrt_pos.mpr (by positivity)) Real.pi_pos
  have hA0 : 0≤A := (hE 0).trans (hA (Set.mem_range_self 0))
  refine ⟨c+A,by linarith,?_⟩
  intro n hn z
  have hs : 0<Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  by_cases hz : Even ((n:ℤ)+z)
  · have he := (abs_le.mp (h n hn z hz)).2
    have hx : Real.exp (-((z:ℝ)/Real.sqrt n)^2/2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ((z:ℝ)/Real.sqrt n)])
    have hh := mul_le_mul_of_nonneg_left hx hc.le
    apply (le_div_iff₀ hs).mpr
    have ha := hA (Set.mem_range_self n)
    dsimp [c] at hh ⊢
    nlinarith
  · have hz' : (z+(n:ℤ))%2≠0 := by
      simpa only [Int.even_iff,add_comm] using hz
    rw [kernel_binomial,ite_eq_right hz']
    positivity

lemma sum_difference_shift_le (f : ℕ → ℝ) (hf : ∀ j,0≤f j) (d N : ℕ) :
    (∑ j∈Finset.range N,(f j-f (j+d))) ≤ ∑ j∈Finset.range d,f j := by
  have h1 := Finset.sum_range_add f N d
  have h2 := Finset.sum_range_add f d N
  have ht : (∑ j∈Finset.range N,f j)+(∑ j∈Finset.range d,f (j+N))=
      (∑ j∈Finset.range d,f j)+(∑ j∈Finset.range N,f (j+d)) := by
    rw [Nat.add_comm N d] at h1
    simpa only [Nat.add_comm] using h1.symm.trans h2
  have hp : 0≤∑ j∈Finset.range d,f (j+N) := Finset.sum_nonneg (fun _ _ => hf _)
  rw [Finset.sum_sub_distrib]
  linarith

lemma killed_sum_bound {C : ℝ} (hC : ∀ n : ℕ,0<n → ∀ z : ℤ,kernel n z ≤ C/Real.sqrt n)
    (n : ℕ) (hn : 0<n) (a N : ℕ) :
    (∑ b∈Finset.range N,killed n a b) ≤ (2*(a+1:ℕ):ℝ)*(C/Real.sqrt n) := by
  have he (b : ℕ) : (b:ℤ)+a+2=(b+(2*(a+1)):ℕ)-a := by push_cast; ring
  simp_rw [killed_reflection,he]
  apply (sum_difference_shift_le (fun b => kernel n ((b:ℤ)-a)) (fun b => kernel_nonneg _ _) (2*(a+1)) N).trans
  calc
    _ ≤ ∑ _b∈Finset.range (2*(a+1)),C/Real.sqrt n := Finset.sum_le_sum (fun b _ => hC n hn _)
    _ = _ := by simp

end FKCRT.SimpleWalk
namespace FKCRT.Inventory

lemma signSum_bounds (x : ℕ → Letter) (n : ℕ) : -(n:ℤ)≤ signSum x n ∧ signSum x n≤ n := by
  induction n with
  | zero => simp [signSum]
  | succ n ih =>
    rw [signSum_succ]
    have hi := increment_bounds (x n)
    push_cast
    omega

def rawSurvival (a n : ℕ) : Set (ℕ → Letter) := {x | ∀ j≤ n,0≤(a:ℤ)+signSum x j}
lemma rawSurvival_union (a n : ℕ) :
    rawSurvival a n=⋃ b∈Finset.range (a+n+1),rawKilled a b n := by
  ext x
  simp only [rawSurvival,Set.mem_ofPred_eq,Set.mem_iUnion,Finset.mem_range,rawKilled]
  constructor
  · intro hx
    have hn := hx n le_rfl
    refine ⟨((a:ℤ)+signSum x n).toNat,?_,hx,?_⟩
    · have hb := signSum_bounds x n
      omega
    · omega
  · rintro ⟨b,_,hb,_⟩
    exact hb
lemma signSum_measurable (n : ℕ) : Measurable (fun x : ℕ → Letter => signSum x n) := by
  unfold signSum
  exact Finset.measurable_sum _ (fun j _ => (measurable_of_countable Letter.increment).comp (measurable_pi_apply j))
lemma rawKilled_measurable (a b n : ℕ) : MeasurableSet (rawKilled a b n) := by
  have h1 : MeasurableSet {x : ℕ → Letter | ∀ j≤n,0≤(a:ℤ)+signSum x j} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun j : ℕ => MeasurableSet.iInter (fun _ : j≤n =>
      measurableSet_le measurable_const ((signSum_measurable j).const_add (a:ℤ))))
  exact h1.inter (measurableSet_eq_fun ((signSum_measurable n).const_add (a:ℤ))
    (measurable_const (a := (b:ℤ))))
lemma rawSurvival_measurable (a n : ℕ) : MeasurableSet (rawSurvival a n) := by
  rw [rawSurvival_union]
  exact MeasurableSet.iUnion (fun b => MeasurableSet.iUnion (fun _ => rawKilled_measurable a b n))
lemma rawSurvival_measure (P : Parameters) (a n : ℕ) :
    (streamLaw P ℕ).real (rawSurvival a n)=∑ b∈Finset.range (a+n+1),SimpleWalk.killed n a b := by
  rw [rawSurvival_union,measureReal_biUnion_finset]
  · exact Finset.sum_congr rfl (fun b _ => rawKilled_measure P a b n)
  · intro b _ c _ hbc
    apply Set.disjoint_left.mpr
    intro x hb hc
    exact hbc (by have h1 := hb.2; have h2 := hc.2; omega)
  · intro b _; exact rawKilled_measurable a b n

/-- Reflection gives a uniform first-passage survival bound for the actual inventory stream. -/
theorem rawSurvival_bound : ∃ C : ℝ,0<C ∧ ∀ (P : Parameters) (a n : ℕ),0<n →
    (streamLaw P ℕ).real (rawSurvival a n) ≤ C*(a+1)/Real.sqrt n := by
  obtain ⟨C,hC,h⟩ := SimpleWalk.kernel_uniform_bound
  refine ⟨2*C,by positivity,?_⟩
  intro P a n hn
  rw [rawSurvival_measure]
  convert SimpleWalk.killed_sum_bound h n hn a (a+n+1) using 1
  push_cast
  ring

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

def bottom {α : Type*} (s : List α) (k : ℕ) : List α := s.drop (s.length-k)
lemma bottom_cons {α : Type*} (b : α) (s : List α) {k : ℕ} (hk : k ≤ s.length) :
    bottom (b::s) k=bottom s k := by
  unfold bottom
  have he : (b::s).length-k=(s.length-k)+1 := by simp only [List.length_cons]; omega
  rw [he,List.drop_succ_cons]
lemma bottom_all {α : Type*} (s : List α) : bottom s s.length=s := by simp [bottom]
lemma count_bottom_le (s : List Bool) (k : ℕ) (a : Bool) : (bottom s k).count a ≤ s.count a :=
  List.Sublist.count_le a (List.drop_sublist _ _)

lemma pop_fixed_count {b a : Bool} {s t : List Bool} (h : pop (some b) s=some t) :
    s.count a=t.count a+if a=b then 1 else 0 := by
  induction s generalizing t with
  | nil => simp [pop] at h
  | cons c s ih =>
    by_cases he : b=c
    · subst c
      simp only [pop,eligible,Option.some.injEq,or_true,ite_true] at h
      cases h
      by_cases ha : a=b
      · subst a; simp only [List.count_cons_self,ite_true]
      · simp only [List.count_cons_of_ne (Ne.symm ha),ite_eq_right ha,Nat.add_zero]
    · have hel : ¬eligible (some b) c := by simp [eligible,he]
      simp only [pop,ite_eq_right hel] at h
      cases hp : pop (some b) s with
      | none => simp [hp] at h
      | some t' =>
        simp only [hp,Option.map_some,Option.some.injEq] at h
        subst t
        have hi := ih hp
        simp only [List.count_cons]
        omega

/-- Removing the freshest burger of type b never reduces the bottom-k
supply of another type. If it reduces the type-b supply, all of the
remaining type-b supply is in the bottom k. -/
lemma pop_fixed_bottom {b a : Bool} {s t : List Bool} (h : pop (some b) s=some t)
    {k : ℕ} (hk : k ≤ t.length) :
    (bottom s k).count a ≤ (bottom t k).count a ∨
      (a=b ∧ t.count a=(bottom t k).count a) := by
  induction s generalizing t k with
  | nil => simp [pop] at h
  | cons c s ih =>
    by_cases he : b=c
    · subst c
      have hel : eligible (some b) b := by simp [eligible]
      simp only [pop,ite_eq_left hel,Option.some.injEq] at h
      subst t
      exact Or.inl (by rw [bottom_cons _ _ hk])
    · have hel : ¬eligible (some b) c := by simp [eligible,he]
      simp only [pop,ite_eq_right hel] at h
      cases hp : pop (some b) s with
      | none => simp [hp] at h
      | some t' =>
        simp only [hp,Option.map_some,Option.some.injEq] at h
        subst t
        have hl := pop_length hp
        by_cases hk' : k ≤ t'.length
        · rw [bottom_cons c s (by omega),bottom_cons c t' hk']
          rcases ih hp hk' with h | ⟨rfl,h⟩
          · exact Or.inl h
          · exact Or.inr ⟨rfl,by simpa [List.count_cons,he,eq_comm] using h⟩
        · have hk'' : k=(c::t').length := by simp only [List.length_cons] at *; omega
          rw [hk'',bottom_all]
          by_cases ha : a=b
          · exact Or.inr ⟨ha,rfl⟩
          · exact Or.inl ((count_bottom_le _ _ a).trans (by
              have hc := pop_fixed_count (a := a) (show pop (some b) (c::s)=some (c::t') by
                simp only [pop,ite_eq_right hel,hp,Option.map_some])
              simpa [ha] using hc.le))

/-- Exact source criterion, expressed in freshest-first stack order. -/
def SupplyCondition (s : List Bool) (os : List Order) : Prop :=
  s.length=os.length ∧ ∀ k ≤ os.length,∀ a : Bool,
    (bottom os k).count (some a) ≤ (bottom s k).count a

lemma fixed_pop_exists {b : Bool} {s : List Bool} (h : 0<s.count b) :
    ∃ t,pop (some b) s=some t := by
  cases hp : pop (some b) s with
  | some t => exact ⟨t,rfl⟩
  | none =>
    have hb : b∈s := List.count_pos_iff.mp h
    have hn := (pop_eq_none_iff (some b) s).mp hp b hb
    exact False.elim (hn (by simp [eligible]))

lemma supplyCondition_step {s : List Bool} {a : Order} {os : List Order}
    (h : SupplyCondition s (a::os)) :
    ∃ t,pop a s=some t ∧ SupplyCondition t os := by
  obtain ⟨hl,hc⟩ := h
  cases a with
  | none =>
    cases s with
    | nil => simp at hl
    | cons b s =>
      refine ⟨s,by simp [pop,eligible],?_⟩
      have hs : s.length=os.length := by simp only [List.length_cons] at hl; omega
      refine ⟨hs,fun k hk c => ?_⟩
      have hh := hc k (by simp only [List.length_cons]; omega) c
      rw [bottom_cons none os hk,bottom_cons b s (by omega)] at hh
      exact hh
  | some b =>
    have hh := hc (some b::os).length le_rfl b
    rw [bottom_all,← hl,bottom_all] at hh
    have hp : 0<s.count b := by
      simp only [List.count_cons_self] at hh
      omega
    obtain ⟨t,ht⟩ := fixed_pop_exists hp
    have htl := pop_length ht
    refine ⟨t,ht,⟨by simp only [List.length_cons] at hl; omega,fun k hk c => ?_⟩⟩
    have horig := hc k (by simp only [List.length_cons]; omega) c
    rw [bottom_cons (some b) os hk] at horig
    rcases pop_fixed_bottom (a := c) (k := k) ht (by simp only [List.length_cons] at hl; omega) with hge | ⟨hcb,he⟩
    · exact horig.trans hge
    · subst c
      have hall := hc (some b::os).length le_rfl b
      rw [bottom_all,← hl,bottom_all] at hall
      have hc' := pop_fixed_count (a := b) ht
      simp only [List.count_cons_self,ite_true] at hall hc'
      have htail : os.count (some b) ≤ t.count b := by omega
      exact ((List.Sublist.count_le (some b) (List.drop_sublist _ _)).trans htail).trans_eq he

theorem matching_of_supplyCondition {s : List Bool} {os : List Order} (h : SupplyCondition s os) :
    evalOrders os s=⟨[],[]⟩ := by
  induction os generalizing s with
  | nil =>
    have hs : s=[] := List.length_eq_zero_iff.mp (by simpa using h.1)
    subst s
    rfl
  | cons a os ih =>
    obtain ⟨t,ht,hcond⟩ := supplyCondition_step h
    rw [evalOrders_cons,ht]
    exact ih hcond

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

lemma pop_fixed_exists {c : Bool} {s : List Bool} (h : 0<s.count c) : ∃ t,pop (some c) s=some t := by
  cases hp : pop (some c) s with
  | some t => exact ⟨t,rfl⟩
  | none =>
    have hh := (pop_eq_none_iff _ _).mp hp c (List.count_pos_iff.mp h)
    exact (hh (by simp [eligible])).elim

lemma fixed_run_buffer {w : List Letter} (hw : FixedWord w) {s : List Bool}
    (hs : ∀ b,w.length ≤ s.count b) :
    (run w ⟨[],s⟩).orders=[] ∧ ∀ b,((run w ⟨[],s⟩).burgers.count b:ℤ)=(s.count b:ℤ)+typeNet b w := by
  induction w generalizing s with
  | nil => simp [run,typeNet]
  | cons a w ih =>
    have hf : FixedWord w := fun h => hw (List.mem_cons_of_mem a h)
    have ha : a≠Letter.order none := by intro h; exact hw (by simp [h])
    cases a with
    | burger c =>
      have hh : ∀ b,w.length ≤ (c::s).count b := by
        intro b
        have hb := hs b
        simp only [List.length_cons] at hb
        have hle : s.count b ≤ (c::s).count b := List.Sublist.count_le b (List.sublist_cons_self ..)
        omega
      obtain ⟨ho,hcount⟩ := ih hf hh
      refine ⟨ho,fun b => ?_⟩
      change ((run w ⟨[],c::s⟩).burgers.count b:ℤ)=(s.count b:ℤ)+(Letter.typeNet b (.burger c)+typeNet b w)
      rw [hcount]
      by_cases hcb : c=b
      · subst c; simp only [List.count_cons_self,Nat.cast_add,Nat.cast_one,Letter.typeNet,ite_true]; ring
      · simp only [List.count_cons_of_ne hcb,Letter.typeNet,ite_eq_right hcb,zero_add]
    | order o =>
      cases o with
      | none => exact (ha rfl).elim
      | some c =>
        obtain ⟨t,ht⟩ := pop_fixed_exists (c := c) (s := s) (by have := hs c; simp only [List.length_cons] at this; omega)
        have hh : ∀ b,w.length ≤ t.count b := by
          intro b
          have hb := hs b
          have hc := pop_fixed_count (a := b) ht
          simp only [List.length_cons] at hb
          split_ifs at hc <;> omega
        obtain ⟨ho,hcount⟩ := ih hf hh
        simp only [run,step,ht]
        refine ⟨ho,fun b => ?_⟩
        rw [hcount]
        change (t.count b:ℤ)+typeNet b w=(s.count b:ℤ)+(Letter.typeNet b (.order (some c))+typeNet b w)
        have hc := pop_fixed_count (a := b) ht
        by_cases hbc : b=c
        · subst b
          simp only [ite_true] at hc
          simp only [Letter.typeNet,ite_true]
          omega
        · have hcb : c≠b := Ne.symm hbc
          simp only [ite_eq_right hbc,Nat.add_zero] at hc
          simp only [Letter.typeNet,ite_eq_right hcb,zero_add,hc]

def piecesPrefix (x : ℕ → List Letter) : ℕ → List Letter
  | 0 => []
  | n+1 => piecesPrefix x n++x n

def pieceSum (b : Bool) (x : ℕ → List Letter) (n : ℕ) : ℤ :=
  ∑ j∈Finset.range n,typeNet b (x j)

def PieceBuffer (K : ℕ) (x : ℕ → List Letter) : Prop :=
  ∀ n b,((x n).length:ℤ) ≤ (K:ℤ)+pieceSum b x n

lemma run_pieces_buffer {x : ℕ → List Letter} (hx : ∀ n,FixedWord (x n)) {K : ℕ}
    (hb : PieceBuffer K x) {s : List Bool} (hs : ∀ b,K ≤ s.count b) (n : ℕ) :
    (run (piecesPrefix x n) ⟨[],s⟩).orders=[] ∧
      ∀ b,((run (piecesPrefix x n) ⟨[],s⟩).burgers.count b:ℤ)=(s.count b:ℤ)+pieceSum b x n := by
  induction n with
  | zero => simp [piecesPrefix,run,pieceSum]
  | succ n ih =>
    let t : List Bool := (run (piecesPrefix x n) ⟨[],s⟩).burgers
    have hcount : ∀ b,(x n).length ≤ t.count b := by
      intro b
      have hh := hb n b
      have hi := ih.2 b
      have hsb := hs b
      change ((run (piecesPrefix x n) ⟨[],s⟩).burgers.count b:ℤ)=_ at hi
      dsimp [t]
      omega
    obtain ⟨ho,hc⟩ := fixed_run_buffer (hx n) hcount
    have he : run (piecesPrefix x n) ⟨[],s⟩=⟨[],t⟩ := by
      have hh := ih.1
      dsimp [t]
      generalize he : run (piecesPrefix x n) ⟨[],s⟩=e at *
      cases e with
      | mk os bs => simp only at hh; subst os; rfl
    rw [piecesPrefix,run_append,he]
    refine ⟨ho,fun b => ?_⟩
    rw [hc]
    change ((run (piecesPrefix x n) ⟨[],s⟩).burgers.count b:ℤ)+typeNet b (x n)=_
    rw [ih.2]
    simp only [pieceSum,Finset.sum_range_succ]
    ring

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

lemma term_div_zero_of_averages {a : ℕ → ℝ} {l : ℝ}
    (h : Tendsto (fun n => (∑ i∈Finset.range n,a i)/(n:ℝ)) atTop (𝓝 l)) :
    Tendsto (fun n => a n/(n:ℝ)) atTop (𝓝 0) := by
  have hr : Tendsto (fun n : ℕ => ((n:ℝ)+1)/(n:ℝ)) atTop (𝓝 1) := by
    have hh := (tendsto_const_nhds (x := (1:ℝ))).add tendsto_one_div_atTop_nhds_zero_nat
    simp only [add_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
    have hn0 : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
    field_simp
  have hs := (h.comp (tendsto_add_atTop_nat 1)).mul hr
  have ht := hs.sub h
  have hz : l*1-l=0 := by ring
  rw [hz] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  have hnp : (n:ℝ)+1≠0 := by positivity
  dsimp only [Function.comp_def]
  rw [Finset.sum_range_succ]
  push_cast
  field_simp
  ring

lemma positive_piece_buffer {x : ℕ → List Letter}
    (hnet : ∀ b,Tendsto (fun n => (pieceSum b x n:ℝ)/(n:ℝ)) atTop (𝓝 (1/2)))
    {l : ℝ} (hlen : Tendsto (fun n => (∑ j∈Finset.range n,((x j).length:ℝ))/(n:ℝ)) atTop (𝓝 l)) :
    ∃ K,PieceBuffer K x := by
  have ht := term_div_zero_of_averages hlen
  have hp (b : Bool) : ∀ᶠ n : ℕ in atTop,0 ≤ (pieceSum b x n:ℤ)-((x n).length:ℤ) := by
    have hh := (hnet b).sub ht
    have he : (1/2:ℝ)-0=1/2 := sub_zero _
    rw [he] at hh
    have hev := (tendsto_order.mp hh).1 0 (by norm_num)
    filter_upwards [hev,eventually_gt_atTop (0:ℕ)] with n hn hn0
    have hnR : (0:ℝ)<n := by exact_mod_cast hn0
    have hnum : 0<(pieceSum b x n:ℝ)-((x n).length:ℝ) := by
      rw [← sub_div] at hn
      exact (div_pos_iff.mp hn).resolve_right (fun h => (not_lt_of_ge hnR.le) h.2) |>.1
    exact_mod_cast hnum.le
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((hp false).and (hp true))
  let K : ℕ := ∑ j∈Finset.range (N+1),(x j).length
  refine ⟨K,fun n b => ?_⟩
  by_cases hn : N ≤ n
  · have hh : 0 ≤ pieceSum b x n-((x n).length:ℤ) := by
      cases b
      · exact (hN n hn).1
      · exact (hN n hn).2
    omega
  · have hnN : n<N := by omega
    have hsum : -(((∑ j∈Finset.range n,(x j).length):ℕ):ℤ) ≤ pieceSum b x n := by
      simp only [pieceSum,Nat.cast_sum]
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_le_sum (fun j _ => (abs_le.mp (abs_typeNet_le b (x j))).1)
    have hK : (∑ j∈Finset.range n,(x j).length)+(x n).length ≤ K := by
      rw [← Finset.sum_range_succ]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun _ _ _ => Nat.zero_le _)
    omega

def naturalPiecesLaw (ν : Measure (List Letter)) [IsProbabilityMeasure ν] : Measure (ℕ → List Letter) :=
  Measure.infinitePi (fun _ : ℕ => ν)
instance naturalPieces_probability (ν : Measure (List Letter)) [IsProbabilityMeasure ν] : IsProbabilityMeasure (naturalPiecesLaw ν) := by
  unfold naturalPiecesLaw
  infer_instance

lemma iid_piece_averages (ν : Measure (List Letter)) [IsProbabilityMeasure ν]
    {f : List Letter → ℝ} (hf : Integrable f ν) :
    ∀ᵐ x ∂naturalPiecesLaw ν,Tendsto (fun n => (∑ j∈Finset.range n,f (x j))/(n:ℝ)) atTop (𝓝 (∫ w,f w ∂ν)) := by
  have hfm : Measurable f := measurable_of_countable _
  have hl (j : ℕ) : HasLaw (fun x : ℕ → List Letter => f (x j)) (ν.map f) (naturalPiecesLaw ν) :=
    HasLaw.comp (show HasLaw f (ν.map f) ν from ⟨hfm.aemeasurable,rfl⟩) (measurePreserving_eval_infinitePi (fun _ : ℕ => ν) j).hasLaw
  have hi : iIndepFun (fun j (x : ℕ → List Letter) => f (x j)) (naturalPiecesLaw ν) :=
    iIndepFun_infinitePi (P := fun _ : ℕ => ν) (X := fun _ => f) (fun _ => hfm)
  have hint := (measurePreserving_eval_infinitePi (fun _ : ℕ => ν) 0).integrable_comp_of_integrable hf
  have he := (measurePreserving_eval_infinitePi (fun _ : ℕ => ν) 0).hasLaw.integral_comp hf.aestronglyMeasurable
  change (∫ x,f (x 0) ∂naturalPiecesLaw ν)=(∫ w,f w ∂ν) at he
  dsimp only [naturalPiecesLaw] at he ⊢
  simpa only [he] using strong_law_ae_real (fun j (x : ℕ → List Letter) => f (x j)) hint
    (fun _ _ h => hi.indepFun h) (fun j => (hl j).identDistrib (hl 0))

lemma iid_piece_buffer_ae (ν : Measure (List Letter)) [IsProbabilityMeasure ν]
    (hlen : Integrable (fun w : List Letter => (w.length:ℝ)) ν)
    (hnet : ∀ b,Integrable (fun w => (typeNet b w:ℝ)) ν)
    (hmean : ∀ b,(∫ w,(typeNet b w:ℝ) ∂ν)=1/2) :
    ∀ᵐ x ∂naturalPiecesLaw ν,∃ K,PieceBuffer K x := by
  have hn (b : Bool) := iid_piece_averages ν (hnet b)
  filter_upwards [iid_piece_averages ν hlen,hn false,hn true] with x hl hf ht
  apply positive_piece_buffer (l := ∫ w,(w.length:ℝ) ∂ν) (hlen := hl)
  intro b
  have he (n : ℕ) : (pieceSum b x n:ℝ)=∑ j∈Finset.range n,(typeNet b (x j):ℝ) := by simp [pieceSum]
  simp only [he]
  cases b
  · simpa only [hmean] using hf
  · simpa only [hmean] using ht

lemma measurableSet_pieceBuffer (K : ℕ) : MeasurableSet {x : ℕ → List Letter | PieceBuffer K x} := by
  simp only [PieceBuffer,Set.ofPred_forall]
  apply MeasurableSet.iInter; intro n
  apply MeasurableSet.iInter; intro b
  exact measurableSet_le ((measurable_of_countable (fun w : List Letter => (w.length:ℤ))).comp (measurable_pi_apply n))
    (measurable_const.add (Finset.measurable_sum _ (fun j _ =>
      (measurable_of_countable (fun w : List Letter => typeNet b w)).comp (measurable_pi_apply j))))

lemma positive_piece_buffer_probability (ν : Measure (List Letter)) [IsProbabilityMeasure ν]
    (hlen : Integrable (fun w : List Letter => (w.length:ℝ)) ν)
    (hnet : ∀ b,Integrable (fun w => (typeNet b w:ℝ)) ν)
    (hmean : ∀ b,(∫ w,(typeNet b w:ℝ) ∂ν)=1/2) :
    ∃ K,0<naturalPiecesLaw ν {x | PieceBuffer K x} := by
  by_contra h
  push Not at h
  have hz (K : ℕ) : naturalPiecesLaw ν {x | PieceBuffer K x}=0 := le_antisymm (h K) (by positivity)
  have hall := iid_piece_buffer_ae ν hlen hnet hmean
  have hu : naturalPiecesLaw ν (⋃ K,{x | PieceBuffer K x})=1 := by
    rw [← prob_compl_eq_zero_iff (MeasurableSet.iUnion measurableSet_pieceBuffer)]
    simpa only [ae_iff,Set.compl_iUnion,Set.compl_ofPred,Set.iInter_ofPred,not_exists] using hall
  have hh := measure_iUnion_le (μ := naturalPiecesLaw ν) (fun K => {x | PieceBuffer K x})
  simp only [hz,tsum_zero,hu] at hh
  exact not_le_of_gt (zero_lt_one' ℝ≥0∞) hh

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

def piecesTail (n : ℕ) (x : ℕ → List Letter) : ℕ → List Letter := fun k => x (n+k)
lemma piecesTail_measurable (n : ℕ) : Measurable (piecesTail n) :=
  Measurable.of_eval (fun index => measurable_pi_apply (n+index))
lemma piecesTail_preserving (ν : Measure (List Letter)) [IsProbabilityMeasure ν] (n : ℕ) :
    MeasurePreserving (piecesTail n) (naturalPiecesLaw ν) (naturalPiecesLaw ν) :=
  ⟨piecesTail_measurable n,Measure.map_infinitePi_infinitePi_of_inj (fun _ _ h => Nat.add_left_cancel h)⟩

@[instance_reducible] def pieceCoords (S : Set ℕ) : MeasurableSpace (ℕ → List Letter) :=
  ⨆ j∈S,MeasurableSpace.comap (fun x : ℕ → List Letter => x j) inferInstance
lemma pieceCoords_indep (ν : Measure (List Letter)) [IsProbabilityMeasure ν] {S R : Set ℕ}
    (h : Disjoint S R) : Indep (pieceCoords S) (pieceCoords R) (naturalPiecesLaw ν) :=
  indep_iSup_of_disjoint (fun j => (measurable_pi_apply j).comap_le)
    (iIndepFun_infinitePi (P := fun _ : ℕ => ν) (X := fun _ (w : List Letter) => w) (fun _ => measurable_id)) h
lemma piecesTail_coords (n : ℕ) : Measurable[pieceCoords {j | n ≤ j}] (piecesTail n) := by
  let : MeasurableSpace (ℕ → List Letter) := pieceCoords {j | n ≤ j}
  apply Measurable.of_eval
  intro k
  apply measurable_iff_comap_le.mpr
  exact le_iSup_of_le (n+k) (le_iSup_of_le (show n ≤ n+k by omega) le_rfl)

def pieceCylinder (u : List (List Letter)) : Set (ℕ → List Letter) :=
  {x | ∀ i : Fin u.length,x i=u.get i}
lemma pieceCylinder_coords (u : List (List Letter)) :
    MeasurableSet[pieceCoords {j | j<u.length}] (pieceCylinder u) := by
  let : MeasurableSpace (ℕ → List Letter) := pieceCoords {j | j<u.length}
  have hm (i : Fin u.length) : Measurable (fun x : ℕ → List Letter => x i) := by
    apply measurable_iff_comap_le.mpr
    exact le_iSup_of_le i (le_iSup_of_le i.isLt le_rfl)
  simp only [pieceCylinder,Set.ofPred_forall]
  exact MeasurableSet.iInter (fun i => (hm i) (measurableSet_singleton (u.get i)))
lemma pieceCylinder_measurable (u : List (List Letter)) : MeasurableSet (pieceCylinder u) := by
  have hle : pieceCoords {j | j<u.length} ≤ (inferInstance : MeasurableSpace (ℕ → List Letter)) :=
    iSup_le (fun j => iSup_le (fun _ => (measurable_pi_apply j).comap_le))
  exact hle _ (pieceCylinder_coords u)
lemma pieceCylinder_eq_pi (u : List (List Letter)) :
    pieceCylinder u=Set.pi (Finset.range u.length) (fun j => {u[j]?.getD []}) := by
  ext x
  simp only [pieceCylinder,Set.mem_ofPred_eq,Set.mem_pi,Finset.mem_coe,Finset.mem_range,Set.mem_singleton_iff]
  constructor
  · intro h j hj
    simpa only [List.getElem?_eq_getElem hj,Option.getD_some,List.get_eq_getElem] using h ⟨j,hj⟩
  · intro h i
    simpa only [List.getElem?_eq_getElem i.isLt,Option.getD_some,List.get_eq_getElem] using h i i.isLt
lemma pieceCylinder_positive (ν : Measure (List Letter)) [IsProbabilityMeasure ν]
    {u : List (List Letter)} (hu : ∀ w∈u,0<ν {w}) : 0<naturalPiecesLaw ν (pieceCylinder u) := by
  rw [pieceCylinder_eq_pi]
  unfold naturalPiecesLaw
  rw [Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
  apply bot_lt_iff_ne_bot.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  have hj' : j<u.length := Finset.mem_range.mp hj
  rw [List.getElem?_eq_getElem hj',Option.getD_some]
  exact ne_of_gt (hu _ (List.getElem_mem hj'))

lemma pieceCylinder_tail_rectangle (ν : Measure (List Letter)) [IsProbabilityMeasure ν]
    (u : List (List Letter)) {B : Set (ℕ → List Letter)} (hB : MeasurableSet B) :
    naturalPiecesLaw ν (pieceCylinder u ∩ piecesTail u.length ⁻¹' B)=
      naturalPiecesLaw ν (pieceCylinder u)*naturalPiecesLaw ν B := by
  have hi := pieceCoords_indep ν (S := {j | j<u.length}) (R := {j | u.length ≤ j})
    (Set.disjoint_left.mpr (fun j hj hj' => by change j<u.length at hj; change u.length ≤ j at hj'; omega))
  have hh := ((indep_iff_forall_indepSet _).mp hi (pieceCylinder u) (piecesTail u.length ⁻¹' B)
    (pieceCylinder_coords u) (piecesTail_coords u.length hB)).measure_inter_eq_mul
  rw [(piecesTail_preserving ν u.length).measure_preimage hB.nullMeasurableSet] at hh
  exact hh

lemma piecesPrefix_ofFn (x : ℕ → List Letter) (n : ℕ) :
    piecesPrefix x n=(List.ofFn (fun i : Fin n => x i)).flatten := by
  induction n with
  | zero => simp [piecesPrefix]
  | succ n ih =>
    rw [piecesPrefix,ih,List.ofFn_succ']
    simp only [List.concat_eq_append,List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil,
      Fin.val_castSucc,Fin.val_last]
lemma piecesPrefix_of_cylinder {u : List (List Letter)} {x : ℕ → List Letter} (hx : x∈pieceCylinder u) :
    piecesPrefix x u.length=u.flatten := by
  rw [piecesPrefix_ofFn]
  have h : (fun i : Fin u.length => x i)=u.get := funext hx
  rw [h,List.ofFn_get]
lemma piecesPrefix_add (x : ℕ → List Letter) (m n : ℕ) :
    piecesPrefix x (m+n)=piecesPrefix x m++piecesPrefix (piecesTail m x) n := by
  induction n with
  | zero => simp [piecesPrefix]
  | succ n ih =>
    rw [Nat.add_succ,piecesPrefix,ih,piecesPrefix,List.append_assoc]
    rfl

end FKCRT.Inventory
end

end OAI
