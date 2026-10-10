import OAI.Probability.FKMaps.InventoryRenewal
import OAI.Probability.FKMaps.PlaneTrees
import OAI.Probability.FKMaps.SimpleWalk

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

def stoppedWord (T : (ℕ → Letter) → WithTop ℕ) (x : ℕ → Letter) : List Letter :=
  revealed x ((T x).untopD 0+1)
def stoppedTail (T : (ℕ → Letter) → WithTop ℕ) (x : ℕ → Letter) : ℕ → Letter :=
  tail ((T x).untopD 0+1) x
lemma measurable_revealed (n : ℕ) : Measurable (fun x : ℕ → Letter => revealed x n) :=
  (measurable_of_countable (fun y : Fin n → Letter => (List.ofFn y).reverse)).comp
    (Measurable.of_eval (fun index => measurable_pi_apply (index:ℕ)))
lemma measurable_stoppedWord {T : (ℕ → Letter) → WithTop ℕ} (hT : Measurable T) : Measurable (stoppedWord T) := by
  have hm : Measurable (fun x => (T x).untopD 0+1) := (measurable_of_countable (fun t : WithTop ℕ => t.untopD 0+1)).comp hT
  have hh : Measurable (fun z : ℕ × (ℕ → Letter) => revealed z.2 z.1) :=
    measurable_from_prod_countable_right measurable_revealed
  exact hh.comp (hm.prodMk measurable_id)
lemma measurable_stoppedTail {T : (ℕ → Letter) → WithTop ℕ} (hT : Measurable T) : Measurable (stoppedTail T) := by
  have hm : Measurable (fun x => (T x).untopD 0+1) := (measurable_of_countable (fun t : WithTop ℕ => t.untopD 0+1)).comp hT
  have hh : Measurable (fun z : ℕ × (ℕ → Letter) => tail z.1 z.2) :=
    measurable_from_prod_countable_right measurable_tail
  exact hh.comp (hm.prodMk measurable_id)
lemma stoppedWord_of_hit {T : (ℕ → Letter) → WithTop ℕ} {x : ℕ → Letter} {n : ℕ}
    (h : T x=WithTop.some n) : stoppedWord T x=revealed x (n+1) := by simp only [stoppedWord,h]; rfl
lemma stoppedTail_of_hit {T : (ℕ → Letter) → WithTop ℕ} {x : ℕ → Letter} {n : ℕ}
    (h : T x=WithTop.some n) : stoppedTail T x=tail (n+1) x := by simp only [stoppedTail,h]; rfl

lemma stoppedWord_rectangle_sum (P : Parameters) {T : (ℕ → Letter) → WithTop ℕ}
    (hT : IsStoppingTime rawFiltration T) (hfin : ∀ᵐ x ∂streamLaw P ℕ,T x≠⊤)
    (A : Set (List Letter)) (B : Set (ℕ → Letter)) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    streamLaw P ℕ (stoppedWord T ⁻¹' A ∩ stoppedTail T ⁻¹' B)=
      (∑' n : ℕ,streamLaw P ℕ ({x | T x=WithTop.some n} ∩ (fun x => revealed x (n+1)) ⁻¹' A))*streamLaw P ℕ B := by
  let C : ℕ → Set (ℕ → Letter) := fun n => {x | T x=WithTop.some n} ∩ (fun x => revealed x (n+1)) ⁻¹' A
  have hC (n : ℕ) : MeasurableSet[rawFiltration n] (C n) :=
    (hT.measurableSet_eq n).inter (prefix_measurable n (fun y => (List.ofFn y).reverse) hA)
  have hCm (n : ℕ) : MeasurableSet (C n) := rawFiltration.le n _ (hC n)
  have he : (stoppedWord T ⁻¹' A ∩ stoppedTail T ⁻¹' B : Set (ℕ → Letter)) =ᵐ[streamLaw P ℕ]
      (⋃ n,C n ∩ tail (n+1) ⁻¹' B : Set (ℕ → Letter)) := by
    filter_upwards [hfin] with x hx
    obtain ⟨n,hn⟩ := WithTop.ne_top_iff_exists.mp hx
    have hn' : T x=WithTop.some n := hn.symm
    apply propext
    constructor
    · rintro ⟨ha,hb⟩
      exact Set.mem_iUnion.mpr ⟨n,⟨hn',by simpa only [Set.mem_preimage,← stoppedWord_of_hit hn'] using ha⟩,
        by simpa only [Set.mem_preimage,← stoppedTail_of_hit hn'] using hb⟩
    · intro h
      obtain ⟨m,⟨hm,ha⟩,hb⟩ := Set.mem_iUnion.mp h
      exact ⟨by simpa only [Set.mem_preimage,stoppedWord_of_hit hm] using ha,
        by simpa only [Set.mem_preimage,stoppedTail_of_hit hm] using hb⟩
  rw [measure_congr he,measure_iUnion]
  · have hs (n : ℕ) : streamLaw P ℕ (C n ∩ tail (n+1) ⁻¹' B)=streamLaw P ℕ (C n)*streamLaw P ℕ B := by
      have h := ((indep_iff_forall_indepSet _).mp (raw_indep_tail P n) _ _ (hC n)
        (measurable_iff_comap_le.mpr le_rfl hB)).measure_inter_eq_mul
      rw [(tail_preserving P (n+1)).measure_preimage hB.nullMeasurableSet] at h
      exact h
    simp_rw [hs]
    rw [ENNReal.tsum_mul_right]
  · intro n m hnm
    exact Set.disjoint_left.mpr (fun x hn hm => hnm (WithTop.coe_injective (hn.1.1.symm.trans hm.1.1)))
  · intro n
    exact (hCm n).inter ((measurable_tail (n+1)) hB)

lemma stoppedWord_rectangle (P : Parameters) {T : (ℕ → Letter) → WithTop ℕ}
    (hT : IsStoppingTime rawFiltration T) (hfin : ∀ᵐ x ∂streamLaw P ℕ,T x≠⊤)
    (A : Set (List Letter)) (B : Set (ℕ → Letter)) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    streamLaw P ℕ (stoppedWord T ⁻¹' A ∩ stoppedTail T ⁻¹' B)=
      streamLaw P ℕ (stoppedWord T ⁻¹' A)*streamLaw P ℕ B := by
  rw [stoppedWord_rectangle_sum P hT hfin A B hA hB]
  have h := stoppedWord_rectangle_sum P hT hfin A Set.univ hA MeasurableSet.univ
  simp only [Set.preimage_univ,Set.inter_univ,measure_univ,mul_one] at h
  rw [h]
lemma stoppedTail_preserving (P : Parameters) {T : (ℕ → Letter) → WithTop ℕ}
    (hTm : Measurable T) (hT : IsStoppingTime rawFiltration T) (hfin : ∀ᵐ x ∂streamLaw P ℕ,T x≠⊤) :
    MeasurePreserving (stoppedTail T) (streamLaw P ℕ) (streamLaw P ℕ) := by
  refine ⟨measurable_stoppedTail hTm,?_⟩
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply (measurable_stoppedTail hTm) hB]
  simpa using stoppedWord_rectangle P hT hfin Set.univ B MeasurableSet.univ hB
lemma stoppedWord_indep_tail (P : Parameters) {T : (ℕ → Letter) → WithTop ℕ}
    (hTm : Measurable T) (hT : IsStoppingTime rawFiltration T) (hfin : ∀ᵐ x ∂streamLaw P ℕ,T x≠⊤) :
    IndepFun (stoppedWord T) (stoppedTail T) (streamLaw P ℕ) := by
  apply indepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro A B hA hB
  rw [(stoppedTail_preserving P hTm hT hfin).measure_preimage hB.nullMeasurableSet]
  exact stoppedWord_rectangle P hT hfin A B hA hB

def wordPieces (T : (ℕ → Letter) → WithTop ℕ) (j : ℕ) (x : ℕ → Letter) : List Letter :=
  stoppedWord T ((stoppedTail T)^[j] x)
lemma stoppedWordPieces_iid (P : Parameters) {T : (ℕ → Letter) → WithTop ℕ}
    (hTm : Measurable T) (hT : IsStoppingTime rawFiltration T) (hfin : ∀ᵐ x ∂streamLaw P ℕ,T x≠⊤) :
    iIndepFun (wordPieces T) (streamLaw P ℕ) :=
  TreeCoding.regenerative_iIndepFun (streamLaw P ℕ) (stoppedWord T) (stoppedTail T) (measurable_stoppedWord hTm)
    (stoppedTail_preserving P hTm hT hfin) (stoppedWord_indep_tail P hTm hT hfin)

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT
namespace TreeCoding

lemma firstZero_eq_iff {Ω : Type*} (S : ℕ → Ω → ℤ) (x : Ω) (n : ℕ) :
    firstZero S x=WithTop.some n ↔ S n x=0 ∧ ∀ j<n,S j x≠0 := by
  classical
  unfold firstZero
  split_ifs with h
  · rw [WithTop.coe_inj]
    exact Nat.find_eq_iff h
  · simp only [WithTop.top_ne_coe,false_iff,not_and]
    intro hn
    exact (h ⟨n,hn⟩).elim

end TreeCoding
namespace Inventory

lemma stopping_measurable {T : (ℕ → Letter) → WithTop ℕ} (hT : IsStoppingTime rawFiltration T) : Measurable T := by
  have hme (n : ℕ) : MeasurableSet {x | T x=WithTop.some n} := rawFiltration.le n _ (hT.measurableSet_eq n)
  have hmf : MeasurableSet {x | T x≠⊤} := by
    have he : {x | T x≠⊤}=⋃ n : ℕ,{x | T x=WithTop.some n} := by
      ext x
      simp only [Set.mem_ofPred_eq,Set.mem_iUnion]
      simpa only [eq_comm] using (WithTop.ne_top_iff_exists (x := T x))
    rw [he]
    exact MeasurableSet.iUnion hme
  apply measurable_to_countable'
  intro n
  obtain rfl | ⟨n,rfl⟩ := eq_or_ne n ⊤ |>.imp_right (fun h => WithTop.ne_top_iff_exists.mp h)
  · convert hmf.compl using 1
    ext x; simp
  · exact hme n

def downPath (h : ℕ) (n : ℕ) (x : ℕ → Letter) : ℤ := (h:ℤ)+signSum x (n+1)
def firstDown (h : ℕ) : (ℕ → Letter) → WithTop ℕ := TreeCoding.firstZero (downPath h)
lemma downPath_adapted (h : ℕ) : StronglyAdapted rawFiltration (downPath h) := by
  intro n
  convert (prefix_measurable n (fun y => (h:ℤ)+(((List.ofFn y).reverse).map Letter.increment).sum)).stronglyMeasurable using 1
  ext x
  exact congrArg (fun z : ℤ => (h:ℤ)+z) (revealed_sum x (n+1)).symm
lemma firstDown_stopping (h : ℕ) : IsStoppingTime rawFiltration (firstDown h) :=
  TreeCoding.firstZero_isStoppingTime (downPath_adapted h)
lemma firstDown_measurable (h : ℕ) : Measurable (firstDown h) := stopping_measurable (firstDown_stopping h)
lemma downPath_step (h n : ℕ) (x : ℕ → Letter) : downPath h n x-1 ≤ downPath h (n+1) x := by
  unfold downPath
  rw [signSum_succ x (n+1)]
  have := (increment_bounds (x (n+1))).1
  omega
lemma downPath_initial (h : ℕ) (hh : 0<h) (x : ℕ → Letter) : 0 ≤ downPath h 0 x := by
  have := (increment_bounds (x 0)).1
  simp only [downPath,signSum,Nat.zero_add,Finset.sum_range_one]
  omega
lemma downPath_martingale (P : Parameters) (h : ℕ) :
    Martingale (fun n x => (downPath h n x:ℝ)) rawFiltration (streamLaw P ℕ) := by
  convert (martingale_const rawFiltration (streamLaw P ℕ) (h:ℝ)).add (raw_sign_martingale P) using 1
  ext n x
  simp [downPath]
lemma firstDown_finite (P : Parameters) (h : ℕ) (hh : 0<h) : ∀ᵐ x ∂streamLaw P ℕ,firstDown h x≠⊤ := by
  have hj : ∀ᵐ x ∂streamLaw P ℕ,∃ᶠ n in atTop,downPath h (n+1) x≠downPath h n x := by
    filter_upwards [] with x
    apply Filter.Eventually.frequently
    filter_upwards [] with n
    unfold downPath
    rw [signSum_succ x (n+1)]
    have := (increment_bounds (x (n+1))).2.2
    omega
  filter_upwards [TreeCoding.integer_martingale_hits_zero (downPath_adapted h) (downPath_martingale P h)
    (downPath_initial h hh) (downPath_step h) hj] with x hx
  classical
  simp [firstDown,TreeCoding.firstZero,hx]

lemma firstDown_of_hit_iff (h : ℕ) (x : ℕ → Letter) (n : ℕ) :
    firstDown h x=WithTop.some n ↔ signSum x (n+1)= -(h:ℤ) ∧ ∀ j<n,signSum x (j+1)≠ -(h:ℤ) := by
  rw [firstDown,TreeCoding.firstZero_eq_iff]
  simp only [downPath]
  constructor
  · rintro ⟨hn,hj⟩
    exact ⟨by omega,fun j h => by have := hj j h; omega⟩
  · rintro ⟨hn,hj⟩
    exact ⟨by omega,fun j h => by have := hj j h; omega⟩
lemma firstDown_prefix_pos {h : ℕ} (hh : 0<h) {x : ℕ → Letter} {n : ℕ}
    (hn : firstDown h x=WithTop.some n) {j : ℕ} (hj : j ≤ n) : -(h:ℤ)<signSum x j := by
  have hd := (TreeCoding.firstZero_eq_iff (downPath h) x n).mp hn
  cases j with
  | zero => simp only [signSum,Finset.range_zero,Finset.sum_empty]; omega
  | succ j =>
    have hj' : j<n := by omega
    have he := TreeCoding.integer_path_nonneg_before_zero (fun k => downPath h k x)
      (downPath_initial h hh x) (fun k => downPath_step h k x) j (fun k hk => hd.2 k (hk.trans hj'))
    have hnz := hd.2 j hj'
    dsimp [downPath] at he hnz
    omega

def reverseRightWord (x : ℕ → Letter) : List Letter := stoppedWord (firstDown 1) x
def reverseRightLaw (P : Parameters) : Measure (List Letter) := (streamLaw P ℕ).map reverseRightWord
lemma reverseRightWord_measurable : Measurable reverseRightWord := measurable_stoppedWord (firstDown_measurable 1)
instance reverseRightLaw_probability (P : Parameters) : IsProbabilityMeasure (reverseRightLaw P) :=
  inferInstanceAs (IsProbabilityMeasure ((streamLaw P ℕ).map reverseRightWord))
lemma reverseRightWord_net (P : Parameters) : ∀ᵐ x ∂streamLaw P ℕ,
    ((reverseRightWord x).map Letter.increment).sum= -1 := by
  filter_upwards [firstDown_finite P 1 (by omega)] with x hx
  obtain ⟨n,hn⟩ := WithTop.ne_top_iff_exists.mp hx
  have hn' : firstDown 1 x=WithTop.some n := hn.symm
  rw [reverseRightWord,stoppedWord_of_hit hn',revealed_sum]
  exact (firstDown_of_hit_iff 1 x n).mp hn' |>.1

end Inventory
end FKCRT
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk

/-- Bounded discrete Green supersolution for the walk killed at -1. -/
def greenMajorant (a b : ℕ) : ℝ := 2*(min (a+1) (b+1):ℕ)
lemma greenMajorant_nonneg (a b : ℕ) : 0 ≤ greenMajorant a b := by unfold greenMajorant; positivity
lemma greenMajorant_zero (b : ℕ) :
    greenMajorant 0 b=(if 0=b then 1 else 0)+greenMajorant 1 b/2 := by
  cases b with
  | zero => norm_num [greenMajorant]
  | succ b => simp [greenMajorant]
lemma greenMajorant_succ (a b : ℕ) :
    greenMajorant (a+1) b=(if a+1=b then 1 else 0)+(greenMajorant a b+greenMajorant (a+2) b)/2 := by
  unfold greenMajorant
  by_cases he : a+1=b
  · subst b
    rw [ite_eq_left rfl]
    simp only [min_eq_left (show a+1 ≤ a+1+1 by omega),min_eq_right (show a+1+1 ≤ a+2+1 by omega),min_self]
    push_cast
    ring
  · rw [ite_eq_right he]
    rcases lt_or_gt_of_ne he with hlt | hgt
    · have h1 : a+1+1 ≤ b+1 := by omega
      have h2 : a+1 ≤ b+1 := by omega
      have h3 : a+2+1 ≤ b+1 := by omega
      rw [min_eq_left h1,min_eq_left h2,min_eq_left h3]
      push_cast
      ring
    · have h1 : b+1 ≤ a+1+1 := by omega
      have h2 : b+1 ≤ a+1 := by omega
      have h3 : b+1 ≤ a+2+1 := by omega
      rw [min_eq_right h1,min_eq_right h2,min_eq_right h3]
      ring

lemma killed_green_partial (N a b : ℕ) :
    (∑ n∈Finset.range N,killed n a b) ≤ greenMajorant a b := by
  induction N generalizing a with
  | zero => simpa only [Finset.range_zero,Finset.sum_empty] using greenMajorant_nonneg a b
  | succ N ih =>
    rw [Finset.sum_range_succ']
    cases a with
    | zero =>
      simp only [killed]
      rw [← Finset.sum_div,greenMajorant_zero]
      linarith [ih 1]
    | succ a =>
      simp only [killed]
      rw [← Finset.sum_div,Finset.sum_add_distrib,greenMajorant_succ]
      linarith [ih a,ih (a+2)]

lemma killed_summable (a b : ℕ) : Summable (fun n => killed n a b) := by
  exact summable_of_sum_range_le (fun n => killed_nonneg n a b) (fun N => killed_green_partial N a b)

/-- Expected visits below a first down-crossing are at most twice the
height above the killing boundary. This includes every initial level. -/
theorem killed_green_bound (a b : ℕ) : (∑' n,killed n a b) ≤ 2*(b+1:ℕ) := by
  have hh : (∑' n,killed n a b) ≤ greenMajorant a b :=
    le_of_tendsto (killed_summable a b).hasSum.tendsto_sum_nat (Filter.Eventually.of_forall (fun N => killed_green_partial N a b))
  apply hh.trans
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast min_le_right (a+1) (b+1)) (by norm_num)

end FKCRT.SimpleWalk
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

def burgerSign : Letter → Bool
  | .burger _ => true
  | .order _ => false
lemma burgerSign_increment (a : Letter) : SimpleWalk.sign (burgerSign a)=a.increment := by
  cases a <;> rfl
lemma burgerSign_preserving (P : Parameters) :
    MeasurePreserving burgerSign (law P).toMeasure TreeCoding.coinLaw := by
  refine ⟨measurable_of_countable _,?_⟩
  apply Measure.ext_of_singleton
  intro b
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),TreeCoding.coinLaw_singleton]
  have he : burgerSign ⁻¹' {b}=Finset.univ.filter (fun a => burgerSign a=b) := by ext a; simp
  rw [he,← sum_measure_singleton]
  simp only [Finset.sum_filter,law_singleton]
  rw [sum_letters]
  cases b <;> simp only [burgerSign,Bool.false_eq_true,Bool.true_eq_false,ite_false,ite_true,mass]
  · simp only [zero_add]
    rw [← ENNReal.ofReal_add (by linarith [P.upper] : 0 ≤ (1-P.p)/4) (by linarith [P.upper]),
      ← ENNReal.ofReal_add (by linarith [P.upper]) (by linarith [P.pos])]
    norm_num [show (1-P.p)/4+(1-P.p)/4+P.p/2=(1:ℝ)/2 by ring,ENNReal.ofReal_div_of_pos]
  · simp only [add_zero]
    rw [← ENNReal.ofReal_add (by norm_num : 0 ≤ (1:ℝ)/4) (by norm_num)]
    norm_num [ENNReal.ofReal_div_of_pos]

def rawPrefix (n : ℕ) (x : ℕ → Letter) : Fin n → Letter := fun i => x i
lemma rawPrefix_measurable (n : ℕ) : Measurable (rawPrefix n) :=
  Measurable.of_eval (fun index => measurable_pi_apply (index:ℕ))
lemma rawPrefix_preserving (P : Parameters) (n : ℕ) :
    MeasurePreserving (rawPrefix n) (streamLaw P ℕ) (Measure.pi (fun _ : Fin n => (law P).toMeasure)) := by
  have hi : iIndepFun (fun k (x : ℕ → Letter) => x k) (streamLaw P ℕ) :=
    iIndepFun_infinitePi (X := fun _ (a : Letter) => a) (fun _ => measurable_id)
  refine ⟨rawPrefix_measurable n,?_⟩
  have hh := (hi.precomp Fin.val_injective).map_fun_eq_pi_map (fun i : Fin n => (measurable_pi_apply (i:ℕ)).aemeasurable)
  change (streamLaw P ℕ).map (fun x (i : Fin n) => x i)=_
  rw [hh]
  congr 1
  funext i
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ => (law P).toMeasure) (i:ℕ)).map_eq

def rawWord (x : ℕ → Letter) (n : ℕ) : List Letter := List.ofFn (rawPrefix n x)
def wordWeight (P : Parameters) (w : List Letter) : ℝ≥0∞ := (w.map (fun a => (law P).toMeasure {a})).prod
lemma rawWord_cylinder (P : Parameters) (w : List Letter) :
    streamLaw P ℕ {x | rawWord x w.length=w}=wordWeight P w := by
  have he : {x | rawWord x w.length=w}=rawPrefix w.length ⁻¹' {w.get} := by
    ext x
    simp only [Set.mem_ofPred_eq,Set.mem_preimage,Set.mem_singleton_iff,rawWord]
    constructor
    · intro h
      funext i
      have := congrArg (fun l : List Letter => l[i.val]?) h
      simpa using this
    · intro h; rw [h,List.ofFn_get]
  rw [he,(rawPrefix_preserving P w.length).measure_preimage (measurableSet_singleton _).nullMeasurableSet,
    Measure.pi_singleton]
  unfold wordWeight
  conv_rhs => rw [← List.ofFn_get w,List.map_ofFn,List.prod_ofFn]
  rfl

def finiteSigns {n : ℕ} (x : Fin n → Letter) : SimpleWalk.Path n := fun i => burgerSign (x i)
lemma finiteSigns_preserving (P : Parameters) (n : ℕ) :
    MeasurePreserving finiteSigns (Measure.pi (fun _ : Fin n => (law P).toMeasure))
      (Measure.pi (fun _ : Fin n => TreeCoding.coinLaw)) := by
  refine ⟨measurable_of_countable _,?_⟩
  change (Measure.pi _).map (fun x i => burgerSign (x i))=Measure.pi _
  rw [Measure.pi_map_pi (fun _ => (measurable_of_countable _).aemeasurable)]
  simp only [(burgerSign_preserving P).map_eq]
lemma raw_sign_pathSum (x : ℕ → Letter) (n k : ℕ) (hk : k ≤ n) :
    SimpleWalk.pathSum (finiteSigns (rawPrefix n x)) k=signSum x k := by
  unfold SimpleWalk.pathSum finiteSigns rawPrefix signSum
  simp only [burgerSign_increment]
  rw [← Finset.sum_filter]
  rw [← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_bij (fun i hi => ⟨i.val,(Finset.mem_filter.mp hi).2⟩)
    (by intro i hi; simp) (by intro i hi j hj he; exact Fin.ext (congrArg (fun z : Fin k => z.val) he))
    (by intro j hj; exact ⟨⟨j.val,lt_of_lt_of_le j.isLt hk⟩,by simp [j.isLt],rfl⟩)
    (by intro i hi; rfl)

def rawKilled (a b n : ℕ) : Set (ℕ → Letter) :=
  {x | (∀ j ≤ n,0 ≤ (a:ℤ)+signSum x j) ∧ (a:ℤ)+signSum x n=b}
lemma rawKilled_measure (P : Parameters) (a b n : ℕ) :
    (streamLaw P ℕ).real (rawKilled a b n)=SimpleWalk.killed n a b := by
  have hp := (finiteSigns_preserving P n).comp (rawPrefix_preserving P n)
  have he : rawKilled a b n=(fun x => finiteSigns (rawPrefix n x)) ⁻¹'
      {d | SimpleWalk.nonnegativePath a d ∧ (a:ℤ)+SimpleWalk.pathSum d n=b} := by
    ext x
    simp only [rawKilled,Set.mem_ofPred_eq,Set.mem_preimage,SimpleWalk.nonnegativePath]
    simp_rw [raw_sign_pathSum x n n le_rfl]
    apply and_congr_left
    intro _
    apply forall_congr'
    intro j
    apply forall_congr'
    intro hj
    rw [raw_sign_pathSum x n j hj]
  rw [he,measureReal_def]
  change ((streamLaw P ℕ) ((finiteSigns ∘ rawPrefix n) ⁻¹' _)).toReal=_
  rw [hp.measure_preimage (Set.to_countable _).measurableSet.nullMeasurableSet,
    ← measureReal_def,TreeCoding.coinPath_event,SimpleWalk.pathMass_killed]

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable
namespace FKCRT.Inventory

lemma typed_fixed_balance {v : List TypedLetter} (h : stackTypedRun v []=some []) :
    ((v.map TypedLetter.fixed).map Letter.increment).sum=0 := by
  apply ((emptyReducing_dyck _ ((emptyReducing_iff_identify _).mpr ⟨v,identify_fixed h⟩)).1)

def burgerCount (v : List TypedLetter) : ℕ :=
  (v.filter (fun a => match a with | .burger _ => true | .order _ => false)).length

def orderCount (v : List TypedLetter) : ℕ :=
  (v.filter (fun a => match a with | .burger _ => false | .order _ => true)).length

lemma typed_counts (v : List TypedLetter) :
    burgerCount v+orderCount v=v.length ∧
    ((v.map TypedLetter.fixed).map Letter.increment).sum=(burgerCount v:ℤ)-orderCount v := by
  induction v with
  | nil => simp [burgerCount,orderCount]
  | cons a v ih =>
    cases a <;> simp [burgerCount,orderCount,TypedLetter.fixed,Letter.increment] at * <;> omega

lemma fixed_wordMass (P : Parameters) (v : List TypedLetter) :
    wordMass P (v.map TypedLetter.fixed)=(1/4:ℝ)^burgerCount v*((1-P.p)/4)^orderCount v := by
  induction v with
  | nil => simp [wordMass,burgerCount,orderCount]
  | cons a v ih =>
    cases a <;> simp_all [wordMass,burgerCount,orderCount,TypedLetter.fixed,mass,pow_succ] <;> ring

lemma fixed_wordMass_empty (P : Parameters) {m : ℕ} {v : List TypedLetter}
    (hv : v.length=2*m) (h : stackTypedRun v []=some []) :
    wordMass P (v.map TypedLetter.fixed)=((1-P.p)/16)^m := by
  have hb := typed_fixed_balance h
  obtain ⟨ha,hb'⟩ := typed_counts v
  have hB : burgerCount v=m := by omega
  have hO : orderCount v=m := by omega
  rw [fixed_wordMass,hB,hO,← mul_pow]
  congr 1
  ring

lemma markings_mass_empty (P : Parameters) {m : ℕ} {v : List TypedLetter}
    (hv : v.length=2*m) (h : stackTypedRun v []=some []) :
    (∑ w∈markings v [],wordMass P w)=
      ((1-P.p)/16)^m*(1+2*P.p/(1-P.p))^flexibleCount v [] := by
  rw [markings_mass P h,fixed_wordMass_empty P hv h]

def wordsOfLength (α : Type*) [Fintype α] [DecidableEq α] (N : ℕ) : Finset (List α) :=
  Finset.univ.image (List.ofFn : (Fin N→α)→List α)

lemma mem_wordsOfLength {α : Type*} [Fintype α] [DecidableEq α] {N : ℕ} {w : List α} :
    w∈wordsOfLength α N ↔ w.length=N := by
  constructor
  · intro h
    obtain ⟨f,_,rfl⟩ := Finset.mem_image.mp h
    exact List.length_ofFn
  · intro h
    subst N
    apply Finset.mem_image.mpr
    exact ⟨fun i => w[i],Finset.mem_univ _,by simp⟩

def emptyWords (N : ℕ) : Finset (List Letter) := (wordsOfLength Letter N).filter EmptyReducing

def typedEmptyWords (N : ℕ) : Finset (List TypedLetter) :=
  (wordsOfLength TypedLetter N).filter (fun v => stackTypedRun v []=some [])

lemma emptyWords_markings (N : ℕ) :
    emptyWords N=(typedEmptyWords N).biUnion (fun v => markings v []) := by
  ext w
  simp only [emptyWords,Finset.mem_filter,mem_wordsOfLength,Finset.mem_biUnion,
    typedEmptyWords,mem_markings]
  constructor
  · rintro ⟨hl,hw⟩
    obtain ⟨v,hv⟩ := (emptyReducing_iff_identify _).mp hw
    obtain ⟨_,hr,he⟩ := identify_sound hv
    exact ⟨v,⟨he.trans hl,hr⟩,[],hv⟩
  · rintro ⟨v,⟨hl,hr⟩,t,ht⟩
    obtain ⟨_,hr',he⟩ := identify_sound ht
    have htt : t=[] := by rw [hr] at hr'; exact Option.some.inj hr'.symm
    subst t
    exact ⟨he.symm.trans hl,(emptyReducing_iff_identify _).mpr ⟨v,ht⟩⟩

lemma markings_disjoint (N : ℕ) : (typedEmptyWords N : Set (List TypedLetter)).PairwiseDisjoint
    (fun v => markings v []) := by
  intro v _ u _ hne
  apply Finset.disjoint_left.mpr
  intro w hv hu
  obtain ⟨t,ht⟩ := mem_markings.mp hv
  obtain ⟨s,hs⟩ := mem_markings.mp hu
  exact hne (Prod.mk.inj (Option.some.inj (ht.symm.trans hs))).1

/-- Exact total genuine iid weight, before identifying it with its cylinder
probability. All flexible markings are summed, not picked deterministically. -/
theorem empty_wordMass_sum (P : Parameters) (m : ℕ) :
    (∑ w∈emptyWords (2*m),wordMass P w)=
      ((1-P.p)/16)^m * ∑ v∈typedEmptyWords (2*m),
        (1+2*P.p/(1-P.p))^flexibleCount v [] := by
  rw [emptyWords_markings,Finset.sum_biUnion (markings_disjoint _),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  obtain ⟨hl,hr⟩ := Finset.mem_filter.mp hv
  exact markings_mass_empty P (mem_wordsOfLength.mp hl) hr

lemma wordMass_nonneg (P : Parameters) (w : List Letter) : 0≤wordMass P w :=
  List.prod_nonneg (fun a ha => by obtain ⟨b,_,rfl⟩ := List.mem_map.mp ha; exact (mass_pos P b).le)

lemma wordWeight_eq (P : Parameters) (w : List Letter) :
    wordWeight P w=ENNReal.ofReal (wordMass P w) := by
  induction w with
  | nil => simp [wordWeight,wordMass]
  | cons a w ih =>
    simp only [wordWeight,wordMass,List.map_cons,List.prod_cons] at *
    rw [law_singleton,ih,ENNReal.ofReal_mul (mass_pos P a).le]

lemma rawEmpty_measure (P : Parameters) (N : ℕ) :
    streamLaw P ℕ {x | EmptyReducing (rawWord x N)}=
      ENNReal.ofReal (∑ w∈emptyWords N,wordMass P w) := by
  have he : {x | EmptyReducing (rawWord x N)}=
      ⋃ w∈emptyWords N,{x | rawWord x N=w} := by
    ext x
    simp only [Set.mem_ofPred_eq,Set.mem_iUnion]
    constructor
    · intro h
      exact ⟨rawWord x N,Finset.mem_filter.mpr ⟨mem_wordsOfLength.mpr (by simp [rawWord]),h⟩,rfl⟩
    · rintro ⟨w,hw,hx⟩
      rw [hx]
      exact (Finset.mem_filter.mp hw).2
  have hd : (emptyWords N : Set (List Letter)).PairwiseDisjoint
      (fun w => {x | rawWord x N=w}) := by
    intro v _ w _ hvw
    exact Set.disjoint_left.mpr (fun x hv hw => hvw (hv.symm.trans hw))
  have hm (w : List Letter) : MeasurableSet {x : ℕ→Letter | rawWord x N=w} :=
    ((measurable_of_countable List.ofFn).comp (rawPrefix_measurable N)) (measurableSet_singleton w)
  rw [he,measure_biUnion_finset hd (fun w _ => hm w)]
  have hh (w) (hw : w∈emptyWords N) :
      streamLaw P ℕ {x | rawWord x N=w}=ENNReal.ofReal (wordMass P w) := by
    have hl := mem_wordsOfLength.mp (Finset.mem_filter.mp hw).1
    rw [← hl,rawWord_cylinder,wordWeight_eq]
  simp_rw [Finset.sum_congr rfl hh]
  exact (ENNReal.ofReal_sum_of_nonneg (fun w _ => wordMass_nonneg P w)).symm

lemma rawEmpty_real (P : Parameters) (N : ℕ) :
    (streamLaw P ℕ).real {x | EmptyReducing (rawWord x N)}=
      ∑ w∈emptyWords N,wordMass P w := by
  rw [measureReal_def,rawEmpty_measure,ENNReal.toReal_ofReal (Finset.sum_nonneg (fun w _ => wordMass_nonneg P w))]

end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm
open scoped BigOperators ENNReal
namespace FKCRT.Inventory

lemma cornerInsert_length (l : List (TypedLetter×List TypedLetter)) :
    (cornerInsert l).length=l.length+(l.map (fun x => x.2.length)).sum := by
  induction l with
  | nil => simp [cornerInsert]
  | cons x l ih =>
    simp only [cornerInsert,List.flatMap_cons,List.length_append,List.length_cons] at *
    simp only [List.map_cons,List.sum_cons]
    omega

lemma cornerList_length (c : Core) (f : Fin c.val.length→List TypedLetter) :
    (cornerInsert (cornerList c f)).length=c.val.length+∑ i,(f i).length := by
  rw [cornerInsert_length]
  simp only [cornerList,List.length_ofFn,List.map_ofFn,List.sum_ofFn,Function.comp_apply]

lemma cornerList_flexible (c : Core) (f : Fin c.val.length→EmptyTypedWord) :
    flexibleCount (cornerInsert (cornerList c (fun i => (f i).val))) []=
      flexibleCount c.val []+∑ i,flexibleCount (f i).val [] := by
  have h := (cornerInsert_run_count _ (cornerList_valid c f).2
    (coreWord_empty _ (cornerList_valid c f).1)).2
  rw [cornerList_fst] at h
  simpa only [cornerList,List.map_ofFn,List.sum_ofFn,Function.comp_apply] using h

lemma empty_length_even (w : EmptyTypedWord) : Even w.val.length := by
  have h := typed_fixed_balance w.property
  obtain ⟨ha,hb⟩ := typed_counts w.val
  refine ⟨burgerCount w.val,?_⟩
  omega

namespace CoreTree

def vertexCount : CoreTree→ℕ
  | leaf => 1
  | branch _ ts => 1+∑ i,vertexCount (ts i)

lemma word_length (t : CoreTree) : t.word.length+1=t.vertexCount := by
  induction t with
  | leaf => rfl
  | branch c ts ih =>
    change (cornerInsert (cornerList c (fun i => (ts i).word))).length+1=1+∑ i,(ts i).vertexCount
    rw [cornerList_length]
    simp_rw [← ih]
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one]
    omega

end CoreTree

/-- Literal weight in the letter-size variable. Specializing r²=u gives
exactly the source weight t^flex u^edges. -/
def wordMonomial {R : Type*} [CommMonoid R] (t r : R) (w : List TypedLetter) : R :=
  t^flexibleCount w []*r^w.length

lemma wordMonomial_nil {R : Type*} [CommMonoid R] (t r : R) : wordMonomial t r []=1 := by
  simp [wordMonomial,flexibleCount]

lemma wordMonomial_corners {R : Type*} [CommMonoid R] (t r : R) (c : Core)
    (f : Fin c.val.length→EmptyTypedWord) :
    wordMonomial t r (cornerInsert (cornerList c (fun i => (f i).val)))=
      wordMonomial t r c.val * ∏ i,wordMonomial t r (f i).val := by
  simp only [wordMonomial,cornerList_length,cornerList_flexible,pow_add,Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  ac_rfl

/-- The full genuine word generating series, with no convergence premise. -/
def wordSeries (t r : ℝ≥0∞) : ℝ≥0∞ := ∑' w : EmptyTypedWord,wordMonomial t r w.val

lemma tsum_fin_product {α : Type*} (f : α→ℝ≥0∞) (n : ℕ) :
    (∑' g : Fin n→α,∏ i,f (g i))=(∑' a,f a)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (n+1) => α)).tsum_eq]
    simp only [Fin.consEquiv_apply,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]
    rw [ENNReal.tsum_prod']
    simp_rw [ENNReal.tsum_mul_left,ih]
    rw [ENNReal.tsum_mul_right,pow_succ']

lemma coreChildrenEquiv_weight (t r : ℝ≥0∞) (d : CornerData) :
    wordMonomial t r (coreChildrenEquiv d).val.val=
      wordMonomial t r d.1.val*∏ i,wordMonomial t r (d.2 i).val :=
  wordMonomial_corners t r d.1 d.2

/-- The nonempty part of T is exactly the nonnegative connected-core
substitution series. No independence or coefficient identity is assumed. -/
theorem nonempty_word_series (t r : ℝ≥0∞) :
    (∑' w : NonemptyTypedWord,wordMonomial t r w.val.val)=
      ∑' c : Core,t^flexibleCount c.val []*(r*wordSeries t r)^c.val.length := by
  rw [← coreChildrenEquiv.tsum_eq]
  simp_rw [coreChildrenEquiv_weight]
  rw [ENNReal.tsum_sigma (fun (c : Core) (f : Fin c.val.length→EmptyTypedWord) => wordMonomial t r c.val*∏ i,wordMonomial t r (f i).val)]
  apply tsum_congr
  intro c
  rw [ENNReal.tsum_mul_left,tsum_fin_product (fun w : EmptyTypedWord => wordMonomial t r w.val) c.val.length,wordMonomial,mul_pow]
  exact mul_assoc _ _ _

end FKCRT.Inventory
end

end OAI
