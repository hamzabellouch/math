import OAI.Probability.FKMaps.LadderCuts
import OAI.Probability.FKMaps.StationaryCuts

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

instance : MeasurableSpace Order := ⊤
instance : MeasurableSingletonClass Order := ⟨fun _ => trivial⟩
instance : MeasurableSpace (List Order) := ⊤
instance : MeasurableSingletonClass (List Order) := ⟨fun _ => trivial⟩

/-- Chronological concatenation between whole-piece boundaries. -/
def intervalWord (x : ℤ → List Letter) (a : ℤ) (n : ℕ) : List Letter :=
  piecesPrefix (fun j => x (a+j)) n
lemma intervalWord_zero (x : ℤ → List Letter) (a : ℤ) : intervalWord x a 0=[] := rfl
lemma intervalWord_succ (x : ℤ → List Letter) (a : ℤ) (n : ℕ) :
    intervalWord x a (n+1)=intervalWord x a n++x (a+n) := rfl
lemma intervalWord_add (x : ℤ → List Letter) (a : ℤ) (m n : ℕ) :
    intervalWord x a (m+n)=intervalWord x a m++intervalWord x (a+m) n := by
  rw [intervalWord,piecesPrefix_add]
  congr 2
  funext j
  dsimp only [piecesTail]
  congr 1
  push_cast
  ring
lemma intervalWord_measurable (a : ℤ) (n : ℕ) : Measurable (fun x : ℤ → List Letter => intervalWord x a n) :=
  (piecesPrefix_measurable n).comp (Measurable.of_eval (fun j => measurable_pi_apply (a+j)))
lemma intervalWord_shift (x : ℤ → List Letter) (a b : ℤ) (n : ℕ) :
    intervalWord (Stationary.shift b x) a n=intervalWord x (a+b) n := by
  unfold intervalWord
  congr 1
  funext j
  simp only [Stationary.shift]
  congr 1
  omega
lemma intervalWord_net (x : ℤ → List Letter) (a : ℤ) (n : ℕ) (d : ℤ)
    (hd : ∀ j,((x j).map Letter.increment).sum=d) :
    ((intervalWord x a n).map Letter.increment).sum=(n:ℤ)*d := by
  induction n with
  | zero => simp [intervalWord_zero]
  | succ n ih => rw [intervalWord_succ,List.map_append,List.sum_append,ih,hd]; push_cast; ring

lemma reduce_append_no_burgers (u v : List Letter) (hu : (reduce u).burgers=[]) :
    reduce (u++v)=⟨(reduce u).orders++(reduce v).orders,(reduce v).burgers⟩ := by
  unfold reduce
  rw [run_append]
  have he : run u ⟨[],[]⟩=⟨(reduce u).orders,[]⟩ := by cases h : reduce u; simp_all [reduce]
  rw [he]
  simpa only [List.append_nil] using run_orders_prefix v (reduce u).orders (⟨[],[]⟩ : Evaluation)
lemma reduce_append_no_orders (u v : List Letter) (hv : (reduce v).orders=[]) :
    reduce (u++v)=⟨(reduce u).orders,(reduce v).burgers++(reduce u).burgers⟩ := by
  have h := run_orders_prefix v (reduce u).orders (⟨[],(reduce u).burgers⟩ : Evaluation)
  simp only [List.append_nil] at h
  rw [reduce,run_append]
  rw [show run u ⟨[],[]⟩=⟨(reduce u).orders,(reduce u).burgers⟩ by rfl,h,run_older_supply,hv,evalOrders_nil]
  simp only [List.append_nil]

def leftCutAt (x : ℤ → List Letter) (a : ℤ) : Prop := ∀ n,(reduce (intervalWord x a n)).orders=[]
def rightCutAt (x : ℤ → List Letter) (b : ℤ) : Prop := ∀ n : ℕ,(reduce (intervalWord x (b-n) n)).burgers=[]
lemma leftCutAt_measurable (a : ℤ) : MeasurableSet {x | leftCutAt x a} := by
  simp only [leftCutAt,Set.ofPred_forall]
  exact MeasurableSet.iInter (fun n => (intervalWord_measurable a n) ((Set.to_countable {w : List Letter | (reduce w).orders=[]}).measurableSet))
lemma rightCutAt_measurable (b : ℤ) : MeasurableSet {x | rightCutAt x b} := by
  simp only [rightCutAt,Set.ofPred_forall]
  exact MeasurableSet.iInter (fun n => (intervalWord_measurable (b-n) n) ((Set.to_countable {w : List Letter | (reduce w).burgers=[]}).measurableSet))
lemma leftCutAt_shift (x : ℤ → List Letter) (a b : ℤ) :
    leftCutAt (Stationary.shift b x) a ↔ leftCutAt x (a+b) := by
  simp only [leftCutAt,intervalWord_shift]
lemma rightCutAt_shift (x : ℤ → List Letter) (a b : ℤ) :
    rightCutAt (Stationary.shift b x) a ↔ rightCutAt x (a+b) := by
  simp only [rightCutAt,intervalWord_shift]
  have he (n : ℕ) : a-(n:ℤ)+b=a+b-n := by omega
  simp only [he]
lemma no_burgers_interval {x : ℤ → List Letter} {a : ℤ} {n : ℕ} (h : rightCutAt x (a+n)) :
    (reduce (intervalWord x a n)).burgers=[] := by simpa using h n

def rightOrders (x : ℤ → List Letter) (a : ℤ) (n : ℕ) : List Order := (reduce (intervalWord x a n)).orders
lemma rightOrders_length {x : ℤ → List Letter} (hd : ∀ j,((x j).map Letter.increment).sum= -1)
    (a : ℤ) (n : ℕ) (hb : rightCutAt x (a+n)) : (rightOrders x a n).length=n := by
  have he := reduce_imbalance (intervalWord x a n)
  rw [imbalance,no_burgers_interval hb,intervalWord_net x a n (-1) hd] at he
  simp only [List.length_nil,Nat.cast_zero,zero_sub,mul_neg_one] at he
  dsimp [rightOrders]
  omega
lemma rightOrders_append {x : ℤ → List Letter} (a : ℤ) (m n : ℕ)
    (hm : rightCutAt x (a+m)) : rightOrders x a (m+n)=rightOrders x a m++rightOrders x (a+m) n := by
  simp only [rightOrders,intervalWord_add,reduce_append_no_burgers _ _ (no_burgers_interval hm)]
def rightOutput (x : ℤ → List Letter) (i : ℤ) : Order := CutOutput.output (rightCutAt x) (rightOrders x) none i
lemma rightOutput_measurable (i : ℤ) : Measurable (fun x => rightOutput x i) := by
  apply CutOutput.output_measurable _ _ none i rightCutAt_measurable
  intro a n
  exact (measurable_of_countable (fun w : List Letter => (reduce w).orders)).comp (intervalWord_measurable a n)
lemma rightOutput_shift (x : ℤ → List Letter) (a i : ℤ) :
    rightOutput (Stationary.shift a x) i=rightOutput x (i+a) := by
  have hc : rightCutAt (Stationary.shift a x)=fun j => rightCutAt x (j+a) := by
    funext j; exact propext (rightCutAt_shift x j a)
  have hw : rightOrders (Stationary.shift a x)=fun j n => rightOrders x (j+a) n := by
    funext j n; simp only [rightOrders,intervalWord_shift]
  exact (show CutOutput.output (rightCutAt (Stationary.shift a x)) (rightOrders (Stationary.shift a x)) none i=_ by
    rw [hc,hw,CutOutput.output_translate]; rfl)
def rightOutputData (x : ℤ → List Letter) (hd : ∀ j,((x j).map Letter.increment).sum= -1) : CutOutput.Data Order where
  cut := rightCutAt x
  word := rightOrders x
  length a n _ hb := rightOrders_length hd a n hb
  append a m n _ hm _ := rightOrders_append a m n hm
lemma rightOutput_segment {x : ℤ → List Letter} (hd : ∀ j,((x j).map Letter.increment).sum= -1)
    (a : ℤ) (n : ℕ) (ha : rightCutAt x a) (hb : rightCutAt x (a+n)) :
    List.ofFn (fun j : Fin n => rightOutput x (a+j))=rightOrders x a n :=
  (rightOutputData x hd).output_segment none a n ha hb

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

def rightWord (x : ℕ → Letter) : List Letter := (reverseRightWord x).reverse
def rightLaw (P : Parameters) : Measure (List Letter) := (reverseRightLaw P).map List.reverse
lemma rightWord_measurable : Measurable rightWord := (measurable_of_countable List.reverse).comp reverseRightWord_measurable
lemma rightLaw_eq (P : Parameters) : rightLaw P=(streamLaw P ℕ).map rightWord := by
  rw [rightLaw,reverseRightLaw,Measure.map_map (measurable_of_countable List.reverse) reverseRightWord_measurable]
  rfl
instance rightLaw_probability (P : Parameters) : IsProbabilityMeasure (rightLaw P) :=
  inferInstanceAs (IsProbabilityMeasure ((reverseRightLaw P).map List.reverse))
lemma rightLaw_reverse (P : Parameters) : (rightLaw P).map List.reverse=reverseRightLaw P := by
  rw [rightLaw,Measure.map_map (measurable_of_countable List.reverse) (measurable_of_countable List.reverse)]
  simp only [Function.comp_def,List.reverse_reverse]
  exact Measure.map_id
lemma rightLaw_net (P : Parameters) : ∀ᵐ w ∂rightLaw P,(w.map Letter.increment).sum= -1 := by
  rw [rightLaw_eq,ae_map_iff rightWord_measurable.aemeasurable ((Set.to_countable _).measurableSet)]
  simpa only [rightWord,List.map_reverse,List.sum_reverse] using reverseRightWord_net P
lemma rightSeq_net (P : Parameters) : ∀ᵐ x ∂Stationary.seqLaw (rightLaw P),∀ j,((x j).map Letter.increment).sum= -1 := by
  apply ae_all_iff.mpr
  intro j
  exact (measurePreserving_eval_infinitePi (fun _ : ℤ => rightLaw P) j).quasiMeasurePreserving.ae (rightLaw_net P)

def reversedPast (x : ℤ → List Letter) : ℕ → List Letter := fun j => (x (-1-j)).reverse
lemma reversedPast_measurable : Measurable reversedPast :=
  Measurable.of_eval (fun j => (measurable_of_countable List.reverse).comp (measurable_pi_apply (-1-(j:ℤ))))
lemma reversedPast_preserving (P : Parameters) :
    MeasurePreserving reversedPast (Stationary.seqLaw (rightLaw P)) (naturalPiecesLaw (reverseRightLaw P)) := by
  let f : (ℤ → List Letter) → (ℕ → List Letter) := fun x j => x (-1-j)
  have hf : MeasurePreserving f (Stationary.seqLaw (rightLaw P)) (naturalPiecesLaw (rightLaw P)) := by
    refine ⟨Measurable.of_eval (fun j => measurable_pi_apply (-1-(j:ℤ))),?_⟩
    exact Measure.map_infinitePi_infinitePi_of_inj (fun i j h => by omega)
  have hg : MeasurePreserving (fun x : ℕ → List Letter => fun j => (x j).reverse)
      (naturalPiecesLaw (rightLaw P)) (naturalPiecesLaw (reverseRightLaw P)) := by
    refine ⟨Measurable.of_eval (fun j => (measurable_of_countable List.reverse).comp (measurable_pi_apply j)),?_⟩
    change (Measure.infinitePi _).map _=Measure.infinitePi _
    rw [Measure.infinitePi_map_pi (fun _ : ℕ => rightLaw P) (fun _ => measurable_of_countable List.reverse)]
    simp only [rightLaw_reverse]
  exact hg.comp hf
lemma intervalWord_first (x : ℤ → List Letter) (a : ℤ) (n : ℕ) :
    intervalWord x a (n+1)=x a++intervalWord x (a+1) n := by
  rw [show n+1=1+n by omega,intervalWord_add]
  simp only [intervalWord_succ,intervalWord_zero,List.nil_append,Nat.cast_zero,add_zero,Nat.cast_one]
lemma reversedPast_prefix (x : ℤ → List Letter) (n : ℕ) :
    (piecesPrefix (reversedPast x) n).reverse=intervalWord x (-(n:ℤ)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [piecesPrefix,List.reverse_append,ih,intervalWord_first]
    simp only [reversedPast,List.reverse_reverse,Nat.cast_add,Nat.cast_one]
    rw [show -((n:ℤ)+1)= -1-n by omega,
      show -1-(n:ℤ)+1= -n by omega]
lemma rightCutAt_zero_iff (x : ℤ → List Letter) : rightCutAt x 0 ↔ RightCut (reversedPast x) := by
  simp only [rightCutAt,RightCut,reversedPast_prefix,zero_sub]
lemma rightCutAt_positive (P : Parameters) : 0<Stationary.seqLaw (rightLaw P) {x | rightCutAt x 0} := by
  have he := (reversedPast_preserving P).measure_preimage measurableSet_rightCut.nullMeasurableSet
  have hs : {x | rightCutAt x 0}=reversedPast ⁻¹' {x | RightCut x} := by ext x; exact rightCutAt_zero_iff x
  rw [hs,he]
  exact positive_rightCut P

lemma rightWord_of_order {x : ℕ → Letter} {o : Order} (hx : x 0=Letter.order o) :
    rightWord x=[Letter.order o] := by
  have hh : firstDown 1 x=WithTop.some 0 := by
    rw [firstDown_of_hit_iff]
    constructor
    · simp [signSum,hx,Letter.increment]
    · intro j hj; omega
  simp [rightWord,reverseRightWord,stoppedWord_of_hit hh,revealed,hx]
lemma rightLaw_order_positive (P : Parameters) (o : Order) : 0<rightLaw P {[Letter.order o]} := by
  rw [rightLaw_eq,Measure.map_apply rightWord_measurable (measurableSet_singleton _)]
  have hle : streamLaw P ℕ {x | x 0=Letter.order o} ≤ streamLaw P ℕ (rightWord ⁻¹' {[Letter.order o]}) :=
    measure_mono (fun x hx => rightWord_of_order hx)
  have he : streamLaw P ℕ {x | x 0=Letter.order o}=(law P).toMeasure {Letter.order o} :=
    (measurePreserving_eval_infinitePi (fun _ : ℕ => (law P).toMeasure) 0).measure_preimage
      (measurableSet_singleton (Letter.order o)).nullMeasurableSet
  rw [he,law_singleton] at hle
  exact (ENNReal.ofReal_pos.mpr (mass_pos P _)).trans_le hle

lemma increment_flip (a : Letter) : a.flip.increment=a.increment := by cases a <;> rfl
lemma signSum_flip (x : ℕ → Letter) (n : ℕ) : signSum (flipStream x) n=signSum x n := by
  simp only [signSum,flipStream,increment_flip]
lemma firstDown_flip (h : ℕ) (x : ℕ → Letter) : firstDown h (flipStream x)=firstDown h x := by
  apply eq_of_forall_ge_iff
  intro n
  cases n with
  | top => simp
  | coe n => simp only [firstDown,TreeCoding.firstZero_le_iff,downPath,signSum_flip]
lemma rightWord_flip (x : ℕ → Letter) : rightWord (flipStream x)=(rightWord x).map Letter.flip := by
  simp only [rightWord,reverseRightWord,stoppedWord,firstDown_flip,revealed_flip,List.map_reverse]
lemma rightLaw_flip_preserving (P : Parameters) :
    MeasurePreserving (List.map Letter.flip) (rightLaw P) (rightLaw P) := by
  refine ⟨measurable_of_countable _,?_⟩
  rw [rightLaw_eq,Measure.map_map (measurable_of_countable _) rightWord_measurable]
  have he : List.map Letter.flip ∘ rightWord=rightWord ∘ flipStream := by funext x; exact (rightWord_flip x).symm
  rw [he,← Measure.map_map rightWord_measurable measurable_flipStream,(flipStream_preserving P).map_eq]

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

def flipPieceSeq (x : ℤ → List Letter) : ℤ → List Letter := fun j => (x j).map Letter.flip
lemma flipPieceSeq_measurable : Measurable flipPieceSeq :=
  Measurable.of_eval (fun j => (measurable_of_countable _).comp (measurable_pi_apply j))
lemma flipPieceSeq_preserving (P : Parameters) :
    MeasurePreserving flipPieceSeq (Stationary.seqLaw (rightLaw P)) (Stationary.seqLaw (rightLaw P)) := by
  refine ⟨flipPieceSeq_measurable,?_⟩
  change (Measure.infinitePi _).map (fun x : ℤ → List Letter => fun j => (x j).map Letter.flip)=Measure.infinitePi _
  rw [Measure.infinitePi_map_pi (fun _ : ℤ => rightLaw P) (fun _ => measurable_of_countable (List.map Letter.flip))]
  simp only [(rightLaw_flip_preserving P).map_eq]
lemma intervalWord_flip (x : ℤ → List Letter) (a : ℤ) (n : ℕ) :
    intervalWord (flipPieceSeq x) a n=(intervalWord x a n).map Letter.flip := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [intervalWord_succ,ih,flipPieceSeq,List.map_append]
lemma rightCutAt_flip (x : ℤ → List Letter) (a : ℤ) : rightCutAt (flipPieceSeq x) a ↔ rightCutAt x a := by
  simp only [rightCutAt,intervalWord_flip,burgers_flip_empty_iff]
lemma rightOrders_flip (x : ℤ → List Letter) (a : ℤ) (n : ℕ) :
    rightOrders (flipPieceSeq x) a n=(rightOrders x a n).map (Option.map Bool.not) := by
  simp only [rightOrders,intervalWord_flip,reduce_flip,Evaluation.flip]
lemma rightOutput_flip (x : ℤ → List Letter) (i : ℤ) :
    rightOutput (flipPieceSeq x) i=(rightOutput x i).map Bool.not := by
  have hc : rightCutAt (flipPieceSeq x)=rightCutAt x := by funext j; exact propext (rightCutAt_flip x j)
  unfold rightOutput CutOutput.output
  rw [hc,rightOrders_flip,List.getElem?_map]
  exact Option.getD_map (Option.map Bool.not) none _

lemma rightCutAt_zero_past_measurable :
    MeasurableSet[Stationary.coords (α := List Letter) {j | j<0}] {x | rightCutAt x 0} := by
  have hm : Measurable[Stationary.coords (α := List Letter) {j | j<0}] reversedPast := by
    let : MeasurableSpace (ℤ → List Letter) := Stationary.coords {j | j<0}
    apply Measurable.of_eval
    intro j
    apply (measurable_of_countable List.reverse).comp
    apply measurable_iff_comap_le.mpr
    exact le_iSup_of_le (-1-(j:ℤ)) (le_iSup_of_le (show -1-(j:ℤ)<0 by omega) le_rfl)
  have hs : {x | rightCutAt x 0}=reversedPast ⁻¹' {x | RightCut x} := by ext x; exact rightCutAt_zero_iff x
  rw [hs]
  exact hm measurableSet_rightCut
lemma rightCutAt_one_of_order {x : ℤ → List Letter} (hc : rightCutAt x 0) {o : Order}
    (hx : x 0=[Letter.order o]) : rightCutAt x 1 := by
  intro n
  cases n with
  | zero => simp [intervalWord_zero,reduce,run]
  | succ n =>
    rw [intervalWord_succ]
    have ha : (1:ℤ)-(n+1)= -(n:ℤ) := by omega
    have hb : (1:ℤ)-(n+1)+n=0 := by omega
    simp only [Nat.cast_add,Nat.cast_one]
    rw [hb,hx,ha]
    have hh : (reduce (intervalWord x (-(n:ℤ)) n)).burgers=[] := by simpa using hc n
    exact append_order_no_burgers hh o
lemma rightOutput_of_cut_order {x : ℤ → List Letter} (hc : rightCutAt x 0) {o : Order}
    (hx : x 0=[Letter.order o]) : rightOutput x 0=o := by
  have hd := rightCutAt_one_of_order hc hx
  have hl : CutOutput.left (rightCutAt x) 0=0 := by
    apply Nat.eq_zero_of_le_zero
    exact CutOutput.firstIndex_le (p := fun k => rightCutAt x (0-k)) (k := 0) (by simpa using hc)
  have hr : CutOutput.right (rightCutAt x) 0=0 := by
    apply Nat.eq_zero_of_le_zero
    exact CutOutput.firstIndex_le (p := fun k => rightCutAt x (0+1+k)) (k := 0) (by simpa using hd)
  simp [rightOutput,CutOutput.output,hl,hr,rightOrders,intervalWord_succ,intervalWord_zero,hx,reduce,run,step,pop]
lemma rightOutput_flexible_positive (P : Parameters) :
    0<Stationary.seqLaw (rightLaw P) {x | rightOutput x 0=none} := by
  let A : Set (ℤ → List Letter) := {x | rightCutAt x 0}
  let B : Set (ℤ → List Letter) := {x | x 0=[Letter.order none]}
  have hB : MeasurableSet[Stationary.coords (α := List Letter) {j | 0 ≤ j}] B := by
    have hm : Measurable[Stationary.coords (α := List Letter) {j | 0 ≤ j}] (fun x : ℤ → List Letter => x 0) := by
      apply measurable_iff_comap_le.mpr
      exact le_iSup_of_le 0 (le_iSup_of_le (show (0:ℤ) ≤ 0 by omega) le_rfl)
    exact hm (measurableSet_singleton _)
  have hi := Stationary.indep_coords (rightLaw P) (S := {j | j<0}) (R := {j | 0 ≤ j})
    (Set.disjoint_left.mpr (fun j hj hj' => by change j<0 at hj; change 0 ≤ j at hj'; omega))
  have he := (indep_iff_forall_indepSet _).mp hi A B rightCutAt_zero_past_measurable hB |>.measure_inter_eq_mul
  have hBp : 0<Stationary.seqLaw (rightLaw P) B := by
    have hh := (measurePreserving_eval_infinitePi (fun _ : ℤ => rightLaw P) 0).measure_preimage
      (measurableSet_singleton [Letter.order none]).nullMeasurableSet
    change Stationary.seqLaw (rightLaw P) B=rightLaw P {[Letter.order none]} at hh
    rw [hh]
    exact rightLaw_order_positive P none
  have hpos : 0<Stationary.seqLaw (rightLaw P) (A∩B) := by rw [he]; exact ENNReal.mul_pos_iff.mpr ⟨rightCutAt_positive P,hBp⟩
  exact hpos.trans_le (measure_mono (fun x hx => rightOutput_of_cut_order hx.1 hx.2))

def outputIndicator (o : Order) (x : ℤ → List Letter) : ℝ := if rightOutput x 0=o then 1 else 0
lemma outputIndicator_measurable (o : Order) : Measurable (outputIndicator o) := by
  apply Measurable.ite (measurableSet_eq_fun (rightOutput_measurable 0) measurable_const) measurable_const measurable_const
lemma outputIndicator_integrable (P : Parameters) (o : Order) : Integrable (outputIndicator o) (Stationary.seqLaw (rightLaw P)) := by
  apply (integrable_const (1:ℝ)).mono' (outputIndicator_measurable o).aestronglyMeasurable
  filter_upwards [] with x
  simp only [outputIndicator]
  split_ifs <;> norm_num

def outputMass (P : Parameters) (o : Order) : ℝ := ∫ x,outputIndicator o x ∂Stationary.seqLaw (rightLaw P)
lemma outputMass_eq_measure (P : Parameters) (o : Order) :
    outputMass P o=(Stationary.seqLaw (rightLaw P) {x | rightOutput x 0=o}).toReal := by
  simpa only [outputMass,outputIndicator,Set.indicator,Pi.one_apply,Measure.real,Set.mem_ofPred_eq] using
    integral_indicator_one (μ := Stationary.seqLaw (rightLaw P)) (s := {x | rightOutput x 0=o})
      (measurableSet_eq_fun (rightOutput_measurable 0) measurable_const)
lemma outputMass_flexible_pos (P : Parameters) : 0<outputMass P none := by
  rw [outputMass_eq_measure]
  exact ENNReal.toReal_pos (ne_of_gt (rightOutput_flexible_positive P)) (measure_ne_top _ _)
lemma outputMass_fixed_eq (P : Parameters) : outputMass P (some false)=outputMass P (some true) := by
  have hh := (flipPieceSeq_preserving P).hasLaw.integral_comp (outputIndicator_measurable (some false)).aestronglyMeasurable
  have hf (x : ℤ → List Letter) : outputIndicator (some false) (flipPieceSeq x)=outputIndicator (some true) x := by
    simp only [outputIndicator,rightOutput_flip]
    cases h : rightOutput x 0 with
    | none => simp
    | some b => cases b <;> simp
  simpa only [Function.comp_apply,hf,outputMass] using hh.symm
lemma outputMass_sum (P : Parameters) : outputMass P none+outputMass P (some false)+outputMass P (some true)=1 := by
  have hp (x : ℤ → List Letter) : outputIndicator none x+outputIndicator (some false) x+outputIndicator (some true) x=1 := by
    simp only [outputIndicator]
    cases h : rightOutput x 0 with
    | none =>
      have h₀ : (none : Order) ≠ some false := by intro h; cases h
      have h₁ : (none : Order) ≠ some true := by intro h; cases h
      simp only [h₀,h₁,ite_true,ite_false,add_zero]
    | some b => cases b <;> simp only [Option.some_ne_none,Option.some.injEq,Bool.false_eq_true,Bool.true_eq_false,ite_false,ite_true,zero_add,add_zero]
  have hi := integral_congr_ae (μ := Stationary.seqLaw (rightLaw P)) (Filter.Eventually.of_forall hp)
  have ha := integral_add ((outputIndicator_integrable P none).add (outputIndicator_integrable P (some false)))
    (outputIndicator_integrable P (some true))
  simp only [Pi.add_apply] at ha
  rw [ha,integral_add (outputIndicator_integrable P none) (outputIndicator_integrable P (some false))] at hi
  simpa [outputMass] using hi
lemma outputMass_fixed (P : Parameters) (b : Bool) : outputMass P (some b)=(1-outputMass P none)/2 := by
  have h₁ := outputMass_fixed_eq P
  have h₂ := outputMass_sum P
  cases b <;> linarith

theorem rightOutput_frequencies (P : Parameters) (o : Order) :
    ∀ᵐ x ∂Stationary.seqLaw (rightLaw P),
      Tendsto (fun n => (∑ j∈Finset.range n,if rightOutput x (j:ℤ)=o then (1:ℝ) else 0)/(n:ℝ)) atTop (𝓝 (outputMass P o)) := by
  have hh := Stationary.iid_shift_strong_law (rightLaw P) (outputIndicator_measurable o) (outputIndicator_integrable P o)
  filter_upwards [hh] with x hx
  simpa only [Stationary.average,Stationary.shift_iterate,outputIndicator,rightOutput_shift,zero_add,outputMass] using hx

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.CutOutput
open Classical

/-- Number of marked boundaries before n. -/
def count (C : ℕ → Prop) (n : ℕ) : ℕ := by
  classical
  exact ∑ i∈Finset.range n,if C i then 1 else 0
def last (C : ℕ → Prop) (n : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest C n
lemma last_le (C : ℕ → Prop) (n : ℕ) : last C n ≤ n := Nat.findGreatest_le _
lemma last_spec {C : ℕ → Prop} (hC : C 0) (n : ℕ) : C (last C n) := Nat.findGreatest_spec (Nat.zero_le n) hC
lemma count_le (C : ℕ → Prop) (n : ℕ) : count C n ≤ n := by
  classical
  calc
    _ ≤ ∑ _ ∈ Finset.range n,1 := Finset.sum_le_sum (fun j _ => by split_ifs <;> omega)
    _ = n := by simp
lemma count_at_last (C : ℕ → Prop) (n : ℕ) : count C (last C n+1)=count C (n+1) := by
  classical
  apply Finset.sum_subset (Finset.range_mono (by have := last_le C n; omega))
  intro j hj hj'
  have hjle : j ≤ n := by have := Finset.mem_range.mp hj; omega
  have hjgt : last C n<j := by have := Finset.mem_range.not.mp hj'; omega
  have hn : ¬C j := Nat.findGreatest_is_greatest hjgt hjle
  simp [hn]
lemma countReal (C : ℕ → Prop) (n : ℕ) :
    (count C n:ℝ)=∑ i∈Finset.range n,if C i then (1:ℝ) else 0 := by
  classical
  simp only [count,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> norm_num

/-- Positive density is enough; no independence between cuts is used. -/
lemma last_tendsto (C : ℕ → Prop) {δ : ℝ} (hδ : 0<δ)
    (hd : Tendsto (fun n => (count C n:ℝ)/(n:ℝ)) atTop (𝓝 δ)) :
    Tendsto (fun n => last C n+1) atTop atTop := by
  have hshift : Tendsto (fun n : ℕ => n+1) atTop atTop := tendsto_add_atTop_nat 1
  have hc : Tendsto (fun n => (count C (n+1):ℝ)) atTop atTop := by
    have hm := (hd.comp hshift).pos_mul_atTop hδ (tendsto_natCast_atTop_atTop.comp hshift)
    convert hm using 1
    funext n
    exact (div_mul_cancel₀ _ (by positivity : ((n+1:ℕ):ℝ)≠0)).symm
  rw [← tendsto_natCast_atTop_iff (R := ℝ)]
  apply tendsto_atTop_mono (fun n => ?_) hc
  rw [← count_at_last C n]
  exact_mod_cast count_le C (last C n+1)

lemma last_ratio (C : ℕ → Prop) {δ : ℝ} (hδ : 0<δ)
    (hd : Tendsto (fun n => (count C n:ℝ)/(n:ℝ)) atTop (𝓝 δ)) :
    Tendsto (fun n => ((last C n+1:ℕ):ℝ)/((n+1:ℕ):ℝ)) atTop (𝓝 1) := by
  have hshift : Tendsto (fun n : ℕ => n+1) atTop atTop := tendsto_add_atTop_nat 1
  have ha := hd.comp hshift
  have hb := hd.comp (last_tendsto C hδ hd)
  have hdiv := ha.div hb (ne_of_gt hδ)
  rw [div_self (ne_of_gt hδ)] at hdiv
  apply hdiv.congr'
  have hp := (tendsto_order.mp ha).1 0 hδ
  filter_upwards [hp] with n hn
  dsimp only [Function.comp_def,Pi.div_apply] at hn ⊢
  have hc : (count C (n+1):ℝ)≠0 := by intro hz; rw [hz,zero_div] at hn; exact lt_irrefl _ hn
  rw [count_at_last]
  field_simp

lemma last_gap_ratio (C : ℕ → Prop) {δ : ℝ} (hδ : 0<δ)
    (hd : Tendsto (fun n => (count C n:ℝ)/(n:ℝ)) atTop (𝓝 δ)) :
    Tendsto (fun n => ((n-last C n:ℕ):ℝ)/((n+1:ℕ):ℝ)) atTop (𝓝 0) := by
  have hh := (tendsto_const_nhds (x := (1:ℝ)) (f := (atTop : Filter ℕ))).sub (last_ratio C hδ hd)
  rw [sub_self (1:ℝ)] at hh
  convert hh using 1
  funext n
  rw [Nat.cast_sub (last_le C n)]
  push_cast
  field_simp
  ring

lemma last_gap_div (C : ℕ → Prop) {δ : ℝ} (hδ : 0<δ)
    (hd : Tendsto (fun n => (count C n:ℝ)/(n:ℝ)) atTop (𝓝 δ)) :
    Tendsto (fun n => ((n-last C n:ℕ):ℝ)/(n:ℝ)) atTop (𝓝 0) := by
  have hh := (last_gap_ratio C hδ hd).div (tendsto_natCast_div_add_atTop (1:ℝ)) (by norm_num : (1:ℝ)≠0)
  simp only [zero_div] at hh
  apply hh.congr'
  filter_upwards [eventually_ne_atTop (0:ℕ)] with n hn
  dsimp only [Pi.div_apply]
  push_cast
  field_simp

lemma last_div (C : ℕ → Prop) {δ : ℝ} (hδ : 0<δ)
    (hd : Tendsto (fun n => (count C n:ℝ)/(n:ℝ)) atTop (𝓝 δ)) :
    Tendsto (fun n => (last C n:ℝ)/(n:ℝ)) atTop (𝓝 1) := by
  have hh := (tendsto_const_nhds (x := (1:ℝ)) (f := (atTop : Filter ℕ))).sub (last_gap_div C hδ hd)
  simp only [sub_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ne_atTop (0:ℕ)] with n hn
  rw [Nat.cast_sub (last_le C n)]
  have hne : (n:ℝ)≠0 := Nat.cast_ne_zero.mpr hn
  field_simp
  ring

end FKCRT.CutOutput
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT
namespace Stationary
variable {α : Type*}
lemma shift_neg_iterate (n : ℕ) (x : ℤ → α) : (shift (-1))^[n] x=shift (-(n:ℤ)) x := by
  induction n with
  | zero => ext k; simp [shift]
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih]
    ext k
    simp only [shift,Nat.cast_add,Nat.cast_one]
    congr 1
    omega
end Stationary
namespace Inventory
open Classical
lemma rightOutput_reverse_frequencies (P : Parameters) (o : Order) :
    ∀ᵐ x ∂Stationary.seqLaw (rightLaw P),
      Tendsto (fun n => (∑ j∈Finset.range n,if rightOutput x (-1-j)=o then (1:ℝ) else 0)/(n:ℝ)) atTop (𝓝 (outputMass P o)) := by
  have hh := Stationary.iid_reverse_shift_strong_law (rightLaw P) (outputIndicator_measurable o) (outputIndicator_integrable P o)
  have ht := (Stationary.shift_preserving (rightLaw P) (-1)).quasiMeasurePreserving.ae hh
  filter_upwards [ht] with x hx
  have he (j : ℕ) : rightOutput (Stationary.shift (-(j:ℤ)) (Stationary.shift (-1) x)) 0=rightOutput x (-1-j) := by
    rw [rightOutput_shift,rightOutput_shift]
    congr 1
    omega
  simpa only [Stationary.average,Stationary.shift_neg_iterate,outputIndicator,he,outputMass] using hx

def rightCutDensity (P : Parameters) : ℝ := (Stationary.seqLaw (rightLaw P) {x | rightCutAt x 0}).toReal
lemma rightCutDensity_pos (P : Parameters) : 0<rightCutDensity P :=
  ENNReal.toReal_pos (ne_of_gt (rightCutAt_positive P)) (measure_ne_top _ _)
lemma rightCut_reverse_density (P : Parameters) :
    ∀ᵐ x ∂Stationary.seqLaw (rightLaw P),
      Tendsto (fun n => (CutOutput.count (fun k => rightCutAt x (-(k:ℤ))) n:ℝ)/(n:ℝ)) atTop (𝓝 (rightCutDensity P)) := by
  let f : (ℤ → List Letter) → ℝ := fun x => if rightCutAt x 0 then 1 else 0
  have hf : Measurable f := Measurable.ite (rightCutAt_measurable 0) measurable_const measurable_const
  have hi : Integrable f (Stationary.seqLaw (rightLaw P)) := by
    apply (integrable_const (1:ℝ)).mono' hf.aestronglyMeasurable
    filter_upwards [] with x
    dsimp [f]
    split_ifs <;> norm_num
  have he : (∫ x,f x ∂Stationary.seqLaw (rightLaw P))=rightCutDensity P := by
    simpa only [f,Set.indicator,Pi.one_apply,Measure.real,Set.mem_ofPred_eq,rightCutDensity] using
      integral_indicator_one (μ := Stationary.seqLaw (rightLaw P)) (s := {x | rightCutAt x 0}) (rightCutAt_measurable 0)
  have hh := Stationary.iid_reverse_shift_strong_law (rightLaw P) hf hi
  filter_upwards [hh] with x hx
  simpa only [CutOutput.countReal,Stationary.average,Stationary.shift_neg_iterate,f,rightCutAt_shift,zero_add,he] using hx
lemma rightCut_last_gap (P : Parameters) :
    ∀ᵐ x ∂Stationary.seqLaw (rightLaw P),
      Tendsto (fun n => ((n-CutOutput.last (fun k => rightCutAt x (-(k:ℤ))) n:ℕ):ℝ)/((n+1:ℕ):ℝ)) atTop (𝓝 0) := by
  filter_upwards [rightCut_reverse_density P] with x hx
  exact CutOutput.last_gap_ratio _ (rightCutDensity_pos P) hx
end Inventory
end FKCRT
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory
open Classical
variable {α : Type*}
lemma bottom_append {u v : List α} {k : ℕ} (hk : v.length ≤ k) :
    bottom (u++v) k=bottom u (k-v.length)++v := by
  unfold bottom
  rw [List.length_append,List.drop_append_of_le_length (by omega)]
  congr 2
  omega
lemma bottom_append_bounds [BEq α] [LawfulBEq α] (a : α) {u v : List α} {k : ℕ}
    (h₁ : v.length ≤ k) (h₂ : k ≤ u.length+v.length) :
    v.count a ≤ (bottom (u++v) k).count a ∧
      (bottom (u++v) k).count a ≤ v.count a+(k-v.length) := by
  rw [bottom_append h₁,List.count_append]
  have hh : (bottom u (k-v.length)).length=k-v.length := by
    rw [bottom,List.length_drop]
    omega
  have hc := List.count_le_length (a := a) (l := bottom u (k-v.length))
  rw [hh] at hc
  omega
lemma count_real_sum [BEq α] [LawfulBEq α] (a : α) (l : List α) :
    (l.count a:ℝ)=(l.map (fun b => if b=a then (1:ℝ) else 0)).sum := by
  classical
  induction l with
  | nil => simp
  | cons b l ih =>
    by_cases h : b=a
    · subst b; simp [ih,add_comm]
    · simp [h,ih]
lemma count_ofFn_real [BEq α] [LawfulBEq α] (a : α) {n : ℕ} (f : Fin n → α) :
    ((List.ofFn f).count a:ℝ)=∑ j : Fin n,if f j=a then (1:ℝ) else 0 := by
  rw [count_real_sum,List.map_ofFn,List.sum_ofFn]
  rfl
end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory
open Classical

def typeBalance (b : Bool) (e : Evaluation) : ℤ := (e.burgers.count b:ℤ)-(e.orders.count (some b):ℤ)
lemma typeBalance_step (b : Bool) (e : Evaluation) {a : Letter} (ha : a≠Letter.order none) :
    typeBalance b (step e a)=typeBalance b e+Letter.typeNet b a := by
  cases a with
  | burger c =>
    by_cases h : c=b
    · subst c; simp only [typeBalance,step,List.count_cons_self,Nat.cast_add,Nat.cast_one,Letter.typeNet,ite_true]; ring
    · simp only [typeBalance,step,List.count_cons_of_ne h,Letter.typeNet,ite_eq_right h,add_zero]
  | order o =>
    cases o with
    | none => exact (ha rfl).elim
    | some c =>
      cases hp : pop (some c) e.burgers with
      | none =>
        by_cases h : c=b
        · subst c
          simp only [typeBalance,step,hp,List.count_append,List.count_singleton,Nat.cast_add,beq_self_eq_true,ite_true,Nat.cast_one,Letter.typeNet,ite_true]
          ring
        · have he : (some c:Order)≠some b := by simpa using h
          simp only [typeBalance,step,hp,List.count_append,List.count_singleton,beq_eq_false_iff_ne.mpr he,Bool.false_eq_true,ite_false,Letter.typeNet,ite_eq_right h,add_zero]
      | some s =>
        have hc := pop_fixed_count (a := b) hp
        by_cases h : b=c
        · subst c
          simp only [ite_true] at hc
          simp only [typeBalance,step,hp,Letter.typeNet,ite_true]
          omega
        · simp only [ite_eq_right h,Nat.add_zero] at hc
          simp only [typeBalance,step,hp,Letter.typeNet,ite_eq_right (Ne.symm h),add_zero,hc]
lemma typeBalance_run (b : Bool) (e : Evaluation) (w : List Letter) (hw : FixedWord w) :
    typeBalance b (run w e)=typeBalance b e+typeNet b w := by
  induction w generalizing e with
  | nil => simp [run,typeNet]
  | cons a w ih =>
    have ha : a≠Letter.order none := by intro h; exact hw (by simp [h])
    have ht : FixedWord w := fun h => hw (List.mem_cons_of_mem a h)
    rw [run,ih _ ht,typeBalance_step b e ha]
    change _=(typeBalance b e)+(Letter.typeNet b a+typeNet b w)
    ring
lemma burger_count_eq_typeNet {w : List Letter} (hw : FixedWord w) (ho : (reduce w).orders=[]) (b : Bool) :
    ((reduce w).burgers.count b:ℤ)=typeNet b w := by
  have hh := typeBalance_run b ⟨[],[]⟩ w hw
  change typeBalance b (reduce w)=typeBalance b ⟨[],[]⟩+typeNet b w at hh
  simpa only [typeBalance,ho,List.count_nil,Nat.cast_zero,sub_zero,sub_self,zero_add] using hh
lemma intervalWord_fixed {x : ℤ → List Letter} (hx : ∀ j,FixedWord (x j)) (a : ℤ) (n : ℕ) : FixedWord (intervalWord x a n) := by
  induction n with
  | zero => simp [intervalWord_zero,FixedWord]
  | succ n ih =>
    rw [intervalWord_succ]
    exact fun h => (List.mem_append.mp h).elim ih (hx _)
lemma typeNet_intervalWord (x : ℤ → List Letter) (b : Bool) (a : ℤ) (n : ℕ) :
    typeNet b (intervalWord x a n)=∑ j∈Finset.range n,typeNet b (x (a+j)) := by
  induction n with
  | zero => simp [intervalWord_zero,typeNet]
  | succ n ih =>
    rw [intervalWord_succ,Finset.sum_range_succ]
    simpa only [typeNet,List.map_append,List.sum_append] using congrArg (·+typeNet b (x (a+n))) ih

lemma shortLeftLaw_net (P : Parameters) : ∀ᵐ w ∂shortLeftLaw P,(w.map Letter.increment).sum=1 := by
  rw [shortLeftLaw,ae_map_iff measurable_shortLeftWord.aemeasurable ((Set.to_countable _).measurableSet)]
  filter_upwards [ae_left_first_hit P] with x hx
  rw [shortLeftWord_sign,hx.1]
lemma leftSeq_net (P : Parameters) : ∀ᵐ x ∂Stationary.seqLaw (shortLeftLaw P),∀ j,((x j).map Letter.increment).sum=1 := by
  apply ae_all_iff.mpr
  intro j
  exact (measurePreserving_eval_infinitePi (fun _ : ℤ => shortLeftLaw P) j).quasiMeasurePreserving.ae (shortLeftLaw_net P)
lemma leftSeq_fixed (P : Parameters) : ∀ᵐ x ∂Stationary.seqLaw (shortLeftLaw P),∀ j,FixedWord (x j) := by
  apply ae_all_iff.mpr
  intro j
  exact (measurePreserving_eval_infinitePi (fun _ : ℤ => shortLeftLaw P) j).quasiMeasurePreserving.ae (shortLeftLaw_fixed P)

def futurePieces (x : ℤ → List Letter) : ℕ → List Letter := fun j => x j
lemma futurePieces_preserving (ν : Measure (List Letter)) [IsProbabilityMeasure ν] :
    MeasurePreserving futurePieces (Stationary.seqLaw ν) (naturalPiecesLaw ν) := by
  refine ⟨Measurable.of_eval (fun j => measurable_pi_apply (j:ℤ)),?_⟩
  exact Measure.map_infinitePi_infinitePi_of_inj (fun a b h => Int.ofNat_inj.mp h)
lemma futurePieces_prefix (x : ℤ → List Letter) (n : ℕ) : piecesPrefix (futurePieces x) n=intervalWord x 0 n := by
  simp only [intervalWord,zero_add]
  rfl
lemma leftCutAt_zero_iff (x : ℤ → List Letter) : leftCutAt x 0 ↔ LeftCut (futurePieces x) := by
  simp only [leftCutAt,LeftCut,futurePieces_prefix]
lemma leftCutAt_positive (P : Parameters) : 0<Stationary.seqLaw (shortLeftLaw P) {x | leftCutAt x 0} := by
  have hh := (futurePieces_preserving (shortLeftLaw P)).measure_preimage measurableSet_leftCut.nullMeasurableSet
  have he : {x | leftCutAt x 0}=futurePieces ⁻¹' {x | LeftCut x} := Set.ext (fun x => leftCutAt_zero_iff x)
  rw [he,hh]
  exact shortLeft_positive_cut P
end FKCRT.Inventory
end

end OAI
