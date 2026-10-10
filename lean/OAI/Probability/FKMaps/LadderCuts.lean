import OAI.Probability.FKMaps.PieceWalks

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

lemma firstDown_add {h k n m : ℕ} (hh : 0<h) (hk : 0<k) {x : ℕ → Letter}
    (hx : firstDown h x=WithTop.some n) (hy : firstDown k (tail (n+1) x)=WithTop.some m) :
    firstDown (h+k) x=WithTop.some (n+m+1) := by
  apply (firstDown_of_hit_iff _ _ _).mpr
  constructor
  · rw [show n+m+1+1=(n+1)+(m+1) by omega,signSum_add,
      ((firstDown_of_hit_iff _ _ _).mp hx).1,((firstDown_of_hit_iff _ _ _).mp hy).1]
    push_cast; ring
  · intro j hj
    by_cases hjn : j<n+1
    · by_cases hjn' : j<n
      · have hp := firstDown_prefix_pos hh hx (j := j+1) (by omega)
        push_cast; omega
      · have he : j=n := by omega
        subst j
        rw [((firstDown_of_hit_iff _ _ _).mp hx).1]
        push_cast; omega
    · have hp := firstDown_prefix_pos hk hy (j := j+1-(n+1)) (by omega)
      have he : j+1=(n+1)+(j+1-(n+1)) := by omega
      rw [he,signSum_add,((firstDown_of_hit_iff _ _ _).mp hx).1]
      norm_num only [Nat.cast_add]
      omega
lemma stoppedWord_down_add {h k n m : ℕ} (hh : 0<h) (hk : 0<k) {x : ℕ → Letter}
    (hx : firstDown h x=WithTop.some n) (hy : firstDown k (tail (n+1) x)=WithTop.some m) :
    stoppedWord (firstDown (h+k)) x=stoppedWord (firstDown k) (stoppedTail (firstDown h) x)++stoppedWord (firstDown h) x := by
  rw [stoppedWord_of_hit (firstDown_add hh hk hx hy),stoppedTail_of_hit hx,stoppedWord_of_hit hx,stoppedWord_of_hit hy,
    show n+m+1+1=(n+1)+(m+1) by omega,revealed_add]

def rightPieces (x : ℕ → Letter) : ℕ → List Letter := fun j => wordPieces (firstDown 1) j x
lemma rightPieces_measurable : Measurable rightPieces := by
  apply Measurable.of_eval
  intro j
  exact reverseRightWord_measurable.comp ((measurable_stoppedTail (firstDown_measurable 1)).iterate j)
lemma rightPieces_preserving (P : Parameters) :
    MeasurePreserving rightPieces (streamLaw P ℕ) (naturalPiecesLaw (reverseRightLaw P)) := by
  refine ⟨rightPieces_measurable,?_⟩
  change (streamLaw P ℕ).map (fun x j => (reverseRightWord ∘ (stoppedTail (firstDown 1))^[j]) x)=_
  rw [(stoppedWordPieces_iid P (firstDown_measurable 1) (firstDown_stopping 1) (firstDown_finite P 1 (by omega))).map_fun_eq_infinitePi_map
    (fun j => reverseRightWord_measurable.comp ((measurable_stoppedTail (firstDown_measurable 1)).iterate j))]
  unfold naturalPiecesLaw
  congr 1
  funext j
  have hm := (stoppedTail_preserving P (firstDown_measurable 1) (firstDown_stopping 1) (firstDown_finite P 1 (by omega))).iterate j
  change (streamLaw P ℕ).map (reverseRightWord ∘ (stoppedTail (firstDown 1))^[j])=reverseRightLaw P
  rw [← Measure.map_map reverseRightWord_measurable hm.measurable,hm.map_eq]
  rfl

def reversePiecesPrefix (x : ℕ → List Letter) (n : ℕ) : List Letter :=
  ((List.ofFn (fun i : Fin n => x i)).reverse).flatten
lemma reversePiecesPrefix_succ (x : ℕ → List Letter) (n : ℕ) :
    reversePiecesPrefix x (n+1)=reversePiecesPrefix (piecesTail 1 x) n++x 0 := by
  unfold reversePiecesPrefix
  rw [List.ofFn_succ,List.reverse_cons,List.flatten_append]
  simp only [List.flatten_cons,List.flatten_nil,List.append_nil]
  simp [piecesTail,Nat.add_comm]
lemma rightPieces_tail (x : ℕ → Letter) :
    piecesTail 1 (rightPieces x)=rightPieces (stoppedTail (firstDown 1) x) := by
  funext j
  simp only [piecesTail,rightPieces,wordPieces]
  rw [Nat.add_comm 1 j,Function.iterate_succ_apply]

lemma stoppedWord_down_pieces (P : Parameters) (h : ℕ) : ∀ᵐ x ∂streamLaw P ℕ,
    stoppedWord (firstDown (h+1)) x=reversePiecesPrefix (rightPieces x) (h+1) := by
  induction h with
  | zero =>
    filter_upwards [] with x
    simp [reversePiecesPrefix,rightPieces,wordPieces]
  | succ h ih =>
    have hm := stoppedTail_preserving P (firstDown_measurable 1) (firstDown_stopping 1) (firstDown_finite P 1 (by omega))
    filter_upwards [firstDown_finite P 1 (by omega),hm.quasiMeasurePreserving.tendsto_ae ih,
      hm.quasiMeasurePreserving.tendsto_ae (firstDown_finite P (h+1) (by omega))] with x hx hi hy
    obtain ⟨n,hn⟩ := WithTop.ne_top_iff_exists.mp hx
    obtain ⟨m,hmm⟩ := WithTop.ne_top_iff_exists.mp hy
    have hn' := hn.symm
    have hm' : firstDown (h+1) (tail (n+1) x)=WithTop.some m := by simpa only [stoppedTail_of_hit hn'] using hmm.symm
    conv_rhs => rw [reversePiecesPrefix_succ,rightPieces_tail]
    rw [show h+1+1=1+(h+1) by omega,stoppedWord_down_add (by omega) (by omega) hn' hm',hi]
    rfl

def reverseFirstPieces (n : ℕ) (x : ℕ → List Letter) : ℕ → List Letter :=
  fun j => x (TreeCoding.reverseIndex n j)
lemma reverseFirstPieces_preserving (ν : Measure (List Letter)) [IsProbabilityMeasure ν] (n : ℕ) :
    MeasurePreserving (reverseFirstPieces n) (naturalPiecesLaw ν) (naturalPiecesLaw ν) :=
  ⟨Measurable.of_eval (fun _ => measurable_pi_apply _),
    Measure.map_infinitePi_infinitePi_of_inj (TreeCoding.reverseIndex_involutive n).injective⟩
lemma reversePiecesPrefix_eq (x : ℕ → List Letter) (n : ℕ) :
    reversePiecesPrefix x n=piecesPrefix (reverseFirstPieces n x) n := by
  rw [piecesPrefix_ofFn]
  unfold reversePiecesPrefix
  congr 1
  apply List.ext_getElem
  · simp
  · intro j hj hk
    simp only [List.length_reverse,List.length_ofFn] at hj hk
    simp [List.getElem_reverse,reverseFirstPieces,TreeCoding.reverseIndex]

lemma rightPrefix_identDistrib (P : Parameters) (h : ℕ) :
    IdentDistrib (stoppedWord (firstDown (h+1))) (fun x => piecesPrefix x (h+1))
      (streamLaw P ℕ) (naturalPiecesLaw (reverseRightLaw P)) := by
  have hp := (reverseFirstPieces_preserving (reverseRightLaw P) (h+1)).comp (rightPieces_preserving P)
  have hm : Measurable (fun x : ℕ → List Letter => piecesPrefix x (h+1)) := by
    rw [show (fun x : ℕ → List Letter => piecesPrefix x (h+1))=
      (fun f : Fin (h+1) → List Letter => (List.ofFn f).flatten) ∘ (fun x i => x i) by
        funext x; exact piecesPrefix_ofFn x (h+1)]
    exact (measurable_of_countable _).comp (Measurable.of_eval (fun index => measurable_pi_apply (index:ℕ)))
  have hi := (hp.hasLaw.identDistrib ((MeasurePreserving.id _).hasLaw)).comp hm
  apply (IdentDistrib.of_ae_eq (measurable_stoppedWord (firstDown_measurable (h+1))).aemeasurable ?_).trans hi
  filter_upwards [stoppedWord_down_pieces P h] with x hx
  simpa only [Function.comp_apply,reversePiecesPrefix_eq] using hx

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

lemma piecesPrefix_measurable (n : ℕ) : Measurable (fun x : ℕ → List Letter => piecesPrefix x n) := by
  have he : (fun x : ℕ → List Letter => piecesPrefix x n)=
      (fun f : Fin n → List Letter => (List.ofFn f).flatten) ∘ (fun x i => x i) := by
    funext x; exact piecesPrefix_ofFn x n
  rw [he]
  exact (measurable_of_countable _).comp (Measurable.of_eval (fun index => measurable_pi_apply (index:ℕ)))

def NonemptyPieces (x : ℕ → List Letter) : Prop := ∀ j,(x j)≠[]
lemma reverseRightLaw_nonempty (P : Parameters) : ∀ᵐ w ∂reverseRightLaw P,w≠[] := by
  apply (ae_map_iff reverseRightWord_measurable.aemeasurable (measurableSet_singleton ([]:List Letter)).compl).mpr
  filter_upwards [reverseRightWord_net P] with x hx hnil
  change reverseRightWord x=[] at hnil
  simp [hnil] at hx
lemma rightPieces_nonempty (P : Parameters) : ∀ᵐ x ∂naturalPiecesLaw (reverseRightLaw P),NonemptyPieces x := by
  rw [show (fun x => NonemptyPieces x)=(fun x => ∀ j,x j≠[]) by rfl,ae_all_iff]
  intro j
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ => reverseRightLaw P) j).quasiMeasurePreserving.tendsto_ae
    (reverseRightLaw_nonempty P)
lemma piecesPrefix_length {x : ℕ → List Letter} (hx : NonemptyPieces x) (n : ℕ) :
    n ≤ (piecesPrefix x n).length := by
  induction n with
  | zero => omega
  | succ n ih =>
    have hp : 0<(x n).length := List.length_pos_iff.mpr (hx n)
    simp only [piecesPrefix,List.length_append]
    omega
lemma piecesPrefix_extension (x : ℕ → List Letter) {m n : ℕ} (hmn : m ≤ n) :
    ∃ w,piecesPrefix x n=piecesPrefix x m++w := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact ⟨_,piecesPrefix_add x m k⟩

def pieceScan (x : ℕ → List Letter) : ℕ → Letter := fun j =>
  ((piecesPrefix x (j+1))[j]?).getD (.order none)
lemma pieceScan_measurable : Measurable pieceScan := by
  apply Measurable.of_eval
  intro j
  exact (measurable_of_countable (fun w : List Letter => (w[j]?).getD (.order none))).comp (piecesPrefix_measurable (j+1))
lemma pieceScan_get {x : ℕ → List Letter} (hx : NonemptyPieces x) {m j : ℕ} (hj : j < m) :
    pieceScan x j=(piecesPrefix x m)[j]'(lt_of_lt_of_le hj (piecesPrefix_length hx m)) := by
  have hp : j<(piecesPrefix x (j+1)).length := lt_of_lt_of_le (by omega) (piecesPrefix_length hx (j+1))
  obtain ⟨w,hw⟩ := piecesPrefix_extension x (show j+1 ≤ m by omega)
  simp only [pieceScan,List.getElem?_eq_getElem hp,Option.getD_some]
  simp only [hw,List.getElem_append_left hp]
lemma rawWord_pieceScan {x : ℕ → List Letter} (hx : NonemptyPieces x) {m h : ℕ} (hmh : m ≤ h) :
    rawWord (pieceScan x) m=(piecesPrefix x h).take m := by
  have hl := (hmh.trans (piecesPrefix_length hx h))
  apply List.ext_getElem
  · simp [rawWord,List.length_ofFn, min_eq_left hl]
  · intro j hj hk
    have hj' : j < m := by simpa [rawWord] using hj
    simp only [rawWord,List.getElem_ofFn,rawPrefix,List.getElem_take]
    exact pieceScan_get hx (hj'.trans_le hmh)

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

lemma rawWord_measurable (n : ℕ) : Measurable (fun x : ℕ → Letter => rawWord x n) :=
  (measurable_of_countable _).comp (rawPrefix_measurable n)
lemma wordWeight_reverse (P : Parameters) (w : List Letter) : wordWeight P w.reverse=wordWeight P w := by
  simp [wordWeight,List.map_reverse]
lemma rawWord_reverse (x : ℕ → Letter) (n : ℕ) : (rawWord x n).reverse=revealed x n := rfl
lemma increment_sum_bounds (w : List Letter) :
    -(w.length:ℤ) ≤ (w.map Letter.increment).sum ∧ (w.map Letter.increment).sum ≤ (w.length:ℤ) := by
  induction w with
  | nil => simp
  | cons a w ih =>
    have ha := increment_bounds a
    simp only [List.length_cons,List.map_cons,List.sum_cons,Nat.cast_add,Nat.cast_one]
    omega
lemma rightDensity_signSum_bounds (x : ℕ → Letter) (n : ℕ) : -(n:ℤ) ≤ signSum x n ∧ signSum x n ≤ n := by
  have hh := increment_sum_bounds (revealed x n)
  rw [revealed_sum] at hh
  simpa only [revealed,List.length_reverse,List.length_ofFn] using hh
lemma firstDown_length {h n : ℕ} {x : ℕ → Letter} (hx : firstDown h x=WithTop.some n) : h ≤ n+1 := by
  have hh := ((firstDown_of_hit_iff _ _ _).mp hx).1
  have hb := (rightDensity_signSum_bounds x (n+1)).1
  omega

lemma rawKilled_preimage (a b n : ℕ) : rawKilled a b n=rawPrefix n ⁻¹'
    {d | SimpleWalk.nonnegativePath a (finiteSigns d) ∧ (a:ℤ)+SimpleWalk.pathSum (finiteSigns d) n=b} := by
  ext x
  simp only [rawKilled,Set.mem_ofPred_eq,Set.mem_preimage,SimpleWalk.nonnegativePath]
  rw [raw_sign_pathSum x n n le_rfl]
  apply and_congr_left
  intro _
  apply forall_congr'
  intro j
  apply forall_congr'
  intro hj
  rw [raw_sign_pathSum x n j hj]
lemma rightDensity_rawKilled_measurable (a b n : ℕ) : MeasurableSet (rawKilled a b n) := by
  rw [rawKilled_preimage]
  exact rawPrefix_measurable n (Set.to_countable _).measurableSet
lemma rawPrefix_tail_rectangle (P : Parameters) (n : ℕ) (A : Set (Fin n → Letter))
    (B : Set (ℕ → Letter)) (hB : MeasurableSet B) :
    streamLaw P ℕ (rawPrefix n ⁻¹' A ∩ tail n ⁻¹' B)=streamLaw P ℕ (rawPrefix n ⁻¹' A)*streamLaw P ℕ B := by
  cases n with
  | zero =>
    by_cases ha : (fun i : Fin 0 => Fin.elim0 i)∈A
    · have he : rawPrefix 0 ⁻¹' A=Set.univ := by
        ext x
        simp only [Set.mem_preimage,Set.mem_univ,iff_true]
        convert ha using 1
      rw [he,Set.univ_inter,measure_univ,one_mul]
      congr 1
      ext x
      simp only [Set.mem_preimage,tail_zero]
    · have he : rawPrefix 0 ⁻¹' A=∅ := by
        ext x
        simp only [Set.mem_preimage,Set.mem_empty_iff_false,iff_false]
        have hf : rawPrefix 0 x=(fun i : Fin 0 => Fin.elim0 i) := Subsingleton.elim _ _
        rwa [hf]
      rw [he,Set.empty_inter,measure_empty,zero_mul]
  | succ n =>
    have hi := raw_fun_indep_tail P n (f := rawPrefix (n+1)) (prefix_measurable n id)
    have he := hi.measure_inter_preimage_eq_mul A B (Set.to_countable A).measurableSet hB
    rw [(tail_preserving P (n+1)).measure_preimage hB.nullMeasurableSet] at he
    exact he
lemma rawKilled_block_rectangle (P : Parameters) (a b n : ℕ) (w : List Letter) :
    streamLaw P ℕ (rawKilled a b n ∩ {x | rawWord (tail n x) w.length=w})=
      ENNReal.ofReal (SimpleWalk.killed n a b)*wordWeight P w := by
  rw [rawKilled_preimage]
  change streamLaw P ℕ (rawPrefix n ⁻¹' _ ∩ tail n ⁻¹' {x | rawWord x w.length=w})=_
  rw [rawPrefix_tail_rectangle P n _ {x | rawWord x w.length=w} (by exact (rawWord_measurable _) (measurableSet_singleton w)),rawWord_cylinder]
  rw [← rawKilled_preimage]
  congr 1
  rw [← rawKilled_measure P,measureReal_def,ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- A specified reversed terminal string of a first-downcrossing word leaves
a genuine killed-walk prefix and an independent raw suffix. -/
lemma stoppedWord_suffix_witness {h t : ℕ} {x : ℕ → Letter} {w : List Letter}
    (hwpos : 0<w.length) (hh : w.length<h) (hx : firstDown h x=WithTop.some t)
    (hw : (stoppedWord (firstDown h) x).take w.length=w) :
    ∃ r n : ℕ,0<r ∧ (r:ℤ)= -(w.map Letter.increment).sum ∧
      x∈rawKilled (h-1) (r-1) n ∧ rawWord (tail n x) w.length=w.reverse := by
  have ht := firstDown_length hx
  let n := t+1-w.length
  have hn : n+w.length=t+1 := by dsimp [n]; omega
  have hnlt : n ≤ t := by dsimp [n]; omega
  have hwr : revealed (tail n x) w.length=w := by
    rw [stoppedWord_of_hit hx,← hn,revealed_add,
      List.take_left' (by simp [revealed])] at hw
    exact hw
  have hwS : signSum (tail n x) w.length=(w.map Letter.increment).sum := by
    rw [← revealed_sum,hwr]
  have hsum := ((firstDown_of_hit_iff _ _ _).mp hx).1
  rw [← hn,signSum_add,hwS] at hsum
  have hp := firstDown_prefix_pos (by omega : 0<h) hx hnlt
  have hneg : (w.map Letter.increment).sum<0 := by omega
  let r := (-(w.map Letter.increment).sum).toNat
  have hr : (r:ℤ)= -(w.map Letter.increment).sum := Int.toNat_of_nonneg (by omega)
  have hrpos : 0<r := by omega
  refine ⟨r,n,hrpos,hr,⟨?_,?_⟩,?_⟩
  · intro j hj
    have hjp := firstDown_prefix_pos (by omega : 0<h) hx (hj.trans hnlt)
    have hhcast : ((h-1:ℕ):ℤ)=(h:ℤ)-1 := by omega
    rw [hhcast]
    omega
  · have hhcast : ((h-1:ℕ):ℤ)=(h:ℤ)-1 := by omega
    have hrcast : ((r-1:ℕ):ℤ)=(r:ℤ)-1 := by omega
    rw [hhcast,hrcast]
    omega
  · have he := congrArg List.reverse hwr
    simpa only [← rawWord_reverse,List.reverse_reverse] using he

def terminalDeficit (w : List Letter) : ℕ := (-(w.map Letter.increment).sum).toNat

/-- The only density estimate used is a sum of finite-prefix cylinders.
No integrability of the raw downcrossing length is asserted. -/
theorem stoppedWord_prefix_density_bound (P : Parameters) (h : ℕ) (w : List Letter)
    (hwpos : 0<w.length) (hh : w.length<h) :
    streamLaw P ℕ {x | (stoppedWord (firstDown h) x).take w.length=w} ≤
      2*(terminalDeficit w:ℝ≥0∞)*wordWeight P w := by
  let E : Set (ℕ → Letter) := {x | (stoppedWord (firstDown h) x).take w.length=w}
  let r := terminalDeficit w
  have hfin := firstDown_finite P h (by omega)
  by_cases hr : r=0
  · have he : E=ᵐ[streamLaw P ℕ] (∅ : Set (ℕ → Letter)) := by
      filter_upwards [hfin] with x hx
      change ((stoppedWord (firstDown h) x).take w.length=w)=False
      apply propext
      simp only [iff_false]
      intro hw
      obtain ⟨t,ht⟩ := WithTop.ne_top_iff_exists.mp hx
      obtain ⟨s,n,hs,hseq,_,_⟩ := stoppedWord_suffix_witness hwpos hh ht.symm hw
      have hsr : s=r := by dsimp [r,terminalDeficit]; omega
      omega
    rw [measure_congr he,measure_empty]
    exact bot_le
  · have hrpos : 0<r := Nat.pos_of_ne_zero hr
    let C : ℕ → Set (ℕ → Letter) := fun n => rawKilled (h-1) (r-1) n ∩ {x | rawWord (tail n x) w.length=w.reverse}
    have he : E ≤ᵐ[streamLaw P ℕ] ⋃ n,C n := by
      filter_upwards [hfin] with x hx hw
      obtain ⟨t,ht⟩ := WithTop.ne_top_iff_exists.mp hx
      obtain ⟨s,n,hs,hseq,hk,hw'⟩ := stoppedWord_suffix_witness hwpos hh ht.symm hw
      have hsr : s=r := by dsimp [r,terminalDeficit]; omega
      subst s
      exact Set.mem_iUnion.mpr ⟨n,hk,hw'⟩
    have hc (n : ℕ) : streamLaw P ℕ (C n)=ENNReal.ofReal (SimpleWalk.killed n (h-1) (r-1))*wordWeight P w := by
      simpa only [C,List.length_reverse,wordWeight_reverse] using rawKilled_block_rectangle P (h-1) (r-1) n w.reverse
    calc
      streamLaw P ℕ E ≤ streamLaw P ℕ (⋃ n,C n) := measure_mono_ae he
      _ ≤ ∑' n,streamLaw P ℕ (C n) := measure_iUnion_le _
      _ = (∑' n,ENNReal.ofReal (SimpleWalk.killed n (h-1) (r-1)))*wordWeight P w := by
        simp_rw [hc]
        rw [ENNReal.tsum_mul_right]
      _ ≤ (2*(r:ℝ≥0∞))*wordWeight P w := by
        apply mul_le_mul' ?_ le_rfl
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => SimpleWalk.killed_nonneg n (h-1) (r-1))
          (SimpleWalk.killed_summable (h-1) (r-1))]
        have hb := SimpleWalk.killed_green_bound (h-1) (r-1)
        have he' : r-1+1=r := by omega
        rw [he'] at hb
        simpa only [ENNReal.ofReal_mul (by norm_num : 0 ≤ (2:ℝ)),ENNReal.ofReal_ofNat,ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hb

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

def rightScanLaw (P : Parameters) : Measure (ℕ → Letter) :=
  (naturalPiecesLaw (reverseRightLaw P)).map pieceScan
instance (P : Parameters) : IsProbabilityMeasure (rightScanLaw P) :=
  inferInstanceAs (IsProbabilityMeasure ((naturalPiecesLaw (reverseRightLaw P)).map pieceScan))

lemma rightScan_cylinder_bound (P : Parameters) (w : List Letter) (hw : 0<w.length) :
    rightScanLaw P {x | rawWord x w.length=w} ≤
      2*(terminalDeficit w:ℝ≥0∞)*wordWeight P w := by
  rw [rightScanLaw,Measure.map_apply pieceScan_measurable (measurableSet_eq_fun (rawWord_measurable _) measurable_const)]
  have he : pieceScan ⁻¹' {x | rawWord x w.length=w}=ᵐ[naturalPiecesLaw (reverseRightLaw P)]
      {x | (piecesPrefix x (w.length+1)).take w.length=w} := by
    filter_upwards [rightPieces_nonempty P] with x hx
    change (rawWord (pieceScan x) w.length=w)=((piecesPrefix x (w.length+1)).take w.length=w)
    rw [rawWord_pieceScan hx (Nat.le_succ _)]
  rw [measure_congr he]
  have hi := (rightPrefix_identDistrib P w.length).comp
    (measurable_of_countable (fun v : List Letter => v.take w.length))
  have hh := hi.measure_mem_eq (measurableSet_singleton w)
  change streamLaw P ℕ {x | (stoppedWord (firstDown (w.length+1)) x).take w.length=w}=
    naturalPiecesLaw (reverseRightLaw P) {x | (piecesPrefix x (w.length+1)).take w.length=w} at hh
  rw [← hh]
  exact stoppedWord_prefix_density_bound P (w.length+1) w hw (Nat.lt_succ_self _)

lemma rightScan_first_order (P : Parameters) : ∀ᵐ x ∂rightScanLaw P,∃ o,x 0=Letter.order o := by
  have hz (b : Bool) : rightScanLaw P {x | x 0=Letter.burger b}=0 := by
    have hh := rightScan_cylinder_bound P [Letter.burger b] (by simp)
    have he : {x : ℕ → Letter | rawWord x [Letter.burger b].length=[Letter.burger b]}={x | x 0=Letter.burger b} := by
      ext x; simp [rawWord,rawPrefix,List.ofFn_succ]
    rw [he] at hh
    simpa [terminalDeficit,Letter.increment] using hh
  have htrue : ∀ᵐ x ∂rightScanLaw P,x 0≠Letter.burger true := by exact ae_iff.mpr (by simpa only [not_not] using hz true)
  have hfalse : ∀ᵐ x ∂rightScanLaw P,x 0≠Letter.burger false := by exact ae_iff.mpr (by simpa only [not_not] using hz false)
  filter_upwards [htrue,hfalse] with x ht hf
  cases h : x 0 with
  | burger b => cases b <;> contradiction
  | order o => exact ⟨o,rfl⟩

def rightRemainderLaw (P : Parameters) : Measure (ℕ → Letter) := (rightScanLaw P).map (tail 1)
instance (P : Parameters) : IsProbabilityMeasure (rightRemainderLaw P) :=
  inferInstanceAs (IsProbabilityMeasure ((rightScanLaw P).map (tail 1)))

lemma rawWord_succ_head (x : ℕ → Letter) (n : ℕ) :
    rawWord x (n+1)=x 0::rawWord (tail 1 x) n := by
  simp only [rawWord,rawPrefix,List.ofFn_succ]
  congr 2
  funext i
  dsimp [rawPrefix,tail]
  congr 1
  omega
lemma wordWeight_cons (P : Parameters) (a : Letter) (w : List Letter) :
    wordWeight P (a::w)=(law P).toMeasure {a}*wordWeight P w := by simp [wordWeight]
lemma terminalDeficit_order (o : Option Bool) (w : List Letter) :
    terminalDeficit (Letter.order o::w)=(1-(w.map Letter.increment).sum).toNat := by
  simp only [terminalDeficit,List.map_cons,List.sum_cons,Letter.increment]
  congr 1; omega
lemma order_mass_sum (P : Parameters) : ∑ o : Option Bool,(law P).toMeasure {Letter.order o}=(2:ℝ≥0∞)⁻¹ := by
  simp only [law_singleton,Fintype.sum_option,Fintype.sum_bool,mass]
  rw [← ENNReal.ofReal_add (by linarith [P.upper]) (by linarith [P.upper]),
    ← ENNReal.ofReal_add (by linarith [P.pos]) (by linarith [P.upper])]
  norm_num [show P.p/2+((1-P.p)/4+(1-P.p)/4)=(1:ℝ)/2 by ring,ENNReal.ofReal_div_of_pos]

theorem rightRemainder_cylinder_bound (P : Parameters) (w : List Letter) :
    rightRemainderLaw P {x | rawWord x w.length=w} ≤
      ((1-(w.map Letter.increment).sum).toNat:ℝ≥0∞)*wordWeight P w := by
  rw [rightRemainderLaw,Measure.map_apply (measurable_tail 1) (measurableSet_eq_fun (rawWord_measurable _) measurable_const)]
  have he : tail 1 ⁻¹' {x | rawWord x w.length=w}=ᵐ[rightScanLaw P]
      ⋃ o : Option Bool,{x | rawWord x (w.length+1)=Letter.order o::w} := by
    filter_upwards [rightScan_first_order P] with x hx
    obtain ⟨o,ho⟩ := hx
    change (rawWord (tail 1 x) w.length=w)=(x∈⋃ o : Option Bool,{x | rawWord x (w.length+1)=Letter.order o::w})
    apply propext
    rw [Set.mem_iUnion]
    change _ ↔ ∃ o : Option Bool,rawWord x (w.length+1)=Letter.order o::w
    simp only [rawWord_succ_head,ho,List.cons.injEq]
    exact ⟨fun h => ⟨o,rfl,h⟩,fun ⟨_,_,h⟩ => h⟩
  rw [measure_congr he]
  calc
    rightScanLaw P (⋃ o : Option Bool,{x | rawWord x (w.length+1)=Letter.order o::w})
      ≤ ∑ o : Option Bool,rightScanLaw P {x | rawWord x (w.length+1)=Letter.order o::w} := by
        simpa only [tsum_fintype] using measure_iUnion_le (fun o : Option Bool => {x | rawWord x (w.length+1)=Letter.order o::w})
    _ ≤ ∑ o : Option Bool,2*((1-(w.map Letter.increment).sum).toNat:ℝ≥0∞)*((law P).toMeasure {Letter.order o}*wordWeight P w) := by
      apply Finset.sum_le_sum
      intro o _
      simpa only [List.length_cons,terminalDeficit_order,wordWeight_cons] using
        rightScan_cylinder_bound P (Letter.order o::w) (by simp)
    _ = ((1-(w.map Letter.increment).sum).toNat:ℝ≥0∞)*wordWeight P w := by
      rw [← Finset.mul_sum,← Finset.sum_mul,order_mass_sum]
      calc
        _ = ((2:ℝ≥0∞)*2⁻¹)*(((1-(w.map Letter.increment).sum).toNat:ℝ≥0∞)*wordWeight P w) := by ring
        _ = _ := by rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num),one_mul]

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

lemma rawFiltration_eq_comap (n : ℕ) : rawFiltration n=(inferInstance : MeasurableSpace (Fin (n+1) → Letter)).comap (rawPrefix (n+1)) := by
  apply le_antisymm
  · change (⨆ k ≤ n,MeasurableSpace.comap (fun x : ℕ → Letter => x k) inferInstance) ≤ _
    apply iSup_le
    intro k
    apply iSup_le
    intro hk
    have hm : Measurable[(inferInstance : MeasurableSpace (Fin (n+1) → Letter)).comap (rawPrefix (n+1))]
        (fun x : ℕ → Letter => x k) := by
      exact (measurable_pi_apply (⟨k,by omega⟩ : Fin (n+1))).comp (comap_measurable (rawPrefix (n+1)))
    exact hm.comap_le
  · exact (prefix_measurable n id).comap_le

lemma rawPrefix_atom (n : ℕ) (d : Fin n → Letter) :
    {x : ℕ → Letter | rawWord x n=List.ofFn d}=rawPrefix n ⁻¹' {d} := by
  ext x
  simp only [rawWord,Set.mem_ofPred_eq,Set.mem_preimage,Set.mem_singleton_iff,List.ofFn_inj]
lemma rightRemainder_prefix_bound (P : Parameters) (n : ℕ) (d : Fin n → Letter) :
    rightRemainderLaw P (rawPrefix n ⁻¹' {d}) ≤
      ((1-(∑ i,(d i).increment:ℤ)).toNat:ℝ≥0∞)*streamLaw P ℕ (rawPrefix n ⁻¹' {d}) := by
  have hh := rightRemainder_cylinder_bound P (List.ofFn d)
  rw [List.length_ofFn,rawPrefix_atom] at hh
  rw [← rawWord_cylinder P (List.ofFn d),List.length_ofFn,rawPrefix_atom] at hh
  simpa only [List.map_ofFn,List.sum_ofFn,Function.comp_apply] using hh

lemma rightRemainder_prefix_event (P : Parameters) (n : ℕ) (A : Set (Fin n → Letter)) :
    rightRemainderLaw P (rawPrefix n ⁻¹' A) ≤
      ∫⁻ x in rawPrefix n ⁻¹' A,((1-signSum x n).toNat:ℝ≥0∞) ∂streamLaw P ℕ := by
  classical
  let D : (Fin n → Letter) → ℝ≥0∞ := fun d => ((1-(∑ i,(d i).increment:ℤ)).toNat:ℝ≥0∞)
  have hn : MeasurableSet A := (Set.to_countable _).measurableSet
  have he : rawPrefix n ⁻¹' A=⋃ d : Fin n → Letter,if d∈A then rawPrefix n ⁻¹' {d} else ∅ := by
    ext x
    simp only [Set.mem_preimage,Set.mem_iUnion]
    constructor
    · intro hx; exact ⟨rawPrefix n x,by simp [hx]⟩
    · rintro ⟨d,hd⟩
      split_ifs at hd with h
      · have hd' : rawPrefix n x=d := hd; rwa [hd']
      · exact hd.elim
  calc
    rightRemainderLaw P (rawPrefix n ⁻¹' A) ≤
        ∑ d : Fin n → Letter,if d∈A then rightRemainderLaw P (rawPrefix n ⁻¹' {d}) else 0 := by
      rw [he]
      simpa only [tsum_fintype,apply_ite,measure_empty] using
        measure_iUnion_le (fun d : Fin n → Letter => if d∈A then rawPrefix n ⁻¹' {d} else ∅) (μ := rightRemainderLaw P)
    _ ≤ ∑ d : Fin n → Letter,(A.indicator D d)*streamLaw P ℕ (rawPrefix n ⁻¹' {d}) := by
      apply Finset.sum_le_sum
      intro d _
      by_cases hd : d∈A
      · simpa only [hd,ite_eq_left,Set.indicator_of_mem] using rightRemainder_prefix_bound P n d
      · simp only [ite_eq_right hd]; exact bot_le
    _ = ∫⁻ d,A.indicator D d ∂(streamLaw P ℕ).map (rawPrefix n) := by
      rw [lintegral_fintype]
      apply Finset.sum_congr rfl
      intro d _
      rw [Measure.map_apply (rawPrefix_measurable n) (measurableSet_singleton d)]
    _ = ∫⁻ x in rawPrefix n ⁻¹' A,((1-signSum x n).toNat:ℝ≥0∞) ∂streamLaw P ℕ := by
      rw [lintegral_map (measurable_of_countable _) (rawPrefix_measurable n),← lintegral_indicator ((rawPrefix_measurable n) hn)]
      apply lintegral_congr
      intro x
      by_cases hx : rawPrefix n x∈A
      · simp only [Set.indicator_of_mem hx,Set.indicator_of_mem (show x∈rawPrefix n ⁻¹' A from hx),D,rawPrefix]
        rw [Fin.sum_univ_eq_sum_range (fun i => (x i).increment) n]
        rfl
      · simp only [Set.indicator_of_notMem hx,Set.indicator_of_notMem (show x∉rawPrefix n ⁻¹' A from hx)]

lemma K_signSum_of_hit {x : ℕ → Letter} {n : ℕ} (hx : firstSurvivor x=WithTop.some n) :
    (1-signSum x (n+1)).toNat=K x := by
  obtain ⟨b,hb,_⟩ := firstSurvivor_shape hx
  have hh := reduce_imbalance (revealed x (n+1))
  rw [hb,imbalance,revealed_sum] at hh
  simp only [List.length_singleton,Nat.cast_one] at hh
  rw [K_of_hit hx,hb]
  change (1-signSum x (n+1)).toNat=(reduce (revealed x n)).orders.length
  change 1-((reduce (revealed x n)).orders.length:ℤ)=signSum x (n+1) at hh
  omega

theorem rightRemainder_hit_bound (P : Parameters) (n : ℕ) :
    rightRemainderLaw P {x | firstSurvivor x=WithTop.some n} ≤
      ∫⁻ x in {x | firstSurvivor x=WithTop.some n},(K x:ℝ≥0∞) ∂streamLaw P ℕ := by
  have he := firstSurvivor_stopping.measurableSet_eq n
  rw [rawFiltration_eq_comap,MeasurableSpace.measurableSet_comap] at he
  obtain ⟨A,_,hA⟩ := he
  have hb := rightRemainder_prefix_event P (n+1) A
  rw [hA] at hb
  refine hb.trans_eq ?_
  apply setLIntegral_congr_fun (rawFiltration.le n _ (firstSurvivor_stopping.measurableSet_eq n))
  intro x hx
  exact congrArg (fun k : ℕ => (k:ℝ≥0∞)) (K_signSum_of_hit hx)

theorem rightRemainder_survivor_bound (P : Parameters) :
    rightRemainderLaw P {x | firstSurvivor x≠⊤} ≤ ∫⁻ x,(K x:ℝ≥0∞) ∂streamLaw P ℕ := by
  have he : {x : ℕ → Letter | firstSurvivor x≠⊤}=⋃ n : ℕ,{x | firstSurvivor x=WithTop.some n} := by
    ext x; simp only [Set.mem_ofPred_eq,Set.mem_iUnion]
    exact WithTop.ne_top_iff_exists.trans (by simp only [eq_comm])
  have hm (n : ℕ) : MeasurableSet {x : ℕ → Letter | firstSurvivor x=WithTop.some n} :=
    rawFiltration.le n _ (firstSurvivor_stopping.measurableSet_eq n)
  calc
    rightRemainderLaw P {x | firstSurvivor x≠⊤} ≤ ∑' n : ℕ,rightRemainderLaw P {x | firstSurvivor x=WithTop.some n} := by rw [he]; exact measure_iUnion_le _
    _ ≤ ∑' n : ℕ,∫⁻ x in {x | firstSurvivor x=WithTop.some n},(K x:ℝ≥0∞) ∂streamLaw P ℕ := ENNReal.tsum_le_tsum (rightRemainder_hit_bound P)
    _ = ∫⁻ x in {x | firstSurvivor x≠⊤},(K x:ℝ≥0∞) ∂streamLaw P ℕ := by
      rw [he,lintegral_iUnion hm]
      intro i j hij
      exact Set.disjoint_left.mpr (fun x hi hj => hij (WithTop.coe_injective (hi.symm.trans hj)))
    _ ≤ ∫⁻ x,(K x:ℝ≥0∞) ∂streamLaw P ℕ := setLIntegral_le_lintegral _ _

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

def RightCut (x : ℕ → List Letter) : Prop := ∀ n,(reduce (piecesPrefix x n).reverse).burgers=[]
lemma measurableSet_rightCut : MeasurableSet {x | RightCut x} := by
  simp only [RightCut,Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro n
  exact (piecesPrefix_measurable n) (Set.to_countable {w : List Letter | (reduce w.reverse).burgers=[]}).measurableSet

lemma rawWord_pieceScan_prefix {x : ℕ → List Letter} (hx : NonemptyPieces x) (n : ℕ) :
    rawWord (pieceScan x) (piecesPrefix x n).length=piecesPrefix x n := by
  let m := (piecesPrefix x n).length
  rw [rawWord_pieceScan hx (show m ≤ n+m by omega)]
  obtain ⟨w,hw⟩ := piecesPrefix_extension x (show n ≤ n+m by omega)
  rw [hw]
  exact List.take_left' rfl

lemma noSurvivor_burgers {x : ℕ → Letter} (hx : firstSurvivor x=⊤) (n : ℕ) :
    (reduce (revealed x n)).burgers=[] := by
  cases n with
  | zero => simp [revealed_zero,reduce,run]
  | succ n =>
    by_contra h
    have hh := (firstSurvivor_le_iff x n).mpr h
    rw [hx] at hh
    exact WithTop.not_top_le_coe n hh
lemma append_order_no_burgers {w : List Letter} (hw : (reduce w).burgers=[]) (o : Option Bool) :
    (reduce (w++[Letter.order o])).burgers=[] := by
  change (run (w++[Letter.order o]) ⟨[],[]⟩).burgers=[]
  rw [run_append]
  change (step (reduce w) (Letter.order o)).burgers=[]
  simp only [step,hw,pop]
lemma remainder_noSurvivor_implies_cut {x : ℕ → List Letter} (hx : NonemptyPieces x)
    (ho : ∃ o,pieceScan x 0=Letter.order o) (hs : firstSurvivor (tail 1 (pieceScan x))=⊤) : RightCut x := by
  intro n
  rw [← rawWord_pieceScan_prefix hx n,rawWord_reverse]
  let m := (piecesPrefix x n).length
  change (reduce (revealed (pieceScan x) m)).burgers=[]
  cases m with
  | zero => simp [revealed_zero,reduce,run]
  | succ m =>
    obtain ⟨o,ho⟩ := ho
    rw [show m+1=1+m by omega,revealed_add]
    have he : revealed (pieceScan x) 1=[Letter.order o] := by simp [revealed,List.ofFn_succ,ho]
    rw [he]
    exact append_order_no_burgers (noSurvivor_burgers hs m) o

lemma K_lintegral_lt_one (P : Parameters) : (∫⁻ x,(K x:ℝ≥0∞) ∂streamLaw P ℕ)<1 := by
  have he := ofReal_integral_eq_lintegral_ofReal (integrable_K P)
    (Filter.Eventually.of_forall (fun x => Nat.cast_nonneg (K x)))
  simp only [ENNReal.ofReal_natCast] at he
  rw [← he]
  exact_mod_cast (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0:ℝ)<1)).mpr (integral_K_lt_one P)

lemma rightRemainder_noSurvivor_pos (P : Parameters) :
    0<rightRemainderLaw P {x | firstSurvivor x=⊤} := by
  have hlt := lt_of_le_of_lt (rightRemainder_survivor_bound P) (K_lintegral_lt_one P)
  have hm : MeasurableSet {x | firstSurvivor x=⊤} := measurableSet_eq_fun measurable_firstSurvivor measurable_const
  have he : {x | firstSurvivor x≠⊤}={x : ℕ → Letter | firstSurvivor x=⊤}ᶜ := rfl
  rw [he,measure_compl hm (measure_ne_top _ _),measure_univ] at hlt
  by_contra! hh
  have hz := le_antisymm hh bot_le
  rw [hz,tsub_zero] at hlt
  exact lt_irrefl _ hlt

theorem positive_rightCut (P : Parameters) :
    0<naturalPiecesLaw (reverseRightLaw P) {x | RightCut x} := by
  have hm : MeasurableSet {x | firstSurvivor x=⊤} := measurableSet_eq_fun measurable_firstSurvivor measurable_const
  have hpos := rightRemainder_noSurvivor_pos P
  rw [rightRemainderLaw,Measure.map_apply (measurable_tail 1) hm,
    rightScanLaw,Measure.map_apply pieceScan_measurable ((measurable_tail 1) hm)] at hpos
  refine hpos.trans_le (measure_mono_ae ?_)
  have ho : ∀ᵐ x ∂naturalPiecesLaw (reverseRightLaw P),∃ o,pieceScan x 0=Letter.order o := by
    exact (ae_map_iff pieceScan_measurable.aemeasurable (by
      simp only [Set.ofPred_exists]
      exact MeasurableSet.iUnion (fun o => measurableSet_eq_fun (measurable_pi_apply 0) measurable_const))).mp (rightScan_first_order P)
  filter_upwards [rightPieces_nonempty P,ho] with x hx ho hs
  exact remainder_noSurvivor_implies_cut hx ho hs

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

lemma orders_step_sublist (a : Letter) (e : Evaluation) : e.orders.Sublist (step e a).orders := by
  cases a with
  | burger b => exact List.Sublist.refl _
  | order o => cases h : pop o e.burgers <;> simp [step,h]
lemma orders_run_sublist (w : List Letter) (e : Evaluation) : e.orders.Sublist (run w e).orders := by
  induction w generalizing e with
  | nil => exact List.Sublist.refl _
  | cons a w ih => exact (orders_step_sublist a e).trans (ih _)

def LeftCut (x : ℕ → List Letter) : Prop := ∀ n,(reduce (piecesPrefix x n)).orders=[]
lemma measurable_piecesPrefix (n : ℕ) : Measurable (fun x : ℕ → List Letter => piecesPrefix x n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (measurable_of_countable (fun z : List Letter × List Letter => z.1++z.2)).comp (ih.prodMk (measurable_pi_apply n))
lemma measurableSet_leftCut : MeasurableSet {x | LeftCut x} := by
  simp only [LeftCut,Set.ofPred_forall]
  exact MeasurableSet.iInter (fun n => (measurable_piecesPrefix n)
    ((Set.to_countable {w : List Letter | (reduce w).orders=[]}).measurableSet))

def supplyPieces (K : ℕ) : List (List Letter) :=
  List.replicate K [Letter.burger false]++List.replicate K [Letter.burger true]
def startingSupply (K : ℕ) : List Bool := List.replicate K true++List.replicate K false
lemma supplyPieces_flatten (K : ℕ) : (supplyPieces K).flatten=(startingSupply K).reverse.map Letter.burger := by
  have hh (b : Bool) : (List.replicate K [Letter.burger b]).flatten=List.replicate K (Letter.burger b) := by
    induction K with
    | zero => rfl
    | succ K ih => simp [List.replicate_succ,ih]
  simp [supplyPieces,startingSupply,hh]
lemma run_supplyPieces (K : ℕ) : run (supplyPieces K).flatten ⟨[],[]⟩=⟨[],startingSupply K⟩ := by
  rw [supplyPieces_flatten,run_burgers]
  simp
lemma startingSupply_count (K : ℕ) (b : Bool) : (startingSupply K).count b=K := by
  cases b <;> simp [startingSupply,List.count_replicate]
lemma supplyPieces_mem {K : ℕ} {w : List Letter} (h : w∈supplyPieces K) :
    w=[Letter.burger false] ∨ w=[Letter.burger true] := by
  rcases List.mem_append.mp h with h | h
  · exact Or.inl (List.mem_replicate.mp h).2
  · exact Or.inr (List.mem_replicate.mp h).2

lemma leftCut_of_buffer_prefix {x : ℕ → List Letter} {K : ℕ}
    (hc : x∈pieceCylinder (supplyPieces K))
    (hf : ∀ n,FixedWord (piecesTail (supplyPieces K).length x n))
    (hb : PieceBuffer K (piecesTail (supplyPieces K).length x)) : LeftCut x := by
  have he : reduce (piecesPrefix x (supplyPieces K).length)=⟨[],startingSupply K⟩ := by
    rw [piecesPrefix_of_cylinder hc]
    exact run_supplyPieces K
  intro n
  by_cases hn : (supplyPieces K).length ≤ n
  · obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [piecesPrefix_add,reduce,run_append]
    change (run (piecesPrefix (piecesTail (supplyPieces K).length x) r)
      (reduce (piecesPrefix x (supplyPieces K).length))).orders=[]
    rw [he]
    exact (run_pieces_buffer hf hb (fun b => (startingSupply_count K b).ge) r).1
  · have hle : n ≤ (supplyPieces K).length := by omega
    obtain ⟨r,hr⟩ := Nat.exists_eq_add_of_le hle
    have hh := orders_run_sublist (piecesPrefix (piecesTail n x) r) (reduce (piecesPrefix x n))
    have he' := he
    rw [hr,piecesPrefix_add,reduce,run_append] at he'
    change run (piecesPrefix (piecesTail n x) r) (reduce (piecesPrefix x n))=⟨[],startingSupply K⟩ at he'
    rw [he'] at hh
    exact List.sublist_nil.mp hh

lemma iid_all_fixed (ν : Measure (List Letter)) [IsProbabilityMeasure ν]
    (hf : ∀ᵐ w ∂ν,FixedWord w) : ∀ᵐ x ∂naturalPiecesLaw ν,∀ n,FixedWord (x n) := by
  apply ae_all_iff.mpr
  intro n
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ => ν) n).quasiMeasurePreserving.ae hf

/-- Positive L-cut probability using only shortened-piece integrability,
positive type-drift and the two genuine one-burger atoms. -/
theorem positive_leftCut_general (ν : Measure (List Letter)) [IsProbabilityMeasure ν]
    (hlen : Integrable (fun w : List Letter => (w.length:ℝ)) ν)
    (hnet : ∀ b,Integrable (fun w => (typeNet b w:ℝ)) ν)
    (hmean : ∀ b,(∫ w,(typeNet b w:ℝ) ∂ν)=1/2)
    (hf : ∀ᵐ w ∂ν,FixedWord w)
    (hburger : ∀ b,0<ν {[Letter.burger b]}) :
    0<naturalPiecesLaw ν {x | LeftCut x} := by
  obtain ⟨K,hK⟩ := positive_piece_buffer_probability ν hlen hnet hmean
  let B : Set (ℕ → List Letter) := {x | PieceBuffer K x ∧ ∀ n,FixedWord (x n)}
  have hFm : MeasurableSet {x : ℕ → List Letter | ∀ n,FixedWord (x n)} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun n => (show Measurable (fun x : ℕ → List Letter => x n) from measurable_pi_apply n)
      ((Set.to_countable {w : List Letter | FixedWord w}).measurableSet))
  have hBm : MeasurableSet B := (measurableSet_pieceBuffer K).inter hFm
  have hBp : 0<naturalPiecesLaw ν B := by
    have he : B =ᵐ[naturalPiecesLaw ν] {x | PieceBuffer K x} := by
      filter_upwards [iid_all_fixed ν hf] with x hx
      exact propext (and_iff_left hx)
    rwa [measure_congr he]
  have hC : 0<naturalPiecesLaw ν (pieceCylinder (supplyPieces K)) := by
    apply pieceCylinder_positive ν
    intro w hw
    rcases supplyPieces_mem hw with rfl | rfl
    · exact hburger false
    · exact hburger true
  have hpos : 0<naturalPiecesLaw ν (pieceCylinder (supplyPieces K) ∩ piecesTail (supplyPieces K).length ⁻¹' B) := by
    rw [pieceCylinder_tail_rectangle ν _ hBm]
    exact ENNReal.mul_pos hC.ne' hBp.ne'
  apply hpos.trans_le
  apply measure_mono
  rintro x ⟨hc,hb⟩
  exact leftCut_of_buffer_prefix hc hb.2 hb.1

/-- Source ladder:cuts, L side, for the actual shortened first +1 pieces. -/
theorem shortLeft_positive_cut (P : Parameters) :
    0<naturalPiecesLaw (shortLeftLaw P) {x | LeftCut x} :=
  positive_leftCut_general (shortLeftLaw P) (shortLeftLaw_length_integrable P)
    (shortLeftLaw_typeNet_integrable P) (shortLeftLaw_typeNet_mean P) (shortLeftLaw_fixed P)
    (shortLeftLaw_burger_positive P)

end FKCRT.Inventory
end

end OAI
