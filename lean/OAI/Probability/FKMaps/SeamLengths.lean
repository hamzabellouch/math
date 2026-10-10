import OAI.Probability.FKMaps.UniformSeams

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory
def upPath (h : ℕ) (n : ℕ) (x : ℕ → Letter) : ℤ := (h:ℤ)-signSum x (n+1)
def firstUp (h : ℕ) : (ℕ → Letter) → WithTop ℕ := TreeCoding.firstZero (upPath h)
lemma upPath_adapted (h : ℕ) : StronglyAdapted rawFiltration (upPath h) := by
  intro n
  convert (prefix_measurable n (fun y => (h:ℤ)-(((List.ofFn y).reverse).map Letter.increment).sum)).stronglyMeasurable using 1
  ext x
  exact congrArg (fun z : ℤ => (h:ℤ)-z) (revealed_sum x (n+1)).symm
lemma firstUp_stopping (h : ℕ) : IsStoppingTime rawFiltration (firstUp h) :=
  TreeCoding.firstZero_isStoppingTime (upPath_adapted h)
lemma firstUp_measurable (h : ℕ) : Measurable (firstUp h) := stopping_measurable (firstUp_stopping h)
lemma upPath_step (h n : ℕ) (x : ℕ → Letter) : upPath h n x-1 ≤ upPath h (n+1) x := by
  unfold upPath
  rw [signSum_succ x (n+1)]
  have := (increment_bounds (x (n+1))).2.1
  omega
lemma upPath_initial (h : ℕ) (hh : 0<h) (x : ℕ → Letter) : 0 ≤ upPath h 0 x := by
  have := (increment_bounds (x 0)).2.1
  simp only [upPath,signSum,Nat.zero_add,Finset.sum_range_one]
  omega
lemma upPath_martingale (P : Parameters) (h : ℕ) :
    Martingale (fun n x => (upPath h n x:ℝ)) rawFiltration (streamLaw P ℕ) := by
  convert (martingale_const rawFiltration (streamLaw P ℕ) (h:ℝ )).sub (raw_sign_martingale P) using 1
  ext n x
  simp [upPath]
lemma firstUp_finite (P : Parameters) (h : ℕ) (hh : 0<h) : ∀ᵐ x ∂streamLaw P ℕ,firstUp h x≠⊤ := by
  have hj : ∀ᵐ x ∂streamLaw P ℕ,∃ᶠ n in atTop,upPath h (n+1) x≠upPath h n x := by
    filter_upwards [] with x
    apply Filter.Eventually.frequently
    filter_upwards [] with n
    unfold upPath
    rw [signSum_succ x (n+1)]
    have := (increment_bounds (x (n+1))).2.2
    omega
  filter_upwards [TreeCoding.integer_martingale_hits_zero (upPath_adapted h) (upPath_martingale P h)
    (upPath_initial h hh) (upPath_step h) hj] with x hx
  classical
  simp [firstUp,TreeCoding.firstZero,hx]

lemma firstUp_of_hit_iff (h : ℕ) (x : ℕ → Letter) (n : ℕ) :
    firstUp h x=WithTop.some n ↔ signSum x (n+1)= (h:ℤ) ∧ ∀ j<n,signSum x (j+1)≠ (h:ℤ) := by
  rw [firstUp,TreeCoding.firstZero_eq_iff]
  simp only [upPath]
  constructor
  · rintro ⟨hn,hj⟩
    exact ⟨by omega,fun j h => by have := hj j h; omega⟩
  · rintro ⟨hn,hj⟩
    exact ⟨by omega,fun j h => by have := hj j h; omega⟩
lemma firstUp_prefix_lt {h : ℕ} (hh : 0<h) {x : ℕ → Letter} {n : ℕ}
    (hn : firstUp h x=WithTop.some n) {j : ℕ} (hj : j ≤ n) : signSum x j<(h:ℤ) := by
  have hd := (TreeCoding.firstZero_eq_iff (upPath h) x n).mp hn
  cases j with
  | zero => simp only [signSum,Finset.range_zero,Finset.sum_empty]; omega
  | succ j =>
    have hj' : j<n := by omega
    have he := TreeCoding.integer_path_nonneg_before_zero (fun k => upPath h k x)
      (upPath_initial h hh x) (fun k => upPath_step h k x) j (fun k hk => hd.2 k (hk.trans hj'))
    have hnz := hd.2 j hj'
    dsimp [upPath] at he hnz
    omega


lemma stoppedWord_up_eq_leftWord (P : Parameters) : ∀ᵐ x ∂streamLaw P ℕ,
    stoppedWord (firstUp 1) x=leftWord x := by
  filter_upwards [ae_left_first_hit P] with x hx
  let N := parsingOffset (leftSteps x) x
  have hN : 0<N := by
    by_contra hh
    have he : N=0 := by omega
    have hz := hx.1
    change signSum x N=1 at hz
    simp only [he,signSum,Finset.range_zero,Finset.sum_empty] at hz
    omega
  have he : firstUp 1 x=WithTop.some (N-1) := by
    apply (firstUp_of_hit_iff _ _ _).mpr
    refine ⟨by simpa only [Nat.cast_one,Nat.sub_add_cancel hN] using hx.1,?_⟩
    intro j hj
    have hh := hx.2 (j+1) (by omega)
    omega
  rw [stoppedWord_of_hit he,Nat.sub_add_cancel hN]
  rfl

def rawLeftLaw (P : Parameters) : Measure (List Letter) := (streamLaw P ℕ).map (stoppedWord (firstUp 1))
instance rawLeftLaw_probability (P : Parameters) : IsProbabilityMeasure (rawLeftLaw P) :=
  inferInstanceAs (IsProbabilityMeasure ((streamLaw P ℕ).map (stoppedWord (firstUp 1))))
lemma rawLeftLaw_normal (P : Parameters) :
    (rawLeftLaw P).map (fun w => normalWord (reduce w))=
      (shortLeftLaw P).map (fun w => normalWord (reduce w)) := by
  unfold rawLeftLaw shortLeftLaw
  rw [Measure.map_map (measurable_of_countable _) (measurable_stoppedWord (firstUp_measurable 1)),
    Measure.map_map (measurable_of_countable _) measurable_shortLeftWord]
  apply Measure.map_congr
  filter_upwards [stoppedWord_up_eq_leftWord P] with x hx
  simp only [Function.comp_apply,hx]
  exact congrArg normalWord (run_shortLeftWord x ⟨[],[]⟩).symm

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory
lemma firstUp_add {h k n m : ℕ} (hh : 0<h) (hk : 0<k) {x : ℕ → Letter}
    (hx : firstUp h x=WithTop.some n) (hy : firstUp k (tail (n+1) x)=WithTop.some m) :
    firstUp (h+k) x=WithTop.some (n+m+1) := by
  apply (firstUp_of_hit_iff _ _ _).mpr
  constructor
  · rw [show n+m+1+1=(n+1)+(m+1) by omega,signSum_add,
      ((firstUp_of_hit_iff _ _ _).mp hx).1,((firstUp_of_hit_iff _ _ _).mp hy).1]
    push_cast; ring
  · intro j hj
    by_cases hjn : j<n+1
    · by_cases hjn' : j<n
      · have hp := firstUp_prefix_lt hh hx (j := j+1) (by omega)
        push_cast; omega
      · have he : j=n := by omega
        subst j
        rw [((firstUp_of_hit_iff _ _ _).mp hx).1]
        push_cast; omega
    · have hp := firstUp_prefix_lt hk hy (j := j+1-(n+1)) (by omega)
      have he : j+1=(n+1)+(j+1-(n+1)) := by omega
      rw [he,signSum_add,((firstUp_of_hit_iff _ _ _).mp hx).1]
      norm_num only [Nat.cast_add]
      omega
lemma stoppedWord_up_add {h k n m : ℕ} (hh : 0<h) (hk : 0<k) {x : ℕ → Letter}
    (hx : firstUp h x=WithTop.some n) (hy : firstUp k (tail (n+1) x)=WithTop.some m) :
    stoppedWord (firstUp (h+k)) x=stoppedWord (firstUp k) (stoppedTail (firstUp h) x)++stoppedWord (firstUp h) x := by
  rw [stoppedWord_of_hit (firstUp_add hh hk hx hy),stoppedTail_of_hit hx,stoppedWord_of_hit hx,stoppedWord_of_hit hy,
    show n+m+1+1=(n+1)+(m+1) by omega,revealed_add]

def leftPieces (x : ℕ → Letter) : ℕ → List Letter := fun j => wordPieces (firstUp 1) j x
lemma leftPieces_measurable : Measurable leftPieces := by
  apply Measurable.of_eval
  intro j
  exact (measurable_stoppedWord (firstUp_measurable 1)).comp ((measurable_stoppedTail (firstUp_measurable 1)).iterate j)
lemma leftPieces_preserving (P : Parameters) :
    MeasurePreserving leftPieces (streamLaw P ℕ) (naturalPiecesLaw (rawLeftLaw P)) := by
  refine ⟨leftPieces_measurable,?_⟩
  change (streamLaw P ℕ).map (fun x j => (stoppedWord (firstUp 1) ∘ (stoppedTail (firstUp 1))^[j]) x)=_
  rw [(stoppedWordPieces_iid P (firstUp_measurable 1) (firstUp_stopping 1) (firstUp_finite P 1 (by omega))).map_fun_eq_infinitePi_map
    (fun j => (measurable_stoppedWord (firstUp_measurable 1)).comp ((measurable_stoppedTail (firstUp_measurable 1)).iterate j))]
  unfold naturalPiecesLaw
  congr 1
  funext j
  have hm := (stoppedTail_preserving P (firstUp_measurable 1) (firstUp_stopping 1) (firstUp_finite P 1 (by omega))).iterate j
  change (streamLaw P ℕ).map (stoppedWord (firstUp 1) ∘ (stoppedTail (firstUp 1))^[j])=rawLeftLaw P
  rw [← Measure.map_map (measurable_stoppedWord (firstUp_measurable 1)) hm.measurable,hm.map_eq]
  rfl

lemma leftPieces_tail (x : ℕ → Letter) :
    piecesTail 1 (leftPieces x)=leftPieces (stoppedTail (firstUp 1) x) := by
  funext j
  simp only [piecesTail,leftPieces,wordPieces]
  rw [Nat.add_comm 1 j,Function.iterate_succ_apply]

lemma stoppedWord_up_pieces (P : Parameters) (h : ℕ) : ∀ᵐ x ∂streamLaw P ℕ,
    stoppedWord (firstUp (h+1)) x=reversePiecesPrefix (leftPieces x) (h+1) := by
  induction h with
  | zero =>
    filter_upwards [] with x
    simp [reversePiecesPrefix,leftPieces,wordPieces]
  | succ h ih =>
    have hm := stoppedTail_preserving P (firstUp_measurable 1) (firstUp_stopping 1) (firstUp_finite P 1 (by omega))
    filter_upwards [firstUp_finite P 1 (by omega),hm.quasiMeasurePreserving.tendsto_ae ih,
      hm.quasiMeasurePreserving.tendsto_ae (firstUp_finite P (h+1) (by omega))] with x hx hi hy
    obtain ⟨n,hn⟩ := WithTop.ne_top_iff_exists.mp hx
    obtain ⟨m,hmm⟩ := WithTop.ne_top_iff_exists.mp hy
    have hn' := hn.symm
    have hm' : firstUp (h+1) (tail (n+1) x)=WithTop.some m := by simpa only [stoppedTail_of_hit hn'] using hmm.symm
    conv_rhs => rw [reversePiecesPrefix_succ,leftPieces_tail]
    rw [show h+1+1=1+(h+1) by omega,stoppedWord_up_add (by omega) (by omega) hn' hm',hi]
    rfl

lemma leftPrefix_identDistrib (P : Parameters) (h : ℕ) :
    IdentDistrib (stoppedWord (firstUp (h+1))) (fun x => piecesPrefix x (h+1))
      (streamLaw P ℕ) (naturalPiecesLaw (rawLeftLaw P)) := by
  have hp := (reverseFirstPieces_preserving (rawLeftLaw P) (h+1)).comp (leftPieces_preserving P)
  have hm : Measurable (fun x : ℕ → List Letter => piecesPrefix x (h+1)) := by
    rw [show (fun x : ℕ → List Letter => piecesPrefix x (h+1))=
      (fun f : Fin (h+1) → List Letter => (List.ofFn f).flatten) ∘ (fun x i => x i) by
        funext x; exact piecesPrefix_ofFn x (h+1)]
    exact (measurable_of_countable _).comp (Measurable.of_eval (fun index => measurable_pi_apply (index:ℕ)))
  have hi := (hp.hasLaw.identDistrib ((MeasurePreserving.id _).hasLaw)).comp hm
  apply (IdentDistrib.of_ae_eq (measurable_stoppedWord (firstUp_measurable (h+1))).aemeasurable ?_).trans hi
  filter_upwards [stoppedWord_up_pieces P h] with x hx
  simpa only [Function.comp_apply,reversePiecesPrefix_eq] using hx


end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory
open Classical

def mappedPieceLaw (ν : Measure (List Letter)) (f : List Letter → List Letter) : Measure (List Letter) := ν.map f
instance mappedPieceLaw_probability (ν : Measure (List Letter)) [IsProbabilityMeasure ν] (f : List Letter → List Letter) :
    IsProbabilityMeasure (mappedPieceLaw ν f) := inferInstanceAs (IsProbabilityMeasure (ν.map f))
def mapPieces (f : List Letter → List Letter) (x : ℕ → List Letter) : ℕ → List Letter := fun j => f (x j)
lemma mapPieces_preserving (ν : Measure (List Letter)) [IsProbabilityMeasure ν] (f : List Letter → List Letter) :
    MeasurePreserving (mapPieces f) (naturalPiecesLaw ν) (naturalPiecesLaw (mappedPieceLaw ν f)) := by
  refine ⟨Measurable.of_eval (fun index => (measurable_of_countable f).comp (measurable_pi_apply index)),?_⟩
  exact Measure.infinitePi_map_pi (fun _ : ℕ => ν) (fun _ => measurable_of_countable f)
lemma run_normalPieces (x : ℕ → List Letter) (h : ℕ) (e : Evaluation) :
    run (piecesPrefix (mapPieces (fun w => normalWord (reduce w)) x) h) e=run (piecesPrefix x h) e := by
  induction h with
  | zero => rfl
  | succ h ih =>
    simp only [piecesPrefix,run_append,ih,mapPieces,run_normalWord]
lemma pieceSeamEvent_normal_preimage (h : ℕ) :
    (Prod.map (mapPieces (fun w => normalWord (reduce w))) id) ⁻¹' pieceSeamEvent h=pieceSeamEvent h := by
  ext z
  change EmptyReducing (piecesPrefix (mapPieces (fun w => normalWord (reduce w)) z.1) h++piecesPrefix z.2 h) ↔
    EmptyReducing (piecesPrefix z.1 h++piecesPrefix z.2 h)
  change run (piecesPrefix (mapPieces (fun w => normalWord (reduce w)) z.1) h++piecesPrefix z.2 h) ⟨[],[]⟩=⟨[],[]⟩ ↔
    run (piecesPrefix z.1 h++piecesPrefix z.2 h) ⟨[],[]⟩=⟨[],[]⟩
  rw [run_append,run_append,run_normalPieces]
lemma pieceSeam_normal_measure (μ ν R : Measure (List Letter)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [IsProbabilityMeasure R]
    (hμν : μ.map (fun w => normalWord (reduce w))=ν.map (fun w => normalWord (reduce w))) (h : ℕ) :
    ((naturalPiecesLaw μ).prod (naturalPiecesLaw R)) (pieceSeamEvent h)=
      ((naturalPiecesLaw ν).prod (naturalPiecesLaw R)) (pieceSeamEvent h) := by
  have hμ := (mapPieces_preserving μ (fun w => normalWord (reduce w))).prod
    (MeasurePreserving.id (naturalPiecesLaw R))
  have hν := (mapPieces_preserving ν (fun w => normalWord (reduce w))).prod
    (MeasurePreserving.id (naturalPiecesLaw R))
  have heμ := hμ.measure_preimage (pieceSeamEvent_measurable h).nullMeasurableSet
  have heν := hν.measure_preimage (pieceSeamEvent_measurable h).nullMeasurableSet
  have hmapped : mappedPieceLaw μ (fun w => normalWord (reduce w))=mappedPieceLaw ν (fun w => normalWord (reduce w)) := hμν
  simp only [pieceSeamEvent_normal_preimage,hmapped] at heμ
  rw [pieceSeamEvent_normal_preimage] at heν
  exact heμ.trans heν.symm

lemma reverse_reversePiecesPrefix (x : ℕ → List Letter) (n : ℕ) :
    (reversePiecesPrefix x n).reverse=piecesPrefix (mapPieces List.reverse x) n := by
  rw [reversePiecesPrefix,piecesPrefix_ofFn,List.reverse_flatten]
  simp only [List.map_reverse,List.reverse_reverse,List.map_ofFn,mapPieces,Function.comp_def]
lemma chronologicalRight_identDistrib (P : Parameters) (h : ℕ) :
    IdentDistrib (fun x => (stoppedWord (firstDown (h+1)) x).reverse) (fun x => piecesPrefix x (h+1))
      (streamLaw P ℕ) (naturalPiecesLaw (rightLaw P)) := by
  have hp := (mapPieces_preserving (reverseRightLaw P) List.reverse).comp (rightPieces_preserving P)
  have hi := (hp.hasLaw.identDistrib ((MeasurePreserving.id _).hasLaw)).comp (piecesPrefix_measurable (h+1))
  apply (IdentDistrib.of_ae_eq ((measurable_of_countable List.reverse).comp
    (measurable_stoppedWord (firstDown_measurable (h+1)))).aemeasurable ?_).trans hi
  filter_upwards [stoppedWord_down_pieces P h] with x hx
  simp only [hx,reverse_reversePiecesPrefix,Function.comp_apply]

def rawSeamWord (h : ℕ) (z : (ℕ → Letter) × (ℕ → Letter)) : List Letter :=
  stoppedWord (firstUp h) z.1++(stoppedWord (firstDown h) z.2).reverse
lemma rawSeamWord_measurable (h : ℕ) : Measurable (rawSeamWord h) :=
  (measurable_of_countable (fun z : List Letter×List Letter => z.1++z.2)).comp
    (((measurable_stoppedWord (firstUp_measurable h)).comp measurable_fst).prodMk
      (((measurable_of_countable List.reverse).comp (measurable_stoppedWord (firstDown_measurable h))).comp measurable_snd))
lemma rawSeam_measure (P : Parameters) (h : ℕ) :
    ((streamLaw P ℕ).prod (streamLaw P ℕ)) {z | EmptyReducing (rawSeamWord (h+1) z)}=
      ((naturalPiecesLaw (rawLeftLaw P)).prod (naturalPiecesLaw (rightLaw P))) (pieceSeamEvent (h+1)) := by
  let f := stoppedWord (firstUp (h+1))
  let g := fun x => (stoppedWord (firstDown (h+1)) x).reverse
  let l := fun x : ℕ → List Letter => piecesPrefix x (h+1)
  have hf : Measurable f := measurable_stoppedWord (firstUp_measurable (h+1))
  have hg : Measurable g := (measurable_of_countable List.reverse).comp (measurable_stoppedWord (firstDown_measurable (h+1)))
  have hl : Measurable l := piecesPrefix_measurable (h+1)
  have he : (((streamLaw P ℕ).prod (streamLaw P ℕ)).map (Prod.map f g))=
      ((naturalPiecesLaw (rawLeftLaw P)).prod (naturalPiecesLaw (rightLaw P))).map (Prod.map l l) := by
    rw [← Measure.map_prod_map _ _ hf hg,← Measure.map_prod_map _ _ hl hl,
      (leftPrefix_identDistrib P h).map_eq,(chronologicalRight_identDistrib P h).map_eq]
  let E : Set (List Letter×List Letter) := {z | EmptyReducing (z.1++z.2)}
  have hE : MeasurableSet E := (Set.to_countable E).measurableSet
  have hh := congrArg (fun ν : Measure (List Letter×List Letter) => ν E) he
  rw [Measure.map_apply (hf.prodMap hg) hE,Measure.map_apply (hl.prodMap hl) hE] at hh
  exact hh

/-- Source ladder:uniform for the actual two independent raw hit intervals.
No conditioning on success or stopping-length moment is assumed. -/
theorem raw_seam_uniform (P : Parameters) : ∃ δ : ℝ,0<δ ∧ ∀ h : ℕ,0<h →
    ENNReal.ofReal δ≤((streamLaw P ℕ).prod (streamLaw P ℕ)) {z | EmptyReducing (rawSeamWord h z)} := by
  obtain ⟨δ,hδ,hbound⟩ := piece_seam_uniform P
  refine ⟨δ,hδ,?_⟩
  intro h hh
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : h≠0)
  rw [rawSeam_measure,pieceSeam_normal_measure (rawLeftLaw P) (shortLeftLaw P) (rightLaw P) (rawLeftLaw_normal P)]
  exact hbound (k+1)
end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk

lemma sign_not (b : Bool) : sign (!b)= -sign b := by cases b <;> norm_num [sign]
def reflectPath {n : ℕ} (d : Path n) : Path n := fun i => !(d i)
lemma reflectPath_sum {n : ℕ} (d : Path n) (k : ℕ) : pathSum (reflectPath d) k= -pathSum d k := by
  unfold pathSum reflectPath
  simp only [sign_not,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp
lemma not_coin_preserving : MeasurePreserving Bool.not TreeCoding.coinLaw TreeCoding.coinLaw := by
  refine ⟨measurable_of_countable _,?_⟩
  apply Measure.ext_of_singleton
  intro b
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have he : Bool.not ⁻¹' {b}={!b} := by ext a; cases a <;> cases b <;> simp
  rw [he,TreeCoding.coinLaw_singleton,TreeCoding.coinLaw_singleton]
lemma reflectPath_preserving (n : ℕ) : MeasurePreserving (@reflectPath n)
    (Measure.pi (fun _ : Fin n => TreeCoding.coinLaw)) (Measure.pi (fun _ : Fin n => TreeCoding.coinLaw)) := by
  refine ⟨measurable_of_countable _,?_⟩
  change (Measure.pi _).map (fun d i => !(d i))=Measure.pi _
  rw [Measure.pi_map_pi (fun _ => (measurable_of_countable Bool.not).aemeasurable)]
  simp only [not_coin_preserving.map_eq]

end FKCRT.SimpleWalk
namespace FKCRT.Inventory

def rawUpperSurvival (a n : ℕ) : Set (ℕ → Letter) := {x | ∀ j≤n,0≤(a:ℤ)-signSum x j}
lemma rawUpperSurvival_measure (P : Parameters) (a n : ℕ) :
    streamLaw P ℕ (rawUpperSurvival a n)=streamLaw P ℕ (rawSurvival a n) := by
  let f := finiteSigns ∘ rawPrefix n
  let A : Set (SimpleWalk.Path n) := {d | SimpleWalk.nonnegativePath a d}
  have hp := (finiteSigns_preserving P n).comp (rawPrefix_preserving P n)
  have hu : rawUpperSurvival a n=(SimpleWalk.reflectPath ∘ f) ⁻¹' A := by
    ext x
    simp only [rawUpperSurvival,Set.mem_ofPred_eq,Set.mem_preimage,A,SimpleWalk.nonnegativePath,Function.comp_apply]
    apply forall_congr'
    intro j
    apply forall_congr'
    intro hj
    rw [SimpleWalk.reflectPath_sum]
    change 0≤(a:ℤ)-signSum x j ↔ 0≤(a:ℤ)+ -SimpleWalk.pathSum (finiteSigns (rawPrefix n x)) j
    rw [raw_sign_pathSum x n j hj]
    rfl
  have hl : rawSurvival a n=f ⁻¹' A := by
    ext x
    simp only [rawSurvival,Set.mem_ofPred_eq,Set.mem_preimage,A,SimpleWalk.nonnegativePath]
    apply forall_congr'
    intro j
    apply forall_congr'
    intro hj
    change 0≤(a:ℤ)+signSum x j ↔ 0≤(a:ℤ)+SimpleWalk.pathSum (finiteSigns (rawPrefix n x)) j
    rw [raw_sign_pathSum x n j hj]
  rw [hu,hl,((SimpleWalk.reflectPath_preserving n).comp hp).measure_preimage (Set.to_countable A).measurableSet.nullMeasurableSet,
    hp.measure_preimage (Set.to_countable A).measurableSet.nullMeasurableSet]

lemma stoppedWord_length_of_hit {T : (ℕ → Letter) → WithTop ℕ} {x : ℕ → Letter} {n : ℕ}
    (h : T x=WithTop.some n) : (stoppedWord T x).length=n+1 := by
  rw [stoppedWord_of_hit h]
  simp [revealed]
lemma stoppedWord_length_top {T : (ℕ → Letter) → WithTop ℕ} {x : ℕ → Letter}
    (h : T x=⊤) : (stoppedWord T x).length=1 := by simp [stoppedWord,h,revealed]
lemma down_length_tail_subset {h n : ℕ} (hh : 0<h) (hn : 0<n) :
    {x | n<(stoppedWord (firstDown h) x).length} ⊆ rawSurvival (h-1) n := by
  intro x hx
  obtain ht | ⟨k,hk⟩ := eq_or_ne (firstDown h x) ⊤ |>.imp_right (fun he => WithTop.ne_top_iff_exists.mp he)
  · simp only [Set.mem_ofPred_eq,stoppedWord_length_top ht] at hx
    omega
  · have hk' : firstDown h x=WithTop.some k := hk.symm
    rw [Set.mem_ofPred_eq,stoppedWord_length_of_hit hk'] at hx
    intro j hj
    have hp := firstDown_prefix_pos hh hk' (j := j) (by omega)
    have he : (↑(h-1):ℤ)=(h:ℤ)-1 := by omega
    rw [he]
    omega
lemma up_length_tail_subset {h n : ℕ} (hh : 0<h) (hn : 0<n) :
    {x | n<(stoppedWord (firstUp h) x).length} ⊆ rawUpperSurvival (h-1) n := by
  intro x hx
  obtain ht | ⟨k,hk⟩ := eq_or_ne (firstUp h x) ⊤ |>.imp_right (fun he => WithTop.ne_top_iff_exists.mp he)
  · simp only [Set.mem_ofPred_eq,stoppedWord_length_top ht] at hx
    omega
  · have hk' : firstUp h x=WithTop.some k := hk.symm
    rw [Set.mem_ofPred_eq,stoppedWord_length_of_hit hk'] at hx
    intro j hj
    have hp := firstUp_prefix_lt hh hk' (j := j) (by omega)
    have he : (↑(h-1):ℤ)=(h:ℤ)-1 := by omega
    rw [he]
    omega

/-- Both actual first-passage lengths obey the same uniform square-root tail. -/
theorem stopped_lengths_tail : ∃ C : ℝ,0<C ∧ ∀ (P : Parameters) (h n : ℕ),0<h → 0<n →
    (streamLaw P ℕ).real {x | n<(stoppedWord (firstDown h) x).length} ≤ C*h/Real.sqrt n ∧
    (streamLaw P ℕ).real {x | n<(stoppedWord (firstUp h) x).length} ≤ C*h/Real.sqrt n := by
  obtain ⟨C,hC,h⟩ := rawSurvival_bound
  refine ⟨C,hC,?_⟩
  intro P a n ha hn
  have hb := h P (a-1) n hn
  have he : ((a-1:ℕ):ℝ)+1=(a:ℝ) := by exact_mod_cast Nat.sub_add_cancel ha
  rw [he] at hb
  constructor
  · exact (measureReal_mono (down_length_tail_subset ha hn)).trans hb
  · apply le_trans (measureReal_mono (up_length_tail_subset ha hn))
    simpa only [measureReal_def,rawUpperSurvival_measure] using hb

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

lemma rawSeamWord_length (h : ℕ) (z : (ℕ → Letter) × (ℕ → Letter)) :
    (rawSeamWord h z).length=(stoppedWord (firstUp h) z.1).length+(stoppedWord (firstDown h) z.2).length := by
  simp [rawSeamWord]
lemma rawSeam_length_tail {C : ℝ}
    (hC : ∀ (P : Parameters) (h n : ℕ),0<h → 0<n →
      (streamLaw P ℕ).real {x | n<(stoppedWord (firstDown h) x).length} ≤ C*h/Real.sqrt n ∧
      (streamLaw P ℕ).real {x | n<(stoppedWord (firstUp h) x).length} ≤ C*h/Real.sqrt n)
    (P : Parameters) (h n : ℕ) (hh : 0<h) (hn : 0<n) :
    ((streamLaw P ℕ).prod (streamLaw P ℕ)).real {z | 2*n<(rawSeamWord h z).length} ≤ 2*C*h/Real.sqrt n := by
  let U : Set (ℕ → Letter) := {x | n<(stoppedWord (firstUp h) x).length}
  let D : Set (ℕ → Letter) := {x | n<(stoppedWord (firstDown h) x).length}
  have hU : MeasurableSet U := (Set.to_countable {w : List Letter | n<w.length}).measurableSet.preimage
    (measurable_stoppedWord (firstUp_measurable h))
  have hD : MeasurableSet D := (Set.to_countable {w : List Letter | n<w.length}).measurableSet.preimage
    (measurable_stoppedWord (firstDown_measurable h))
  have hs : {z | 2*n<(rawSeamWord h z).length} ⊆ Prod.fst ⁻¹' U ∪ Prod.snd ⁻¹' D := by
    intro z hz
    rw [Set.mem_ofPred_eq,rawSeamWord_length] at hz
    change n<(stoppedWord (firstUp h) z.1).length ∨ n<(stoppedWord (firstDown h) z.2).length
    omega
  apply (measureReal_mono hs).trans
  apply (measureReal_union_le _ _).trans
  have hf := (measurePreserving_fst (μ := streamLaw P ℕ) (ν := streamLaw P ℕ)).measure_preimage hU.nullMeasurableSet
  have hg := (measurePreserving_snd (μ := streamLaw P ℕ) (ν := streamLaw P ℕ)).measure_preimage hD.nullMeasurableSet
  simp only [measureReal_def,hf,hg]
  have hb := hC P h n hh hn
  change _+_≤_
  dsimp only [U,D] at *
  dsimp only [measureReal_def] at hb
  calc
    _ ≤ C*h/Real.sqrt n+C*h/Real.sqrt n := add_le_add hb.2 hb.1
    _ = _ := by ring

/-- Successful genuine seam intervals have a uniform positive probability of
quadratic length; no independence of length and success is used. -/
theorem short_seam_uniform (P : Parameters) : ∃ (δ : ℝ) (A : ℕ),0<δ ∧ 0<A ∧ ∀ h : ℕ,0<h →
    δ ≤ ((streamLaw P ℕ).prod (streamLaw P ℕ)).real
      {z | EmptyReducing (rawSeamWord h z) ∧ (rawSeamWord h z).length≤2*A*h^2} := by
  obtain ⟨δ,hδ,hsuccess⟩ := raw_seam_uniform P
  obtain ⟨C,hC,htail⟩ := stopped_lengths_tail
  obtain ⟨k,hk⟩ := exists_nat_gt (max 1 (4*C/δ))
  have hk1 : 1<(k:ℝ) := lt_of_le_of_lt (le_max_left _ _) hk
  have hk0 : 0<k := by exact_mod_cast (lt_trans zero_lt_one hk1)
  have hkC : 4*C/δ<(k:ℝ) := lt_of_le_of_lt (le_max_right _ _) hk
  have hsmall : 2*C/(k:ℝ)≤δ/2 := by
    have hkd : 4*C<(k:ℝ)*δ := (div_lt_iff₀ hδ).mp hkC
    apply (div_le_iff₀ (by positivity : 0<(k:ℝ))).mpr
    nlinarith
  refine ⟨δ/2, k^2,by positivity,by positivity,?_⟩
  intro h hh
  let μ := (streamLaw P ℕ).prod (streamLaw P ℕ)
  let S : Set ((ℕ → Letter) × (ℕ → Letter)) := {z | EmptyReducing (rawSeamWord h z)}
  let T : Set ((ℕ → Letter) × (ℕ → Letter)) := {z | 2*k^2*h^2<(rawSeamWord h z).length}
  have hs : δ≤μ.real S := by
    have he := ENNReal.toReal_mono (measure_ne_top μ S) (hsuccess h hh)
    change δ≤(μ S).toReal
    simpa only [ENNReal.toReal_ofReal hδ.le] using he
  have ht : μ.real T≤δ/2 := by
    have he : 2*(k*h)^2=2*k^2*h^2 := by ring
    have hb := rawSeam_length_tail htail P h ((k*h)^2) hh (by positivity)
    rw [he] at hb
    have hden : Real.sqrt (((k*h)^2:ℕ):ℝ)=(k:ℝ)*h := by
      push_cast
      rw [Real.sqrt_sq (by positivity)]
    rw [hden] at hb
    have heq : 2*C*(h:ℝ)/((k:ℝ)*h)=2*C/(k:ℝ) := by
      have hhR : (h:ℝ)≠0 := by positivity
      field_simp
    rw [heq] at hb
    exact hb.trans hsmall
  have he : S\T={z | EmptyReducing (rawSeamWord h z) ∧ (rawSeamWord h z).length≤2*k^2*h^2} := by
    ext z
    simp only [Set.mem_sdiff,Set.mem_ofPred_eq,S,T,not_lt]
  have hd := le_measureReal_sdiff (μ := μ) (s₁ := S) (s₂ := T)
  rw [he] at hd
  change δ/2≤μ.real _
  linarith

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

def letterSplit (l r : ℕ) : (Fin (l+r) → Letter) ≃ᵐ ((Fin l → Letter) × (Fin r → Letter)) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin (l+r) => Letter) finSumFinEquiv).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin l ⊕ Fin r => Letter))
lemma letterSplit_preserving (P : Parameters) (l r : ℕ) :
    MeasurePreserving (letterSplit l r) (Measure.pi (fun _ : Fin (l+r) => (law P).toMeasure))
      ((Measure.pi (fun _ : Fin l => (law P).toMeasure)).prod (Measure.pi (fun _ : Fin r => (law P).toMeasure))) :=
  (measurePreserving_sumPiEquivProdPi (fun _ : Fin l ⊕ Fin r => (law P).toMeasure)).comp
    (measurePreserving_piCongrLeft (fun _ : Fin (l+r) => (law P).toMeasure) finSumFinEquiv).symm
lemma letterSplit_word (l r : ℕ) (w : Fin (l+r) → Letter) :
    List.ofFn (letterSplit l r w).1++List.ofFn (letterSplit l r w).2=List.ofFn w := by
  exact List.ofFn_add.symm

def reverseLetters (l : ℕ) : (Fin l → Letter) ≃ᵐ (Fin l → Letter) :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin l => Letter) Fin.revPerm
lemma reverseLetters_apply (l : ℕ) (w : Fin l → Letter) (i : Fin l) : reverseLetters l w i=w i.rev := by
  simpa only [Fin.revPerm_apply,Fin.rev_rev,reverseLetters] using
    MeasurableEquiv.piCongrLeft_apply_apply Fin.revPerm (β := fun _ : Fin l => Letter) w i.rev
lemma reverseLetters_word (l : ℕ) (w : Fin l → Letter) : List.ofFn (reverseLetters l w)=(List.ofFn w).reverse := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_ofFn,List.getElem_reverse]
    rw [reverseLetters_apply]
    congr 1
    apply Fin.ext
    simp only [Fin.rev,Fin.val_mk,List.length_ofFn]
    omega
lemma reverseLetters_preserving (P : Parameters) (l : ℕ) : MeasurePreserving (reverseLetters l)
    (Measure.pi (fun _ : Fin l => (law P).toMeasure)) (Measure.pi (fun _ : Fin l => (law P).toMeasure)) :=
  measurePreserving_piCongrLeft (fun _ : Fin l => (law P).toMeasure) Fin.revPerm

def seamWord (l r : ℕ) (z : (ℕ → Letter) × (ℕ → Letter)) : List Letter := revealed z.1 l++rawWord z.2 r
lemma seamWord_measurable (l r : ℕ) : Measurable (seamWord l r) :=
  (measurable_of_countable (fun z : List Letter×List Letter => z.1++z.2)).comp
    (((measurable_revealed l).comp measurable_fst).prodMk
      (((measurable_of_countable List.ofFn).comp (rawPrefix_measurable r)).comp measurable_snd))
lemma seamWord_length (l r : ℕ) (z : (ℕ → Letter) × (ℕ → Letter)) : (seamWord l r z).length=l+r := by
  simp [seamWord,revealed,rawWord]
lemma seamWord_preserving (P : Parameters) (l r : ℕ) : IdentDistrib (seamWord l r)
    (fun x => rawWord x (l+r)) ((streamLaw P ℕ).prod (streamLaw P ℕ)) (streamLaw P ℕ) := by
  let f := (letterSplit l r).symm ∘ Prod.map (reverseLetters l) id ∘ Prod.map (rawPrefix l) (rawPrefix r)
  have hp : MeasurePreserving f _ (Measure.pi (fun _ : Fin (l+r) => (law P).toMeasure)) :=
    (letterSplit_preserving P l r).symm.comp
      (((reverseLetters_preserving P l).prod (MeasurePreserving.id _)).comp
        ((rawPrefix_preserving P l).prod (rawPrefix_preserving P r)))
  have hi := hp.hasLaw.identDistrib (rawPrefix_preserving P (l+r)).hasLaw
  have hh := hi.comp (measurable_of_countable List.ofFn)
  convert hh using 1
  · funext z
    change revealed z.1 l++rawWord z.2 r=List.ofFn (f z)
    rw [← letterSplit_word l r]
    simp only [f,Function.comp_apply,MeasurableEquiv.apply_symm_apply]
    change revealed z.1 l++rawWord z.2 r=List.ofFn (reverseLetters l (rawPrefix l z.1))++List.ofFn (rawPrefix r z.2)
    rw [reverseLetters_word]
    rfl
  · rfl

def emptyProb (P : Parameters) (N : ℕ) : ℝ := (streamLaw P ℕ).real {x | EmptyReducing (rawWord x N)}
lemma emptyProb_nonneg (P : Parameters) (N : ℕ) : 0≤emptyProb P N := measureReal_nonneg
lemma seamWord_empty_measure (P : Parameters) (l r : ℕ) :
    ((streamLaw P ℕ).prod (streamLaw P ℕ)).real {z | EmptyReducing (seamWord l r z)}=emptyProb P (l+r) := by
  have h := (seamWord_preserving P l r).map_eq
  have he := congrArg (fun μ : Measure (List Letter) => μ {w | EmptyReducing w}) h
  have hm : Measurable (fun x => rawWord x (l+r)) :=
    (measurable_of_countable List.ofFn).comp (rawPrefix_measurable (l+r))
  rw [Measure.map_apply (seamWord_measurable l r) (Set.to_countable _).measurableSet,
    Measure.map_apply hm (Set.to_countable _).measurableSet] at he
  exact congrArg ENNReal.toReal he

end FKCRT.Inventory
end

end OAI
