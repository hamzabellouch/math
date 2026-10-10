import OAI.Probability.FKMaps.ExcursionLaw
import OAI.Probability.FKMaps.FiniteLaw
import OAI.Probability.FKMaps.MarkedBounds
import OAI.Probability.FKMaps.MeasuredCoding

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding
attribute [local instance] Classical.propDecidable
local instance : MeasurableSpace C(unitInterval,ℝ) := borel _
local instance : BorelSpace C(unitInterval,ℝ) := ⟨rfl⟩
local instance : MeasurableSpace C(unitInterval,ℝ×ℝ) := borel _
local instance : BorelSpace C(unitInterval,ℝ×ℝ) := ⟨rfl⟩

/-- Second continuous coordinate of the actual joint coding. -/
def heightProjection (f : C(unitInterval,ℝ×ℝ)) : C(unitInterval,ℝ) :=
  (⟨Prod.snd,continuous_snd⟩ : C(ℝ×ℝ,ℝ)).comp f

lemma heightProjection_continuous : Continuous heightProjection :=
  ContinuousMap.continuous_postcomp ⟨Prod.snd,continuous_snd⟩

lemma heightProjection_diagonal (f : C(unitInterval,ℝ)) : heightProjection (diagonalPath f)=f := by
  ext t
  rfl

/-- Actual normalized preorder height path, including both endpoint cells. -/
def heightCode {N : ℕ} (p : CriticalEvenOffspring) (d : Code N) : C(unitInterval,ℝ) :=
  interpolation N (fun i => p.sigma*height d.val i.val/(2*Real.sqrt N))

lemma heightCode_eq {N : ℕ} (p : CriticalEvenOffspring) (d : Code N) :
    heightCode p d=heightProjection (jointCode p.sigma d) := by ext t;rfl

/-- The unconditional, full height-path limit with the exact excursion
law; this only reuses the already proved joint invariance theorem. -/
theorem CriticalEvenOffspring.heightCode_CLT (p : CriticalEvenOffspring)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : Fin 3 → ℝ≥0 → Ω → ℝ} (hB : ∀ i,IsBrownianReal (B i) P)
    (hI : iIndepFun (fun i ω t => B i t ω) P) :
    TendstoInDistribution (fun n (d : Code (2*n+1)) => heightCode p d) atTop
      (excursionPath B) p.codeLaw P := by
  have hh := (p.jointCode_vervaat_CLT (hB 0)).continuous_comp heightProjection_continuous
  simp only [Function.comp_def,← heightCode_eq,heightProjection_diagonal] at hh
  have hi := vervaat_identDistrib_excursion (hB 0) hB hI
  refine ⟨hh.forall_aemeasurable,hi.aemeasurable_snd,?_⟩
  convert hh.tendsto using 1
  congr 2
  exact hi.map_eq.symm

/-- Continuous-tree observables converge under the genuine code law. -/
theorem CriticalEvenOffspring.heightCRT_tests (p : CriticalEvenOffspring)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : Fin 3 → ℝ≥0 → Ω → ℝ} (hB : ∀ i,IsBrownianReal (B i) P)
    (hI : iIndepFun (fun i ω t => B i t ω) P)
    (F : FKCRT.MetricMeasureData → ℝ) (hF : FKCRT.IsGHPTest F) :
    Tendsto (fun n => ∫ d,F (FKCRT.treeSpace (heightCode p d)) ∂p.codeLaw n) atTop
      (𝓝 (FKCRT.brownianExpectation P B F)) := by
  obtain ⟨C,hC⟩ := hF.1
  have hh := integral_tendsto_of_tendstoInDistribution (p.heightCode_CLT hB hI)
    hF.continuous_treeSpace (fun x => by simpa only [Real.norm_eq_abs] using hC (FKCRT.treeSpace x))
  have he : (fun ω => F (FKCRT.treeSpace (excursionPath B ω)))=ᵐ[P]
      (fun ω => F (FKCRT.treeSpace (FKCRT.standardExcursion B ω))) := by
    filter_upwards [excursionPath_ae_eq hB] with ω hω
    exact congrArg (fun e => F (FKCRT.treeSpace e)) hω
  simpa only [Function.comp_def,integral_congr_ae he,FKCRT.brownianExpectation] using hh

end FKCRT.TreeCoding
end


noncomputable section
open List Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology
namespace FKCRT.Inventory.CoreTree
open FKCRT.TreeCoding
attribute [local instance] Classical.propDecidable

lemma maxDegree_le_iff (t : CoreTree) (K : ℕ) :
    t.maxDegree ≤ K ↔ ∀ a∈t.labels,a.arity ≤ K := by
  induction t with
  | leaf => simp [maxDegree,labels,CoreLabel.arity]
  | branch c ts ih =>
    simp only [maxDegree,max_le_iff,Finset.sup_le_iff,Finset.mem_univ,forall_true_left,ih]
    rw [labels_branch]
    simp only [List.mem_cons,List.mem_flatMap,List.mem_ofFn,forall_eq_or_imp,
      CoreLabel.arity]
    constructor
    · rintro ⟨hc,ht⟩
      refine ⟨hc,?_⟩
      rintro a ⟨l,⟨i,rfl⟩,ha⟩
      exact ht i a ha
    · rintro ⟨hc,ht⟩
      exact ⟨hc,fun i a ha => ht a ⟨_,⟨i,rfl⟩,ha⟩⟩

lemma maxDegree_le_ofMarkedCode {N : ℕ} (x : MarkedCode N) :
    (ofMarkedCode x).maxDegree ≤ Finset.univ.sup (fun i => (x.val.1.val i).val) := by
  rw [maxDegree_le_iff,ofMarkedCode_labels]
  intro a ha
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
  rw [x.property i]
  exact Finset.le_sup (f := fun i => (x.val.1.val i).val) (Finset.mem_univ i)

lemma maxDegree_large_ofMarkedCode {N : ℕ} (x : MarkedCode N) {R : ℝ}
    (hR : 0 ≤ R) (h : R<((ofMarkedCode x).maxDegree:ℝ)) :
    ∃ i,R<((x.val.1.val i).val:ℝ) := by
  by_contra hh
  push Not at hh
  have hb : (↑(Finset.univ.sup (fun i => (x.val.1.val i).val) : ℕ):ℝ) ≤ R := by
    apply Finset.sup_induction (p := fun v : ℕ => (v:ℝ) ≤ R) (by simpa using hR)
    · intro a ha b hb
      rw [Nat.cast_max]
      exact max_le ha hb
    · intro i _
      exact hh i
  have hm : ((ofMarkedCode x).maxDegree:ℝ) ≤ (↑(Finset.univ.sup (fun i => (x.val.1.val i).val) : ℕ):ℝ) :=
    Nat.cast_le.mpr (maxDegree_le_ofMarkedCode x)
  linarith

end FKCRT.Inventory.CoreTree
end


noncomputable section
open List Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology
namespace FKCRT.Inventory.CoreTree
open FKCRT.TreeCoding
attribute [local instance] Classical.propDecidable

lemma nodePoint_gridPoint (t : CoreTree) (v : t.Node) :
    t.nodePoint v=gridPoint t.labels.length ⟨t.nodeIndex v,(t.nodeIndex_bound v).trans_le (Nat.le_succ _)⟩ := by
  apply Subtype.ext
  simp only [nodePoint,wordNodeEquiv_val,gridPoint,labels_length,Nat.cast_add,Nat.cast_one]

lemma heightCode_nodePoint (p : CriticalEvenOffspring) (t : CoreTree) (v : t.Node) :
    heightCode p t.toCode (t.nodePoint v)=p.sigma*(t.depth v:ℝ)/(2*Real.sqrt t.labels.length) := by
  rw [nodePoint_gridPoint,heightCode,interpolation_gridPoint (List.length_pos_iff.mpr t.labels_nonempty),← depth_height]

/-- Normalized marked error is evaluated at exactly the same coding mesh. -/
lemma route_heightCode_fit (p : CriticalEvenOffspring) (t : CoreTree) (β scale a : ℝ)
    (hs : 0 ≤ scale)
    (herr : ∀ v,|(t.routeLength v:ℝ)-β*t.depth v| ≤ a*Real.sqrt t.labels.length) :
    ∀ v,|scale*(t.routeLength v:ℝ)-
      ((scale*β*2*Real.sqrt t.labels.length/p.sigma) • heightCode p t.toCode) (t.nodePoint v)| ≤
        scale*a*Real.sqrt t.labels.length := by
  intro v
  rw [ContinuousMap.smul_apply,smul_eq_mul,heightCode_nodePoint]
  have hσ := p.sigma_pos
  have hn : 0<Real.sqrt (t.labels.length:ℝ) := Real.sqrt_pos.mpr (by
    exact_mod_cast List.length_pos_iff.mpr t.labels_nonempty)
  have he : scale*(t.routeLength v:ℝ)-
      (scale*β*2*Real.sqrt t.labels.length/p.sigma)*(p.sigma*(t.depth v:ℝ)/(2*Real.sqrt t.labels.length))=
        scale*((t.routeLength v:ℝ)-β*t.depth v) := by field_simp
  rw [he,abs_mul,abs_of_nonneg hs]
  exact (mul_le_mul_of_nonneg_left (herr v) hs).trans_eq (by ring)

/-- Direct genuine-map GHP bound in the actual normalized height path. -/
theorem heightCode_ghp_bound (p : CriticalEvenOffspring) (t : CoreTree)
    {n : ℕ} (w : FKCRT.SuccessfulWord n) (hw : t.word=List.ofFn w.val)
    (β scale a η δ : ℝ) (hs : 0<scale) (hδ : 0<δ)
    (herr : ∀ v,|(t.routeLength v:ℝ)-β*t.depth v| ≤ a*Real.sqrt t.labels.length)
    (hmod : ∀ s u,dist s u ≤ 1/(t.word.length:ℝ) →
      |((scale*β*2*Real.sqrt t.labels.length/p.sigma) • heightCode p t.toCode) s-
        ((scale*β*2*Real.sqrt t.labels.length/p.sigma) • heightCode p t.toCode) u| ≤ η)
    (hsmall : 4*scale*(t.maxDegree:ℝ)+4*(scale*a*Real.sqrt t.labels.length)+4*η ≤ 2*δ) :
    FKCRT.ghpEDist
      (FKCRT.treeSpace ((scale*β*2*Real.sqrt t.labels.length/p.sigma) • heightCode p t.toCode))
      (FKCRT.mapSpace scale ((FKCRT.rootedWordEquiv n).symm w).1) ≤ ENNReal.ofReal δ := by
  have hlen : t.word.length=2*(n+1) := by rw [hw,List.length_ofFn]
  obtain ⟨e,he,hp⟩ := t.realized_intertwine w hw
  exact t.ghp_tree_map_bound _ e (by omega) he hp hlen _ hs hδ
    (t.route_heightCode_fit p β scale a hs.le herr) hmod hsmall

end FKCRT.Inventory.CoreTree
end


noncomputable section
open List Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology
namespace FKCRT.TreeCoding
attribute [local instance] Classical.propDecidable
lemma CriticalEvenOffspring.code_event_probability (p : CriticalEvenOffspring) (n : ℕ)
    (E : (Fin (2*n+1) → Fin (2*n+1)) → Prop) :
    (p.codeLaw n).real {d | E d.val}=codeEventProbability p (2*n+1) E := by
  rw [← integral_indicator_one (μ := p.codeLaw n) (show MeasurableSet {d | E d.val} from trivial),p.code_integral]
  unfold codeEventProbability codeEventMass
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d _
  by_cases h : E d.val <;> simp [Set.indicator,h]

lemma CriticalEvenOffspring.actual_max_degree (p : CriticalEvenOffspring) {ε : ℝ} (hε : 0<ε) :
    Tendsto (fun n => (p.codeLaw n).real
      {d | ∃ i,ε*Real.sqrt ((2*n+1:ℕ):ℝ)<((d.val i).val:ℝ)}) atTop (𝓝 0) := by
  have h := p.conditioned_max_degree ε hε
  convert h using 1
  funext n
  rw [p.code_event_probability n (fun d => ∃ i,ε*Real.sqrt ((2*n+1:ℕ):ℝ)<((d i).val:ℝ))]
  congr 2
  norm_cast
end FKCRT.TreeCoding
namespace FKCRT.Inventory
open FKCRT.TreeCoding
attribute [local instance] Classical.propDecidable

/-- The actual largest core has vanishing square-root scale, under the
original compatible marked law. Impossible marks are not sampled. -/
theorem actual_max_core (P : Parameters) {ε : ℝ} (hε : 0<ε) :
    Tendsto (fun n => ((actualOffspring P).markedCodeLaw
      (fun k => (CoreLabel.markLaw P k).toMeasure) n).real
      {x | ∃ h : ∀ i,(x.2 i).arity=(x.1.val i).val,
        ε*Real.sqrt ((2*n+1:ℕ):ℝ)<((CoreTree.ofMarkedCode ⟨x,h⟩).maxDegree:ℝ)}) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => measureReal_nonneg) _ ((actualOffspring P).actual_max_degree hε)
  intro n
  rw [← (actualOffspring P).markedCodeLaw_fst (fun k => (CoreLabel.markLaw P k).toMeasure)]
  apply measureReal_mono _ (measure_ne_top _ _)
  intro x hx
  obtain ⟨h,hx⟩ := hx
  exact CoreTree.maxDegree_large_ofMarkedCode ⟨x,h⟩ (by positivity) hx
end FKCRT.Inventory
end


noncomputable section
open List Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology
namespace FKCRT.Inventory.CoreTree
open FKCRT.TreeCoding
attribute [local instance] Classical.propDecidable

lemma code_marks_of_labels (t : CoreTree) (x : MarkedCode t.labels.length)
    (hx : t.labels=List.ofFn x.val.2) :
    t.toCode=x.val.1 ∧ (fun i : Fin t.labels.length => t.labels[i.val])=x.val.2 := by
  have ha : (fun i : Fin t.labels.length => t.labels[i.val])=x.val.2 := by
    funext i
    have hd := congrArg (fun l : List CoreLabel => l[i.val]?) hx
    rw [List.getElem?_eq_getElem i.isLt,List.getElem?_ofFn,dite_eq_left i.isLt] at hd
    exact Option.some.inj hd
  refine ⟨?_,ha⟩
  apply Subtype.ext
  funext i
  apply Fin.ext
  change (t.labels[i.val]).arity=(x.val.1.val i).val
  rw [show t.labels[i.val]=x.val.2 i from congrFun ha i,x.property]

lemma marked_route_error {N : ℕ} (x : MarkedCode N) (β R : ℝ)
    (h : ∀ j : Fin N,|markedSpineSum coreIncrement x.val.1 j.isLt.le x.val.2-
      β*height x.val.1.val j.val| ≤ R) :
    ∀ v : (ofMarkedCode x).Node,
      |((ofMarkedCode x).routeLength v:ℝ)-β*(ofMarkedCode x).depth v| ≤ R := by
  generalize ht : ofMarkedCode x=t at *
  have hs := ofMarkedCode_size x
  rw [ht] at hs
  subst N
  have hl := ofMarkedCode_labels x
  rw [ht] at hl
  obtain ⟨hd,ha⟩ := code_marks_of_labels t x hl
  intro v
  rw [routeLength_marked,depth_height,hd,ha]
  exact h ⟨t.nodeIndex v,t.nodeIndex_bound v⟩

lemma marked_heightCode {N : ℕ} (p : CriticalEvenOffspring) (x : MarkedCode N) :
    heightCode p (ofMarkedCode x).toCode=heightCode p x.val.1 := by
  generalize ht : ofMarkedCode x=t
  have hs := ofMarkedCode_size x
  rw [ht] at hs
  subst N
  have hl := ofMarkedCode_labels x
  rw [ht] at hl
  rw [(code_marks_of_labels t x hl).1]

lemma ofMarkedCode_word_successful (n : ℕ) (x : MarkedCode (2*(n+1)+1)) :
    (ofMarkedCode x).word=List.ofFn ((successfulMarkedEquiv n).symm x).val := by
  have h := successfulMarked_word n ((successfulMarkedEquiv n).symm x)
  rw [(successfulMarkedEquiv n).apply_symm_apply] at h
  exact h

/-- The full deterministic measured comparison for a genuine marked draw:
no independent copy of the tree, changed metric, or approximate degree law. -/
theorem marked_height_ghp_bound (p : CriticalEvenOffspring) (n : ℕ)
    (x : MarkedCode (2*(n+1)+1)) (β scale a η δ : ℝ) (hs : 0<scale) (hδ : 0<δ)
    (herr : ∀ j : Fin (2*(n+1)+1),
      |markedSpineSum coreIncrement x.val.1 j.isLt.le x.val.2-β*height x.val.1.val j.val| ≤
        a*Real.sqrt ((2*(n+1)+1:ℕ):ℝ))
    (hmod : ∀ s u,dist s u ≤ 1/(2*((n:ℝ)+1)) →
      |((scale*β*2*Real.sqrt ((2*(n+1)+1:ℕ):ℝ)/p.sigma) • heightCode p x.val.1) s-
        ((scale*β*2*Real.sqrt ((2*(n+1)+1:ℕ):ℝ)/p.sigma) • heightCode p x.val.1) u| ≤ η)
    (hsmall : 4*scale*((ofMarkedCode x).maxDegree:ℝ)+
      4*(scale*a*Real.sqrt ((2*(n+1)+1:ℕ):ℝ))+4*η ≤ 2*δ) :
    FKCRT.ghpEDist
      (FKCRT.treeSpace ((scale*β*2*Real.sqrt ((2*(n+1)+1:ℕ):ℝ)/p.sigma) • heightCode p x.val.1))
      (FKCRT.mapSpace scale ((FKCRT.rootedWordEquiv n).symm ((successfulMarkedEquiv n).symm x)).1) ≤
        ENNReal.ofReal δ := by
  let t := ofMarkedCode x
  have hsize := ofMarkedCode_size x
  have hw := ofMarkedCode_word_successful n x
  have hlen : t.word.length=2*(n+1) := by rw [hw,List.length_ofFn]
  have he : ∀ v : t.Node,|(t.routeLength v:ℝ)-β*t.depth v| ≤ a*Real.sqrt t.labels.length := by
    rw [hsize]
    exact marked_route_error x β _ herr
  have hm : ∀ s u,dist s u ≤ 1/(t.word.length:ℝ) →
      |((scale*β*2*Real.sqrt t.labels.length/p.sigma) • heightCode p t.toCode) s-
        ((scale*β*2*Real.sqrt t.labels.length/p.sigma) • heightCode p t.toCode) u| ≤ η := by
    simpa only [hlen,t,hsize,marked_heightCode,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one] using hmod
  have hb := heightCode_ghp_bound p t _ hw β scale a η δ hs hδ he hm (by simpa only [t,hsize] using hsmall)
  simpa only [t,hsize,marked_heightCode] using hb

end FKCRT.Inventory.CoreTree
end

end OAI
