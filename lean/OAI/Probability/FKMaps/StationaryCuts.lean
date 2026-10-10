import Mathlib

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.CutOutput

/-- Totalized first index; on nonempty predicates this is the ordinary least index. -/
def firstIndex (p : ℕ → Prop) : ℕ := by
  classical
  exact Nat.find (show ∃ n,p n ∨ ¬∃ k,p k from by
    by_cases h : ∃ k,p k
    · obtain ⟨k,hk⟩ := h; exact ⟨k,Or.inl hk⟩
    · exact ⟨0,Or.inr h⟩)
lemma firstIndex_spec {p : ℕ → Prop} (hp : ∃ k,p k) : p (firstIndex p) := by
  classical
  exact (Nat.find_spec (show ∃ n,p n ∨ ¬∃ k,p k from by
    obtain ⟨k,hk⟩ := hp; exact ⟨k,Or.inl hk⟩)).resolve_right (by simpa using hp)
lemma firstIndex_le {p : ℕ → Prop} {k : ℕ} (hk : p k) : firstIndex p ≤ k := by
  classical
  exact Nat.find_min' _ (Or.inl hk)
lemma firstIndex_measurable {Ω : Type*} [MeasurableSpace Ω] (p : Ω → ℕ → Prop)
    (hm : ∀ k,MeasurableSet {x | p x k}) : Measurable (fun x => firstIndex (p x)) := by
  classical
  unfold firstIndex
  apply measurable_find
  intro k
  have hh : MeasurableSet {x | ∃ j,p x j} := by
    simp only [Set.ofPred_exists]; exact MeasurableSet.iUnion hm
  exact (hm k).union hh.compl

structure Data (β : Type*) where
  cut : ℤ → Prop
  word : ℤ → ℕ → List β
  length : ∀ (a : ℤ) (n : ℕ),cut a → cut (a+n) → (word a n).length=n
  append : ∀ (a : ℤ) (m n : ℕ),cut a → cut (a+m) → cut (a+m+n) →
    word a (m+n)=word a m++word (a+m) n

variable {β : Type*}
def left (C : ℤ → Prop) (i : ℤ) : ℕ := firstIndex (fun k => C (i-k))
def right (C : ℤ → Prop) (i : ℤ) : ℕ := firstIndex (fun k => C (i+1+k))
def output (C : ℤ → Prop) (W : ℤ → ℕ → List β) (d : β) (i : ℤ) : β :=
  ((W (i-left C i) (left C i+1+right C i))[left C i]?).getD d

lemma Data.output_eq_get (D : Data β) (d : β) (a : ℤ) (n : ℕ) (i : ℤ)
    (ha : D.cut a) (hb : D.cut (a+n)) (hai : a ≤ i) (hib : i<a+n) :
    output D.cut D.word d i=(D.word a n)[(i-a).toNat]'(by rw [D.length a n ha hb]; omega) := by
  let l := left D.cut i
  let r := right D.cut i
  have hl : l ≤ (i-a).toNat := by
    apply firstIndex_le
    have he : i-((i-a).toNat:ℤ)=a := by omega
    rw [he]
    exact ha
  have hr : r ≤ (a+n-i-1).toNat := by
    apply firstIndex_le
    have he : i+1+((a+n-i-1).toNat:ℤ)=a+n := by omega
    rw [he]
    exact hb
  have hc : D.cut (i-l) := firstIndex_spec (p := fun k => D.cut (i-k)) ⟨(i-a).toNat,by
    have he : i-((i-a).toNat:ℤ)=a := by omega
    rw [he]; exact ha⟩
  have hd : D.cut (i+1+r) := firstIndex_spec (p := fun k => D.cut (i+1+k)) ⟨(a+n-i-1).toNat,by
    have he : i+1+((a+n-i-1).toNat:ℤ)=a+n := by omega
    rw [he]; exact hb⟩
  let u := (i-a).toNat-l
  let v := l+1+r
  let t := n-u-v
  have hn : n=u+v+t := by dsimp [u,v,t]; omega
  have hac : a+u=i-l := by dsimp [u]; omega
  have hcd : a+u+v=i+1+r := by dsimp [u,v]; omega
  have he : D.word a n=D.word a u++D.word (a+u) v++D.word (a+u+v) t := by
    have hd' : D.cut (a+(u+v:ℕ)) := by
      rw [show a+((u+v:ℕ):ℤ)=i+1+r by omega]; exact hd
    have hb' : D.cut (a+(u+v:ℕ)+t) := by
      rw [show a+((u+v:ℕ):ℤ)+t=a+n by omega]; exact hb
    rw [hn,D.append a (u+v) t ha hd' hb']
    rw [D.append a u v ha (by simpa only [hac] using hc) (by simpa only [hcd] using hd)]
    simp only [Nat.cast_add,add_assoc]
  have hu : (D.word a u).length=u := D.length a u ha (by simpa only [hac] using hc)
  have hv : (D.word (a+u) v).length=v := D.length _ _ (by simpa only [hac] using hc) (by simpa only [hcd] using hd)
  have hget : (D.word a n)[(i-a).toNat]?=(D.word (i-l) v)[l]? := by
    rw [he,List.getElem?_append]
    have hii : (i-a).toNat<(D.word a u++D.word (a+u) v).length := by simp only [List.length_append,hu,hv]; dsimp [u,v]; omega
    rw [ite_eq_left hii,List.getElem?_append,hu,ite_eq_right (by dsimp [u]; omega)]
    have hidx : (i-a).toNat-u=l := by dsimp [u]; omega
    rw [hidx,hac]
  have hni : (i-a).toNat<(D.word a n).length := by rw [D.length a n ha hb]; omega
  have hh := congrArg (fun o : Option β => o.getD d) hget
  simpa only [List.getElem?_eq_getElem hni,Option.getD_some,output,l,r,v] using hh.symm

lemma Data.output_segment (D : Data β) (d : β) (a : ℤ) (n : ℕ)
    (ha : D.cut a) (hb : D.cut (a+n)) :
    List.ofFn (fun j : Fin n => output D.cut D.word d (a+j))=D.word a n := by
  apply List.ext_getElem
  · simp [D.length a n ha hb]
  · intro j hj hk
    have hj' : j<n := by simpa using hj
    simp only [List.getElem_ofFn]
    simpa only [add_sub_cancel_left,Int.toNat_natCast] using D.output_eq_get d a n (a+j) ha hb (by omega) (by omega)

lemma output_translate (C : ℤ → Prop) (W : ℤ → ℕ → List β) (d : β) (a i : ℤ) :
    output (fun j => C (j+a)) (fun j n => W (j+a) n) d i=output C W d (i+a) := by
  have hl : left (fun j => C (j+a)) i=left C (i+a) := by
    unfold left
    congr 1
    funext k
    dsimp only
    rw [show i-(k:ℤ)+a=i+a-k by omega]
  have hr : right (fun j => C (j+a)) i=right C (i+a) := by
    unfold right
    congr 1
    funext k
    dsimp only
    rw [show i+1+(k:ℤ)+a=i+a+1+k by omega]
  unfold output
  rw [hl,hr]
  dsimp only
  rw [show i-(left C (i+a):ℤ)+a=i+a-left C (i+a) by omega]

lemma output_measurable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (C : Ω → ℤ → Prop) (W : Ω → ℤ → ℕ → List β) (d : β) (i : ℤ)
    [MeasurableSpace (List β)] [MeasurableSingletonClass (List β)] [Countable (List β)]
    (hC : ∀ j,MeasurableSet {x | C x j}) (hW : ∀ a n,Measurable (fun x => W x a n)) :
    Measurable (fun x => output (C x) (W x) d i) := by
  have hl : Measurable (fun x => left (C x) i) := firstIndex_measurable _ (fun k => hC (i-k))
  have hr : Measurable (fun x => right (C x) i) := firstIndex_measurable _ (fun k => hC (i+1+k))
  have hw : Measurable (fun x => W x (i-left (C x) i) (left (C x) i+1+right (C x) i)) := by
    let f : Ω × (ℤ × ℕ) → List β := fun p => W p.1 p.2.1 p.2.2
    have hf : Measurable f := measurable_from_prod_countable_left (fun p => hW p.1 p.2)
    exact hf.comp (measurable_id.prodMk (((measurable_of_countable (fun n : ℕ => i-(n:ℤ))).comp hl).prodMk ((hl.add_const 1).add hr)))
  exact (measurable_of_countable (fun p : List β × ℕ => (p.1[p.2]?).getD d)).comp (hw.prodMk hl)

end FKCRT.CutOutput
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Stationary
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The nonnegative running maximum of the partial sums of a stationary observable. -/
def maxSum (T : Ω → Ω) (f : Ω → ℝ) : ℕ → Ω → ℝ
  | 0, _ => 0
  | n+1,x => max 0 (f x+maxSum T f n (T x))

omit [MeasurableSpace Ω] in
lemma maxSum_nonneg (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) (x : Ω) :
    0 ≤ maxSum T f n x := by
  cases n <;> simp [maxSum]

omit [MeasurableSpace Ω] in
lemma maxSum_mono (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) (x : Ω) :
    maxSum T f n x ≤ maxSum T f (n+1) x := by
  induction n generalizing x with
  | zero => exact maxSum_nonneg T f 1 x
  | succ n ih => exact max_le_max_left 0 (by linarith [ih (T x)])

lemma measurable_maxSum {T : Ω → Ω} {f : Ω → ℝ} (hT : Measurable T) (hf : Measurable f)
    (n : ℕ) : Measurable (maxSum T f n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact measurable_const.max (hf.add (ih.comp hT))

lemma integrable_maxSum {T : Ω → Ω} {f : Ω → ℝ} (hT : MeasurePreserving T μ μ)
    (hf : Integrable f μ) (n : ℕ) : Integrable (maxSum T f n) μ := by
  induction n with
  | zero => exact integrable_const _
  | succ n ih => exact (integrable_const _).sup (hf.add (hT.integrable_comp_of_integrable ih))

omit [MeasurableSpace Ω] in
lemma maxSum_bound_sum (T : Ω → Ω) (f : Ω → ℝ) (n k : ℕ) (hk : k ≤ n) (x : Ω) :
    ∑ i∈Finset.range k, f (T^[i] x) ≤ maxSum T f n x := by
  induction k generalizing n x with
  | zero => simpa using maxSum_nonneg T f n x
  | succ k ih =>
    cases n with
    | zero => omega
    | succ n =>
      rw [Finset.sum_range_succ']
      simp only [Function.iterate_zero_apply,Function.iterate_succ_apply]
      have hh := ih n (by omega) (T x)
      have hb := le_max_right 0 (f x+maxSum T f n (T x))
      change _ ≤ max 0 (f x+maxSum T f n (T x))
      linarith

/-- Finite maximal ergodic inequality.  In particular no independence of the
observations is used in the maximal step. -/
lemma integral_on_maxSum_nonneg {T : Ω → Ω} {f : Ω → ℝ}
    (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) (hm : Measurable f) (n : ℕ) :
    0 ≤ ∫ x in {x | 0 < maxSum T f n x},f x ∂μ := by
  cases n with
  | zero => simp [maxSum]
  | succ n =>
    let A : Set Ω := {x | 0 < maxSum T f (n+1) x}
    have hA : MeasurableSet A := measurableSet_lt measurable_const (measurable_maxSum hT.measurable hm _)
    have hg := integrable_maxSum hT hf n
    have hg' := integrable_maxSum hT hf (n+1)
    have hp := hT.integrable_comp_of_integrable hg
    change Integrable (fun x => maxSum T f n (T x)) μ at hp
    have hi : Integrable (A.indicator f) μ := hf.indicator hA
    have hb (x : Ω) : maxSum T f (n+1) x-maxSum T f n (T x) ≤ A.indicator f x := by
      by_cases hx : x∈A
      · rw [Set.indicator_of_mem hx]
        have hx' : 0 < f x+maxSum T f n (T x) := by
          simpa only [A,Set.mem_ofPred_eq,maxSum,lt_max_iff,lt_self_iff_false,false_or] using hx
        rw [maxSum,max_eq_right hx'.le]
        linarith
      · rw [Set.indicator_of_notMem hx]
        have hx' : maxSum T f (n+1) x=0 := le_antisymm (le_of_not_gt hx) (maxSum_nonneg _ _ _ _)
        rw [hx']
        linarith [maxSum_nonneg T f n (T x)]
    have h := integral_mono (hg'.sub hp) hi hb
    change (∫ x,maxSum T f (n+1) x-maxSum T f n (T x) ∂μ) ≤ _ at h
    rw [integral_sub hg' hp] at h
    have he := hT.hasLaw.integral_comp hg.aestronglyMeasurable
    change (∫ x,maxSum T f n (T x) ∂μ)=(∫ x,maxSum T f n x ∂μ) at he
    rw [he] at h
    have hmono := integral_mono hg hg' (maxSum_mono T f n)
    rw [integral_indicator hA] at h
    exact le_trans (by linarith) h

lemma finite_maximal_bound {T : Ω → Ω} {U : Ω → ℝ}
    (hT : MeasurePreserving T μ μ) (hU : Integrable U μ) (hm : Measurable U)
    (hpos : ∀ x,0 ≤ U x) (η : ℝ) (hη : 0 < η) (n : ℕ) :
    μ.real {x | 0 < maxSum T (fun x => U x-η) n x} ≤ (∫ x,U x ∂μ)/η := by
  let A : Set Ω := {x | 0 < maxSum T (fun x => U x-η) n x}
  have hA : MeasurableSet A := measurableSet_lt measurable_const
    (measurable_maxSum hT.measurable (hm.sub_const η) n)
  have h := integral_on_maxSum_nonneg hT (hU.sub (integrable_const η)) (hm.sub_const η) n
  change 0 ≤ ∫ x in A,U x-η ∂μ at h
  rw [integral_sub hU.integrableOn (integrable_const η),setIntegral_const] at h
  have hb : ∫ x in A,U x ∂μ ≤ ∫ x,U x ∂μ :=
    setIntegral_le_integral hU (Filter.Eventually.of_forall hpos)
  simp only [smul_eq_mul] at h
  apply (le_div_iff₀ hη).mpr
  simpa only [smul_eq_mul] using (by linarith : μ.real A*η ≤ ∫ x,U x ∂μ)

/-- Hopf's stationary maximal bound, for a nonnegative integrable observable. -/
lemma maximal_bound {T : Ω → Ω} {U : Ω → ℝ}
    (hT : MeasurePreserving T μ μ) (hU : Integrable U μ) (hm : Measurable U)
    (hpos : ∀ x,0 ≤ U x) (η : ℝ) (hη : 0 < η) :
    μ {x | ∃ n : ℕ,(n:ℝ)*η < ∑ i∈Finset.range n,U (T^[i] x)} ≤
      ENNReal.ofReal ((∫ x,U x ∂μ)/η) := by
  let A : ℕ → Set Ω := fun n => {x | 0 < maxSum T (fun x => U x-η) n x}
  have ha : Monotone A := by
    apply monotone_nat_of_le_succ
    intro n x hx
    exact lt_of_lt_of_le hx (maxSum_mono T (fun x => U x-η) n x)
  have hs : {x | ∃ n : ℕ,(n:ℝ)*η < ∑ i∈Finset.range n,U (T^[i] x)} ⊆ ⋃ n,A n := by
    rintro x ⟨n,hn⟩
    apply Set.mem_iUnion.mpr
    refine ⟨n,?_⟩
    have hb := maxSum_bound_sum T (fun x => U x-η) n n le_rfl x
    simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hb
    change 0 < maxSum T (fun x => U x-η) n x
    linarith
  apply (measure_mono hs).trans
  rw [ha.measure_iUnion]
  apply iSup_le
  intro n
  have h := ENNReal.ofReal_le_ofReal (finite_maximal_bound hT hU hm hpos η hη n)
  rw [measureReal_def,ENNReal.ofReal_toReal (measure_ne_top _ _)] at h
  exact h

def average (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) (x : Ω) : ℝ :=
  (∑ i∈Finset.range n, f (T^[i] x))/(n:ℝ)

lemma measurable_average {T : Ω → Ω} {f : Ω → ℝ} (hT : Measurable T)
    (hf : Measurable f) (n : ℕ) : Measurable (average T f n) := by
  exact (Finset.measurable_sum _ (fun i _ => hf.comp (hT.iterate i))).div_const n

omit [MeasurableSpace Ω] in
lemma average_sub (T : Ω → Ω) (f g : Ω → ℝ) (n : ℕ) (x : Ω) :
    average T (fun x => f x-g x) n x=average T f n x-average T g n x := by
  simp only [average,Finset.sum_sub_distrib,sub_div]

lemma maximal_abs_average_bound {T : Ω → Ω} {f : Ω → ℝ}
    (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) (hm : Measurable f)
    (η : ℝ) (hη : 0 < η) :
    μ {x | ∃ n : ℕ,η < |average T f n x|} ≤
      ENNReal.ofReal ((∫ x,|f x| ∂μ)/η) := by
  apply (measure_mono (show {x | ∃ n : ℕ,η < |average T f n x|} ⊆
      {x | ∃ n : ℕ,(n:ℝ)*η < ∑ i∈Finset.range n,|f (T^[i] x)|} from ?_)).trans
    (maximal_bound hT hf.abs hm.abs (fun _ => abs_nonneg _) η hη)
  rintro x ⟨n,hn⟩
  have hn0 : n≠0 := by rintro rfl; simp only [average,Finset.range_zero,Finset.sum_empty,zero_div,abs_zero] at hn; linarith
  have hnp : (0:ℝ)<n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
  have hh : η*(n:ℝ) < |∑ i∈Finset.range n,f (T^[i] x)| := by
    simpa only [average,abs_div,abs_of_pos hnp] using (lt_div_iff₀ hnp).mp
      (show η < |∑ i∈Finset.range n,f (T^[i] x)|/(n:ℝ) by simpa only [average,abs_div,abs_of_pos hnp] using hn)
  exact ⟨n,by nlinarith [Finset.abs_sum_le_sum_abs (f := fun i => f (T^[i] x)) (s := Finset.range n)]⟩

end FKCRT.Stationary

end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Stationary
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The stationary maximal inequality makes almost-sure convergence of
averages stable under L¹ approximation. -/
theorem ae_average_limit_of_L1_approx {T : Ω → Ω} {f : Ω → ℝ} {g : ℕ → Ω → ℝ}
    {m : ℝ} {a : ℕ → ℝ} (hT : MeasurePreserving T μ μ)
    (hf : Integrable f μ) (hmf : Measurable f)
    (hg : ∀ k,Integrable (g k) μ) (hmg : ∀ k,Measurable (g k))
    (happrox : Tendsto (fun k => ∫ x,|f x-g k x| ∂μ) atTop (𝓝 0))
    (ha : Tendsto a atTop (𝓝 m))
    (hgood : ∀ k,∀ᵐ x ∂μ,Tendsto (fun n => average T (g k) n x) atTop (𝓝 (a k))) :
    ∀ᵐ x ∂μ,Tendsto (fun n => average T f n x) atTop (𝓝 m) := by
  have hnull (ε : ℝ) (hε : 0 < ε) :
      μ {x | ∃ᶠ n in atTop,ε < |average T f n x-m|}=0 := by
    let B : Set Ω := {x | ∃ᶠ n in atTop,ε < |average T f n x-m|}
    have hb : ∀ᶠ k in atTop,μ B ≤ ENNReal.ofReal ((∫ x,|f x-g k x| ∂μ)/(ε/3)) := by
      filter_upwards [(Metric.tendsto_nhds.mp ha) (ε/3) (by positivity)] with k hk
      have he : B ≤ᵐ[μ] {x | ∃ n,ε/3 < |average T (fun x => f x-g k x) n x|} := by
        filter_upwards [hgood k] with x hx
        intro hB
        have hex := hB.and_eventually ((Metric.tendsto_nhds.mp hx) (ε/3) (by positivity))
        obtain ⟨n,hn,hgn⟩ := hex.exists
        refine ⟨n,?_⟩
        rw [average_sub]
        have hh := abs_add_three (average T f n x-average T (g k) n x)
          (average T (g k) n x-a k) (a k-m)
        have heq : (average T f n x-average T (g k) n x)+
            (average T (g k) n x-a k)+(a k-m)=average T f n x-m := by ring
        rw [heq] at hh
        rw [Real.dist_eq] at hk hgn
        linarith
      exact (measure_mono_ae he).trans
        (maximal_abs_average_bound hT (hf.sub (hg k)) (hmf.sub (hmg k)) _ (by positivity))
    have ht : Tendsto (fun k => ENNReal.ofReal ((∫ x,|f x-g k x| ∂μ)/(ε/3))) atTop (𝓝 0) := by
      simpa only [zero_div,ENNReal.ofReal_zero,Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (happrox.div_const (ε/3))
    exact le_antisymm (le_of_tendsto_of_tendsto tendsto_const_nhds ht hb) bot_le
  have hae (k : ℕ) : ∀ᵐ x ∂μ,¬(∃ᶠ n in atTop,(1:ℝ)/(k+1) < |average T f n x-m|) :=
    measure_eq_zero_iff_ae_notMem.mp (hnull _ (by positivity))
  filter_upwards [ae_all_iff.mpr hae] with x hx
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨k,hk⟩ := exists_nat_gt (1/ε)
  have hkpos : (0:ℝ)<(k:ℝ)+1 := by positivity
  have hδ : (1:ℝ)/(k+1)<ε := by
    apply (div_lt_iff₀ hkpos).mpr
    have hh : 1<ε*(k:ℝ) := by simpa [mul_comm] using (div_lt_iff₀ hε).mp hk
    nlinarith
  have hh : ∀ᶠ n in atTop,|average T f n x-m| ≤ (1:ℝ)/(k+1) := by
    simpa only [not_frequently,not_lt] using hx k
  filter_upwards [hh] with n hn
  simpa only [Real.dist_eq] using hn.trans_lt hδ

end FKCRT.Stationary
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Stationary

lemma linear_remainder_of_ratio {S : ℕ → ℝ} {m : ℝ}
    (ht : Tendsto (fun n => S n/(n:ℝ)) atTop (𝓝 m)) (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ,0 ≤ A ∧ ∀ n,|S n-m*n| ≤ ε*n+A := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((Metric.tendsto_nhds.mp ht) ε hε)
  refine ⟨∑ i∈Finset.range (N+1),|S i-m*i|,Finset.sum_nonneg (fun _ _ => abs_nonneg _),fun n => ?_⟩
  by_cases hn : N+1 ≤ n
  · have hnpos : (0:ℝ)<n := by exact_mod_cast (show 0 < n by omega)
    have h := hN n (by omega)
    rw [Real.dist_eq,show S n/(n:ℝ)-m=(S n-m*n)/(n:ℝ) by field_simp,abs_div,abs_of_pos hnpos] at h
    have hh := (div_lt_iff₀ hnpos).mp h
    exact hh.le.trans (le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => abs_nonneg _)))
  · have h := Finset.single_le_sum (f := fun i => |S i-m*i|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.mpr (show n < N+1 by omega))
    exact h.trans (le_add_of_nonneg_left (mul_nonneg hε.le (Nat.cast_nonneg n)))

lemma ratio_limit_of_linear_remainder {S : ℕ → ℝ} {m : ℝ}
    (h : ∀ ε : ℝ,0 < ε → ∃ A : ℝ,0 ≤ A ∧ ∀ n,|S n-m*n| ≤ ε*n+A) :
    Tendsto (fun n => S n/(n:ℝ)) atTop (𝓝 m) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨A,_,hA⟩ := h (ε/2) (by positivity)
  have ht : Tendsto (fun n : ℕ => A/(n:ℝ)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gt_atTop 0,(tendsto_order.mp ht).2 (ε/2) (by positivity)] with n hn hsmall
  have hnpos : (0:ℝ)<n := Nat.cast_pos.mpr hn
  rw [Real.dist_eq,show S n/(n:ℝ)-m=(S n-m*n)/(n:ℝ) by field_simp,abs_div,abs_of_pos hnpos]
  have hb := (div_le_div_iff_of_pos_right hnpos).mpr (hA n)
  have he : (ε/2*(n:ℝ)+A)/(n:ℝ)=ε/2+A/(n:ℝ) := by field_simp
  rw [he] at hb
  linarith

/-- Monotonicity fills the bounded gaps between a fixed arithmetic subsequence. -/
lemma ratio_limit_of_multiples {S : ℕ → ℝ} (hS : Monotone S) (r : ℕ) (hr : 0 < r)
    (m : ℝ) (ht : Tendsto (fun q => S (r*q)/(q:ℝ)) atTop (𝓝 ((r:ℝ)*m))) :
    Tendsto (fun n => S n/(n:ℝ)) atTop (𝓝 m) := by
  apply ratio_limit_of_linear_remainder
  intro ε hε
  obtain ⟨A,hA,hbound⟩ := linear_remainder_of_ratio ht ε hε
  refine ⟨A+ε+|m| *r,by positivity,fun n => ?_⟩
  let q := n/r
  have hlo : r*q ≤ n := Nat.mul_div_le n r
  have hhi : n < r*(q+1) := by
    have hmod := Nat.mod_lt n hr
    have hdiv := Nat.mod_add_div n r
    dsimp [q]
    nlinarith
  have hq : q ≤ n := Nat.div_le_self n r
  have hslo := hS hlo
  have hshi := hS hhi.le
  have hblo := abs_le.mp (hbound q)
  have hbhi := abs_le.mp (hbound (q+1))
  have hc1 : (r:ℝ)*q ≤ n := by exact_mod_cast hlo
  have hc2 : (n:ℝ) ≤ r*(q+1) := by exact_mod_cast hhi.le
  have hc3 : (q:ℝ) ≤ n := by exact_mod_cast hq
  have habs1 : m*((n:ℝ)-r*q) ≤ |m| *r := by
    have hh : 0 ≤ (n:ℝ)-r*q := by linarith
    have hhh : (n:ℝ)-r*q ≤ r := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right (le_abs_self m) hh,abs_nonneg m]
  have habs2 : m*((r:ℝ)*(q+1)-n) ≤ |m| *r := by
    have hh : 0 ≤ (r:ℝ)*(q+1)-n := by linarith
    have hhh : (r:ℝ)*(q+1)-n ≤ r := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right (le_abs_self m) hh,abs_nonneg m]
  have hns1 : -m*((n:ℝ)-r*q) ≤ |m| *r := by
    have hh : 0 ≤ (n:ℝ)-r*q := by linarith
    have hhh : (n:ℝ)-r*q ≤ r := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right (neg_le_abs m) hh,abs_nonneg m]
  have hns2 : -m*((r:ℝ)*(q+1)-n) ≤ |m| *r := by
    have hh : 0 ≤ (r:ℝ)*(q+1)-n := by linarith
    have hhh : (r:ℝ)*(q+1)-n ≤ r := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right (neg_le_abs m) hh,abs_nonneg m]
  push_cast at hblo hbhi
  apply abs_le.mpr
  constructor <;> nlinarith

lemma sum_range_blocks (f : ℕ → ℝ) (r q : ℕ) :
    ∑ j∈Finset.range (r*q),f j=∑ a∈Finset.range r,∑ i∈Finset.range q,f (a+r*i) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ,Finset.sum_range_add,ih]
    simp only [Finset.sum_range_succ,Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    congr 1
    omega

lemma interlaced_nonneg_limit {f : ℕ → ℝ} (hf : ∀ n,0 ≤ f n) (r : ℕ) (hr : 0 < r)
    (m : ℝ) (ht : ∀ a < r,Tendsto (fun q => (∑ i∈Finset.range q,f (a+r*i))/(q:ℝ)) atTop (𝓝 m)) :
    Tendsto (fun n => (∑ i∈Finset.range n,f i)/(n:ℝ)) atTop (𝓝 m) := by
  refine ratio_limit_of_multiples (S := fun n => ∑ i∈Finset.range n,f i) ?_ r hr m ?_
  · apply monotone_nat_of_le_succ
    intro n
    rw [Finset.sum_range_succ]
    linarith [hf n]
  · have h := tendsto_finsetSum (Finset.range r) (fun a ha => ht a (Finset.mem_range.mp ha))
    simpa only [← Finset.sum_div,← sum_range_blocks,Finset.sum_const,Finset.card_range,nsmul_eq_mul] using h

end FKCRT.Stationary
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Stationary
variable {α : Type*} [MeasurableSpace α]

def seqLaw (ν : Measure α) [IsProbabilityMeasure ν] : Measure (ℤ → α) :=
  Measure.infinitePi (fun _ : ℤ => ν)
instance seqLaw_probability (ν : Measure α) [IsProbabilityMeasure ν] : IsProbabilityMeasure (seqLaw ν) := by
  unfold seqLaw
  infer_instance

def shift (a : ℤ) (x : ℤ → α) : ℤ → α := fun k => x (k+a)

lemma measurable_shift (a : ℤ) : Measurable (shift (α := α) a) :=
  Measurable.of_eval (fun index => measurable_pi_apply (index+a))

lemma shift_preserving (ν : Measure α) [IsProbabilityMeasure ν] (a : ℤ) :
    MeasurePreserving (shift a) (seqLaw ν) (seqLaw ν) := by
  refine ⟨measurable_shift a,?_⟩
  exact Measure.map_infinitePi_infinitePi_of_inj (fun _ _ h => add_right_cancel h)

omit [MeasurableSpace α] in
lemma shift_add (a b : ℤ) (x : ℤ → α) : shift a (shift b x)=shift (a+b) x := by
  ext k
  simp [shift,add_assoc]
omit [MeasurableSpace α] in
lemma shift_iterate (n : ℕ) (x : ℤ → α) : (shift 1)^[n] x=shift (n:ℤ) x := by
  induction n with
  | zero => ext k; simp [shift]
  | succ n ih => rw [Function.iterate_succ_apply',ih,shift_add]; congr 1; omega

@[instance_reducible] def coords (S : Set ℤ) : MeasurableSpace (ℤ → α) :=
  ⨆ k∈S,MeasurableSpace.comap (fun x : ℤ → α => x k) inferInstance

lemma coords_mono {S R : Set ℤ} (h : S ⊆ R) : coords (α := α) S ≤ coords R := by
  apply iSup_le
  intro k
  apply iSup_le
  intro hk
  exact le_iSup_of_le k (le_iSup_of_le (h hk) le_rfl)

lemma coords_le (S : Set ℤ) : coords (α := α) S ≤ (inferInstance : MeasurableSpace (ℤ → α)) := by
  exact iSup_le fun k => iSup_le fun _ => (measurable_pi_apply k).comap_le

lemma measurable_shift_coords (S : Set ℤ) (a : ℤ) :
    Measurable[coords (S.image (fun k => k+a)),coords S] (shift (α := α) a) := by
  apply measurable_iff_comap_le.mpr
  simp only [coords,MeasurableSpace.comap_iSup]
  apply iSup_le
  intro k
  apply iSup_le
  intro hk
  rw [MeasurableSpace.comap_comp]
  change MeasurableSpace.comap (fun x : ℤ → α => x (k+a)) inferInstance ≤ _
  exact le_iSup_of_le (k+a) (le_iSup_of_le (Set.mem_image_of_mem _ hk) le_rfl)

lemma indep_coords (ν : Measure α) [IsProbabilityMeasure ν] {S R : Set ℤ} (h : Disjoint S R) :
    Indep (coords (α := α) S) (coords R) (seqLaw ν) := by
  exact indep_iSup_of_disjoint (fun k => (measurable_pi_apply k).comap_le)
    (iIndepFun_infinitePi (P := fun _ : ℤ => ν) (X := fun _ (a : α) => a) (fun _ => measurable_id)) h

def window (n : ℕ) : Set ℤ := {k | -(n:ℤ) ≤ k ∧ k ≤ n}

lemma window_mono {m n : ℕ} (h : m ≤ n) : window m ⊆ window n := by
  intro k hk
  dsimp [window] at hk ⊢
  omega

lemma window_disjoint (r i j : ℕ) (a : ℤ) (hij : i≠j) :
    Disjoint ((window r).image (fun k => k+(a+(2*(r:ℤ)+1)*i)))
      ((window r).image (fun k => k+(a+(2*(r:ℤ)+1)*j))) := by
  apply Set.disjoint_left.mpr
  rintro k ⟨s,hs,rfl⟩ ⟨t,ht,he⟩
  dsimp [window] at hs ht
  have hii : (i:ℤ)≠j := by exact_mod_cast hij
  rcases lt_or_gt_of_ne hii with hi | hi
  · have hh : (i:ℤ)+1 ≤ j := by omega
    have hmult := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 2*(r:ℤ)+1)
    nlinarith
  · have hh : (j:ℤ)+1 ≤ i := by omega
    have hmult := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 2*(r:ℤ)+1)
    nlinarith

lemma finite_window_progression_indep (ν : Measure α) [IsProbabilityMeasure ν]
    {f : (ℤ → α) → ℝ} {r : ℕ} (hf : Measurable[coords (window r)] f) (a : ℤ) :
    Pairwise (fun i j : ℕ => IndepFun (fun x => f (shift (a+(2*(r:ℤ)+1)*i) x))
      (fun x => f (shift (a+(2*(r:ℤ)+1)*j) x)) (seqLaw ν)) := by
  intro i j hij
  have hfi := hf.comp (measurable_shift_coords (window r) (a+(2*(r:ℤ)+1)*i))
  have hfj := hf.comp (measurable_shift_coords (window r) (a+(2*(r:ℤ)+1)*j))
  exact indep_of_indep_of_le_right
    (indep_of_indep_of_le_left (indep_coords ν (window_disjoint r i j a hij)) hfi.comap_le) hfj.comap_le

lemma finite_window_progression_limit (ν : Measure α) [IsProbabilityMeasure ν]
    {f : (ℤ → α) → ℝ} {r : ℕ} (hf : Measurable[coords (window r)] f)
    (hint : Integrable f (seqLaw ν)) (a : ℤ) :
    ∀ᵐ x ∂seqLaw ν,Tendsto (fun q : ℕ =>
      (∑ i∈Finset.range q,f (shift (a+(2*(r:ℤ)+1)*i) x))/(q:ℝ)) atTop (𝓝 (∫ x,f x ∂seqLaw ν)) := by
  have hfm : Measurable f := hf.mono (coords_le _) le_rfl
  let X : ℕ → (ℤ → α) → ℝ := fun i x => f (shift (a+(2*(r:ℤ)+1)*i) x)
  have hident (i : ℕ) : IdentDistrib (X i) f (seqLaw ν) (seqLaw ν) :=
    by
    refine ⟨(hfm.comp (measurable_shift _)).aemeasurable,hfm.aemeasurable,?_⟩
    change Measure.map (f ∘ shift _) (seqLaw ν)=_
    rw [← Measure.map_map hfm (measurable_shift _),(shift_preserving ν _).map_eq]
  have hi : Integrable (X 0) (seqLaw ν) := (hident 0).integrable_iff.mpr hint
  have h := strong_law_ae_real X hi (finite_window_progression_indep ν hf a)
    (fun i => (hident i).trans (hident 0).symm)
  have he := (hident 0).integral_eq
  simpa only [he] using h

lemma finite_window_nonneg_limit (ν : Measure α) [IsProbabilityMeasure ν]
    {f : (ℤ → α) → ℝ} {r : ℕ} (hf : Measurable[coords (window r)] f)
    (hint : Integrable f (seqLaw ν)) (hn : ∀ x,0 ≤ f x) :
    ∀ᵐ x ∂seqLaw ν,Tendsto (fun n => average (shift 1) f n x) atTop
      (𝓝 (∫ x,f x ∂seqLaw ν)) := by
  have h := ae_all_iff.mpr (fun a : ℕ => finite_window_progression_limit ν hf hint (a:ℤ))
  filter_upwards [h] with x hx
  have hh := interlaced_nonneg_limit (f := fun i => f (shift (i:ℤ) x))
    (fun i => hn _) (2*r+1) (by omega) (∫ x,f x ∂seqLaw ν) (fun a _ => ?_)
  · simpa only [average,shift_iterate] using hh
  · simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat] using hx a

lemma finite_window_limit (ν : Measure α) [IsProbabilityMeasure ν]
    {f : (ℤ → α) → ℝ} {r : ℕ} (hf : Measurable[coords (window r)] f)
    (hint : Integrable f (seqLaw ν)) :
    ∀ᵐ x ∂seqLaw ν,Tendsto (fun n => average (shift 1) f n x) atTop
      (𝓝 (∫ x,f x ∂seqLaw ν)) := by
  let fp : (ℤ → α) → ℝ := fun x => max (f x) 0
  let fm : (ℤ → α) → ℝ := fun x => max (-f x) 0
  have hp : Integrable fp (seqLaw ν) := hint.sup (integrable_const 0)
  have hm : Integrable fm (seqLaw ν) := hint.neg.sup (integrable_const 0)
  have heq : (fun x => fp x-fm x)=f := by
    funext x
    dsimp [fp,fm]
    by_cases hx : 0 ≤ f x
    · rw [max_eq_left hx,max_eq_right (by linarith)]; ring
    · rw [max_eq_right (by linarith),max_eq_left (by linarith)]; ring
  have hmean : (∫ x,fp x ∂seqLaw ν)-(∫ x,fm x ∂seqLaw ν)=∫ x,f x ∂seqLaw ν := by
    rw [← integral_sub hp hm,heq]
  filter_upwards [finite_window_nonneg_limit ν (hf.max measurable_const) hp (fun _ => le_max_right _ _),
    finite_window_nonneg_limit ν (hf.neg.max measurable_const) hm (fun _ => le_max_right _ _)] with x hxp hxm
  change Tendsto (fun n => average (shift 1) fp n x) atTop (𝓝 (∫ x,fp x ∂seqLaw ν)) at hxp
  change Tendsto (fun n => average (shift 1) fm n x) atTop (𝓝 (∫ x,fm x ∂seqLaw ν)) at hxm
  have hh := hxp.sub hxm
  simpa only [← average_sub,heq,hmean] using hh

def windowFiltration : Filtration ℕ (inferInstance : MeasurableSpace (ℤ → α)) where
  seq r := coords (window r)
  mono' _ _ h := coords_mono (window_mono h)
  le' _ := coords_le _

lemma windowFiltration_sup : (⨆ r,windowFiltration (α := α) r)=(inferInstance : MeasurableSpace (ℤ → α)) := by
  apply le_antisymm (iSup_le (fun r => (windowFiltration (α := α)).le r))
  change (⨆ k : ℤ,MeasurableSpace.comap (fun x : ℤ → α => x k) inferInstance) ≤ _
  apply iSup_le
  intro k
  apply le_iSup_of_le k.natAbs
  change _ ≤ coords (window k.natAbs)
  exact le_iSup_of_le k (le_iSup_of_le ⟨by simpa using neg_le_neg (@Int.le_natAbs (-k)),Int.le_natAbs⟩ le_rfl)

end FKCRT.Stationary
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Stationary
variable {α : Type*} [MeasurableSpace α]

/-- Stationary averages of any integrable observation of a two-sided iid
sequence, not just cylinder observations. -/
theorem iid_shift_strong_law (ν : Measure α) [IsProbabilityMeasure ν]
    {f : (ℤ → α) → ℝ} (hf : Measurable f) (hint : Integrable f (seqLaw ν)) :
    ∀ᵐ x ∂seqLaw ν,Tendsto (fun n => average (shift 1) f n x) atTop
      (𝓝 (∫ x,f x ∂seqLaw ν)) := by
  let μ := seqLaw ν
  let g : ℕ → (ℤ → α) → ℝ := fun r => μ[f | windowFiltration r]
  have hg (r : ℕ) : Integrable (g r) μ := integrable_condExp
  have hmg (r : ℕ) : Measurable[coords (window r)] (g r) := stronglyMeasurable_condExp.measurable
  have ht : Tendsto (fun r => eLpNorm (g r-f) 1 μ) atTop (𝓝 0) := by
    apply hint.tendsto_eLpNorm_condExp (ℱ := windowFiltration)
    rw [windowFiltration_sup]
    exact hf.stronglyMeasurable
  have he (r : ℕ) : (∫ x,|f x-g r x| ∂μ)=(eLpNorm (g r-f) 1 μ).toReal := by
    rw [eLpNorm_one_eq_lintegral_enorm ((hg r).sub hint).aestronglyMeasurable]
    simpa only [Pi.sub_apply,Real.norm_eq_abs,abs_sub_comm] using
      integral_norm_eq_lintegral_enorm ((hg r).sub hint).aestronglyMeasurable
  have happ : Tendsto (fun r => ∫ x,|f x-g r x| ∂μ) atTop (𝓝 0) := by
    simpa only [he,ENNReal.toReal_zero,Function.comp_def] using
      (ENNReal.tendsto_toReal (by simp : (0:ℝ≥0∞)≠⊤)).comp ht
  apply ae_average_limit_of_L1_approx (μ := μ) (g := g)
    (a := fun _ => ∫ x,f x ∂μ) (shift_preserving ν 1) hint hf hg
    (fun r => (hmg r).mono (coords_le _) le_rfl) happ tendsto_const_nhds
  intro r
  have hh := finite_window_limit ν (hmg r) (hg r)
  have hi : (∫ x,g r x ∂μ)=∫ x,f x ∂μ := integral_condExp (windowFiltration.le r)
  change ∀ᵐ x ∂μ,Tendsto (fun n => average (shift 1) (g r) n x) atTop (𝓝 (∫ x,g r x ∂μ)) at hh
  simpa only [hi] using hh

def reflect (x : ℤ → α) : ℤ → α := fun k => x (-k)
lemma measurable_reflect : Measurable (reflect (α := α)) :=
  Measurable.of_eval (fun index => measurable_pi_apply (-index))
lemma reflect_preserving (ν : Measure α) [IsProbabilityMeasure ν] :
    MeasurePreserving reflect (seqLaw ν) (seqLaw ν) :=
  ⟨measurable_reflect,Measure.map_infinitePi_infinitePi_of_inj neg_injective⟩
omit [MeasurableSpace α] in
lemma reflected_shift_iterate (n : ℕ) (x : ℤ → α) :
    reflect ((shift 1)^[n] (reflect x))=(shift (-1))^[n] x := by
  induction n with
  | zero => ext k; simp [reflect]
  | succ n ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
    have hh (y : ℤ → α) : reflect (shift 1 y)=shift (-1) (reflect y) := by
      ext k; simp [reflect,shift]; congr 1; omega
    rw [hh,ih]

theorem iid_reverse_shift_strong_law (ν : Measure α) [IsProbabilityMeasure ν]
    {f : (ℤ → α) → ℝ} (hf : Measurable f) (hint : Integrable f (seqLaw ν)) :
    ∀ᵐ x ∂seqLaw ν,Tendsto (fun n => average (shift (-1)) f n x) atTop
      (𝓝 (∫ x,f x ∂seqLaw ν)) := by
  have hid : IdentDistrib (f ∘ reflect) f (seqLaw ν) (seqLaw ν) := by
    refine ⟨(hf.comp measurable_reflect).aemeasurable,hf.aemeasurable,?_⟩
    rw [← Measure.map_map hf measurable_reflect,(reflect_preserving ν).map_eq]
  have h := iid_shift_strong_law ν (hf.comp measurable_reflect) (hid.integrable_iff.mpr hint)
  have hh := (reflect_preserving ν).quasiMeasurePreserving.ae h
  filter_upwards [hh] with x hx
  have hi : (∫ x,f (reflect x) ∂seqLaw ν)=∫ x,f x ∂seqLaw ν := hid.integral_eq
  simpa only [average,Function.comp_apply,reflected_shift_iterate,hi] using hx

end FKCRT.Stationary
end

end OAI
