import OAI.Probability.FKMaps.WordLaw

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

def revealed (x : ℕ → Letter) (n : ℕ) : List Letter :=
  (List.ofFn (fun i : Fin n => x i)).reverse

lemma revealed_zero (x : ℕ → Letter) : revealed x 0=[] := by simp [revealed]
lemma revealed_succ (x : ℕ → Letter) (n : ℕ) :
    revealed x (n+1)=x n::revealed x n := by
  unfold revealed
  rw [List.ofFn_succ']
  simp only [List.concat_eq_append,List.reverse_concat,Fin.val_last,Fin.val_castSucc]

lemma revealed_sum (x : ℕ → Letter) (n : ℕ) :
    ((revealed x n).map Letter.increment).sum=signSum x n := by
  simp only [revealed,List.map_reverse,List.sum_reverse,List.map_ofFn,List.sum_ofFn]
  exact Fin.sum_univ_eq_sum_range (fun i => (x i).increment) n

lemma survivor_mono (x : ℕ → Letter) {n m : ℕ} (hnm : n ≤ m)
    (hn : (reduce (revealed x n)).burgers ≠ []) :
    (reduce (revealed x m)).burgers ≠ [] := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hnm
  clear hnm
  induction k with
  | zero => simpa using hn
  | succ k ih =>
    rw [show n+(k+1)=n+k+1 by omega,revealed_succ]
    cases h : (reduce (revealed x (n+k))).burgers with
    | nil => exact (ih h).elim
    | cons b bs =>
      have hh := freshest_survivor_prepend (revealed x (n+k)) [x (n+k)] h
      intro hz
      simp only [List.singleton_append,hz,List.head?_nil] at hh
      contradiction

def rawFiltration : Filtration ℕ (inferInstance : MeasurableSpace (ℕ → Letter)) :=
  Filtration.natural (fun n x => x n) (fun n => (measurable_pi_apply n).stronglyMeasurable)

lemma raw_adapted (n k : ℕ) (hk : k ≤ n) :
    Measurable[rawFiltration n] (fun x : ℕ → Letter => x k) := by
  exact ((Filtration.stronglyAdapted_natural
    (fun j : ℕ => (measurable_pi_apply j).stronglyMeasurable)) k).measurable.mono
      (rawFiltration.mono hk) le_rfl

lemma prefix_measurable {β : Type*} [MeasurableSpace β] (n : ℕ)
    (f : (Fin (n+1) → Letter) → β) :
    Measurable[rawFiltration n] (fun x => f (fun i => x i)) := by
  let : MeasurableSpace (ℕ → Letter) := rawFiltration n
  exact (measurable_of_countable f).comp
    (Measurable.of_eval fun index => raw_adapted n index (by omega))

lemma signSum_adapted : StronglyAdapted rawFiltration
    (fun n x => (signSum x (n+1):ℝ)) := by
  intro n
  have hh := prefix_measurable n (fun y => ((∑ i:Fin (n+1),(y i).increment:ℤ):ℝ))
  convert hh.stronglyMeasurable using 1
  ext x
  exact congrArg (fun z : ℤ => (z:ℝ))
    (Fin.sum_univ_eq_sum_range (fun i => (x i).increment) (n+1)).symm

lemma raw_sign_martingale (P : Parameters) :
    Martingale (fun n x => (signSum x (n+1):ℝ)) rawFiltration (streamLaw P ℕ) := by
  have hi (n : ℕ) : Integrable (fun x : ℕ → Letter => ((x n).increment:ℝ)) (streamLaw P ℕ) := by
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ => (law P).toMeasure) n).integrable_comp_of_integrable
      (integrableOn_univ.mp (IntegrableOn.of_finite (Set.finite_univ) :
        IntegrableOn (fun a : Letter => (a.increment:ℝ)) Set.univ (law P).toMeasure))
  have hint (n : ℕ) : Integrable (fun x => (signSum x (n+1):ℝ)) (streamLaw P ℕ) := by
    simp only [signSum,Int.cast_sum]
    exact integrable_finsetSum _ (fun k _ => hi k)
  apply martingale_nat signSum_adapted hint
  intro n
  have hind : Indep (MeasurableSpace.comap (fun x : ℕ → Letter => x (n+1)) inferInstance)
      (rawFiltration n) (streamLaw P ℕ) := by
    have h := indep_iSup_of_disjoint
      (fun k : ℕ => (measurable_pi_apply k : Measurable (fun x : ℕ → Letter => x k)).comap_le)
      (iIndepFun_infinitePi (P := fun _ : ℕ => (law P).toMeasure) (X := fun _ (a : Letter) => a) (fun _ => measurable_id))
      (show Disjoint ({n+1} : Set ℕ) {k | k ≤ n} by simp)
    simpa only [iSup_singleton,rawFiltration,Filtration.natural,Set.mem_ofPred_eq,streamLaw] using h
  have hc := condExp_indep_eq
    (measurable_pi_apply (n+1) : Measurable (fun x : ℕ → Letter => x (n+1))).comap_le
    (rawFiltration.le n)
    (((measurable_of_countable (fun a : Letter => (a.increment:ℝ))).comp
      (comap_measurable (fun x : ℕ → Letter => x (n+1)))).stronglyMeasurable) hind
  change (streamLaw P ℕ)[(fun x => ((x (n+1)).increment:ℝ)) | rawFiltration n] =ᵐ[streamLaw P ℕ]
    (fun _ => ∫ x,((x (n+1)).increment:ℝ) ∂streamLaw P ℕ) at hc
  have hz : ∫ x,((x (n+1)).increment:ℝ) ∂streamLaw P ℕ=0 := by
    exact ((measurePreserving_eval_infinitePi (fun _ : ℕ => (law P).toMeasure) (n+1)).hasLaw.integral_comp
      (f := fun a : Letter => (a.increment:ℝ)) (measurable_of_countable _).aestronglyMeasurable).trans
      (integral_increment P)
  have he : (fun x => (signSum x (n+1+1):ℝ))=
      (fun x => (signSum x (n+1):ℝ))+(fun x => ((x (n+1)).increment:ℝ)) := by
    ext x; simp only [signSum_succ,Int.cast_add,Pi.add_apply]
  rw [he]
  filter_upwards [condExp_add (hint n) (hi (n+1)) (rawFiltration n),hc] with x hsum hx
  rw [condExp_of_stronglyMeasurable (rawFiltration.le n) (signSum_adapted n) (hint n),
    Pi.add_apply,hx,hz,add_zero] at hsum
  exact hsum.symm

def survivorFlag (n : ℕ) (x : ℕ → Letter) : ℤ :=
  if (reduce (revealed x (n+1))).burgers=[] then 1 else 0

def firstSurvivor (x : ℕ → Letter) : WithTop ℕ := TreeCoding.firstZero survivorFlag x

lemma survivorFlag_adapted : StronglyAdapted rawFiltration survivorFlag := by
  intro n
  exact (prefix_measurable n (fun y => if (reduce (List.ofFn y).reverse).burgers=[] then (1:ℤ) else 0)).stronglyMeasurable

lemma firstSurvivor_stopping : IsStoppingTime rawFiltration firstSurvivor :=
  TreeCoding.firstZero_isStoppingTime survivorFlag_adapted

lemma firstSurvivor_le_iff (x : ℕ → Letter) (n : ℕ) :
    firstSurvivor x ≤ (WithTop.some n) ↔ (reduce (revealed x (n+1))).burgers ≠ [] := by
  change TreeCoding.firstZero survivorFlag x ≤ WithTop.some n ↔ _
  rw [TreeCoding.firstZero_le_iff]
  constructor
  · rintro ⟨k,hk,h⟩
    have hh : (reduce (revealed x (k+1))).burgers ≠ [] := by
      simpa [survivorFlag] using h
    exact survivor_mono x (by omega) hh
  · intro h
    exact ⟨n,le_rfl,by simp [survivorFlag,h]⟩

lemma firstSurvivor_finite (P : Parameters) :
    ∀ᵐ x ∂streamLaw P ℕ, firstSurvivor x ≠ ⊤ := by
  filter_upwards [signs_hit_one P] with x hx
  obtain ⟨n,hn⟩ := hx
  have hb : (reduce (revealed x n)).burgers ≠ [] :=
    survivor_of_sum_pos _ (by rw [revealed_sum,hn]; norm_num)
  have hle := (firstSurvivor_le_iff x n).mpr (survivor_mono x (by omega) hb)
  exact ne_top_of_le_ne_top WithTop.coe_ne_top hle

lemma firstSurvivor_shape {x : ℕ → Letter} {n : ℕ}
    (h : firstSurvivor x=(WithTop.some n)) :
    ∃ b, reduce (revealed x (n+1))=⟨(reduce (revealed x n)).orders,[b]⟩ ∧
      ∀ o∈(reduce (revealed x n)).orders,o=some (!b) := by
  have h₁ := (firstSurvivor_le_iff x n).mp (by rw [h])
  have h₀ : (reduce (revealed x n)).burgers=[] := by
    cases n with
    | zero => simp [revealed_zero,reduce,run]
    | succ n =>
      by_contra hn
      have hle := (firstSurvivor_le_iff x n).mpr hn
      rw [h] at hle
      have hh : n+1 ≤ n := WithTop.coe_le_coe.mp hle
      omega
  rw [revealed_succ] at h₁ ⊢
  obtain ⟨b,_,hb,ho⟩ := first_survivor_shape (x n) (revealed x n) h₀ h₁
  exact ⟨b,hb,ho⟩

def stoppedDefect (n : ℕ) (x : ℕ → Letter) : ℝ :=
  stoppedProcess (fun k x => 1-(signSum x (k+1):ℝ)) firstSurvivor n x

lemma stoppedDefect_martingale (P : Parameters) :
    Martingale stoppedDefect rawFiltration (streamLaw P ℕ) := by
  exact TreeCoding.martingale_stoppedProcess_real
    ((martingale_const rawFiltration (streamLaw P ℕ) (1:ℝ)).sub (raw_sign_martingale P))
    firstSurvivor_stopping

lemma stoppedDefect_nonneg (n : ℕ) (x : ℕ → Letter) : 0 ≤ stoppedDefect n x := by
  by_cases h : firstSurvivor x ≤ (WithTop.some n)
  · obtain ⟨k,hk⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_le_ne_top WithTop.coe_ne_top h)
    have hk' : firstSurvivor x=(WithTop.some k) := hk.symm
    obtain ⟨b,hb,_⟩ := firstSurvivor_shape hk'
    have hs := reduce_imbalance (revealed x (k+1))
    rw [hb,imbalance,revealed_sum] at hs
    simp only [List.length_singleton,Nat.cast_one] at hs
    change 0 ≤ 1-(signSum x ((min (WithTop.some n) (firstSurvivor x)).untopA+1):ℝ)
    rw [min_eq_right h,hk',WithTop.untopA_eq_untop WithTop.coe_ne_top,WithTop.untop_coe]
    have hr : (signSum x (k+1):ℝ)=1-(((reduce (revealed x (k+1))).orders.length):ℝ) := by
      rw [hb]
      exact_mod_cast hs.symm
    rw [hr]
    linarith [Nat.cast_nonneg (α := ℝ) ((reduce (revealed x (k+1))).orders.length)]
  · have hb : (reduce (revealed x (n+1))).burgers=[] := by
      by_contra hn
      exact h ((firstSurvivor_le_iff x n).mpr hn)
    have hs := reduce_imbalance (revealed x (n+1))
    rw [imbalance,hb,revealed_sum] at hs
    simp only [List.length_nil,Nat.cast_zero,zero_sub] at hs
    change 0 ≤ 1-(signSum x ((min (WithTop.some n) (firstSurvivor x)).untopA+1):ℝ)
    rw [min_eq_left (le_of_not_ge h),WithTop.untopA_eq_untop WithTop.coe_ne_top,WithTop.untop_coe]
    have hr : (signSum x (n+1):ℝ) ≤ 0 := by exact_mod_cast (by omega : signSum x (n+1) ≤ 0)
    linarith

lemma stoppedDefect_integral (P : Parameters) (n : ℕ) :
    ∫ x,stoppedDefect n x ∂streamLaw P ℕ=1 := by
  have he := (stoppedDefect_martingale P).setIntegral_eq (Nat.zero_le n) MeasurableSet.univ
  simp only [Measure.restrict_univ] at he
  rw [← he]
  have he0 : stoppedDefect 0=fun x => 1-((x 0).increment:ℝ) := by
    ext x
    simp [stoppedDefect,stoppedProcess,signSum]
  have hi : Integrable (fun x : ℕ → Letter => ((x 0).increment:ℝ)) (streamLaw P ℕ) := by
    simpa [signSum] using (raw_sign_martingale P).integrable 0
  rw [he0,integral_sub (integrable_const _) hi]
  have hz := ((measurePreserving_eval_infinitePi (fun _ : ℕ => (law P).toMeasure) 0).hasLaw.integral_comp
    (f := fun a : Letter => (a.increment:ℝ)) (measurable_of_countable _).aestronglyMeasurable).trans
    (integral_increment P)
  change ∫ x,((x 0).increment:ℝ) ∂streamLaw P ℕ=0 at hz
  simp only [integral_const,probReal_univ,one_smul,hz,sub_zero]

lemma measurableSet_firstSurvivor_eq (n : ℕ) :
    MeasurableSet {x | firstSurvivor x=WithTop.some n} :=
  rawFiltration.le n _ (firstSurvivor_stopping.measurableSet_eq n)

lemma measurableSet_firstSurvivor_finite : MeasurableSet {x | firstSurvivor x ≠ ⊤} := by
  have he : {x | firstSurvivor x ≠ ⊤}=⋃ n : ℕ,{x | firstSurvivor x=WithTop.some n} := by
    ext x
    simp only [Set.mem_ofPred_eq,Set.mem_iUnion]
    exact WithTop.ne_top_iff_exists.trans (by simp only [eq_comm])
  rw [he]
  exact MeasurableSet.iUnion measurableSet_firstSurvivor_eq

lemma measurable_firstSurvivor : Measurable firstSurvivor := by
  apply measurable_to_countable'
  intro n
  obtain rfl | ⟨n,rfl⟩ := eq_or_ne n ⊤ |>.imp_right (fun h => WithTop.ne_top_iff_exists.mp h)
  · convert measurableSet_firstSurvivor_finite.compl using 1
    ext x
    simp
  · exact measurableSet_firstSurvivor_eq n

def K (x : ℕ → Letter) : ℕ :=
  if firstSurvivor x=⊤ then 0 else
    (reduce (revealed x ((firstSurvivor x).untopD 0+1))).orders.length

lemma K_of_hit {x : ℕ → Letter} {n : ℕ} (h : firstSurvivor x=WithTop.some n) :
    K x=(reduce (revealed x (n+1))).orders.length := by
  simp only [K,h,WithTop.coe_ne_top,ite_false]
  rfl

lemma measurable_K : Measurable K := by
  have hm (n : ℕ) : Measurable (fun x : ℕ → Letter => (reduce (revealed x (n+1))).orders.length) :=
    (prefix_measurable n (fun y => (reduce (List.ofFn y).reverse).orders.length)).mono
      (rawFiltration.le n) le_rfl
  have hp : Measurable (fun x : ℕ → Letter =>
      (reduce (revealed x ((firstSurvivor x).untopD 0+1))).orders.length) :=
    (measurable_from_prod_countable_right (f := fun z : ℕ × (ℕ → Letter) =>
      (reduce (revealed z.2 (z.1+1))).orders.length) hm).comp
      (((measurable_of_countable (fun n : WithTop ℕ => n.untopD 0)).comp measurable_firstSurvivor).prodMk measurable_id)
  exact measurable_const.ite (measurableSet_eq_fun measurable_firstSurvivor measurable_const) hp

lemma stoppedDefect_eq_K {n : ℕ} {x : ℕ → Letter}
    (h : firstSurvivor x ≤ WithTop.some n) : stoppedDefect n x=K x := by
  obtain ⟨k,hk⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_le_ne_top WithTop.coe_ne_top h)
  have hk' : firstSurvivor x=WithTop.some k := hk.symm
  obtain ⟨b,hb,_⟩ := firstSurvivor_shape hk'
  have hs := reduce_imbalance (revealed x (k+1))
  rw [hb,imbalance,revealed_sum] at hs
  simp only [List.length_singleton,Nat.cast_one] at hs
  change 1-(signSum x ((min (WithTop.some n) (firstSurvivor x)).untopA+1):ℝ)=(K x:ℝ)
  rw [min_eq_right h,hk',WithTop.untopA_eq_untop WithTop.coe_ne_top,WithTop.untop_coe,K_of_hit hk',hb]
  dsimp only
  have hr : (signSum x (k+1):ℝ)=1-(((reduce (revealed x k)).orders.length):ℝ) := by
    exact_mod_cast hs.symm
  rw [hr]
  ring

lemma stoppedDefect_tendsto (P : Parameters) :
    ∀ᵐ x ∂streamLaw P ℕ,Tendsto (fun n => stoppedDefect n x) atTop (𝓝 (K x:ℝ)) := by
  filter_upwards [firstSurvivor_finite P] with x hx
  obtain ⟨k,hk⟩ := WithTop.ne_top_iff_exists.mp hx
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop k] with n hn
  exact (stoppedDefect_eq_K (by rw [← hk]; exact WithTop.coe_le_coe.mpr hn)).symm

/-- The source first optional-stopping bound, without any finite-mean
hypothesis on the stopping time. -/
theorem K_lintegral_le_one (P : Parameters) :
    ∫⁻ x,ENNReal.ofReal (K x:ℝ) ∂streamLaw P ℕ ≤ 1 := by
  have hm (n : ℕ) : Measurable (fun x => ENNReal.ofReal (stoppedDefect n x)) :=
    (((stoppedDefect_martingale P).stronglyMeasurable n).measurable.mono (rawFiltration.le n) le_rfl).ennreal_ofReal
  have hb (n : ℕ) : ∫⁻ x,ENNReal.ofReal (stoppedDefect n x) ∂streamLaw P ℕ=1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal ((stoppedDefect_martingale P).integrable n)
      (Filter.Eventually.of_forall (stoppedDefect_nonneg n)),stoppedDefect_integral]
    simp
  have he : (fun x => ENNReal.ofReal (K x:ℝ)) =ᵐ[streamLaw P ℕ]
      (fun x => liminf (fun n => ENNReal.ofReal (stoppedDefect n x)) atTop) := by
    filter_upwards [stoppedDefect_tendsto P] with x hx
    exact (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hx).liminf_eq.symm
  rw [lintegral_congr_ae he]
  exact (lintegral_liminf_le hm).trans_eq (by simp only [hb,liminf_const])

theorem integrable_K (P : Parameters) : Integrable (fun x => (K x:ℝ)) (streamLaw P ℕ) := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    ((measurable_of_countable (fun k : ℕ => (k:ℝ))).comp measurable_K).aestronglyMeasurable (Filter.Eventually.of_forall (fun x => Nat.cast_nonneg (K x)))).mp
  exact ne_top_of_le_ne_top (by norm_num) (K_lintegral_le_one P)

theorem integral_K_le_one (P : Parameters) : ∫ x,(K x:ℝ) ∂streamLaw P ℕ ≤ 1 := by
  have h := K_lintegral_le_one P
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_K P)
    (Filter.Eventually.of_forall (fun x => Nat.cast_nonneg (K x)))] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp (by simpa using h)

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

def typeSign (b : Bool) : ℤ := if b then 1 else -1
lemma typeSign_not (b : Bool) : typeSign (!b)= -typeSign b := by cases b <;> norm_num [typeSign]
lemma abs_typeSign (b : Bool) : |typeSign b|=1 := by cases b <;> norm_num [typeSign]
lemma typeSign_sq (b : Bool) : typeSign b^2=1 := by cases b <;> norm_num [typeSign]

def orderType (o : Order) (t : Bool) : Bool := o.getD t

def assignedSign (a : Letter × Bool) : ℤ := match a.1 with
  | .burger b => typeSign b
  | .order o => -typeSign (orderType o a.2)

lemma abs_assignedSign (a : Letter × Bool) : |assignedSign a|=1 := by
  rcases a with ⟨a,t⟩
  cases a <;> simp [assignedSign,abs_typeSign]

structure TypedEvaluation where
  orders : List (Order × Bool)
  burgers : List Bool

def TypedEvaluation.erase (e : TypedEvaluation) : Evaluation :=
  ⟨e.orders.map Prod.fst,e.burgers⟩

def typedStep (e : TypedEvaluation) (a : Letter × Bool) : TypedEvaluation := match a.1 with
  | .burger b => ⟨e.orders,b::e.burgers⟩
  | .order o => match pop o e.burgers with
    | some bs => ⟨e.orders,bs⟩
    | none => ⟨e.orders++[(o,a.2)],e.burgers⟩

def typedRun : List (Letter × Bool) → TypedEvaluation → TypedEvaluation
  | [],e => e
  | a::w,e => typedRun w (typedStep e a)

def validStep (s : List Bool) (a : Letter × Bool) : Prop :=
  a.1=.order none → (s=[] ∨ s.head?=some a.2)

def ValidTyping : List (Letter × Bool) → List Bool → Prop
  | [],_ => True
  | a::w,s => validStep s a ∧ ValidTyping w (step ⟨[],s⟩ a.1).burgers

lemma erase_typedStep (e : TypedEvaluation) (a : Letter × Bool) :
    (typedStep e a).erase=step e.erase a.1 := by
  rcases a with ⟨a,t⟩
  cases a with
  | burger b => rfl
  | order o =>
    simp only [typedStep,step,TypedEvaluation.erase]
    cases pop o e.burgers <;> simp

lemma erase_typedRun (w : List (Letter × Bool)) (e : TypedEvaluation) :
    (typedRun w e).erase=run (w.map Prod.fst) e.erase := by
  induction w generalizing e with
  | nil => rfl
  | cons a w ih => simp only [typedRun,ih,erase_typedStep,List.map_cons,run]

lemma typedStep_burgers (e : TypedEvaluation) (a : Letter × Bool) :
    (typedStep e a).burgers=(step ⟨[],e.burgers⟩ a.1).burgers := by
  rcases a with ⟨a,t⟩
  cases a with
  | burger b => rfl
  | order o => simp only [typedStep,step]; cases pop o e.burgers <;> rfl

lemma pop_sign_sum {o : Order} {s s' : List Bool} {t : Bool}
    (h : pop o s=some s') (ht : o=none → s=[] ∨ s.head?=some t) :
    (s.map typeSign).sum=(s'.map typeSign).sum+typeSign (orderType o t) := by
  induction s generalizing s' with
  | nil => simp [pop] at h
  | cons b bs ih =>
    simp only [pop] at h
    split_ifs at h with he
    · simp only [Option.some.injEq] at h
      subst s'
      have hb : orderType o t=b := by
        obtain rfl | ho := he
        · obtain hf | hb := ht rfl
          · simp at hf
          · simpa [orderType] using (Option.some.inj (by simpa using hb)).symm
        · simp [orderType,ho]
      simp only [List.map_cons,List.sum_cons,hb]
      omega
    · cases hp : pop o bs with
      | none => simp [hp] at h
      | some cs =>
        simp only [hp,Option.map_some,Option.some.injEq] at h
        subst s'
        have hnone : o ≠ none := fun ho => he (Or.inl ho)
        have hh := ih hp (fun ho => (hnone ho).elim)
        simp only [List.map_cons,List.sum_cons]
        omega

def typedImbalance (e : TypedEvaluation) : ℤ :=
  (e.burgers.map typeSign).sum-(e.orders.map (fun o => typeSign (orderType o.1 o.2))).sum

lemma typedStep_imbalance (e : TypedEvaluation) (a : Letter × Bool)
    (h : validStep e.burgers a) :
    typedImbalance (typedStep e a)=typedImbalance e+assignedSign a := by
  rcases a with ⟨a,t⟩
  cases a with
  | burger b => simp [typedStep,typedImbalance,assignedSign]; ring
  | order o =>
    simp only [typedStep,assignedSign]
    cases hp : pop o e.burgers with
    | none => simp [typedImbalance]; ring
    | some bs =>
      have hh := pop_sign_sum hp (fun ho => h (by rw [ho]))
      simp only [typedImbalance]
      dsimp only at *
      omega

lemma typedRun_imbalance (w : List (Letter × Bool)) (e : TypedEvaluation)
    (h : ValidTyping w e.burgers) :
    typedImbalance (typedRun w e)=(w.map assignedSign).sum+typedImbalance e := by
  induction w generalizing e with
  | nil => simp [typedRun]
  | cons a w ih =>
    rw [typedRun,ih (typedStep e a) (by simpa only [typedStep_burgers] using h.2),typedStep_imbalance e a h.1]
    simp only [List.map_cons,List.sum_cons]
    omega

lemma sum_typeSign_abs_le (l : List Bool) : |(l.map typeSign).sum| ≤ l.length := by
  induction l with
  | nil => simp
  | cons b bs ih =>
    simpa only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one,abs_typeSign,add_comm]
      using (abs_add_le (typeSign b) (bs.map typeSign).sum).trans (add_le_add (le_of_eq (abs_typeSign b)) ih)

lemma typed_orders_sum_abs_le (l : List (Order × Bool)) :
    |(l.map (fun o => typeSign (orderType o.1 o.2))).sum| ≤ l.length := by
  simpa only [List.map_map,List.length_map,Function.comp_def] using
    sum_typeSign_abs_le (l.map (fun o => orderType o.1 o.2))

lemma typedRun_no_survivor_bound (w : List (Letter × Bool)) (h : ValidTyping w [])
    (h₀ : (reduce (w.map Prod.fst)).burgers=[]) :
    |(w.map assignedSign).sum| ≤ ((reduce (w.map Prod.fst)).orders.length:ℤ) := by
  let e := typedRun w ⟨[],[]⟩
  have he : e.erase=reduce (w.map Prod.fst) := erase_typedRun w ⟨[],[]⟩
  have hs : (w.map assignedSign).sum=typedImbalance e := by
    simpa [typedImbalance] using (typedRun_imbalance w ⟨[],[]⟩ h).symm
  have hb : e.burgers=[] := by
    rw [← h₀,← he]; rfl
  have hl : (reduce (w.map Prod.fst)).orders.length=e.orders.length := by
    rw [← he]; simp [TypedEvaluation.erase]
  rw [hl,hs,typedImbalance,hb]
  simpa using typed_orders_sum_abs_le e.orders

lemma typed_orders_opposite_sum (l : List (Order × Bool)) (b : Bool)
    (h : ∀ o∈l,o.1=some (!b)) :
    (l.map (fun o => typeSign (orderType o.1 o.2))).sum= -(l.length:ℤ)*typeSign b := by
  induction l with
  | nil => simp
  | cons o os ih =>
    rw [List.map_cons,List.sum_cons,ih (fun o ho => h o (by simp [ho]))]
    rw [show orderType o.1 o.2= !b by simp [orderType,h o (by simp)],typeSign_not]
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    ring

lemma typedRun_first_survivor_sum (w : List (Letter × Bool)) (b : Bool)
    (h : ValidTyping w []) (hb : (reduce (w.map Prod.fst)).burgers=[b])
    (ho : ∀ o∈(reduce (w.map Prod.fst)).orders,o=some (!b)) :
    (w.map assignedSign).sum=typeSign b*(1+((reduce (w.map Prod.fst)).orders.length:ℤ)) := by
  let e := typedRun w ⟨[],[]⟩
  have he : e.erase=reduce (w.map Prod.fst) := erase_typedRun w ⟨[],[]⟩
  have hs : (w.map assignedSign).sum=typedImbalance e := by
    simpa [typedImbalance] using (typedRun_imbalance w ⟨[],[]⟩ h).symm
  have hb' : e.burgers=[b] := by rw [← hb,← he]; rfl
  have ho' : ∀ o∈e.orders,o.1=some (!b) := by
    intro o hm
    apply ho o.1
    rw [← he]
    exact List.mem_map.mpr ⟨o,hm,rfl⟩
  have hl : (reduce (w.map Prod.fst)).orders.length=e.orders.length := by
    rw [← he]; simp [TypedEvaluation.erase]
  rw [hs,typedImbalance,hb',typed_orders_opposite_sum e.orders b ho',hl]
  simp only [List.map_singleton,List.sum_singleton]
  ring

lemma ValidTyping_append (w v : List (Letter × Bool)) (e : TypedEvaluation) :
    ValidTyping (w++v) e.burgers ↔ ValidTyping w e.burgers ∧ ValidTyping v (typedRun w e).burgers := by
  induction w generalizing e with
  | nil => simp [ValidTyping,typedRun]
  | cons a w ih =>
    simp only [List.cons_append,ValidTyping,typedRun]
    rw [← typedStep_burgers e a,ih]
    tauto

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

def Letter.flip : Letter → Letter
  | .burger b => .burger (!b)
  | .order o => .order (o.map Bool.not)

lemma Letter.flip_flip (a : Letter) : a.flip.flip=a := by
  cases a with
  | burger b => simp [Letter.flip]
  | order o => cases o <;> simp [Letter.flip]

lemma eligible_flip (o : Order) (b : Bool) : eligible (o.map Bool.not) (!b) ↔ eligible o b := by
  cases o with
  | none => simp [eligible]
  | some c => cases c <;> cases b <;> simp [eligible]

lemma pop_flip (o : Order) (s : List Bool) :
    pop (o.map Bool.not) (s.map Bool.not)=(pop o s).map (List.map Bool.not) := by
  induction s with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons,pop,eligible_flip]
    split_ifs <;> simp only [Option.map_some,ih,Option.map_map,Function.comp_def,List.map_cons]

def Evaluation.flip (e : Evaluation) : Evaluation :=
  ⟨e.orders.map (Option.map Bool.not),e.burgers.map Bool.not⟩

lemma step_flip (e : Evaluation) (a : Letter) : step e.flip a.flip=(step e a).flip := by
  cases a with
  | burger b => rfl
  | order o =>
    simp only [Letter.flip,Evaluation.flip,step,pop_flip]
    cases pop o e.burgers <;> simp

lemma run_flip (w : List Letter) (e : Evaluation) :
    run (w.map Letter.flip) e.flip=(run w e).flip := by
  induction w generalizing e with
  | nil => rfl
  | cons a w ih => simp only [List.map_cons,run,step_flip,ih]

lemma reduce_flip (w : List Letter) : reduce (w.map Letter.flip)=(reduce w).flip := by
  exact run_flip w ⟨[],[]⟩

lemma burgers_flip_empty_iff (w : List Letter) :
    (reduce (w.map Letter.flip)).burgers=[] ↔ (reduce w).burgers=[] := by
  simp [reduce_flip,Evaluation.flip]

end FKCRT.Inventory
end

end OAI
