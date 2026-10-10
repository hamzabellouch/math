import OAI.Probability.FKMaps.InventoryStopping

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

def tail (n : ℕ) (x : ℕ → Letter) : ℕ → Letter := fun k => x (n+k)
lemma tail_zero (x : ℕ → Letter) : tail 0 x=x := by ext k; simp [tail]
lemma tail_tail (m n : ℕ) (x : ℕ → Letter) : tail m (tail n x)=tail (n+m) x := by
  ext k; simp [tail,Nat.add_assoc]

lemma measurable_tail (n : ℕ) : Measurable (tail n) := by
  exact Measurable.of_eval fun index => measurable_pi_apply (n+index)

lemma tail_preserving (P : Parameters) (n : ℕ) : MeasurePreserving (tail n) (streamLaw P ℕ) (streamLaw P ℕ) := by
  refine ⟨measurable_tail n,?_⟩
  exact Measure.map_infinitePi_infinitePi_of_inj (fun a b h => Nat.add_left_cancel h)

lemma revealed_add (x : ℕ → Letter) (n k : ℕ) :
    revealed x (n+k)=revealed (tail n x) k++revealed x n := by
  induction k with
  | zero => simp [revealed_zero]
  | succ k ih =>
    rw [show n+(k+1)=n+k+1 by omega,revealed_succ,revealed_succ,ih]
    rfl

lemma revealed_append_newest (x : ℕ → Letter) (n : ℕ) :
    revealed x (n+1)=revealed (tail 1 x) n++[x 0] := by
  rw [show n+1=1+n by omega,revealed_add]
  simp [revealed_succ,revealed_zero]

lemma revealed_extension (x : ℕ → Letter) {n m : ℕ} (h : n ≤ m) :
    ∃ w,revealed x m=w++revealed x n := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le h
  exact ⟨revealed (tail n x) k,revealed_add x n k⟩

def firstType (x : ℕ → Letter) : Bool :=
  (reduce (revealed x ((firstSurvivor x).untopD 0+1))).burgers.headD false

lemma firstType_of_hit {x : ℕ → Letter} {n : ℕ} (h : firstSurvivor x=WithTop.some n) :
    firstType x=(reduce (revealed x (n+1))).burgers.headD false := by
  unfold firstType
  rw [h]
  rfl

lemma firstType_of_survivor {x : ℕ → Letter} {n : ℕ} {b : Bool} {bs : List Bool}
    (h : (reduce (revealed x n)).burgers=b::bs) : firstType x=b := by
  cases n with
  | zero => simp [revealed_zero,reduce,run] at h
  | succ n =>
    have hle : firstSurvivor x ≤ WithTop.some n :=
      (firstSurvivor_le_iff x n).mpr (by rw [h]; simp)
    obtain ⟨k,hk⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_le_ne_top WithTop.coe_ne_top hle)
    have hk' : firstSurvivor x=WithTop.some k := hk.symm
    obtain ⟨c,hc,_⟩ := firstSurvivor_shape hk'
    obtain ⟨w,hw⟩ := revealed_extension x (show k+1 ≤ n+1 from by
      rw [← hk] at hle; exact Nat.add_le_add_right (WithTop.coe_le_coe.mp hle) 1)
    have hp := freshest_survivor_prepend (revealed x (k+1)) w (congrArg Evaluation.burgers hc)
    rw [← hw,h] at hp
    simp only [List.head?_cons,Option.some.injEq] at hp
    rw [firstType_of_hit hk',hc]
    exact hp.symm

lemma measurable_firstType : Measurable firstType := by
  have hm (n : ℕ) : Measurable (fun x : ℕ → Letter =>
      (reduce (revealed x (n+1))).burgers.headD false) :=
    (prefix_measurable n (fun y => (reduce (List.ofFn y).reverse).burgers.headD false)).mono
      (rawFiltration.le n) le_rfl
  exact (measurable_from_prod_countable_right (f := fun z : ℕ × (ℕ → Letter) =>
      (reduce (revealed z.2 (z.1+1))).burgers.headD false) hm).comp
      (((measurable_of_countable (fun n : WithTop ℕ => n.untopD 0)).comp measurable_firstSurvivor).prodMk measurable_id)

def typedRevealed (x : ℕ → Letter) (n : ℕ) : List (Letter × Bool) :=
  (List.ofFn (fun i : Fin n => (x i,firstType (tail (i+1) x)))).reverse

lemma typedRevealed_erase (x : ℕ → Letter) (n : ℕ) :
    (typedRevealed x n).map Prod.fst=revealed x n := by
  simp [typedRevealed,revealed,List.map_reverse,List.map_ofFn,Function.comp_def]

lemma typedRevealed_append_newest (x : ℕ → Letter) (n : ℕ) :
    typedRevealed x (n+1)=typedRevealed (tail 1 x) n++[(x 0,firstType (tail 1 x))] := by
  unfold typedRevealed
  rw [List.ofFn_succ,List.reverse_cons]
  apply congrArg (· ++ [(x 0,firstType (tail 1 x))])
  apply congrArg List.reverse
  apply congrArg List.ofFn
  funext i
  apply Prod.ext
  · simp [FKCRT.Inventory.tail,Nat.add_comm]
  · change firstType (tail (i.val+1+1) x)=firstType (tail (i.val+1) (tail 1 x))
    rw [tail_tail]
    congr 2
    omega

lemma typedRevealed_valid (x : ℕ → Letter) (n : ℕ) : ValidTyping (typedRevealed x n) [] := by
  induction n generalizing x with
  | zero => simp [typedRevealed,ValidTyping]
  | succ n ih =>
    rw [typedRevealed_append_newest]
    apply (ValidTyping_append _ _ ⟨[],[]⟩).mpr
    refine ⟨ih _,?_,trivial⟩
    intro ha
    have he := congrArg Evaluation.burgers (erase_typedRun (typedRevealed (tail 1 x) n) ⟨[],[]⟩)
    rw [typedRevealed_erase] at he
    change (typedRun (typedRevealed (tail 1 x) n) ⟨[],[]⟩).burgers=
      (reduce (revealed (tail 1 x) n)).burgers at he
    rw [he]
    cases hb : (reduce (revealed (tail 1 x) n)).burgers with
    | nil => exact Or.inl rfl
    | cons b bs =>
      right
      simp only [List.head?_cons,Option.some.injEq]
      exact (firstType_of_survivor hb).symm

def D (x : ℕ → Letter) (n : ℕ) : ℤ := assignedSign (x n,firstType (tail (n+1) x))
def Dsum (x : ℕ → Letter) (n : ℕ) : ℤ := ∑ i∈Finset.range n,D x i

lemma abs_D (x : ℕ → Letter) (n : ℕ) : |D x n|=1 := abs_assignedSign _
lemma measurable_D (n : ℕ) : Measurable (fun x => D x n) :=
  (measurable_of_countable assignedSign).comp
    ((measurable_pi_apply n).prodMk (measurable_firstType.comp (measurable_tail (n+1))))
lemma measurable_Dsum (n : ℕ) : Measurable (fun x => Dsum x n) := by
  exact Finset.measurable_sum _ (fun i _ => measurable_D i)

lemma typedRevealed_sum (x : ℕ → Letter) (n : ℕ) :
    ((typedRevealed x n).map assignedSign).sum=Dsum x n := by
  simp only [typedRevealed,List.map_reverse,List.sum_reverse,List.map_ofFn,List.sum_ofFn]
  exact Fin.sum_univ_eq_sum_range (D x) n

lemma D_shift (x : ℕ → Letter) (n k : ℕ) : D (tail n x) k=D x (n+k) := by
  simp [D,tail_tail,tail,Nat.add_assoc]
lemma Dsum_add (x : ℕ → Letter) (n k : ℕ) : Dsum x (n+k)=Dsum x n+Dsum (tail n x) k := by
  simp only [Dsum,Finset.sum_range_add,D_shift]

lemma Dsum_no_survivor {x : ℕ → Letter} {n : ℕ} (h : (reduce (revealed x n)).burgers=[]) :
    |Dsum x n| ≤ -signSum x n := by
  have hh := typedRun_no_survivor_bound (typedRevealed x n) (typedRevealed_valid x n)
    (by rw [typedRevealed_erase]; exact h)
  rw [typedRevealed_sum,typedRevealed_erase] at hh
  have hs := reduce_imbalance (revealed x n)
  rw [imbalance,h,revealed_sum] at hs
  simp only [List.length_nil,Nat.cast_zero,zero_sub] at hs
  omega

lemma Dsum_at_hit {x : ℕ → Letter} {n : ℕ} (h : firstSurvivor x=WithTop.some n) :
    Dsum x (n+1)=typeSign (firstType x)*(1+(K x:ℤ)) := by
  obtain ⟨b,hb,ho⟩ := firstSurvivor_shape h
  have ht : firstType x=b := firstType_of_survivor (congrArg Evaluation.burgers hb)
  have hh := typedRun_first_survivor_sum (typedRevealed x (n+1)) b (typedRevealed_valid x (n+1))
    (by rw [typedRevealed_erase,hb])
    (by rw [typedRevealed_erase,hb]; exact ho)
  rw [typedRevealed_sum,typedRevealed_erase] at hh
  rw [ht,K_of_hit h]
  exact hh

lemma abs_Dsum_le (x : ℕ → Letter) (n : ℕ) : |Dsum x n| ≤ n := by
  unfold Dsum
  exact (Finset.abs_sum_le_sum_abs _ _).trans_eq (by simp [abs_D])

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

lemma law_flip_preserving (P : Parameters) :
    MeasurePreserving Letter.flip (law P).toMeasure (law P).toMeasure := by
  refine ⟨measurable_of_countable _,?_⟩
  apply Measure.ext_of_singleton
  intro a
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton a)]
  have he : Letter.flip ⁻¹' {a}={a.flip} := by
    ext b
    simp only [Set.mem_preimage,Set.mem_singleton_iff]
    constructor
    · intro h
      simpa only [Letter.flip_flip] using congrArg Letter.flip h
    · rintro rfl
      exact Letter.flip_flip _
  rw [he,law_singleton,law_singleton]
  congr 1
  cases a with
  | burger b => rfl
  | order o => cases o <;> rfl

def flipStream (x : ℕ → Letter) : ℕ → Letter := fun i => (x i).flip
lemma measurable_flipStream : Measurable flipStream := by
  exact Measurable.of_eval (fun index => (measurable_of_countable Letter.flip).comp (measurable_pi_apply index))
lemma flipStream_preserving (P : Parameters) :
    MeasurePreserving flipStream (streamLaw P ℕ) (streamLaw P ℕ) := by
  refine ⟨measurable_flipStream,?_⟩
  unfold streamLaw flipStream
  rw [Measure.infinitePi_map_pi (fun _ : ℕ => (law P).toMeasure) (fun _ => measurable_of_countable Letter.flip)]
  simp only [(law_flip_preserving P).map_eq]

lemma revealed_flip (x : ℕ → Letter) (n : ℕ) :
    revealed (flipStream x) n=(revealed x n).map Letter.flip := by
  simp [revealed,flipStream,List.map_reverse,List.map_ofFn,Function.comp_def]
lemma firstSurvivor_flip (x : ℕ → Letter) : firstSurvivor (flipStream x)=firstSurvivor x := by
  apply eq_of_forall_ge_iff
  intro n
  cases n with
  | top => simp
  | coe n =>
    rw [firstSurvivor_le_iff,firstSurvivor_le_iff,revealed_flip]
    exact not_congr (burgers_flip_empty_iff (revealed x (n+1)))

lemma firstType_flip_of_hit {x : ℕ → Letter} {n : ℕ} (h : firstSurvivor x=WithTop.some n) :
    firstType (flipStream x)= !(firstType x) := by
  obtain ⟨b,hb,_⟩ := firstSurvivor_shape h
  have hh : firstSurvivor (flipStream x)=WithTop.some n := by rw [firstSurvivor_flip,h]
  rw [firstType_of_hit hh,firstType_of_hit h,revealed_flip,reduce_flip,hb]
  rfl

lemma raw_indep_tail (P : Parameters) (n : ℕ) :
    Indep (rawFiltration n) (MeasurableSpace.comap (tail (n+1)) inferInstance) (streamLaw P ℕ) := by
  let m : ℕ → MeasurableSpace (ℕ → Letter) := fun k =>
    MeasurableSpace.comap (fun x : ℕ → Letter => x k) inferInstance
  have h := indep_iSup_of_disjoint
    (fun k : ℕ => (measurable_pi_apply k : Measurable (fun x : ℕ → Letter => x k)).comap_le)
    (iIndepFun_infinitePi (P := fun _ : ℕ => (law P).toMeasure) (X := fun _ (a : Letter) => a) (fun _ => measurable_id))
    (show Disjoint {k : ℕ | k ≤ n} {k : ℕ | n<k} by exact Set.disjoint_left.mpr (fun k hk hk' => by
      change k ≤ n at hk; change n<k at hk'; omega))
  have hm : Measurable[⨆ k∈{k : ℕ | n<k},m k] (tail (n+1)) := by
    let : MeasurableSpace (ℕ → Letter) := ⨆ k∈{k : ℕ | n<k},m k
    apply Measurable.of_eval
    intro k
    apply measurable_iff_comap_le.mpr
    exact le_iSup_of_le (n+1+k) (le_iSup_of_le (show n<n+1+k by omega) le_rfl)
  apply indep_of_indep_of_le_right _ hm.comap_le
  simpa only [rawFiltration,Filtration.natural,Set.mem_ofPred_eq,streamLaw] using h

lemma raw_fun_indep_tail (P : Parameters) (n : ℕ) {β : Type*} [MeasurableSpace β]
    {f : (ℕ → Letter) → β} (hf : Measurable[rawFiltration n] f) :
    IndepFun f (tail (n+1)) (streamLaw P ℕ) := by
  exact indep_of_indep_of_le_left (raw_indep_tail P n) hf.comap_le

lemma integrable_Dsum (P : Parameters) (n : ℕ) : Integrable (fun x => (Dsum x n:ℝ)) (streamLaw P ℕ) := by
  apply Integrable.of_bound
    (((measurable_of_countable (fun z : ℤ => (z:ℝ))).comp (measurable_Dsum n)).aestronglyMeasurable) n
  exact ae_of_all _ (fun x => by
    change |(Dsum x n:ℝ)| ≤ (n:ℝ)
    exact_mod_cast abs_Dsum_le x n)


/-- Signed first-survivor event. Unlike the totalized first type, this is raw-prefix measurable. -/
def hitType (n : ℕ) (x : ℕ → Letter) : ℝ :=
  if firstSurvivor x=WithTop.some n then (typeSign (firstType x):ℝ) else 0

lemma measurable_hitType_raw (n : ℕ) : Measurable[rawFiltration n] (hitType n) := by
  have he : hitType n=fun x => if firstSurvivor x=WithTop.some n then
      (typeSign ((reduce (revealed x (n+1))).burgers.headD false):ℝ) else 0 := by
    ext x
    unfold hitType
    split_ifs with h
    · rw [firstType_of_hit h]
    · rfl
  rw [he]
  apply Measurable.ite (firstSurvivor_stopping.measurableSet_eq n)
  · exact prefix_measurable n (fun y => (typeSign ((reduce (List.ofFn y).reverse).burgers.headD false):ℝ))
  · exact measurable_const
lemma measurable_hitType (n : ℕ) : Measurable (hitType n) :=
  (measurable_hitType_raw n).mono (rawFiltration.le n) le_rfl
lemma abs_hitType_le (n : ℕ) (x : ℕ → Letter) : |hitType n x| ≤ 1 := by
  unfold hitType
  split_ifs
  · simpa only [← Int.cast_abs,abs_typeSign,Int.cast_one] using (le_rfl : (1:ℝ) ≤ 1)
  · simp
lemma integrable_hitType (P : Parameters) (n : ℕ) : Integrable (hitType n) (streamLaw P ℕ) :=
  Integrable.of_bound (measurable_hitType n).aestronglyMeasurable 1 (ae_of_all _ fun x => by
    simpa only [Real.norm_eq_abs] using abs_hitType_le n x)
lemma hitType_flip (n : ℕ) (x : ℕ → Letter) : hitType n (flipStream x)= -hitType n x := by
  unfold hitType
  rw [firstSurvivor_flip]
  split_ifs with h
  · rw [firstType_flip_of_hit h,typeSign_not,Int.cast_neg]
  · simp
lemma integral_hitType (P : Parameters) (n : ℕ) : ∫ x,hitType n x ∂streamLaw P ℕ=0 := by
  have h := (flipStream_preserving P).hasLaw.integral_comp
    (f := hitType n) (measurable_hitType n).aestronglyMeasurable
  change (∫ x,hitType n (flipStream x) ∂streamLaw P ℕ)=∫ x,hitType n x ∂streamLaw P ℕ at h
  simp only [hitType_flip,integral_neg] at h
  linarith
lemma integral_hitType_mul_older (P : Parameters) (n k : ℕ) :
    ∫ x,hitType n x*(Dsum (tail (n+1) x) k:ℝ) ∂streamLaw P ℕ=0 := by
  have h := (raw_fun_indep_tail P n (measurable_hitType_raw n)).comp measurable_id
    ((measurable_of_countable (fun z : ℤ => (z:ℝ))).comp (measurable_Dsum k))
  have hh := h.integral_mul_eq_mul_integral (integrable_hitType P n).aestronglyMeasurable
    ((tail_preserving P (n+1)).integrable_comp_of_integrable (integrable_Dsum P k)).aestronglyMeasurable
  change (∫ x,hitType n x*(Dsum (tail (n+1) x) k:ℝ) ∂streamLaw P ℕ)=
    (∫ x,hitType n x ∂streamLaw P ℕ)*(∫ x,(Dsum (tail (n+1) x) k:ℝ) ∂streamLaw P ℕ) at hh
  rw [integral_hitType,zero_mul] at hh
  exact hh


end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

def T (x : ℕ → Letter) : ℝ := typeSign (firstType x)
lemma measurable_T : Measurable T :=
  (measurable_of_countable (fun b : Bool => (typeSign b:ℝ))).comp measurable_firstType
lemma abs_T (x : ℕ → Letter) : |T x|=1 := by
  unfold T
  exact_mod_cast abs_typeSign (firstType x)
lemma T_sq (x : ℕ → Letter) : T x^2=1 := by
  unfold T
  exact_mod_cast typeSign_sq (firstType x)
lemma bounded_integrable (P : Parameters) {f : (ℕ → Letter) → ℝ} (hf : Measurable f)
    (C : ℝ) (hC : ∀ x,|f x| ≤ C) : Integrable f (streamLaw P ℕ) :=
  Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ fun x => by
    simpa only [Real.norm_eq_abs] using hC x)
lemma measurable_Dsum_real (n : ℕ) : Measurable (fun x => (Dsum x n:ℝ)) :=
  (measurable_of_countable (fun z : ℤ => (z:ℝ))).comp (measurable_Dsum n)
lemma abs_Dsum_real_le (x : ℕ → Letter) (n : ℕ) : |(Dsum x n:ℝ)| ≤ n := by
  exact_mod_cast abs_Dsum_le x n
lemma integrable_T_Dsum (P : Parameters) (n : ℕ) :
    Integrable (fun x => T x*(Dsum x n:ℝ)) (streamLaw P ℕ) := by
  apply bounded_integrable P (measurable_T.mul (measurable_Dsum_real n)) n
  intro x
  change |T x*(Dsum x n:ℝ)| ≤ (n:ℝ)
  rw [abs_mul,abs_T,one_mul]
  exact abs_Dsum_real_le x n

def truncK (m : ℕ) (x : ℕ → Letter) : ℝ :=
  if firstSurvivor x<WithTop.some m then K x else 0
lemma measurable_truncK (m : ℕ) : Measurable (truncK m) :=
  (((measurable_of_countable (fun k : ℕ => (k:ℝ))).comp measurable_K).ite
    (measurableSet_lt measurable_firstSurvivor measurable_const) measurable_const)
lemma integrable_truncK (P : Parameters) (m : ℕ) : Integrable (truncK m) (streamLaw P ℕ) := by
  have he : truncK m=({x | firstSurvivor x<WithTop.some m} : Set (ℕ → Letter)).indicator (fun x => (K x:ℝ)) := by
    ext x
    simp [truncK,Set.indicator]
  rw [he]
  exact (integrable_K P).indicator (measurableSet_lt measurable_firstSurvivor measurable_const)

lemma truncK_nonneg (m : ℕ) (x : ℕ → Letter) : 0 ≤ truncK m x := by
  unfold truncK
  split_ifs <;> positivity
lemma truncK_le (m : ℕ) (x : ℕ → Letter) : truncK m x ≤ K x := by
  unfold truncK
  split_ifs
  · exact le_rfl
  · positivity
lemma truncK_tendsto (P : Parameters) :
    Tendsto (fun m => ∫ x,truncK m x ∂streamLaw P ℕ) atTop (𝓝 (∫ x,(K x:ℝ) ∂streamLaw P ℕ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => (K x:ℝ))
    (fun m => (measurable_truncK m).aestronglyMeasurable) (integrable_K P)
  · intro m
    exact ae_of_all _ (fun x => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (truncK_nonneg m x)] using truncK_le m x)
  · filter_upwards [firstSurvivor_finite P] with x hx
    obtain ⟨k,hk⟩ := WithTop.ne_top_iff_exists.mp hx
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (k+1)] with m hm
    unfold truncK
    rw [← hk,ite_eq_left (WithTop.coe_lt_coe.mpr (by omega))]

/-- The signed contribution of letters strictly older than the first survivor. -/
def olderCorrection (m : ℕ) (x : ℕ → Letter) : ℝ :=
  ∑ j∈Finset.range m,hitType j x*(Dsum (tail (j+1) x) (m-j-1):ℝ)
lemma integrable_older_term (P : Parameters) (m j : ℕ) :
    Integrable (fun x => hitType j x*(Dsum (tail (j+1) x) (m-j-1):ℝ)) (streamLaw P ℕ) := by
  apply bounded_integrable P
    ((measurable_hitType j).mul ((measurable_Dsum_real (m-j-1)).comp (measurable_tail (j+1)))) (m-j-1:ℕ)
  intro x
  change |hitType j x*(Dsum (tail (j+1) x) (m-j-1):ℝ)| ≤ (m-j-1:ℕ)
  rw [abs_mul]
  exact (mul_le_mul (abs_hitType_le j x) (abs_Dsum_real_le _ _) (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
lemma integrable_olderCorrection (P : Parameters) (m : ℕ) : Integrable (olderCorrection m) (streamLaw P ℕ) :=
  integrable_finsetSum _ (fun j _ => integrable_older_term P m j)
lemma integral_olderCorrection (P : Parameters) (m : ℕ) : ∫ x,olderCorrection m x ∂streamLaw P ℕ=0 := by
  unfold olderCorrection
  rw [integral_finsetSum _ (fun j _ => integrable_older_term P m j)]
  simp only [integral_hitType_mul_older,Finset.sum_const_zero]
lemma olderCorrection_hit {x : ℕ → Letter} {m j : ℕ} (h : firstSurvivor x=WithTop.some j)
    (hj : j < m) : olderCorrection m x=T x*(Dsum (tail (j+1) x) (m-j-1):ℝ) := by
  unfold olderCorrection
  rw [Finset.sum_eq_single j]
  · simp only [hitType,h,ite_eq_left,T]
  · intro k _ hkj
    have hk : firstSurvivor x ≠ WithTop.some k := by
      rw [h]
      exact fun he => hkj (WithTop.coe_injective he).symm
    rw [hitType,ite_eq_right hk,zero_mul]
  · intro hj'
    exact (hj' (Finset.mem_range.mpr hj)).elim
lemma olderCorrection_nohit {x : ℕ → Letter} {m : ℕ}
    (h : ¬firstSurvivor x<WithTop.some m) : olderCorrection m x=0 := by
  apply Finset.sum_eq_zero
  intro j hj
  have hn : firstSurvivor x ≠ WithTop.some j := by
    intro he
    exact h (by rw [he]; exact WithTop.coe_lt_coe.mpr (Finset.mem_range.mp hj))
  rw [hitType,ite_eq_right hn,zero_mul]

lemma covariance_pointwise (m : ℕ) (x : ℕ → Letter) :
    1-stoppedDefect m x+2*truncK (m+1) x+olderCorrection (m+1) x ≤ T x*(Dsum x (m+1):ℝ) := by
  by_cases h : firstSurvivor x<WithTop.some (m+1)
  · obtain ⟨j,hj⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt h)
    have hh : firstSurvivor x=WithTop.some j := hj.symm
    have hjm : j < m+1 := by rw [← hj] at h; exact WithTop.coe_lt_coe.mp h
    rw [truncK,ite_eq_left h,stoppedDefect_eq_K (by rw [hh]; exact WithTop.coe_le_coe.mpr (by omega)),olderCorrection_hit hh hjm]
    have he : Dsum x (m+1)=typeSign (firstType x)*(1+(K x:ℤ))+Dsum (tail (j+1) x) (m+1-j-1) := by
      calc
        Dsum x (m+1)=Dsum x (j+1+(m+1-j-1)) := by congr 1; omega
        _ = _ := by rw [Dsum_add,Dsum_at_hit hh]
    have her : (Dsum x (m+1):ℝ)=T x*(1+(K x:ℝ))+(Dsum (tail (j+1) x) (m+1-j-1):ℝ) := by
      dsimp only [T]
      exact_mod_cast he
    rw [her]
    nlinarith [T_sq x]
  · rw [truncK,ite_eq_right h,olderCorrection_nohit h]
    have hle : ¬firstSurvivor x ≤ WithTop.some m := by
      intro hl
      exact h (lt_of_le_of_lt hl (WithTop.coe_lt_coe.mpr (by omega)))
    have hb : (reduce (revealed x (m+1))).burgers=[] := by
      simpa only [firstSurvivor_le_iff,not_not] using hle
    have hs : stoppedDefect m x=1-(signSum x (m+1):ℝ) := by
      change 1-(signSum x ((min (WithTop.some m) (firstSurvivor x)).untopA+1):ℝ)=_
      rw [min_eq_left (le_of_not_ge hle),WithTop.untopA_eq_untop WithTop.coe_ne_top,WithTop.untop_coe]
    rw [hs]
    have hd : |(Dsum x (m+1):ℝ)| ≤ -(signSum x (m+1):ℝ) := by exact_mod_cast Dsum_no_survivor hb
    have ha : |T x*(Dsum x (m+1):ℝ)|=|(Dsum x (m+1):ℝ)| := by rw [abs_mul,abs_T,one_mul]
    have hl := neg_abs_le (T x*(Dsum x (m+1):ℝ))
    rw [ha] at hl
    linarith

def covariance (P : Parameters) (m : ℕ) : ℝ := ∫ x,T x*(Dsum x m:ℝ) ∂streamLaw P ℕ
lemma covariance_lower (P : Parameters) (m : ℕ) :
    2*(∫ x,truncK m x ∂streamLaw P ℕ) ≤ covariance P m := by
  cases m with
  | zero => simp [truncK,covariance,Dsum]
  | succ m =>
    have hi := integral_mono
      ((((integrable_const (1:ℝ)).sub ((stoppedDefect_martingale P).integrable m)).add
        ((integrable_truncK P (m+1)).const_mul 2)).add (integrable_olderCorrection P (m+1)))
      (integrable_T_Dsum P (m+1)) (covariance_pointwise m)
    simp only [Pi.add_apply,Pi.sub_apply] at hi
    rw [integral_add,integral_add,integral_sub,integral_const_mul,stoppedDefect_integral,
      integral_olderCorrection] at hi
    · simpa only [covariance,integral_const,probReal_univ,one_smul,sub_self,zero_add,add_zero] using hi
    all_goals first | exact integrable_const _ | exact (stoppedDefect_martingale P).integrable m |
      exact (integrable_truncK P (m+1)).const_mul 2 | exact integrable_olderCorrection P (m+1) |
      exact (integrable_const _).sub ((stoppedDefect_martingale P).integrable m) |
      exact ((integrable_const _).sub ((stoppedDefect_martingale P).integrable m)).add
        ((integrable_truncK P (m+1)).const_mul 2)

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

lemma integral_assignedSign (P : Parameters) (b : Bool) :
    ∫ a,(assignedSign (a,b):ℝ) ∂(law P).toMeasure= -(P.p/2)*(typeSign b:ℝ) := by
  rw [integral_law,sum_letters]
  cases b <;> norm_num [mass,assignedSign,orderType,typeSign]
lemma abs_assignedSign_real (a : Letter) (b : Bool) : |(assignedSign (a,b):ℝ)|=1 := by
  exact_mod_cast abs_assignedSign (a,b)
lemma measurable_D_real (n : ℕ) : Measurable (fun x => (D x n:ℝ)) :=
  (measurable_of_countable (fun z : ℤ => (z:ℝ))).comp (measurable_D n)
lemma Dsum_newest (x : ℕ → Letter) (m : ℕ) : Dsum x (m+1)=D x 0+Dsum (tail 1 x) m := by
  calc
    Dsum x (m+1)=Dsum x (1+m) := by congr 1; omega
    _ = _ := by rw [Dsum_add]; simp [Dsum]
lemma integral_newest_older (P : Parameters) (m : ℕ) :
    ∫ x,(D x 0:ℝ)*(Dsum (tail 1 x) m:ℝ) ∂streamLaw P ℕ= -(P.p/2)*covariance P m := by
  let F : Letter × (ℕ → Letter) → ℝ := fun z =>
    (assignedSign (z.1,firstType z.2):ℝ)*(Dsum z.2 m:ℝ)
  have hF : Measurable F := by
    exact ((measurable_of_countable (fun a : Letter × Bool => (assignedSign a:ℝ))).comp
      (measurable_fst.prodMk (measurable_firstType.comp measurable_snd))).mul
      ((measurable_Dsum_real m).comp measurable_snd)
  have hi : Integrable F ((law P).toMeasure.prod (streamLaw P ℕ)) := by
    apply Integrable.of_bound hF.aestronglyMeasurable m
    exact ae_of_all _ fun z => by
      change |(assignedSign (z.1,firstType z.2):ℝ)*(Dsum z.2 m:ℝ)| ≤ m
      rw [abs_mul,abs_assignedSign_real,one_mul]
      exact abs_Dsum_real_le z.2 m
  have hh := (raw_fun_indep_tail P 0 (raw_adapted 0 0 le_rfl)).hasLaw_prod
    (measurePreserving_eval_infinitePi (fun _ : ℕ => (law P).toMeasure) 0).hasLaw
    (tail_preserving P 1).hasLaw
  have he := hh.integral_comp hi.aestronglyMeasurable
  change (∫ x,(D x 0:ℝ)*(Dsum (tail 1 x) m:ℝ) ∂streamLaw P ℕ)=∫ z,F z ∂((law P).toMeasure.prod (streamLaw P ℕ)) at he
  rw [he,integral_prod_symm _ hi]
  have hx (x : ℕ → Letter) : ∫ a,F (a,x) ∂(law P).toMeasure= -(P.p/2)*(T x*(Dsum x m:ℝ)) := by
    dsimp only [F,T]
    rw [integral_mul_const,integral_assignedSign]
    ring
  simp only [hx,integral_const_mul,covariance]

def varianceSum (P : Parameters) (m : ℕ) : ℝ := ∫ x,(Dsum x m:ℝ)^2 ∂streamLaw P ℕ
lemma varianceSum_nonneg (P : Parameters) (m : ℕ) : 0 ≤ varianceSum P m :=
  integral_nonneg (fun _ => sq_nonneg _)
lemma integrable_Dsum_sq (P : Parameters) (m : ℕ) : Integrable (fun x => (Dsum x m:ℝ)^2) (streamLaw P ℕ) := by
  apply bounded_integrable P ((measurable_Dsum_real m).pow_const 2) ((m:ℝ)^2)
  intro x
  rw [abs_of_nonneg (sq_nonneg _)]
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (Dsum x m:ℝ)) (Nat.cast_nonneg m)).mpr
    (abs_Dsum_real_le x m)
lemma integrable_newest_older (P : Parameters) (m : ℕ) :
    Integrable (fun x => (D x 0:ℝ)*(Dsum (tail 1 x) m:ℝ)) (streamLaw P ℕ) := by
  apply bounded_integrable P ((measurable_D_real 0).mul ((measurable_Dsum_real m).comp (measurable_tail 1))) m
  intro x
  change |(D x 0:ℝ)*(Dsum (tail 1 x) m:ℝ)| ≤ m
  rw [abs_mul]
  have hd : |(D x 0:ℝ)|=1 := by exact_mod_cast abs_D x 0
  rw [hd,one_mul]
  exact abs_Dsum_real_le _ _
lemma varianceSum_increment (P : Parameters) (m : ℕ) :
    varianceSum P (m+1)-varianceSum P m=1-P.p*covariance P m := by
  have he (x : ℕ → Letter) : (Dsum x (m+1):ℝ)^2=
      1+(Dsum (tail 1 x) m:ℝ)^2+2*((D x 0:ℝ)*(Dsum (tail 1 x) m:ℝ)) := by
    rw [Dsum_newest,Int.cast_add]
    have hd : (D x 0:ℝ)^2=1 := by
      have h : |(D x 0:ℝ)|=1 := by exact_mod_cast abs_D x 0
      nlinarith [sq_abs (D x 0:ℝ)]
    nlinarith
  have hi := (tail_preserving P 1).integrable_comp_of_integrable (integrable_Dsum_sq P m)
  have hshift := (tail_preserving P 1).hasLaw.integral_comp (integrable_Dsum_sq P m).aestronglyMeasurable
  change (∫ x,(Dsum (tail 1 x) m:ℝ)^2 ∂streamLaw P ℕ)=varianceSum P m at hshift
  have hh : varianceSum P (m+1)=1+varianceSum P m+2*(-(P.p/2)*covariance P m) := by
    unfold varianceSum
    simp only [he]
    rw [integral_add,integral_add,integral_const_mul,integral_newest_older,hshift]
    · simp only [integral_const,probReal_univ,one_smul,varianceSum]
    all_goals first | exact (integrable_const _).add hi | exact hi | exact integrable_const _ |
      exact (integrable_newest_older P m).const_mul 2

  linarith
lemma varianceSum_increment_le (P : Parameters) (m : ℕ) :
    varianceSum P (m+1)-varianceSum P m ≤ 1-2*P.p*(∫ x,truncK m x ∂streamLaw P ℕ) := by
  rw [varianceSum_increment]
  have h := mul_le_mul_of_nonneg_left (covariance_lower P m) P.pos.le
  linarith

/-- Strict drift of the actual iid inventory word, without assuming a finite mean stopping time. -/
theorem integral_K_strict_drift (P : Parameters) :
    (∫ x,(K x:ℝ) ∂streamLaw P ℕ) ≤ 1/(2*P.p) := by
  by_contra h
  have hp : 0<2*P.p := mul_pos (by norm_num) P.pos
  have hm : 1<2*P.p*(∫ x,(K x:ℝ) ∂streamLaw P ℕ) := by
    have hh := (div_lt_iff₀ hp).mp (lt_of_not_ge h)
    nlinarith
  let c : ℝ := (1-2*P.p*(∫ x,(K x:ℝ) ∂streamLaw P ℕ))/2
  have hc : c<0 := by dsimp [c]; linarith
  have ht : Tendsto (fun m => 1-2*P.p*(∫ x,truncK m x ∂streamLaw P ℕ)) atTop (𝓝 (2*c)) := by
    have he : 2*c=1-2*P.p*(∫ x,(K x:ℝ) ∂streamLaw P ℕ) := by dsimp [c]; ring
    rw [he]
    exact tendsto_const_nhds.sub ((truncK_tendsto P).const_mul (2*P.p))
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((tendsto_order.mp ht).2 c (by linarith))
  have hb (k : ℕ) : varianceSum P (N+k) ≤ varianceSum P N+(k:ℝ)*c := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hs := (varianceSum_increment_le P (N+k)).trans (hN (N+k) (by omega)).le
      push_cast
      rw [show N+(k+1)=N+k+1 by omega]
      linarith
  obtain ⟨k,hk⟩ := exists_nat_gt (varianceSum P N/(-c))
  have hn : 0 < -c := by linarith
  have hh := (div_lt_iff₀ hn).mp hk
  have hz := varianceSum_nonneg P (N+k)
  have hb' := hb k
  nlinarith

theorem integral_K_lt_one (P : Parameters) : (∫ x,(K x:ℝ) ∂streamLaw P ℕ)<1 := by
  apply lt_of_le_of_lt (integral_K_strict_drift P)
  apply (div_lt_one (mul_pos (by norm_num) P.pos)).mpr
  linarith [P.lower]

end FKCRT.Inventory
end

end OAI
