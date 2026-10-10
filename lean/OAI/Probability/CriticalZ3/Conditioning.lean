import OAI.Probability.CriticalZ3.SeedTrials

namespace OAI

universe uF

open MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

/-! The exact revealed-history law used by the adaptive queue.  In particular,
classifications depending only on revealed values do not change fresh bits. -/
namespace InfiniteConditioning
open MeasureTheory ProbabilityTheory Classical
variable {E : Type} [Countable E]

noncomputable def replace (J : Finset E) (ξ ω : E → Bool) : E → Bool :=
  fun e => if e ∈ J then ξ e else ω e

noncomputable def fixedParameter (p : E → Set.Icc (0 : ℝ) 1)
    (J : Finset E) (ξ : E → Bool) : E → Set.Icc (0 : ℝ) 1 :=
  fun e => if e ∈ J then if ξ e = true then 1 else 0 else p e

def pattern (J : Finset E) (ξ : E → Bool) : Set (E → Bool) :=
  {ω | ∀ e ∈ J, ω e = ξ e}

omit [Countable E] in
theorem measurable_replace (J : Finset E) (ξ : E → Bool) : Measurable (replace J ξ) := by
  apply Measurable.of_eval
  intro e
  by_cases he : e ∈ J
  · simp only [replace, ite_eq_left he]; exact measurable_const
  · simp only [replace, ite_eq_right he]; exact measurable_pi_apply e

theorem measurableSet_pattern (J : Finset E) (ξ : E → Bool) : MeasurableSet (pattern J ξ) := by
  simp only [pattern, Set.ofPred_forall]
  exact MeasurableSet.iInter (fun e => MeasurableSet.iInter (fun _ =>
    measurableSet_eq_fun (measurable_pi_apply e) measurable_const))

omit [Countable E] in
theorem replace_eq_of_pattern {J : Finset E} {ξ ω : E → Bool} (h : ω ∈ pattern J ξ) :
    replace J ξ ω = ω := by
  funext e
  by_cases he : e ∈ J
  · exact (ite_eq_left he).trans (h e he).symm
  · exact ite_eq_right he

omit [Countable E] in
theorem map_replace (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E) (ξ : E → Bool) :
    (ProductCylinder.law p).map (replace J ξ) = ProductCylinder.law (fixedParameter p J ξ) := by
  have h (e : E) :
      (bernoulliMeasure true false (p e)).map (fun b : Bool => if e ∈ J then ξ e else b) =
        bernoulliMeasure true false (fixedParameter p J ξ e) := by
    by_cases he : e ∈ J
    · simp only [he,ite_true,fixedParameter]
      cases ξ e <;> simp
    · simp only [he,ite_false,fixedParameter]
      exact Measure.map_id
  change (Measure.infinitePi (fun e => bernoulliMeasure true false (p e))).map
    (fun ω e => (fun b => if e ∈ J then ξ e else b) (ω e)) = _
  rw [Measure.infinitePi_map_pi]
  · simp only [h,ProductCylinder.law]
  · intro e; exact measurable_of_countable _

private abbrev bitSigma (e : E) : MeasurableSpace (E → Bool) :=
  MeasurableSpace.comap (fun ω => ω e) inferInstance

omit [Countable E] in
private theorem measurable_replace_compl (J : Finset E) (ξ : E → Bool) :
    @Measurable (E → Bool) (E → Bool) (⨆ e ∈ (J : Set E)ᶜ, bitSigma e)
      inferInstance (replace J ξ) := by
  apply @Measurable.of_eval (E → Bool) E (fun _ => Bool) (⨆ e ∈ (J : Set E)ᶜ, bitSigma e) _ (replace J ξ)
  intro e
  by_cases he : e ∈ J
  · simp only [replace,ite_eq_left he]; exact measurable_const
  · simp only [replace,ite_eq_right he]
    exact Measurable.of_comap_le (le_iSup_of_le e (le_iSup_of_le he le_rfl))

private theorem measurable_pattern_sigma (J : Finset E) (ξ : E → Bool) :
    MeasurableSet[⨆ e ∈ (J : Set E), bitSigma e] (pattern J ξ) := by
  simp only [pattern,Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro e
  apply MeasurableSet.iInter
  intro he
  apply measurableSet_eq_fun _ measurable_const
  exact Measurable.of_comap_le (le_iSup_of_le e (le_iSup_of_le he le_rfl))

/-- Literal finite-history factorization, including impossible histories. -/
theorem pattern_inter (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E) (ξ : E → Bool)
    (A : Set (E → Bool)) (hA : MeasurableSet A) :
    ProductCylinder.law p (pattern J ξ ∩ A) =
      ProductCylinder.law p (pattern J ξ) * ProductCylinder.law (fixedParameter p J ξ) A := by
  have hi : iIndepFun (fun e (ω : E → Bool) => ω e) (ProductCylinder.law p) :=
    iIndepFun_infinitePi (X := fun _ => id) (fun _ => measurable_id)
  have hmi : iIndep (bitSigma (E := E)) (ProductCylinder.law p) :=
    (iIndepFun_iff_iIndep _ _ _).mp hi
  have h := indep_iSup_of_disjoint
    (fun e => (measurable_pi_apply e).comap_le) hmi
    (disjoint_compl_right (α := Set E) (a := (J : Set E)))
  have hh := (h.indepSet_of_measurableSet (measurable_pattern_sigma J ξ)
    ((measurable_replace_compl J ξ) hA)).measure_inter_eq_mul
  have heq : pattern J ξ ∩ replace J ξ ⁻¹' A = pattern J ξ ∩ A := by
    ext ω
    constructor <;> rintro ⟨hp,ha⟩
    · exact ⟨hp,by simpa only [Set.mem_preimage,replace_eq_of_pattern hp] using ha⟩
    · exact ⟨hp,by simpa only [Set.mem_preimage,replace_eq_of_pattern hp] using ha⟩
  rw [heq] at hh
  rw [←map_replace p J ξ,Measure.map_apply (measurable_replace J ξ) hA]
  exact hh

theorem pattern_inter_real (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E) (ξ : E → Bool)
    (A : Set (E → Bool)) (hA : MeasurableSet A) :
    (ProductCylinder.law p).real (pattern J ξ ∩ A) =
      (ProductCylinder.law p).real (pattern J ξ) *
        (ProductCylinder.law (fixedParameter p J ξ)).real A := by
  simp only [Measure.real_def,pattern_inter p J ξ A hA,ENNReal.toReal_mul]

omit [Countable E] in
theorem pattern_extend_iff (J : Finset E) (a : J → Bool) (ω : E → Bool) :
    ω ∈ pattern J (ProductCylinder.extend J a) ↔ J.restrict ω = a := by
  constructor
  · intro h; funext e
    simpa only [Finset.restrict,ProductCylinder.extend,dite_eq_left e.2] using h e e.2
  · intro h e he
    have hh := congrFun h ⟨e,he⟩
    simpa only [Finset.restrict,ProductCylinder.extend,dite_eq_left he] using hh

/-- Partition a finite reveal without conditioning on any unrevealed event. -/
theorem measure_select (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E)
    (A : (J → Bool) → Set (E → Bool)) (hA : ∀ a, MeasurableSet (A a)) :
    (ProductCylinder.law p).real {ω | ω ∈ A (J.restrict ω)} =
      ∑ a : J → Bool, (ProductCylinder.law p).real (pattern J (ProductCylinder.extend J a)) *
        (ProductCylinder.law (fixedParameter p J (ProductCylinder.extend J a))).real (A a) := by
  have heq : {ω | ω ∈ A (J.restrict ω)} =
      ⋃ a : J → Bool, pattern J (ProductCylinder.extend J a) ∩ A a := by
    ext ω
    simp only [Set.mem_ofPred_eq,Set.mem_iUnion,Set.mem_inter_iff,pattern_extend_iff]
    exact ⟨fun h => ⟨J.restrict ω,rfl,h⟩, fun ⟨a,ha,h⟩ => ha.symm ▸ h⟩
  rw [heq,measureReal_iUnion_fintype]
  · exact Finset.sum_congr rfl (fun a _ => pattern_inter_real p J _ _ (hA a))
  · intro a b hab
    apply Set.disjoint_left.mpr
    intro ω ha hb
    exact hab (((pattern_extend_iff J a ω).mp ha.1).symm.trans
      ((pattern_extend_iff J b ω).mp hb.1))
  · intro a; exact (measurableSet_pattern _ _).inter (hA a)

theorem sum_pattern_real (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E) :
    ∑ a : J → Bool, (ProductCylinder.law p).real (pattern J (ProductCylinder.extend J a)) = 1 := by
  simpa only [Set.mem_univ,Set.ofPred_true,probReal_univ,mul_one] using
    (measure_select p J (fun _ => Set.univ) (fun _ => MeasurableSet.univ)).symm

omit [Countable E] in
theorem fixedParameter_congr (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E)
    {ξ ξ' : E → Bool} (h : ∀ e ∈ J, ξ e = ξ' e) :
    fixedParameter p J ξ = fixedParameter p J ξ' := by
  funext e
  by_cases he : e ∈ J
  · simp only [fixedParameter,he,ite_true,h e he]
  · simp only [fixedParameter,he,ite_false]

theorem measurableSet_select (J : Finset E)
    (A : (J → Bool) → Set (E → Bool)) (hA : ∀ a, MeasurableSet (A a)) :
    MeasurableSet {ω | ω ∈ A (J.restrict ω)} := by
  have heq : {ω | ω ∈ A (J.restrict ω)} =
      ⋃ a : J → Bool, pattern J (ProductCylinder.extend J a) ∩ A a := by
    ext ω
    simp only [Set.mem_ofPred_eq,Set.mem_iUnion,Set.mem_inter_iff,pattern_extend_iff]
    exact ⟨fun h => ⟨J.restrict ω,rfl,h⟩, fun ⟨a,ha,h⟩ => ha.symm ▸ h⟩
  rw [heq]
  exact MeasurableSet.iUnion (fun a => (measurableSet_pattern _ _).inter (hA a))

end InfiniteConditioning

namespace InfiniteConditioning
open MeasureTheory ProbabilityTheory Classical
variable {E I : Type}

private theorem measurable_determined_sigma (J : Finset E) (A : Set (E → Bool))
    (hA : ProductCylinder.DeterminedBy (F := Prop) J (fun ω => ω ∈ A)) :
    MeasurableSet[⨆ e ∈ (J : Set E), bitSigma e] A := by
  let M := ⨆ e ∈ (J : Set E), bitSigma e
  let mask : (E → Bool) → (E → Bool) := fun ω e => if e ∈ J then ω e else false
  have hm : @Measurable (E → Bool) (E → Bool) M MeasurableSpace.pi mask := by
    apply @Measurable.of_eval (E → Bool) E (fun _ => Bool) M _ mask
    intro e
    by_cases he : e ∈ J
    · simp only [mask,ite_eq_left he]
      exact Measurable.of_comap_le (le_iSup_of_le e (le_iSup_of_le he le_rfl))
    · simp only [mask,ite_eq_right he]; exact measurable_const
  have heq : mask ⁻¹' A = A := by
    ext ω
    exact eq_iff_iff.mp (hA ω (mask ω) (fun e he => by simp [mask,he]))
  rw [←heq]
  exact hm (ProductCylinder.measurableSet_determined J A (fun ω ω' h => eq_iff_iff.mp (hA ω ω' h)))

/-- Arbitrary observables of disjoint finite blocks are independent under the
infinite product law, also when other coordinates have been fixed to 0 or 1. -/
theorem indepSet_determined (p : E → Set.Icc (0 : ℝ) 1) (J K : Finset E)
    (hJK : Disjoint J K) (A B : Set (E → Bool))
    (hA : ProductCylinder.DeterminedBy (F := Prop) J (fun ω => ω ∈ A))
    (hB : ProductCylinder.DeterminedBy (F := Prop) K (fun ω => ω ∈ B)) :
    IndepSet A B (ProductCylinder.law p) := by
  have hi : iIndepFun (fun e (ω : E → Bool) => ω e) (ProductCylinder.law p) :=
    iIndepFun_infinitePi (X := fun _ => id) (fun _ => measurable_id)
  have hmi : iIndep (bitSigma (E := E)) (ProductCylinder.law p) :=
    (iIndepFun_iff_iIndep _ _ _).mp hi
  have h := indep_iSup_of_disjoint (fun e => (measurable_pi_apply e).comap_le) hmi
    (show Disjoint (J : Set E) (K : Set E) from Finset.disjoint_coe.mpr hJK)
  exact h.indepSet_of_measurableSet (measurable_determined_sigma J A hA)
    (measurable_determined_sigma K B hB)

theorem disjoint_blocks_probability (p : E → Set.Icc (0 : ℝ) 1)
    (J : I → Finset E) (hJ : Pairwise (fun i j => Disjoint (J i) (J j)))
    (A : I → Set (E → Bool))
    (hA : ∀ i, ProductCylinder.DeterminedBy (F := Prop) (J i) (fun ω => ω ∈ A i))
    (s : Finset I) :
    (ProductCylinder.law p).real {ω | ∀ i ∈ s, ω ∈ A i} =
      ∏ i ∈ s, (ProductCylinder.law p).real (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.notMem_empty,false_implies,implies_true,Set.ofPred_true,
      probReal_univ,Finset.prod_empty]
  | @insert i s hi ih =>
    have hdis : Disjoint (J i) (s.biUnion J) := by
      rw [Finset.disjoint_left]
      intro e he he'
      obtain ⟨j,hj,hej⟩ := Finset.mem_biUnion.mp he'
      exact Finset.disjoint_left.mp (hJ (ne_of_mem_of_not_mem hj hi).symm) he hej
    have hdet : ProductCylinder.DeterminedBy (F := Prop) (s.biUnion J)
        (fun ω => ∀ j ∈ s, ω ∈ A j) := by
      intro ω ω' h
      apply propext
      constructor <;> intro hh j hj
      · exact (eq_iff_iff.mp (hA j ω ω' (fun e he => h e (Finset.mem_biUnion.mpr ⟨j,hj,he⟩)))).mp (hh j hj)
      · exact (eq_iff_iff.mp (hA j ω ω' (fun e he => h e (Finset.mem_biUnion.mpr ⟨j,hj,he⟩)))).mpr (hh j hj)
    have hh := (indepSet_determined p (J i) (s.biUnion J) hdis (A i)
      {ω | ∀ j ∈ s, ω ∈ A j} (hA i) hdet).measure_inter_eq_mul
    have heq : {ω | ∀ j ∈ insert i s, ω ∈ A j} = A i ∩ {ω | ∀ j ∈ s, ω ∈ A j} := by
      ext ω; simp only [Finset.mem_insert,forall_eq_or_imp,Set.mem_ofPred_eq,Set.mem_inter_iff]
    rw [heq,Measure.real_def,hh,ENNReal.toReal_mul]
    change (ProductCylinder.law p).real (A i) *
      (ProductCylinder.law p).real {ω | ∀ j ∈ s, ω ∈ A j} = _
    rw [ih,Finset.prod_insert hi]

end InfiniteConditioning

namespace InfiniteConditioning
open MeasureTheory ProbabilityTheory Classical
variable {E : Type}

noncomputable def bitProbability (p : Set.Icc (0 : ℝ) 1) (b : Bool) : ℝ :=
  if b then p else 1-(p : ℝ)

theorem single_probability (p : E → Set.Icc (0 : ℝ) 1) (e : E) (b : Bool) :
    (ProductCylinder.law p).real {ω | ω e = b} = bitProbability (p e) b := by
  have h := Measure.infinitePi_map_eval (fun e : E => bernoulliMeasure true false (p e)) e
  have hm : Measurable (fun ω : E → Bool => ω e) := measurable_pi_apply e
  have he : {ω : E → Bool | ω e = b} = (fun ω => ω e) ⁻¹' {b} := rfl
  rw [he,Measure.real_def,←Measure.map_apply hm (measurableSet_singleton _)]
  change ((Measure.infinitePi (fun e : E => bernoulliMeasure true false (p e))).map
    (fun ω => ω e) {b}).toReal = _
  rw [h]
  change (bernoulliMeasure true false (p e)).real {b} = _
  rw [bernoulliMeasure_real_apply (p e) (measurableSet_singleton _)]
  cases b <;> simp [bitProbability,unitInterval.coe_symm_eq]

theorem finite_pattern_probability (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E)
    (ξ : E → Bool) :
    (ProductCylinder.law p).real (pattern J ξ) = ∏ e ∈ J, bitProbability (p e) (ξ e) := by
  classical
  have hd : Pairwise (fun e f : E => Disjoint ({e} : Finset E) {f}) := by
    intro e f h; simpa using h
  have hdet (e : E) : ProductCylinder.DeterminedBy (F := Prop) {e}
      (fun ω : E → Bool => ω e = ξ e) := by
    intro ω ω' h
    dsimp only
    rw [h e (Finset.mem_singleton_self e)]
  have h := disjoint_blocks_probability p (fun e : E => {e}) hd
    (fun e => {ω | ω e = ξ e}) hdet J
  simpa only [pattern,Set.mem_ofPred_eq,single_probability] using h

def allValue (J : Finset E) (b : Bool) : Set (E → Bool) := {ω | ∀ e ∈ J, ω e = b}

theorem allValue_determined (J : Finset E) (b : Bool) :
    ProductCylinder.DeterminedBy (F := Prop) J (fun ω => ω ∈ allValue J b) := by
  intro ω ω' h
  apply propext
  constructor <;> intro hh e he
  · rw [←h e he]; exact hh e he
  · rw [h e he]; exact hh e he

theorem measurableSet_allValue (J : Finset E) (b : Bool) : MeasurableSet (allValue J b) :=
  ProductCylinder.measurableSet_determined J _
    (fun ω ω' h => eq_iff_iff.mp (allValue_determined J b ω ω' h))

theorem allValue_probability (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E) (b : Bool) :
    (ProductCylinder.law p).real (allValue J b) = ∏ e ∈ J, bitProbability (p e) b :=
  finite_pattern_probability p J (fun _ => b)

theorem allValue_probability_constant (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E)
    (q : Set.Icc (0 : ℝ) 1) (hp : ∀ e ∈ J, p e = q) (b : Bool) :
    (ProductCylinder.law p).real (allValue J b) = (bitProbability q b)^J.card := by
  rw [allValue_probability]
  calc
    _ = ∏ _e ∈ J, bitProbability q b := Finset.prod_congr rfl (fun e he => by rw [hp e he])
    _ = _ := by rw [Finset.prod_const]

/-- A reveal has no effect on any observable determined by disjoint bits. -/
theorem fixed_determined_probability (p : E → Set.Icc (0 : ℝ) 1)
    (J K : Finset E) (hJK : Disjoint J K) (ξ : E → Bool) (A : Set (E → Bool))
    (hA : ProductCylinder.DeterminedBy (F := Prop) K (fun ω => ω ∈ A)) :
    (ProductCylinder.law (fixedParameter p J ξ)).real A = (ProductCylinder.law p).real A := by
  have hAm := ProductCylinder.measurableSet_determined K A (fun ω ω' h => eq_iff_iff.mp (hA ω ω' h))
  rw [←map_replace,Measure.real_def,Measure.map_apply (measurable_replace _ _) hAm]
  have heq : replace J ξ ⁻¹' A = A := by
    ext ω
    apply eq_iff_iff.mp (hA ω (replace J ξ ω) ?_)
    intro e he
    apply ite_eq_right
    exact fun heJ => Finset.disjoint_left.mp hJK heJ he
  rw [heq]
  rfl

variable [Countable E]

theorem ae_fixed_pattern (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E) (ξ : E → Bool) :
    ∀ᵐ ω ∂ProductCylinder.law (fixedParameter p J ξ), ω ∈ pattern J ξ := by
  rw [←map_replace]
  apply (ae_map_iff (measurable_replace J ξ).aemeasurable
    (measurableSet_pattern J ξ)).mpr
  exact Filter.Eventually.of_forall (fun ω e he => ite_eq_left he)

/-- On a fixed revealed pattern, every J-determined quantity is constant. -/
theorem ae_fixed_determined {F : Sort uF} (p : E → Set.Icc (0 : ℝ) 1)
    (J : Finset E) (ξ : E → Bool) (f : (E → Bool) → F)
    (hf : ∀ ω ω', (∀ e ∈ J, ω' e = ω e) → f ω' = f ω) :
    ∀ᵐ ω ∂ProductCylinder.law (fixedParameter p J ξ), f ω = f ξ := by
  filter_upwards [ae_fixed_pattern p J ξ] with ω hω
  exact hf ξ ω hω

end InfiniteConditioning

namespace InfiniteConditioning
open MeasureTheory ProbabilityTheory Classical
variable {E : Type} [Countable E]

theorem select_probability_le (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E)
    (A : (J → Bool) → Set (E → Bool)) (hA : ∀ a, MeasurableSet (A a)) {b : ℝ}
    (hb : ∀ a, (ProductCylinder.law (fixedParameter p J (ProductCylinder.extend J a))).real
      (A a) ≤ b) :
    (ProductCylinder.law p).real {ω | ω ∈ A (J.restrict ω)} ≤ b := by
  rw [measure_select p J A hA]
  calc
    _ ≤ ∑ a : J → Bool, (ProductCylinder.law p).real
        (pattern J (ProductCylinder.extend J a)) * b :=
      Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hb a) measureReal_nonneg)
    _ = b := by rw [←Finset.sum_mul,sum_pattern_real,one_mul]

/-- Exact lower bound after a selected reveal; null histories are included. -/
theorem select_probability_lower (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E)
    (P : (J → Bool) → Prop) (A : (J → Bool) → Set (E → Bool))
    (hA : ∀ a, MeasurableSet (A a)) {b : ℝ}
    (hb : ∀ a, P a → b ≤
      (ProductCylinder.law (fixedParameter p J (ProductCylinder.extend J a))).real (A a)) :
    b * (ProductCylinder.law p).real {ω | P (J.restrict ω)} ≤
      (ProductCylinder.law p).real {ω | P (J.restrict ω) ∧ ω ∈ A (J.restrict ω)} := by
  classical
  let B : (J → Bool) → Set (E → Bool) := fun a => if P a then Set.univ else ∅
  let C : (J → Bool) → Set (E → Bool) := fun a => if P a then A a else ∅
  have hPm : {ω | P (J.restrict ω)} = {ω | ω ∈ B (J.restrict ω)} := by
    ext ω; by_cases h : P (J.restrict ω) <;> simp [B,h]
  have hAm : {ω | P (J.restrict ω) ∧ ω ∈ A (J.restrict ω)} =
      {ω | ω ∈ C (J.restrict ω)} := by
    ext ω; by_cases h : P (J.restrict ω) <;> simp [C,h]
  have hB (a) : MeasurableSet (B a) := by dsimp [B]; split_ifs <;> measurability
  have hC (a) : MeasurableSet (C a) := by dsimp [C]; split_ifs; exact hA a; exact MeasurableSet.empty
  rw [hPm,hAm,measure_select p J B hB,measure_select p J C hC,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : P a
  · simp only [B,C,ha,ite_true,probReal_univ,mul_one]
    calc
      _ = (ProductCylinder.law p).real (pattern J (ProductCylinder.extend J a))*b := mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hb a ha) measureReal_nonneg
  · simp only [B,C,ha,ite_false,measureReal_empty,mul_zero]
    exact le_rfl

end InfiniteConditioning

end OAI
