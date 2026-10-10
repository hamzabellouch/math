import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical

lemma poisson_zero : poissonMeasure 0 = Measure.dirac (0 : ℕ) := by
  apply Measure.ext_of_singleton
  intro n
  rw [poissonMeasure_singleton]
  cases n <;> simp

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma hasLaw_coordinate (rate : ι→ℝ≥0) (i : ι) :
    HasLaw (fun ω : ι→ℕ => ω i) (poissonMeasure (rate i)) (batchMeasure rate) :=
  (measurePreserving_eval (fun i => poissonMeasure (rate i)) i).hasLaw

omit [DecidableEq ι] in
lemma coordinate_independent (rate : ι→ℝ≥0) :
    iIndepFun (fun i (ω : ι→ℕ) => ω i) (batchMeasure rate) := by
  exact iIndepFun_pi (fun _ => measurable_id.aemeasurable)

lemma hasLaw_sum (rate : ι→ℝ≥0) (s : Finset ι) :
    HasLaw (fun ω : ι→ℕ => ∑ i∈s,ω i) (poissonMeasure (∑ i∈s,rate i))
      (batchMeasure rate) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty,poisson_zero]
    exact ⟨measurable_const.aemeasurable,by simp⟩
  | @insert i s hi ih =>
    have hind := (coordinate_independent rate).indepFun_finsetSum_of_notMem
      (fun j => measurable_pi_apply j) hi
    have he : (∑ j∈s,fun ω : ι→ℕ => ω j) = (fun ω => ∑ j∈s,ω j) := by
      funext ω
      simp only [Finset.sum_apply]
    rw [he] at hind
    have h := hind.symm.hasLaw_add_poissonMeasure (hasLaw_coordinate rate i) ih
    change HasLaw (fun ω : ι→ℕ => ω i+∑ j∈s,ω j) _ _ at h
    simpa only [Finset.sum_insert hi] using h

variable {D : Type*} [Fintype D] [DecidableEq D]

noncomputable def aggregate (label : ι→D) (ω : ι→ℕ) (d : D) : ℕ :=
  ∑ i : {i // label i=d},ω i

noncomputable def aggregateRate (label : ι→D) (rate : ι→ℝ≥0) (d : D) : ℝ≥0 :=
  ∑ i : {i // label i=d},rate i

theorem measurePreserving_aggregate (label : ι→D) (rate : ι→ℝ≥0) :
    MeasurePreserving (aggregate label) (batchMeasure rate)
      (batchMeasure (aggregateRate label rate)) := by
  have hsum (d : D) : MeasurePreserving
      (fun ω : {i // label i=d}→ℕ => ∑ i,ω i)
      (batchMeasure (fun i : {i // label i=d} => rate i))
      (poissonMeasure (aggregateRate label rate d)) := by
    refine ⟨by fun_prop,?_⟩
    exact (hasLaw_sum (fun i : {i // label i=d} => rate i) Finset.univ).map_eq
  exact (measurePreserving_pi _ _ hsum).comp (measurePreserving_partition rate label)

omit [DecidableEq ι] [Fintype D] in
lemma emptyIndicator_aggregate (label : ι→D) (ω : ι→ℕ) (s : Finset D) :
    emptyIndicator s (aggregate label ω) =
      emptyIndicator (Finset.univ.filter fun i => label i∈s) ω := by
  have he : aggregate label ω∈emptyEvent s ↔
      ω∈emptyEvent (Finset.univ.filter fun i => label i∈s) := by
    simp only [emptyEvent,Set.mem_pi,Finset.mem_coe,Set.mem_singleton_iff,
      aggregate,Finset.sum_eq_zero_iff,forall_const,Finset.mem_univ,
      Finset.mem_filter,true_and]
    constructor
    · intro h i hi
      exact h (label i) hi ⟨i,rfl⟩
    · intro h d hd i
      exact h i (by simpa only [i.property] using hd)
  unfold emptyIndicator
  by_cases h : aggregate label ω∈emptyEvent s
  · simp [h,he.mp h]
  · simp [h,mt he.mpr h]

end

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {D : Type*} [Fintype D] [DecidableEq D]

lemma measurePreserving_schedule_aggregate (label : ι→D) (rate : ι→ℝ≥0) (R : ℕ) :
    MeasurePreserving (fun ω : Fin R→ι→ℕ => fun r => aggregate label (ω r))
      (scheduleMeasure rate R) (scheduleMeasure (aggregateRate label rate) R) :=
  measurePreserving_pi _ _ (fun _ => measurePreserving_aggregate label rate)

omit [DecidableEq ι] [Fintype D] in
lemma scoreTerm_aggregate (label : ι→D) {R : ℕ} (s : Finset D) (b : ℝ)
    (own : Fin R→Bool) (ω : Fin R→ι→ℕ) :
    scoreTerm s b own (fun r => aggregate label (ω r)) =
      scoreTerm (Finset.univ.filter fun i => label i∈s) b own ω := by
  unfold scoreTerm centeredFactor
  simp_rw [emptyIndicator_aggregate]

omit [DecidableEq ι] in
lemma integral_split_counts (rate : ι→ℝ≥0) (p : ι→Prop) [DecidablePred p]
    (F : ({i // p i}→ℕ)→({i // ¬p i}→ℕ)→ℝ)
    (M : ℝ) (hM : ∀ u v,|F u v|≤M) :
    (∫ ω,F (fun i => ω i) (fun i => ω i) ∂batchMeasure rate) =
      ∫ u,∫ v,F u v ∂batchMeasure (fun i : {i // ¬p i} => rate i)
        ∂batchMeasure (fun i : {i // p i} => rate i) := by
  let μ := batchMeasure (fun i : {i // p i} => rate i)
  let ν := batchMeasure (fun i : {i // ¬p i} => rate i)
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℕ) p
  let G : ({i // p i}→ℕ)×({i // ¬p i}→ℕ)→ℝ := fun z => F z.1 z.2
  have hG : Integrable G (μ.prod ν) := by
    apply Integrable.of_bound (measurable_of_countable G).aestronglyMeasurable M
    exact Filter.Eventually.of_forall fun z => by
      simpa only [Real.norm_eq_abs] using hM z.1 z.2
  calc
    _ = ∫ z,G z ∂μ.prod ν :=
      (measurePreserving_piEquivPiSubtypeProd (fun i => poissonMeasure (rate i)) p).integral_comp
        e.measurableEmbedding G
    _ = _ := integral_prod G hG

omit [DecidableEq ι] in
lemma integral_split_counts_le (rate : ι→ℝ≥0) (p : ι→Prop) [DecidablePred p]
    (F : ({i // p i}→ℕ)→({i // ¬p i}→ℕ)→ℝ)
    (M B : ℝ) (hM : ∀ u v,|F u v|≤M)
    (hB : ∀ u,(∫ v,F u v ∂batchMeasure (fun i : {i // ¬p i} => rate i))≤B) :
    (∫ ω,F (fun i => ω i) (fun i => ω i) ∂batchMeasure rate)≤B := by
  rw [integral_split_counts rate p F M hM]
  have hG : Integrable (fun z : ({i // p i}→ℕ)×({i // ¬p i}→ℕ) => F z.1 z.2)
      ((batchMeasure (fun i : {i // p i} => rate i)).prod
        (batchMeasure (fun i : {i // ¬p i} => rate i))) := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable M
    exact Filter.Eventually.of_forall fun z => by
      simpa only [Real.norm_eq_abs] using hM z.1 z.2
  calc
    _ ≤ ∫ _u : {i // p i}→ℕ,B ∂batchMeasure (fun i : {i // p i} => rate i) :=
      integral_mono hG.integral_prod_left (integrable_const B) hB
    _ = B := by simp

end SharpRamseyFive.PoissonScore

namespace SharpRamseyFive.ValidationMoment
open MeasureTheory ProbabilityTheory PoissonScore
open scoped BigOperators NNReal Classical

private lemma add_power_bound {a b : ℝ} (ha : 0≤a) (hb : 0≤b) (R : ℕ) :
    (a+b)^R≤2^R*(a^R+b^R) := by
  apply (add_pow_le ha hb R).trans
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (Nat.sub_le R 1)) (by positivity)

theorem finite_second_sum {H : Type*} [Fintype H] [DecidableEq H]
    (M θ : H → H → ℝ) (d : H → ℝ) (a c : ℝ) (_ha : 0≤a) (hc : 0≤c)
    (hd : ∀ h,0≤d h ∧ d h≤1) (hθ : ∀ h k,0≤θ h k)
    (hdiag : ∀ h,|M h h|≤a) (hoff : ∀ h k,h≠k → |M h k|≤c*(d h*d k+θ h k))
    (R : ℕ) (hR : 2≤R) :
    (∑ h,∑ k,|M h k|^R) ≤ (Fintype.card H:ℝ)*a^R+
      (2*c)^R*((∑ h,(d h)^2)^2+∑ h,∑ k∈Finset.univ.erase h,(θ h k)^R) := by
  have hp (h k : H) (hne : h≠k) : |M h k|^R ≤
      (2*c)^R*((d h)^2*(d k)^2+(θ h k)^R) := by
    calc
      _ ≤ (c*(d h*d k+θ h k))^R := pow_le_pow_left₀ (abs_nonneg _) (hoff h k hne) R
      _ = c^R*(d h*d k+θ h k)^R := mul_pow _ _ _
      _ ≤ c^R*(2^R*((d h*d k)^R+(θ h k)^R)) :=
        mul_le_mul_of_nonneg_left (add_power_bound (mul_nonneg (hd h).1 (hd k).1) (hθ h k) R)
          (pow_nonneg hc R)
      _ = (2*c)^R*((d h)^R*(d k)^R+(θ h k)^R) := by rw [mul_pow,mul_pow];ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply add_le_add <;> try rfl
        exact mul_le_mul (pow_le_pow_of_le_one (hd h).1 (hd h).2 hR)
          (pow_le_pow_of_le_one (hd k).1 (hd k).2 hR) (pow_nonneg (hd k).1 R) (sq_nonneg _)
  have hs : (∑ h,∑ k,|M h k|^R)=
      (∑ h,|M h h|^R)+(∑ h,∑ k∈Finset.univ.erase h,|M h k|^R) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro h _
    exact (Finset.add_sum_erase Finset.univ (fun k => |M h k|^R) (Finset.mem_univ h)).symm
  rw [hs]
  have hdg : (∑ h,|M h h|^R)≤(Fintype.card H:ℝ)*a^R := by
    calc
      _ ≤ ∑ _h : H,a^R := Finset.sum_le_sum fun h _ => pow_le_pow_left₀ (abs_nonneg _) (hdiag h) R
      _ = _ := by simp
  apply add_le_add hdg
  calc
    _ ≤ ∑ h,∑ k∈Finset.univ.erase h,(2*c)^R*((d h)^2*(d k)^2+(θ h k)^R) := by
      apply Finset.sum_le_sum
      intro h _
      apply Finset.sum_le_sum
      intro k hk
      exact hp h k (Ne.symm (Finset.mem_erase.mp hk).1)
    _ = (2*c)^R*((∑ h,∑ k∈Finset.univ.erase h,(d h)^2*(d k)^2)+
        ∑ h,∑ k∈Finset.univ.erase h,(θ h k)^R) := by
      simp only [Finset.mul_sum,Finset.sum_add_distrib,mul_add]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply add_le_add <;> try rfl
      calc
        _ ≤ ∑ h,∑ k,(d h)^2*(d k)^2 := by
          apply Finset.sum_le_sum
          intro h _
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            (fun k _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
        _ = _ := by rw [pow_two,Finset.sum_mul];simp only [Finset.mul_sum]

variable {D H : Type*} [Fintype D] [DecidableEq D] [Fintype H] [DecidableEq H]

omit [Fintype D] [DecidableEq D] in
lemma mass_scale (a : D → ℝ≥0) (L : ℝ≥0) (S : Finset D) :
    mass (fun d => L*a d) S=(L:ℝ)*mass a S := by
  simp only [mass,NNReal.coe_mul,Finset.mul_sum]

lemma diagonal_one_batch (a : D → ℝ≥0) (L : ℝ≥0) (S : Finset D)
    (base c : ℝ) (hc : 0≤c) (hm : c≤ mass a S) (hb : c≤base) :
    |pairMean (fun d => L*a d) S S (Real.exp (-(L:ℝ)*base))| ≤
      2*Real.exp (-(L:ℝ)*c) := by
  rw [pairMean, ←integral_centeredFactor_mul]
  apply (abs_integral_le_integral_abs).trans
  apply le_trans _ (integral_abs_centeredFactor_exp_le _ S L.coe_nonneg (mass_scale a L S) hm hb)
  apply integral_mono (integrable_centeredFactor_mul _ S S _).abs (integrable_centeredFactor _ S _).abs
  intro ω
  dsimp only
  rw [abs_mul]
  have hle := abs_centeredFactor_le_one S (Real.exp (-(L:ℝ)*base))
    ⟨(Real.exp_pos _).le,Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr L.coe_nonneg) (hc.trans hb))⟩ ω
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hle (abs_nonneg (centeredFactor S (Real.exp (-(L:ℝ)*base)) ω))

theorem poisson_validation_second (a : D → ℝ≥0) (lines : H → Finset D)
    (L : ℝ≥0) (hL : 1≤(L:ℝ)) (base c : ℝ) (hc : 0≤c) (hb : c≤base)
    (hm : ∀ h,c≤ mass a (lines h)) (hd : ∀ h,|mass a (lines h)-base|≤1)
    (R : ℕ) (hR : 2≤R) (own : H → Fin R → Bool) :
    (∫ ω,(typicalScore Finset.univ lines (Real.exp (-(L:ℝ)*base)) own ω)^2
      ∂scheduleMeasure (fun d => L*a d) R) ≤
      (Fintype.card H:ℝ)*(2*Real.exp (-(L:ℝ)*c))^R+
      (2*(L:ℝ)^2*Real.exp (-(L:ℝ)*c))^R*
        ((∑ h,|mass a (lines h)-base|^2)^2+
          ∑ h,∑ k∈Finset.univ.erase h,(mass a (lines h ∩ lines k))^R) := by
  apply (integral_typicalScore_sq_le (fun d => L*a d) Finset.univ lines _ own).trans
  have hh := finite_second_sum
    (fun h k => pairMean (fun d => L*a d) (lines h) (lines k) (Real.exp (-(L:ℝ)*base)))
    (fun h k => mass a (lines h ∩ lines k)) (fun h => |mass a (lines h)-base|)
    (2*Real.exp (-(L:ℝ)*c)) ((L:ℝ)^2*Real.exp (-(L:ℝ)*c)) (by positivity) (by positivity)
    (fun h => ⟨abs_nonneg _,hd h⟩) (fun _ _ => mass_nonneg _ _)
    (fun h => diagonal_one_batch a L (lines h) base c hc (hm h) hb) (by
      intro h k _
      rw [pairMean, ←integral_centeredFactor_mul]
      exact abs_integral_centeredFactor_mul_exp_le _ _ _ hL hc
        (mass_scale a L (lines h)) (mass_scale a L (lines k))
        (mass_scale a L (lines h ∩ lines k)) (hm h) (hm k) hb) R hR
  simpa only [mul_assoc] using hh

end SharpRamseyFive.ValidationMoment

end OAI
