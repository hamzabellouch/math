import OAI.Analysis.DiamondDistortion.GraphBounds

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

open scoped ENNReal

open scoped ENNReal Classical
open Filter Topology
namespace LpDual
variable {ι : Type*} (E : ι → Type*) [∀ i,NormedAddCommGroup (E i)] [∀ i,NormedSpace ℝ (E i)]
  (p : ℝ≥0∞) [Fact (1 ≤ p)]

def finite : (Π₀ i,E i) →ₗ[ℝ] lp E p where
  toFun v := ⟨(fun i => v i),(memℓp_zero (by
    classical
    have he : {i | v i ≠ 0}=(v.support : Set ι) := by ext i; simp
    rw [he]
    exact v.support.finite_toSet)).of_exponent_ge bot_le⟩
  map_add' v w := by ext i; rfl
  map_smul' c v := by ext i; rfl
@[simp] lemma finite_apply {ι : Type*} (E : ι → Type*) [∀ i,NormedAddCommGroup (E i)] [∀ i,NormedSpace ℝ (E i)] (p : ℝ≥0∞) [Fact (1 ≤ p)] (v : Π₀ i,E i) (i : ι) : finite E p v i=v i := rfl
lemma finite_injective {ι : Type*} (E : ι → Type*) [∀ i,NormedAddCommGroup (E i)] [∀ i,NormedSpace ℝ (E i)] (p : ℝ≥0∞) [Fact (1 ≤ p)] : Function.Injective (finite E p) := by
  intro v w he
  ext i
  exact congrArg (fun x : lp E p => x i) he
lemma finite_norm_add {ι : Type*} (E : ι → Type*) [∀ i,NormedAddCommGroup (E i)] [∀ i,NormedSpace ℝ (E i)] (p : ℝ≥0∞) [Fact (1 ≤ p)] {r : ℝ} (hr : r=p.toReal) (hp : 0 < p.toReal) (v w : Π₀ i,E i)
    (hd : Disjoint v.support w.support) :
    ‖finite E p (v+w)‖^r=‖finite E p v‖^r+‖finite E p w‖^r := by
  classical
  subst r
  rw [lp.norm_rpow_eq_tsum hp,lp.norm_rpow_eq_tsum hp,lp.norm_rpow_eq_tsum hp,
    ← ((finite E p v).property.summable hp).tsum_add ((finite E p w).property.summable hp)]
  apply tsum_congr
  intro i
  simp only [finite_apply,DFinsupp.add_apply]
  have hz : v i=0 ∨ w i=0 := by
    by_cases h : v i=0
    · exact Or.inl h
    · right
      by_contra hh
      exact (Finset.disjoint_left.mp hd) (DFinsupp.mem_support_iff.mpr h) (DFinsupp.mem_support_iff.mpr hh)
  rcases hz with h|h <;> simp [h,Real.zero_rpow hp.ne']

lemma small_tail_upper (hp : 1 < p.toReal) (x : StrongDual ℝ (lp E p)) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : Finset ι, ∀ v : Π₀ i,E i, (∀ i ∈ v.support,i ∉ C) →
      x (finite E p v) ≤ ε*‖finite E p v‖ := by
  classical
  have hp0 : 0 < p.toReal := lt_trans zero_lt_one hp
  by_contra hn
  push Not at hn
  have hchoose (C : Finset ι) : ∃ q : Π₀ i,E i,
      (∀ i ∈ q.support,i ∉ C) ∧ ‖finite E p q‖=1 ∧ ε < x (finite E p q) := by
    obtain ⟨v,hout,hval⟩ := hn C
    have hvn0 : ‖finite E p v‖ ≠ 0 := by
      intro he
      have hv0 : v=0 := finite_injective E p (by simpa using norm_eq_zero.mp he)
      simp only [hv0,map_zero,norm_zero,mul_zero,lt_self_iff_false] at hval
    have hvn : 0 < ‖finite E p v‖ := lt_of_le_of_ne (norm_nonneg _) hvn0.symm
    let q := ‖finite E p v‖⁻¹ • v
    refine ⟨q, ?_, ?_, ?_⟩
    · intro i hi
      exact hout i (DFinsupp.support_smul _ v hi)
    · simp only [q,map_smul,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hvn)]
      exact inv_mul_cancel₀ hvn0
    · simp only [q,map_smul,smul_eq_mul]
      rw [inv_mul_eq_div]
      exact (lt_div_iff₀ hvn).mpr hval
  have hblocks : ∀ n : ℕ,∃ v : Π₀ i,E i,
      ‖finite E p v‖^p.toReal ≤ (n:ℝ) ∧ (n:ℝ)*ε ≤ x (finite E p v) := by
    intro n
    induction n with
    | zero => exact ⟨0,by simp [Real.zero_rpow hp0.ne'],by simp⟩
    | succ n ih =>
      obtain ⟨v,hvn,hvx⟩ := ih
      obtain ⟨q,hqout,hqn,hqx⟩ := hchoose v.support
      have hd : Disjoint v.support q.support := by
        exact Finset.disjoint_left.mpr (fun i hiv hiq => hqout i hiq hiv)
      refine ⟨v+q, ?_, ?_⟩
      · rw [finite_norm_add E p rfl hp0 v q hd,hqn,Real.one_rpow]
        push_cast
        linarith
      · simp only [map_add,Nat.cast_add,Nat.cast_one]
        linarith
  have ht : Tendsto (fun n : ℕ => (n:ℝ)^(p.toReal-1)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hp)).comp tendsto_natCast_atTop_atTop
  obtain ⟨n,hn,hn0⟩ := ((ht.eventually_gt_atTop (‖x‖^p.toReal/ε^p.toReal)).and
    (eventually_gt_atTop (0:ℕ))).exists
  have hnR : (0:ℝ)<n := by exact_mod_cast hn0
  have hnε : ‖x‖^p.toReal < (n:ℝ)^(p.toReal-1)*ε^p.toReal :=
    (div_lt_iff₀ (Real.rpow_pos_of_pos hε _)).mp hn
  obtain ⟨v,hvn,hvx⟩ := hblocks n
  have hxb : x (finite E p v) ≤ ‖x‖*‖finite E p v‖ :=
    (Real.le_norm_self _).trans (x.le_opNorm _)
  have hprod := hvx.trans hxb
  have hrpow := Real.rpow_le_rpow (mul_nonneg hnR.le hε.le) hprod hp0.le
  rw [Real.mul_rpow hnR.le hε.le,Real.mul_rpow (norm_nonneg _) (norm_nonneg _)] at hrpow
  have hmul := mul_le_mul_of_nonneg_left hvn (Real.rpow_nonneg (norm_nonneg x) p.toReal)
  have he : (n:ℝ)^p.toReal=(n:ℝ)*(n:ℝ)^(p.toReal-1) := by
    rw [Real.rpow_sub hnR]
    simp only [Real.rpow_one]
    field_simp
  rw [he] at hrpow
  have hh : (n:ℝ)*((n:ℝ)^(p.toReal-1)*ε^p.toReal) ≤ (n:ℝ)*‖x‖^p.toReal := by
    nlinarith
  exact (not_le.mpr hnε) ((mul_le_mul_iff_right₀ hnR).mp hh)

lemma small_tail (hp : 1 < p.toReal) (x : StrongDual ℝ (lp E p)) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : Finset ι, ∀ v : Π₀ i,E i, (∀ i ∈ v.support,i ∉ C) →
      |x (finite E p v)| ≤ ε*‖finite E p v‖ := by
  obtain ⟨C,hC⟩ := small_tail_upper E p hp x hε
  refine ⟨C,?_⟩
  intro v hv
  apply abs_le.mpr
  refine ⟨?_,hC v hv⟩
  have h := hC (-v) (by simpa only [DFinsupp.support_neg] using hv)
  simp only [map_neg,norm_neg] at h
  linarith
@[simp] lemma finite_single {ι : Type*} (E : ι → Type*) [∀ i,NormedAddCommGroup (E i)] [∀ i,NormedSpace ℝ (E i)] (p : ℝ≥0∞) [Fact (1 ≤ p)] (i : ι) (v : E i) :
    finite E p (DFinsupp.single i v)=lp.single p i v := by
  ext j
  by_cases he : i=j
  · subst j
    simp [lp.single_apply]
  · simp [lp.single_apply,DFinsupp.single_apply,he]

lemma finite_dense (hp : p ≠ ⊤) : DenseRange (finite E p) := by
  intro v
  apply isClosed_closure.mem_of_tendsto (lp.hasSum_single hp v)
  apply Filter.Eventually.of_forall
  intro S
  apply subset_closure
  refine ⟨∑ i ∈ S,DFinsupp.single i (v i),?_⟩
  simp only [map_sum,finite_single]

def dualInclude (i : ι) : StrongDual ℝ (E i) →L[ℝ] StrongDual ℝ (lp E p) :=
  (lp.evalCLM ℝ E p i).precomp ℝ
lemma dualInclude_apply (i : ι) (x : StrongDual ℝ (E i)) (v : lp E p) :
    dualInclude E p i x v=x (v i) := rfl

def dualHead (C : Finset ι) (x : StrongDual ℝ (lp E p)) : StrongDual ℝ (lp E p) :=
  ∑ i ∈ C,dualInclude E p i (x.comp (lp.singleContinuousLinearMap ℝ E p i))
lemma dualHead_apply (C : Finset ι) (x : StrongDual ℝ (lp E p)) (v : lp E p) :
    dualHead E p C x v=∑ i ∈ C,x (lp.single p i (v i)) := by
  simp only [dualHead,sum_apply,dualInclude_apply,
    ContinuousLinearMap.comp_apply]
  rfl

lemma finite_filter (C : Finset ι) (v : Π₀ i,E i) :
    finite E p (v.filter (fun i => i ∈ C))=∑ i ∈ C,lp.single p i (v i) := by
  ext i
  rw [finite_apply,DFinsupp.filter_apply]
  simp only [lp.coeFn_sum,Finset.sum_apply,lp.single_apply]
  by_cases hi : i ∈ C
  · rw [ite_eq_left hi]
    symm
    calc
      _ = Pi.single i (v i) i := Finset.sum_eq_single i
        (fun j _ hji => Pi.single_eq_of_ne hji.symm _) (fun h => (h hi).elim)
      _ = _ := Pi.single_eq_same i (v i)
  · rw [ite_eq_right hi]
    apply Eq.symm
    apply Finset.sum_eq_zero
    intro j hj
    exact Pi.single_eq_of_ne (ne_of_mem_of_not_mem hj hi).symm _

lemma finite_filter_norm (Q : ι → Prop) [DecidablePred Q] (v : Π₀ i,E i) :
    ‖finite E p (v.filter Q)‖ ≤ ‖finite E p v‖ := by
  apply lp.norm_mono (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p)))
  intro i
  simp only [finite_apply,DFinsupp.filter_apply]
  split_ifs <;> simp

lemma dual_approximation (hp : 1 < p.toReal) (x : StrongDual ℝ (lp E p)) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : Finset ι, ‖x-dualHead E p C x‖ < ε := by
  have hptop : p ≠ ⊤ := by intro he; norm_num [he] at hp
  obtain ⟨C,hC⟩ := small_tail E p hp x (half_pos hε)
  refine ⟨C,?_⟩
  have hb : ‖x-dualHead E p C x‖ ≤ ε/2 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (half_pos hε).le
    intro v
    refine (finite_dense E p hptop).induction_on (p := fun v =>
      ‖(x-dualHead E p C x) v‖ ≤ (ε/2)*‖v‖) v
      (isClosed_le ((x-dualHead E p C x).continuous.norm) (continuous_const.mul continuous_norm)) ?_
    intro w
    let wi := w.filter (fun i => i ∈ C)
    let wo := w.filter (fun i => i ∉ C)
    have hw : wi+wo=w := DFinsupp.filter_add_filter_not _ _
    have hh : dualHead E p C x (finite E p w)=x (finite E p wi) := by
      rw [dualHead_apply]
      dsimp [wi]
      rw [finite_filter,map_sum]
    have he : (x-dualHead E p C x) (finite E p w)=x (finite E p wo) := by
      change x (finite E p w)-dualHead E p C x (finite E p w)=_
      rw [hh,← hw,map_add,map_add]
      ring
    have ho : ∀ i ∈ wo.support,i ∉ C := by
      intro i hi hci
      have hz : wo i=0 := by simp [wo,DFinsupp.filter_apply,hci]
      exact (DFinsupp.mem_support_iff.mp hi) hz
    rw [he,Real.norm_eq_abs]
    exact (hC wo ho).trans (mul_le_mul_of_nonneg_left (finite_filter_norm E p _ w) (half_pos hε).le)
  exact hb.trans_lt (half_lt_self hε)

lemma dual_separable [Countable ι] [∀ i,TopologicalSpace.SeparableSpace (StrongDual ℝ (E i))]
    (hp : 1 < p.toReal) : TopologicalSpace.SeparableSpace (StrongDual ℝ (lp E p)) := by
  let S : Set (StrongDual ℝ (lp E p)) := ⋃ i,Set.range (dualInclude E p i)
  let V := Submodule.span ℝ S
  have hd : Dense (V : Set (StrongDual ℝ (lp E p))) := by
    intro x
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨C,hC⟩ := dual_approximation E p hp x hε
    refine ⟨dualHead E p C x,?_,?_⟩
    · apply Submodule.sum_mem
      intro i hi
      apply Submodule.subset_span
      apply Set.mem_iUnion.mpr
      exact ⟨i,_,rfl⟩
    · simpa only [dist_eq_norm] using hC
  apply hd.isSeparable_iff.mp
  apply TopologicalSpace.IsSeparable.span
  exact TopologicalSpace.IsSeparable.iUnion (fun i =>
    TopologicalSpace.isSeparable_range (dualInclude E p i).continuous)
end LpDual

end DiamondDistortion

end

end OAI
