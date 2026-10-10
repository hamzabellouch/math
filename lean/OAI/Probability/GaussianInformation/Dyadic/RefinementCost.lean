import Mathlib
import OAI.Probability.GaussianInformation.Dyadic.ChannelProducts

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace RepeatedLocalization
lemma finite_entropy_le_subprob_reference {ι : Type*} [Fintype ι]
    (p b : ι → ℝ) (hp : ∀ i,0 ≤ p i) (hpsum : ∑ i,p i = 1)
    (hb : ∀ i,0 < b i) (hbsum : ∑ i,b i ≤ 1) :
    -(∑ i,xlog (p i)) ≤ -∑ i,p i*Real.log (b i) := by
  have hi (i : ι) : p i-b i ≤ p i*Real.log (p i/b i) := by
    have h := log_ratio_lower (hp i) (hb i).le (by norm_num : (0:ℝ) < 1)
      (fun hz => False.elim ((hb i).ne' hz))
    simpa [xlog_one] using h
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
  simp_rw [log_ratio_mul (hb _).ne'] at hs
  simp only [Finset.sum_sub_distrib,hpsum] at hs
  linarith

lemma weighted_log_max_ratio_le {p θ g : ℝ} (hp : 0 ≤ p) (hθ : 0 < θ)
    (hg : 0 < g) (hg1 : g ≤ 1) :
    p*Real.log (max 1 (θ/p)) ≤ -p*Real.log g+g*θ := by
  by_cases hpz : p = 0
  · simp only [hpz,zero_mul,neg_zero,zero_add]
    positivity
  have hpp : 0 < p := lt_of_le_of_ne hp (Ne.symm hpz)
  by_cases hθp : θ ≤ p
  · rw [max_eq_left ((div_le_one hpp).mpr hθp),Real.log_one,mul_zero]
    have hl := Real.log_nonpos hg.le hg1
    have hd := mul_nonpos_of_nonneg_of_nonpos hp hl
    nlinarith [mul_pos hg hθ]
  · rw [max_eq_right ((one_le_div hpp).mpr (le_of_not_ge hθp))]
    have harg : 0 < θ*g/p := div_pos (mul_pos hθ hg) hpp
    have h := Real.log_le_sub_one_of_pos harg
    rw [Real.log_div (mul_pos hθ hg).ne' hpz,Real.log_mul hθ.ne' hg.ne'] at h
    rw [Real.log_div hθ.ne' hpz]
    have hh := mul_le_mul_of_nonneg_left h hp
    have he : p*(θ*g/p) = θ*g := by field_simp
    nlinarith

lemma finite_log_concentration_le {ι : Type*} [Fintype ι]
    (p θ g : ι → ℝ) (hp : ∀ i,0 ≤ p i) (hθ : ∀ i,0 < θ i)
    (hg : ∀ i,0 < g i) (hg1 : ∀ i,g i ≤ 1)
    (hbound : ∑ i,θ i*g i ≤ 1) :
    (∑ i,p i*Real.log (max 1 (θ i/p i))) ≤ -(∑ i,p i*Real.log (g i))+1 := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => weighted_log_max_ratio_le (hp i) (hθ i) (hg i) (hg1 i))
  simp only [Finset.sum_add_distrib,neg_mul,Finset.sum_neg_distrib,mul_comm (g _) (θ _)] at h
  linarith

noncomputable def depthGeometric (j : ℕ) : ℝ := (1/2:ℝ)^(j+1)
lemma depthGeometric_pos (j : ℕ) : 0 < depthGeometric j := by unfold depthGeometric; positivity
lemma depthGeometric_le_one (j : ℕ) : depthGeometric j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
lemma log_depthGeometric (j : ℕ) : Real.log (depthGeometric j) = -((j:ℝ)+1)*Real.log 2 := by
  simp only [depthGeometric,Real.log_pow,Real.log_div one_ne_zero (by norm_num : (2:ℝ) ≠ 0),
    Real.log_one,zero_sub,Nat.cast_add,Nat.cast_one]
  ring

lemma depthGeometric_sum_le_one (D : ℕ) : ∑ j ∈ Finset.range (D+1),depthGeometric j ≤ 1 := by
  have hsum : ∀ d,∑ j ∈ Finset.range d,depthGeometric j = 1-(1/2:ℝ)^d := by
    intro d
    induction d with
    | zero => simp
    | succ d ih => rw [Finset.sum_range_succ,ih]; unfold depthGeometric; rw [pow_succ]; ring
  rw [hsum]
  have := pow_nonneg (show (0:ℝ) ≤ 1/2 by norm_num) (D+1)
  linarith

lemma entropy_and_concentration_depth {ι : Type*} [Fintype ι]
    (n : ℕ) (p : ι → ℝ) (j : ι → ℕ) (hp : ∀ i,0 ≤ p i) (hpsum : ∑ i,p i = 1)
    (hbudget : ∑ i,(2:ℝ)^(-(n:ℝ)*(j i:ℝ)/2)*depthGeometric (j i) ≤ 1) :
    -(∑ i,xlog (p i)) ≤ ((n:ℝ)/2+1)*Real.log 2*(∑ i,p i*(j i:ℝ))+Real.log 2 ∧
    (∑ i,p i*Real.log (max 1 ((2:ℝ)^(-(n:ℝ)*(j i:ℝ)/2)/p i))) ≤
      Real.log 2*(∑ i,p i*(j i:ℝ))+Real.log 2+1 := by
  have hθ (i : ι) : 0 < (2:ℝ)^(-(n:ℝ)*(j i:ℝ)/2) := Real.rpow_pos_of_pos (by norm_num) _
  have hlog (i : ι) : Real.log ((2:ℝ)^(-(n:ℝ)*(j i:ℝ)/2)*depthGeometric (j i)) =
      -((n:ℝ)/2+1)*Real.log 2*(j i:ℝ)-Real.log 2 := by
    rw [Real.log_mul (hθ i).ne' (depthGeometric_pos _).ne',Real.log_rpow (by norm_num : (0:ℝ) < 2),log_depthGeometric]
    ring
  have he := finite_entropy_le_subprob_reference p (fun i => (2:ℝ)^(-(n:ℝ)*(j i:ℝ)/2)*depthGeometric (j i))
    hp hpsum (fun i => mul_pos (hθ i) (depthGeometric_pos _)) hbudget
  have hb := finite_log_concentration_le p (fun i => (2:ℝ)^(-(n:ℝ)*(j i:ℝ)/2))
    (fun i => depthGeometric (j i)) hp hθ (fun i => depthGeometric_pos _) (fun i => depthGeometric_le_one _) hbudget
  have halg (i : ι) : p i*(-((n:ℝ)/2+1)*Real.log 2*(j i:ℝ)-Real.log 2) =
      -(((n:ℝ)/2+1)*Real.log 2)*(p i*(j i:ℝ))-Real.log 2*p i := by ring
  have hbalg (i : ι) : p i*(-((j i:ℝ)+1)*Real.log 2) =
      -(Real.log 2)*(p i*(j i:ℝ))-Real.log 2*p i := by ring
  simp_rw [hlog,halg] at he
  simp_rw [log_depthGeometric,hbalg] at hb
  simp only [Finset.sum_sub_distrib,← Finset.mul_sum,hpsum,mul_one] at he hb
  constructor <;> linarith

structure HeavyRefinement (n : ℕ) (μ : Measure (Coordinate n)) (Q : Cell n) where
  Index : Type
  [finiteIndex : Fintype Index]
  channel : FiniteChannel (Coordinate n) Index
  cell : Index → Cell n
  B : Index → ℝ
  B_one : ∀ i, 1 ≤ B i
  select : Coordinate n → Index
  select_fiber : ∀ i, MeasurableSet {z | select z = i}
  chosen : ∀ i z, 0 < channel.prob i z → select z = i
  cell_subset : ∀ i, cellSet (cell i) ⊆ cellSet Q
  select_mem : ∀ z ∈ cellSet Q, z ∈ cellSet (cell (select z))
  level_ge : ∀ i,Q.1 ≤ (cell i).1
  support : ∀ i,0 < scoreMass μ (channel.prob i) →
    scorePosterior μ (channel.prob i) (cellSet (cell i)) = 1
  spread : ∀ i,0 < scoreMass μ (channel.prob i) →
    DyadicSpread (scorePosterior μ (channel.prob i)) (cell i) (B i)
  entropy_bound : finiteInformation μ channel.prob ≤
    ((n:ℝ)/2+1)*Real.log 2*(∑ i,scoreMass μ (channel.prob i)*((cell i).1-Q.1:ℕ))+Real.log 2
  concentration_bound : (∑ i,scoreMass μ (channel.prob i)*Real.log (B i)) ≤
    Real.log 2*(∑ i,scoreMass μ (channel.prob i)*((cell i).1-Q.1:ℕ))+Real.log 2+1

attribute [instance] HeavyRefinement.finiteIndex

lemma exists_heavy_refinement {n : ℕ} (hn : 0 < n)
    (μ : Measure (Coordinate n)) [IsProbabilityMeasure μ] (Q : Cell n)
    (hQ : μ (cellSet Q) = 1) {C : ℝ} (hC : 0 ≤ C)
    (hdom : ∀ R : Cell n,μ.real (cellSet R) ≤ C*(1/2:ℝ)^(n*R.1)) :
    Nonempty (HeavyRefinement n μ Q) := by
  classical
  obtain ⟨D,hD⟩ := exists_heavy_cutoff hn μ hC hdom Q
  let s := (finite_range_deepHeavyCell μ Q D).toFinset
  let κ := {R : Cell n // R ∈ s}
  let f : Coordinate n → κ := fun z => ⟨deepHeavyCell μ Q D z,by
    simpa only [s,Set.Finite.mem_toFinset] using (Set.mem_range_self z (f := deepHeavyCell μ Q D))⟩
  have hf : Measurable f := (measurable_deepHeavyCell μ Q D).subtype_mk
  let q := FiniteChannel.deterministic f hf
  let j : κ → ℕ := fun i => i.val.1-Q.1
  let P : κ → ℝ := fun i => scoreMass μ (q.prob i)
  let B : κ → ℝ := fun i => max 1 (heavyThreshold n (j i)/P i)
  have hQa : ∀ᵐ z ∂μ,z ∈ cellSet Q := (mem_ae_iff_prob_eq_one (measurableSet_cellSet Q)).mpr hQ
  have hQr : μ.real (cellSet Q) = 1 := by simp [measureReal_def,hQ]
  have hprop (R : Cell n) (hR : R ∈ s) :=
    heavy_selection_range_properties hn μ Q hQr D (by simpa only [s,Set.Finite.mem_toFinset] using hR)
  have hbudget : ∑ i : κ,heavyThreshold n (j i)*depthGeometric (j i) ≤ 1 := by
    change (∑ i : {R : Cell n // R ∈ s}, heavyThreshold n (i.val.1-Q.1)*depthGeometric (i.val.1-Q.1)) ≤ 1
    rw [Finset.sum_coe_sort s (fun R : Cell n => heavyThreshold n (R.1-Q.1)*depthGeometric (R.1-Q.1))]
    exact heavy_cell_weight_budget hn μ Q D s (fun R hR => (hprop R hR).1)
      (fun R hR => (hprop R hR).2.1) (fun R hR => (hprop R hR).2.2)
      depthGeometric (fun j => (depthGeometric_pos j).le) (depthGeometric_sum_le_one D)
  have hest := entropy_and_concentration_depth n P j
    (fun i => scoreMass_nonneg μ _ (q.nonneg i)) (q.mass_total μ) hbudget
  have hev (i : κ) : q.prob i =ᵐ[μ]
      {z | z ∈ cellSet Q ∧ deepHeavyCell μ Q D z = i.val}.indicator (fun _ => (1:ℝ)) := by
    filter_upwards [hQa] with z hz
    have he : f z = i ↔ deepHeavyCell μ Q D z = i.val := Subtype.ext_iff
    simp [q,FiniteChannel.deterministic,he,hz,Set.indicator]
  have hmass (i : κ) : P i = μ.real {z | z ∈ cellSet Q ∧ deepHeavyCell μ Q D z = i.val} := by
    change (∫ z,q.prob i z ∂μ) = _
    rw [integral_congr_ae (hev i)]
    exact scoreMass_indicator_one μ _ (measurable_heavySelectionEvent μ Q D i.val)
  refine ⟨{ Index := κ
            channel := q
            cell := Subtype.val
            B := B
            B_one := fun i => le_max_left _ _
            select := f
            select_fiber := fun i => hf (measurableSet_singleton i)
            chosen := fun i z hz => by
              by_contra h
              simp [q,FiniteChannel.deterministic,h] at hz
            cell_subset := fun i => by
              have hmem : i.val ∈ Set.range (deepHeavyCell μ Q D) := by
                simpa only [s,Set.Finite.mem_toFinset] using i.property
              obtain ⟨z,hz⟩ := hmem
              rw [← hz]
              exact deepHeavyCell_subset hn μ Q D z
            select_mem := fun z hz => deepHeavyCell_mem hn μ Q D hz
            level_ge := fun i => (hprop i.val i.property).1
            support := ?_
            spread := ?_
            entropy_bound := ?_
            concentration_bound := ?_ }⟩
  · intro i hi
    have := scorePosterior_probability μ _ (q.measurable i) (q.nonneg i) (q.le_one i) hi
    apply (prob_compl_eq_zero_iff (measurableSet_cellSet i.val)).mp
    apply (scorePosterior_null_iff μ _ (q.measurable i) (q.nonneg i) hi _ (measurableSet_cellSet i.val).compl).mpr
    filter_upwards [hQa] with z hz
    intro hnot
    have he : f z ≠ i := by
      intro he
      have hm := deepHeavyCell_mem hn μ Q D hz
      have hei : deepHeavyCell μ Q D z = i.val := congrArg Subtype.val he
      rw [hei] at hm
      exact hnot hm
    simp [q,FiniteChannel.deterministic,he]
  · intro i hi
    have hip : 0 < μ.real {z | z ∈ cellSet Q ∧ deepHeavyCell μ Q D z = i.val} := by
      rw [← hmass]; exact hi
    have hposterior : scorePosterior μ (q.prob i) =
        cond μ {z | z ∈ cellSet Q ∧ deepHeavyCell μ Q D z = i.val} := by
      rw [scorePosterior_congr_ae μ (hev i)]
      exact scorePosterior_indicator_one μ _ (measurable_heavySelectionEvent μ Q D i.val) hip
    rw [hposterior]
    have hlev : i.val.1 = Q.1+j i := by have := (hprop i.val i.property).1; dsimp [j]; omega
    dsimp [B]
    rw [hmass]
    exact selected_posterior_spread hn μ Q D hD hlev hip
  · rw [FiniteChannel.deterministic_information]
    exact hest.1
  · exact hest.2

end RepeatedLocalization

end OAI
