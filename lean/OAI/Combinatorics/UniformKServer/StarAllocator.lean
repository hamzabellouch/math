import Mathlib
import OAI.Combinatorics.UniformKServer.StarOutputFeasibility
import OAI.Combinatorics.UniformKServer.SwitchFinite

namespace OAI

                                    
section

/-! The actual causal star allocator.  At time zero it uses the true lower
requirements, avoiding an unjustified feasibility claim for the arbitrary
initial minimizer states.  All subsequent outputs are the source's two rules. -/
noncomputable section
namespace UniformKServer.StarAllocator
open Finset StarRanks StarSchedules StarLower StarOutputData StarOutputFeasibility
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

theorem wholesale_measurable (d : Data Ω ι k) (t : ℕ) {ω v : Ω}
    (h : (d.filtration (t+1)).r ω v) : StarCaps.wholesale d t ω=StarCaps.wholesale d t v := by
  apply CausalSchedules.reset_congr
  · intro s hs
    exact held_measurable d s (refining d hs h)
  · intro s hs
    exact refresh_measurable d StarConstants.delta s (refining d (by omega) h)

def switchData (d : Data Ω ι k) : SwitchFinite.Data Ω ι (Fin k) where
  core := alphaData d
  deficit := deficit d StarConstants.delta
  nonneg := deficit_nonneg d StarConstants.delta
  measurable := fun t _ _ h => deficit_measurable d StarConstants.delta t h
  reset := StarCaps.wholesale d
  reset_measurable := fun t _ _ h => wholesale_measurable d t h

def tag (d : Data Ω ι k) (t : ℕ) (ω : Ω) : SwitchTracker.Rule :=
  SwitchFinite.rule (switchData d) t ω

def ruleOutput (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (q : ℝ) : ι → ℝ :=
  match EpochGeometry.dominant (epoch d StarConstants.delta t ω) with
  | none => one d t ω q
  | some o => match tag d t ω with
    | .one => one d t ω q
    | .two => two d hk t ω q o

def output (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (q : ℝ) : ι → ℝ :=
  match t with
  | 0 => fun i => lower d (childBeta d 0 ω i) 0 ω i
  | t+1 => ruleOutput d hk (t+1) ω q

theorem tag_valid (d : Data Ω ι k) (t : ℕ) (ω : Ω) :
    SwitchTracker.valid (tag d t ω) (StarOutputData.mass d t ω) (deficit d StarConstants.delta t ω) :=
  SwitchFinite.rule_valid (switchData d) t ω

theorem rule_lower (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) {q : ℝ}
    (hq : parentLower d (t+1) ω ≤ q) (i : ι) :
    lower d (childBeta d (t+1) ω i) (t+1) ω i ≤ ruleOutput d hk (t+1) ω q i := by
  have hv := tag_valid d (t+1) ω
  unfold ruleOutput
  cases ho : EpochGeometry.dominant (epoch d StarConstants.delta (t+1) ω) with
  | none =>
    apply one_lower d hk t ω hq
    simp only [deficit,ho,zero_div]
    exact mass_nonneg d (t+1) ω
  | some o =>
    cases hr : tag d (t+1) ω with
    | one => exact one_lower d hk t ω hq (by simpa only [hr,SwitchTracker.valid] using hv) i
    | two => exact two_lower d hk t ω hq o ho (by simpa only [hr,SwitchTracker.valid] using hv) i

theorem rule_upper (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (q : ℝ) (i : ι) :
    ruleOutput d hk t ω q i ≤ StarCaps.cap d t ω i := by
  cases ho : EpochGeometry.dominant (epoch d StarConstants.delta t ω) with
  | none => simpa only [ruleOutput,ho] using one_upper d t ω q i
  | some o =>
    cases hr : tag d t ω <;> simp only [ruleOutput,ho,hr]
    · exact one_upper d t ω q i
    · exact two_upper d hk t ω q o i

theorem rule_budget (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) {q : ℝ}
    (hq : parentLower d t ω ≤ q) : (∑ i, ruleOutput d hk t ω q i) ≤ q := by
  cases ho : EpochGeometry.dominant (epoch d StarConstants.delta t ω) with
  | none => simpa only [ruleOutput,ho] using one_budget d hk t ω hq
  | some o =>
    cases hr : tag d t ω <;> simp only [ruleOutput,ho,hr]
    · exact one_budget d hk t ω hq
    · exact two_budget d hk t ω q o

theorem lower_mono (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (i : ι) :
    lower d (childBeta d t ω i) t ω i ≤ lower d (parentBeta d t ω) t ω i := by
  rw [decomposition,decomposition]
  have h := mul_le_mul_of_nonneg_right (parameter_le d hk t ω i) (core_nonneg d t ω i)
  linarith [flex_mono d hk t ω i]

theorem lower_cap (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (i : ι) :
    lower d (childBeta d t ω i) t ω i ≤ StarCaps.cap d t ω i := by
  rw [decomposition]
  have h := cap_child d hk t ω i
  have hb : 0 ≤ childBeta d t ω i := by linarith [(child_allowed d hk t ω i).1]
  have hh := mul_nonneg hb (core_nonneg d t ω i)
  change _ ≤ RankData.coreCount (flags d t ω i)+StarCaps.flex d t ω i
  change FlexEstimates.trueFlex (input d i) (childBeta d t ω i) t ω ≤ _ at h
  linarith

theorem feasible (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) {q : ℝ}
    (hq : parentLower d t ω ≤ q) :
    (∀ i, lower d (childBeta d t ω i) t ω i ≤ output d hk t ω q i) ∧
    (∀ i, output d hk t ω q i ≤ StarCaps.cap d t ω i) ∧
    (∑ i, output d hk t ω q i) ≤ q := by
  cases t with
  | zero =>
    exact ⟨fun _ => le_rfl,lower_cap d hk 0 ω,
      (sum_le_sum (fun i _ => lower_mono d hk 0 ω i)).trans ((parent_dominates d hk 0 ω).trans hq)⟩
  | succ t => exact ⟨rule_lower d hk t ω hq,rule_upper d hk (t+1) ω q,rule_budget d hk (t+1) ω hq⟩

theorem nonneg (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) {q : ℝ}
    (hq : parentLower d t ω ≤ q) (i : ι) : 0 ≤ output d hk t ω q i :=
  (lower_nonneg d (child_allowed d hk t ω i) t ω i).trans ((feasible d hk t ω hq).1 i)

theorem cap_measurable (d : Data Ω ι k) (t : ℕ) {ω v : Ω}
    (h : (d.filtration t).r ω v) : StarCaps.cap d t ω=StarCaps.cap d t v := by
  funext i
  unfold StarCaps.cap StarCaps.flex
  rw [flag_measurable d t h,epoch_measurable d StarConstants.delta t h,
    upper_measurable d StarConstants.delta t h,flex_measurable d i _ _ t h]

theorem childBeta_measurable (d : Data Ω ι k) (t : ℕ) {ω v : Ω}
    (h : (d.filtration t).r ω v) (i : ι) : childBeta d t ω i=childBeta d t v i := by
  have hp : (fun j => (input d i j).posterior t ω)=(fun j => (input d i j).posterior t v) :=
    funext fun j => (input d i j).posterior_measurable t ω v h
  simp only [childBeta,ParentBeta.trueParam,ParentScale.trueX,hp]

theorem lower_measurable (d : Data Ω ι k) (t : ℕ) {ω v : Ω}
    (h : (d.filtration t).r ω v) (i : ι) :
    lower d (childBeta d t ω i) t ω i=lower d (childBeta d t v i) t v i := by
  unfold lower
  rw [childBeta_measurable d t h i]
  congr 1
  funext j
  exact (input d i j).posterior_measurable t ω v h

theorem rule_measurable (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) {ω v : Ω}
    (h : (d.filtration t).r ω v) (q : ℝ) : ruleOutput d hk t ω q=ruleOutput d hk t v q := by
  have htag : tag d t ω=tag d t v := SwitchFinite.rule_measurable (switchData d) t h
  have ha : alpha d t ω=alpha d t v := AlphaFiniteInput.alpha_measurable (alphaData d) t h
  have hs : side d hk t ω=side d hk t v := SideFiniteInput.tracker_measurable (sideData d hk) t h
  unfold ruleOutput one two
  rw [epoch_measurable d StarConstants.delta t h,htag,cap_measurable d t h,ha,hs,
    deficit_measurable d StarConstants.delta t h]

theorem measurable (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) {ω v : Ω}
    (h : (d.filtration t).r ω v) (q : ℝ) : output d hk t ω q=output d hk t v q := by
  cases t with
  | zero => exact funext fun i => lower_measurable d 0 h i
  | succ t => exact rule_measurable d hk (t+1) h q

end UniformKServer.StarAllocator

end


end

end OAI
