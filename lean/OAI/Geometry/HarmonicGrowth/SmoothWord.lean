import OAI.Geometry.HarmonicGrowth.Flow

namespace OAI

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set
open Set

namespace HarmonicCounterexample.FiniteControl.SmoothWord

def step (j : ℕ) (t : ℝ) : ℝ := Real.smoothTransition (t-(2*(j:ℝ)+1))
def bump (j : ℕ) (t : ℝ) : ℝ := deriv (step j) t

lemma step_smooth (j : ℕ) : ContDiff ℝ ∞ (step j) :=
  Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)

lemma step_deriv (j : ℕ) (t : ℝ) : HasDerivAt (step j) (bump j t) t :=
  ((step_smooth j).differentiable (by simp) t).hasDerivAt

lemma bump_smooth (j : ℕ) : ContDiff ℝ ∞ (bump j) :=
  (contDiff_infty_iff_deriv.1 (step_smooth j)).2

lemma step_zero {j : ℕ} {t : ℝ} (ht : t ≤ 2*(j:ℝ)+1) : step j t=0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

lemma step_one {j : ℕ} {t : ℝ} (ht : 2*(j:ℝ)+2 ≤ t) : step j t=1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

lemma bump_zero_after {j : ℕ} {t : ℝ} (ht : 2*(j:ℝ)+2 < t) : bump j t=0 := by
  have he : step j =ᶠ[𝓝 t] fun _ => (1:ℝ) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    exact step_one hs.le
  exact he.deriv_eq.trans (deriv_const t 1)

lemma bump_zero_before {j : ℕ} {t : ℝ} (ht : t < 2*(j:ℝ)+1) : bump j t=0 := by
  have he : step j =ᶠ[𝓝 t] fun _ => (0:ℝ) := by
    filter_upwards [eventually_lt_nhds ht] with s hs
    exact step_zero hs.le
  exact he.deriv_eq.trans (deriv_const t 0)

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

def state (X : ℕ → A) : ℕ → ℝ → A
  | 0,_ => 1
  | n+1,t => NormedSpace.exp (step n t • X n)*state X n t

def coefficient (X : ℕ → A) (n : ℕ) (t : ℝ) : A :=
  ∑ i ∈ Finset.range n,bump i t • X i

def leftWord (X : ℕ → A) : ℕ → A
  | 0 => 1
  | n+1 => NormedSpace.exp (X n)*leftWord X n

omit [CompleteSpace A] in
lemma coefficient_succ (X : ℕ → A) (n : ℕ) (t : ℝ) :
    coefficient X (n+1) t=coefficient X n t+bump n t • X n := by
  simp [coefficient,Finset.sum_range_succ]

omit [CompleteSpace A] in
lemma coefficient_after (X : ℕ → A) (n : ℕ) {t : ℝ} (ht : 2*(n:ℝ) < t) :
    coefficient X n t=0 := by
  unfold coefficient
  apply Finset.sum_eq_zero
  intro i hi
  have hi' : (i:ℝ)+1 ≤ n := by exact_mod_cast Finset.mem_range.1 hi
  rw [bump_zero_after (by linarith : 2*(i:ℝ)+2 < t),zero_smul]

lemma state_deriv (X : ℕ → A) (n : ℕ) (t : ℝ) :
    HasDerivAt (state X n) (coefficient X n t*state X n t) t := by
  induction n with
  | zero => simpa [state,coefficient] using hasDerivAt_const t (1:A)
  | succ n ih =>
    have he : HasDerivAt (fun s => NormedSpace.exp (step n s • X n))
        ((bump n t • X n)*NormedSpace.exp (step n t • X n)) t := by
      simpa only [Function.comp_def,smul_mul_assoc] using
        (hasDerivAt_exp_smul_const' (X n) (step n t)).scomp t (step_deriv n t)
    have hc : NormedSpace.exp (step n t • X n)*coefficient X n t=
        coefficient X n t*NormedSpace.exp (step n t • X n) := by
      by_cases ht : t ≤ 2*(n:ℝ)+1
      · rw [step_zero ht,zero_smul,NormedSpace.exp_zero,one_mul,mul_one]
      · rw [coefficient_after X n (by linarith : 2*(n:ℝ) < t),mul_zero,zero_mul]
    convert he.mul ih using 1
    · rfl
    · simp only [state,coefficient_succ,add_mul]
      rw [← mul_assoc _ (coefficient X n t),hc]
      noncomm_ring

omit [CompleteSpace A] in
lemma state_initial (X : ℕ → A) (n : ℕ) : state X n 0=1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [state,step_zero (by positivity : (0:ℝ) ≤ 2*(n:ℝ)+1),zero_smul,
      NormedSpace.exp_zero,one_mul,ih]

omit [CompleteSpace A] in
/-- Exact ordered exponentials of actual smooth disjoint pulses. This is not
an approximation by piecewise-constant coefficient controls. -/
theorem state_endpoint (X : ℕ → A) (n : ℕ) {t : ℝ} (ht : 2*(n:ℝ) ≤ t) :
    state X n t=leftWord X n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have ht' : 2*(n:ℝ)+2 ≤ t := by exact_mod_cast ht
    rw [state,step_one ht',one_smul,ih (by linarith),leftWord]

omit [CompleteSpace A] in
lemma coefficient_smooth (X : ℕ → A) (n : ℕ) : ContDiff ℝ ∞ (coefficient X n) := by
  apply ContDiff.sum
  intro i _
  exact (bump_smooth i).smul contDiff_const


omit [CompleteSpace A] in
lemma coefficient_before (X : ℕ → A) (n : ℕ) {t : ℝ} (ht : t < 1) :
    coefficient X n t=0 := by
  unfold coefficient
  apply Finset.sum_eq_zero
  intro i _
  rw [bump_zero_before (by have hi : (0:ℝ) ≤ i := Nat.cast_nonneg i; linarith : t < 2*(i:ℝ)+1),zero_smul]

/-- Unit-interval pulses have genuine open round gaps at both endpoints. -/
def duration (n : ℕ) : ℝ := 2*(n:ℝ)+1

lemma duration_pos (n : ℕ) : 0 < duration n := by unfold duration; positivity

def unitState (X : ℕ → A) (n : ℕ) (t : ℝ) : A := state X n (duration n*t)
def unitCoefficient (X : ℕ → A) (n : ℕ) (t : ℝ) : A :=
  duration n • coefficient X n (duration n*t)

lemma unitState_deriv (X : ℕ → A) (n : ℕ) (t : ℝ) :
    HasDerivAt (unitState X n) (unitCoefficient X n t*unitState X n t) t := by
  unfold unitState unitCoefficient
  simpa only [unitState,unitCoefficient,Function.comp_def,smul_mul_assoc,mul_one] using
    (state_deriv X n (duration n*t)).scomp t ((hasDerivAt_id t).const_mul (duration n))

omit [CompleteSpace A] in
lemma unitCoefficient_smooth (X : ℕ → A) (n : ℕ) :
    ContDiff ℝ ∞ (unitCoefficient X n) := by
  unfold unitCoefficient
  exact (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => duration n)).smul
    ((coefficient_smooth X n).comp ((contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => duration n)).mul contDiff_id))

omit [CompleteSpace A] in
lemma unitState_initial (X : ℕ → A) (n : ℕ) : unitState X n 0=1 := by
  simpa only [unitState,mul_zero] using state_initial X n

omit [CompleteSpace A] in
lemma unitState_endpoint (X : ℕ → A) (n : ℕ) : unitState X n 1=leftWord X n := by
  apply state_endpoint
  simp only [duration,mul_one]
  linarith

omit [CompleteSpace A] in
lemma unitCoefficient_zero_outside (X : ℕ → A) (n : ℕ) {t : ℝ}
    (ht : t ∉ Set.Icc (0:ℝ) 1) : unitCoefficient X n t=0 := by
  simp only [Set.mem_Icc,not_and_or,not_le] at ht
  unfold unitCoefficient
  obtain ht | ht := ht
  · rw [coefficient_before X n (by nlinarith [duration_pos n]),smul_zero]
  · rw [coefficient_after X n (by unfold duration; nlinarith),smul_zero]

omit [CompleteSpace A] in
lemma unitCoefficient_bounded (X : ℕ → A) (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t, ‖unitCoefficient X n t‖ ≤ M := by
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (unitCoefficient_smooth X n).continuous.continuousOn
  refine ⟨max M 0,le_max_right _ _,fun t => ?_⟩
  by_cases ht : t ∈ Set.Icc (0:ℝ) 1
  · exact (hM t ht).trans (le_max_left _ _)
  · rw [unitCoefficient_zero_outside X n ht,norm_zero]
    exact le_max_right _ _

end HarmonicCounterexample.FiniteControl.SmoothWord

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set
open Set

namespace HarmonicCounterexample.FiniteControl.SmoothWord
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

def unitOperator (X : ℕ → A) (n : ℕ) (t : ℝ) : A →L[ℝ] A :=
  ContinuousLinearMap.mul ℝ A (unitCoefficient X n t)

omit [CompleteSpace A] in
lemma unitOperator_continuous (X : ℕ → A) (n : ℕ) :
    Continuous (unitOperator X n) :=
  (ContinuousLinearMap.mul ℝ A).continuous.comp (unitCoefficient_smooth X n).continuous

omit [CompleteSpace A] in
lemma unitOperator_bounded (X : ℕ → A) (n : ℕ) :
    ∃ M : ℝ,0 ≤ M ∧ ∀ t, ‖unitOperator X n t‖ ≤ M := by
  obtain ⟨M,hM,hb⟩ := unitCoefficient_bounded X n
  exact ⟨M,hM,fun t => (ContinuousLinearMap.opNorm_mul_apply_le ℝ A _).trans (hb t)⟩

/-- The genuine globally convergent Peano--Baker sum for a smooth disjoint
pulse is exactly the explicit ordered-exponential state, not a formal symbol. -/
lemma actual_flow_eq_state (X : ℕ → A) (n : ℕ) :
    LinearODE.flow (unitOperator X n) 1 = unitState X n := by
  obtain ⟨M,hM,hb⟩ := unitOperator_bounded X n
  apply LinearODE.solution_unique (t₀ := 0) hM hb
    (LinearODE.flow_hasDerivAt (unitOperator_continuous X n) hM hb 1)
  · exact unitState_deriv X n
  · simp only [LinearODE.flow_initial,unitState_initial]

/-- Exact endpoint realization, including the empty word, by actual smooth
compactly supported coefficients, with the true initial value 1. -/
theorem actual_flow_endpoint (X : ℕ → A) (n : ℕ) :
    LinearODE.flow (unitOperator X n) 1 1=leftWord X n := by
  rw [actual_flow_eq_state,unitState_endpoint]

end HarmonicCounterexample.FiniteControl.SmoothWord

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set
open Set

namespace HarmonicCounterexample.FiniteControl.SmoothWord
open Set Filter
open scoped Topology BigOperators

lemma bump_deriv_zero_before {j : ℕ} {t : ℝ} (ht : t < 2*(j:ℝ)+1) :
    deriv (bump j) t=0 := by
  have he : bump j =ᶠ[𝓝 t] fun _ => (0:ℝ) := by
    filter_upwards [eventually_lt_nhds ht] with s hs
    exact bump_zero_before hs
  exact he.deriv_eq.trans (deriv_const t 0)

lemma bump_deriv_zero_after {j : ℕ} {t : ℝ} (ht : 2*(j:ℝ)+2 < t) :
    deriv (bump j) t=0 := by
  have he : bump j =ᶠ[𝓝 t] fun _ => (0:ℝ) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    exact bump_zero_after hs
  exact he.deriv_eq.trans (deriv_const t 0)

lemma packet_intervals_disjoint {i j : ℕ} (hij : i ≠ j) :
    Disjoint (Icc (2*(i:ℝ)+1) (2*(i:ℝ)+2)) (Icc (2*(j:ℝ)+1) (2*(j:ℝ)+2)) := by
  rw [Set.disjoint_left]
  intro t hi hj
  rcases lt_or_gt_of_ne hij with h|h
  · have hh : (i:ℝ)+1 ≤ j := by exact_mod_cast h
    linarith [hi.2,hj.1]
  · have hh : (j:ℝ)+1 ≤ i := by exact_mod_cast h
    linarith [hj.2,hi.1]

lemma packet_zero_off_interval {i : ℕ} {t : ℝ}
    (ht : t ∉ Icc (2*(i:ℝ)+1) (2*(i:ℝ)+2)) :
    bump i t=0 ∧ deriv (bump i) t=0 := by
  rcases lt_or_ge t (2*(i:ℝ)+1) with h|h
  · exact ⟨bump_zero_before h,bump_deriv_zero_before h⟩
  · have h' : 2*(i:ℝ)+2 < t := lt_of_not_ge (fun hh => ht ⟨h,hh⟩)
    exact ⟨bump_zero_after h',bump_deriv_zero_after h'⟩

/-- The selector is independent of every word amplitude and parameter. It may
jump only outside the active pulse support; no derivative of it is taken. -/
theorem exists_packet_selector (n : ℕ) [NeZero n] :
    ∃ d : ℝ → Fin n,∀ t i,i ≠ d t → bump i t=0 ∧ deriv (bump i) t=0 := by
  classical
  have hex (t : ℝ) : ∃ j : Fin n,∀ i : Fin n,i ≠ j → bump i t=0 ∧ deriv (bump i) t=0 := by
    by_cases ht : ∃ j : Fin n,t ∈ Icc (2*(j:ℝ)+1) (2*(j:ℝ)+2)
    · obtain ⟨j,hj⟩ := ht
      refine ⟨j,fun i hij => packet_zero_off_interval ?_⟩
      intro hi
      exact (Set.disjoint_left.1 (packet_intervals_disjoint (Fin.val_injective.ne hij))) hi hj
    · refine ⟨⟨0,NeZero.pos n⟩,fun i _ => packet_zero_off_interval ?_⟩
      exact fun hi => ht ⟨i,hi⟩
  choose d hd using hex
  exact ⟨d,hd⟩

variable {n : ℕ} {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

def packetScalar (a : Fin n → ℝ) (t : ℝ) : ℝ := ∑ j,a j*bump j t

def packetScalarD (a : Fin n → ℝ) (t : ℝ) : ℝ := ∑ j,a j*deriv (bump j) t

def packetCoefficient (a : Fin n → ℝ) (X : Fin n → A) (t : ℝ) : A :=
  ∑ j,(a j*bump j t) • X j

def packetCoefficientD (a : Fin n → ℝ) (X : Fin n → A) (t : ℝ) : A :=
  ∑ j,(a j*deriv (bump j) t) • X j

lemma packetCoefficient_deriv (a : Fin n → ℝ) (X : Fin n → A) (t : ℝ) :
    HasDerivAt (packetCoefficient a X) (packetCoefficientD a X t) t := by
  apply HasDerivAt.fun_sum
  intro j _
  exact (((bump_smooth j).differentiable (by simp) t).hasDerivAt.const_mul (a j)).smul_const (X j)

lemma packetCoefficient_smooth (a : Fin n → ℝ) (X : Fin n → A) :
    ContDiff ℝ ∞ (packetCoefficient a X) := by
  apply ContDiff.sum
  intro j _
  exact (contDiff_const.mul (bump_smooth j)).smul contDiff_const

lemma packetCoefficient_selected (a : Fin n → ℝ) (X : Fin n → A)
    (d : ℝ → Fin n) (hd : ∀ t i,i ≠ d t → bump i t=0 ∧ deriv (bump i) t=0) (t : ℝ) :
    packetCoefficient a X t=packetScalar a t • X (d t) ∧
    packetCoefficientD a X t=packetScalarD a t • X (d t) := by
  classical
  have hb : ∀ i : Fin n,i ≠ d t → a i*bump i t=0 := fun i hi => by rw [(hd t i hi).1,mul_zero]
  have hbd : ∀ i : Fin n,i ≠ d t → a i*deriv (bump i) t=0 := fun i hi => by rw [(hd t i hi).2,mul_zero]
  constructor
  · unfold packetCoefficient packetScalar
    rw [Finset.sum_eq_single (d t),Finset.sum_eq_single (d t)]
    · intro i _ hi;exact hb i hi
    · simp
    · intro i _ hi;rw [hb i hi,zero_smul]
    · simp
  · unfold packetCoefficientD packetScalarD
    rw [Finset.sum_eq_single (d t),Finset.sum_eq_single (d t)]
    · intro i _ hi;exact hbd i hi
    · simp
    · intro i _ hi;rw [hbd i hi,zero_smul]
    · simp

lemma packetCoefficient_zero (a : Fin n → ℝ) (X : Fin n → A) :
    packetCoefficient a X 0=0 := by
  unfold packetCoefficient
  apply Finset.sum_eq_zero
  intro j _
  rw [bump_zero_before (by positivity : (0:ℝ) < 2*(j:ℝ)+1),mul_zero,zero_smul]

lemma packetCoefficient_end (a : Fin n → ℝ) (X : Fin n → A) :
    packetCoefficient a X (duration n)=0 := by
  unfold packetCoefficient
  apply Finset.sum_eq_zero
  intro j _
  have hj : (j:ℝ)+1 ≤ n := by exact_mod_cast j.isLt
  rw [bump_zero_after (by dsimp [duration];linarith : 2*(j:ℝ)+2 < duration n),mul_zero,zero_smul]

end HarmonicCounterexample.FiniteControl.SmoothWord

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set
open Set

namespace HarmonicCounterexample.FiniteControl.SmoothWord
open Set Filter
open scoped Topology BigOperators

lemma wide_packet_intervals_disjoint {i j : ℕ} (hij : i ≠ j) :
    Disjoint (Icc (2*(i:ℝ)+(3/4:ℝ)) (2*(i:ℝ)+(9/4:ℝ)))
      (Icc (2*(j:ℝ)+(3/4:ℝ)) (2*(j:ℝ)+(9/4:ℝ))) := by
  rw [Set.disjoint_left]
  intro t hi hj
  rcases lt_or_gt_of_ne hij with h|h
  · have hh : (i:ℝ)+1 ≤ j := by exact_mod_cast h
    linarith [hi.2,hj.1]
  · have hh : (j:ℝ)+1 ≤ i := by exact_mod_cast h
    linarith [hj.2,hi.1]

/-- An angular selector whose jumps lie INSIDE open round gaps. This is
stronger than merely vanishing to infinite order at a packet endpoint and
matches the metric builder's exact local-constancy-or-round hypothesis. -/
theorem exists_round_gap_selector (n : ℕ) [NeZero n] :
    ∃ d : ℝ → Fin n,
      (∀ t i,i ≠ d t → bump i t=0 ∧ deriv (bump i) t=0) ∧
      ∀ t,(∀ᶠ s in 𝓝 t,d s=d t) ∨ (∀ᶠ s in 𝓝 t,∀ i : Fin n,bump i s=0) := by
  classical
  have hex (t : ℝ) : ∃ j : Fin n,∀ i : Fin n,
      t ∈ Icc (2*(i:ℝ)+(3/4:ℝ)) (2*(i:ℝ)+(9/4:ℝ)) → j=i := by
    by_cases ht : ∃ j : Fin n,t ∈ Icc (2*(j:ℝ)+(3/4:ℝ)) (2*(j:ℝ)+(9/4:ℝ))
    · obtain ⟨j,hj⟩ := ht
      refine ⟨j,fun i hi => ?_⟩
      by_contra hij
      exact (Set.disjoint_left.1 (wide_packet_intervals_disjoint (Fin.val_injective.ne hij))) hj hi
    · exact ⟨⟨0,NeZero.pos n⟩,fun i hi => (ht ⟨i,hi⟩).elim⟩
  choose d hd using hex
  have hwide {t : ℝ} {i : Fin n} (hi : t ∈ Icc (2*(i:ℝ)+1) (2*(i:ℝ)+2)) :
      t ∈ Icc (2*(i:ℝ)+(3/4:ℝ)) (2*(i:ℝ)+(9/4:ℝ)) := by constructor <;> linarith [hi.1,hi.2]
  refine ⟨d,?_,?_⟩
  · intro t i hne
    apply packet_zero_off_interval
    intro ht
    exact hne (hd t i (hwide ht)).symm
  · intro t
    by_cases ht : ∃ j : Fin n,t ∈ Icc (2*(j:ℝ)+1) (2*(j:ℝ)+2)
    · obtain ⟨j,hj⟩ := ht
      left
      have he : Ioo (2*(j:ℝ)+(3/4:ℝ)) (2*(j:ℝ)+(9/4:ℝ)) ∈ 𝓝 t :=
        Ioo_mem_nhds (by linarith [hj.1]) (by linarith [hj.2])
      filter_upwards [he] with s hs
      rw [hd s j ⟨hs.1.le,hs.2.le⟩,hd t j (hwide hj)]
    · right
      apply Filter.eventually_all.2
      intro j
      have hj : t ∉ Icc (2*(j:ℝ)+1) (2*(j:ℝ)+2) := fun hj => ht ⟨j,hj⟩
      rcases lt_or_ge t (2*(j:ℝ)+1) with h|h
      · filter_upwards [eventually_lt_nhds h] with s hs
        exact bump_zero_before hs
      · have h' : 2*(j:ℝ)+2 < t := lt_of_not_ge (fun hh => hj ⟨h,hh⟩)
        filter_upwards [eventually_gt_nhds h'] with s hs
        exact bump_zero_after hs

end HarmonicCounterexample.FiniteControl.SmoothWord

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set
open Set

namespace HarmonicCounterexample.FiniteControl.SmoothWord
open Set
open scoped BigOperators
variable {n : ℕ} {A H : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
local instance : NormedAddCommGroup (H →L[ℝ] A) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (H →L[ℝ] A) := ContinuousLinearMap.toNormedSpace

lemma packetCoefficient_hasFDerivAt (a : Fin n → H → ℝ) (X : Fin n → A)
    (a' : Fin n → H →L[ℝ] ℝ) {x : H} (ha : ∀ j,HasFDerivAt (a j) (a' j) x) (t : ℝ) :
    HasFDerivAt (fun y => packetCoefficient (fun j => a j y) X t)
      (∑ j,(a' j).smulRight (bump j t • X j)) x := by
  have hh := HasFDerivAt.fun_sum (u := Finset.univ)
    (fun j _ => (ha j).smul_const (bump j t • X j))
  simpa only [packetCoefficient,mul_smul] using hh

lemma packetCoefficient_jet_apply (a' : Fin n → H →L[ℝ] ℝ) (X : Fin n → A) (t : ℝ) (h : H) :
    (∑ j,(a' j).smulRight (bump j t • X j)) h=packetCoefficient (fun j => a' j h) X t := by
  simp only [sum_apply,ContinuousLinearMap.smulRight_apply,
    smul_smul,packetCoefficient]

def unitPacketCoefficient (a : Fin n → ℝ) (X : Fin n → A) (t : ℝ) : A :=
  duration n • packetCoefficient a X (duration n*t)

def unitPacketCoefficientD (a : Fin n → ℝ) (X : Fin n → A) (t : ℝ) : A :=
  (duration n)^2 • packetCoefficientD a X (duration n*t)

def unitPacketScalar (a : Fin n → ℝ) (t : ℝ) : ℝ :=
  duration n*packetScalar a (duration n*t)

def unitPacketScalarD (a : Fin n → ℝ) (t : ℝ) : ℝ :=
  (duration n)^2*packetScalarD a (duration n*t)

lemma unitPacketCoefficient_deriv (a : Fin n → ℝ) (X : Fin n → A) (t : ℝ) :
    HasDerivAt (unitPacketCoefficient a X) (unitPacketCoefficientD a X t) t := by
  have ht : HasDerivAt (fun s : ℝ => duration n*s) (duration n) t := by
    simpa only [mul_one,id_eq] using (hasDerivAt_id t).const_mul (duration n)
  have hh := ((packetCoefficient_deriv a X (duration n*t)).scomp t ht).fun_const_smul (duration n)
  change HasDerivAt (fun s => duration n • packetCoefficient a X (duration n*s)) _ t
  simpa only [unitPacketCoefficientD,smul_smul,pow_two,Function.comp_def] using hh

lemma packetCoefficientD_smooth (a : Fin n → ℝ) (X : Fin n → A) :
    ContDiff ℝ ∞ (packetCoefficientD a X) := by
  apply ContDiff.sum
  intro j _
  exact (contDiff_const.mul ((contDiff_infty_iff_deriv.1 (bump_smooth j)).2)).smul contDiff_const

lemma unitPacketCoefficient_smooth (a : Fin n → ℝ) (X : Fin n → A) :
    ContDiff ℝ ∞ (unitPacketCoefficient a X) :=
  contDiff_const.smul ((packetCoefficient_smooth a X).comp (contDiff_const.mul contDiff_id))

lemma unitPacketCoefficientD_smooth (a : Fin n → ℝ) (X : Fin n → A) :
    ContDiff ℝ ∞ (unitPacketCoefficientD a X) :=
  contDiff_const.smul ((packetCoefficientD_smooth a X).comp (contDiff_const.mul contDiff_id))

lemma unitPacketCoefficient_selected (a : Fin n → ℝ) (X : Fin n → A)
    (d : ℝ → Fin n) (hd : ∀ t i,i ≠ d t → bump i t=0 ∧ deriv (bump i) t=0) (t : ℝ) :
    unitPacketCoefficient a X t=unitPacketScalar a t • X (d (duration n*t)) ∧
    unitPacketCoefficientD a X t=unitPacketScalarD a t • X (d (duration n*t)) := by
  obtain ⟨h₁,h₂⟩ := packetCoefficient_selected a X d hd (duration n*t)
  constructor
  · exact congrArg (fun v : A => duration n • v) h₁ |>.trans (by simp only [smul_smul];rfl)
  · exact congrArg (fun v : A => (duration n)^2 • v) h₂ |>.trans (by simp only [smul_smul];rfl)

lemma unitPacketCoefficient_zero (a : Fin n → ℝ) (X : Fin n → A) :
    unitPacketCoefficient a X 0=0 := by
  simp only [unitPacketCoefficient,mul_zero,packetCoefficient_zero,smul_zero]

lemma unitPacketCoefficient_end (a : Fin n → ℝ) (X : Fin n → A) :
    unitPacketCoefficient a X 1=0 := by
  simp only [unitPacketCoefficient,mul_one,packetCoefficient_end,smul_zero]

lemma unitPacketCoefficient_hasFDerivAt (a : Fin n → H → ℝ) (X : Fin n → A)
    (a' : Fin n → H →L[ℝ] ℝ) {x : H} (ha : ∀ j,HasFDerivAt (a j) (a' j) x) (t : ℝ) :
    HasFDerivAt (fun y => unitPacketCoefficient (fun j => a j y) X t)
      (duration n • (∑ j,(a' j).smulRight (bump j (duration n*t) • X j))) x :=
  (packetCoefficient_hasFDerivAt a X a' ha (duration n*t)).const_smul (duration n)

lemma unitPacketCoefficient_jet_apply (a' : Fin n → H →L[ℝ] ℝ) (X : Fin n → A) (t : ℝ) (h : H) :
    (duration n • (∑ j,(a' j).smulRight (bump j (duration n*t) • X j))) h=
      unitPacketCoefficient (fun j => a' j h) X t := by
  simp only [smul_apply,packetCoefficient_jet_apply,unitPacketCoefficient]

end HarmonicCounterexample.FiniteControl.SmoothWord

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set
open Set

namespace HarmonicCounterexample.FiniteControl.SmoothWord
open Set
open scoped BigOperators
variable {n : ℕ} {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

def extendWord (a : Fin n → ℝ) (X : Fin n → A) (j : ℕ) : A :=
  if h : j < n then a ⟨j,h⟩ • X ⟨j,h⟩ else 0

omit [CompleteSpace A] in
lemma packetCoefficient_eq_coefficient (a : Fin n → ℝ) (X : Fin n → A) (t : ℝ) :
    packetCoefficient a X t=coefficient (extendWord a X) n t := by
  classical
  rw [coefficient,← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  simp only [extendWord,dite_eq_left j.isLt,smul_smul]
  rw [mul_comm]

omit [CompleteSpace A] in
lemma unitPacketCoefficient_eq_unitCoefficient (a : Fin n → ℝ) (X : Fin n → A) (t : ℝ) :
    unitPacketCoefficient a X t=unitCoefficient (extendWord a X) n t := by
  rw [unitPacketCoefficient,unitCoefficient,packetCoefficient_eq_coefficient]

/-- The finite amplitude family used by the switched Berger estimates is
exactly the smooth word family, including its order, not merely asymptotic. -/
theorem actual_packet_endpoint (a : Fin n → ℝ) (X : Fin n → A) :
    LinearODE.flow (fun t => ContinuousLinearMap.mul ℝ A (unitPacketCoefficient a X t)) 1 1=
      leftWord (extendWord a X) n := by
  have he : (fun t => ContinuousLinearMap.mul ℝ A (unitPacketCoefficient a X t))=
      unitOperator (extendWord a X) n := by
    funext t
    rw [unitPacketCoefficient_eq_unitCoefficient]
    rfl
  rw [he]
  exact actual_flow_endpoint (extendWord a X) n

end HarmonicCounterexample.FiniteControl.SmoothWord

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set
open Set

namespace HarmonicCounterexample.FiniteControl.SmoothWord
open Set
open scoped BigOperators

/-- Fixed global bounds on the actual smooth packets and their time
derivatives. These constants do not depend on the word amplitudes. -/
lemma packet_functions_bounded (j : ℕ) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ t,|bump j t| ≤ C ∧ |deriv (bump j) t| ≤ C := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (bump_smooth j).continuous.continuousOn
  obtain ⟨D,hD⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((contDiff_infty_iff_deriv.1 (bump_smooth j)).2).continuous.continuousOn
  refine ⟨max (max C D) 0,le_max_right _ _,fun t => ?_⟩
  by_cases ht : t ∈ Icc (2*(j:ℝ)+1) (2*(j:ℝ)+2)
  · exact ⟨(show |bump j t| ≤ C by simpa only [Real.norm_eq_abs] using hC t ht).trans
        ((le_max_left C D).trans (le_max_left _ _)),
      (show |deriv (bump j) t| ≤ D by simpa only [Real.norm_eq_abs] using hD t ht).trans
        ((le_max_right C D).trans (le_max_left _ _))⟩
  · obtain ⟨h,h'⟩ := packet_zero_off_interval ht
    simpa only [h,h',abs_zero] using And.intro (le_max_right (max C D) 0) (le_max_right (max C D) 0)

/-- Uniform values and time-derivatives on the normalized unit interval (in
fact globally). The radius is fixed prior to any choice of amplitudes. -/
theorem unitPacketScalar_uniform_bound (n : ℕ) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ (a : Fin n → ℝ) (M : ℝ),
      0 ≤ M → (∀ j,|a j| ≤ M) → ∀ t,
      |unitPacketScalar a t| ≤ C*M ∧ |unitPacketScalarD a t| ≤ C*M := by
  classical
  choose Cs hCs hb using fun j : Fin n => packet_functions_bounded j
  let C := ∑ j : Fin n,Cs j
  have hC : 0 ≤ C := Finset.sum_nonneg (fun j _ => hCs j)
  have hb₀ (a : Fin n → ℝ) (M : ℝ) (hM : 0 ≤ M) (ha : ∀ j,|a j| ≤ M) (t : ℝ) :
      |packetScalar a t| ≤ C*M ∧ |packetScalarD a t| ≤ C*M := by
    constructor
    · calc
        _ ≤ ∑ j : Fin n,|a j*bump j t| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j : Fin n,Cs j*M := Finset.sum_le_sum (fun j _ => by
          rw [abs_mul,mul_comm (Cs j) M]
          exact mul_le_mul (ha j) (hb j t).1 (abs_nonneg _) hM)
        _ = C*M := by rw [← Finset.sum_mul]
    · calc
        _ ≤ ∑ j : Fin n,|a j*deriv (bump j) t| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j : Fin n,Cs j*M := Finset.sum_le_sum (fun j _ => by
          rw [abs_mul,mul_comm (Cs j) M]
          exact mul_le_mul (ha j) (hb j t).2 (abs_nonneg _) hM)
        _ = C*M := by rw [← Finset.sum_mul]
  refine ⟨(duration n+(duration n)^2)*C,mul_nonneg (add_nonneg (duration_pos n).le (sq_nonneg _)) hC,?_⟩
  intro a M hM ha t
  have hh := hb₀ a M hM ha (duration n*t)
  have hd := (duration_pos n).le
  constructor
  · calc
      _ = duration n*|packetScalar a (duration n*t)| := by
        rw [unitPacketScalar,abs_mul,abs_of_nonneg hd]
      _ ≤ duration n*(C*M) := mul_le_mul_of_nonneg_left hh.1 hd
      _ ≤ (duration n+(duration n)^2)*C*M := by nlinarith [sq_nonneg (duration n),mul_nonneg hC hM]
  · calc
      _ = (duration n)^2*|packetScalarD a (duration n*t)| := by
        rw [unitPacketScalarD,abs_mul,abs_of_nonneg (sq_nonneg _)]
      _ ≤ (duration n)^2*(C*M) := mul_le_mul_of_nonneg_left hh.2 (sq_nonneg _)
      _ ≤ (duration n+(duration n)^2)*C*M := by nlinarith [mul_nonneg hC hM]

end HarmonicCounterexample.FiniteControl.SmoothWord

end

end OAI
