import Mathlib

namespace OAI

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set

namespace HarmonicCounterexample.LinearODE
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The exact Peano--Baker iterates, with oriented integrals on the entire real line. -/
def term (A : ℝ → E →L[ℝ] E) (x : E) : ℕ → ℝ → E
  | 0, _ => x
  | n+1, t => ∫ s in (0:ℝ)..t, A s (term A x n s)

lemma term_continuous {A : ℝ → E →L[ℝ] E} (hA : Continuous A) (x : E) (n : ℕ) :
    Continuous (term A x n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    have hc := hA.clm_apply ih
    apply continuous_iff_continuousAt.2
    intro t
    exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
      hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).continuousAt

lemma term_succ_hasDerivAt {A : ℝ → E →L[ℝ] E} (hA : Continuous A)
    (x : E) (n : ℕ) (t : ℝ) :
    HasDerivAt (term A x (n+1)) (A t (term A x n t)) t := by
  have hc := hA.clm_apply (term_continuous hA x n)
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

lemma term_bound {A : ℝ → E →L[ℝ] E} (hA : Continuous A) {M : ℝ}
    (hM : 0 ≤ M) (hb : ∀ s, ‖A s‖ ≤ M) (x : E) (n : ℕ) (t : ℝ) :
    ‖term A x n t‖ ≤ ‖x‖ * M^n * |t|^n / (n.factorial:ℝ) := by
  induction n generalizing t with
  | zero => simp [term]
  | succ n ih =>
    have hc := hA.clm_apply (term_continuous hA x n)
    have hcf (s : ℝ) : ‖A s (term A x n s)‖ ≤
        (‖x‖*M^(n+1)/(n.factorial:ℝ)) * |s|^n := by
      calc
        _ ≤ ‖A s‖ * ‖term A x n s‖ := (A s).le_opNorm _
        _ ≤ M * (‖x‖*M^n*|s|^n/(n.factorial:ℝ)) :=
          mul_le_mul (hb s) (ih s) (norm_nonneg _) hM
        _ = _ := by rw [pow_succ]; ring
    change ‖∫ s in (0:ℝ)..t, A s (term A x n s)‖ ≤ _
    calc
      _ ≤ ∫ s in Set.uIoc 0 t, ‖A s (term A x n s)‖ :=
        intervalIntegral.norm_integral_le_integral_norm_uIoc
      _ ≤ ∫ s in Set.uIoc 0 t,
          (‖x‖*M^(n+1)/(n.factorial:ℝ)) * |s|^n := by
        apply integral_mono_ae
        · exact (hc.intervalIntegrable 0 t).def'.norm
        · exact ((continuous_const.mul (continuous_abs.pow n)).intervalIntegrable 0 t).def'
        · exact Filter.Eventually.of_forall hcf
      _ = ‖x‖ * M^(n+1) * |t|^(n+1) / ((n+1).factorial:ℝ) := by
        rw [integral_const_mul]
        have hi := integral_pow_abs_sub_uIoc (a := (0:ℝ)) (b := t) (n := n)
        simp only [sub_zero] at hi
        rw [hi, Nat.factorial_succ]
        push_cast
        field_simp

def flow (A : ℝ → E →L[ℝ] E) (x : E) (t : ℝ) : E := ∑' n, term A x n t



lemma term_summable {A : ℝ → E →L[ℝ] E} (hA : Continuous A) {M : ℝ}
    (hM : 0 ≤ M) (hb : ∀ s, ‖A s‖ ≤ M) (x : E) (t : ℝ) :
    Summable (fun n => term A x n t) := by
  have hs := (Real.summable_pow_div_factorial (M*|t|)).mul_left ‖x‖
  apply hs.of_norm_bounded
  intro n
  simpa only [mul_pow, mul_div_assoc, mul_assoc] using term_bound hA hM hb x n t

lemma flow_eq {A : ℝ → E →L[ℝ] E} (hA : Continuous A) {M : ℝ}
    (hM : 0 ≤ M) (hb : ∀ s, ‖A s‖ ≤ M) (x : E) (t : ℝ) :
    flow A x t = x + ∑' n, term A x (n+1) t := by
  exact (term_summable hA hM hb x t).tsum_eq_zero_add

omit [CompleteSpace E] in
lemma term_zero (A : ℝ → E →L[ℝ] E) (x : E) :
    ∀ n, term A x (n+1) 0 = 0 := by intros; simp [term]

omit [CompleteSpace E] in
lemma flow_initial (A : ℝ → E →L[ℝ] E) (x : E) : flow A x 0 = x := by
  unfold flow
  rw [tsum_eq_single 0]
  · rfl
  · intro n hn
    cases n with
    | zero => contradiction
    | succ n => exact term_zero A x n

/-- A global actual solution, before any positivity, transmission or growth estimates. -/
theorem flow_hasDerivAt {A : ℝ → E →L[ℝ] E} (hA : Continuous A) {M : ℝ}
    (hM : 0 ≤ M) (hb : ∀ s, ‖A s‖ ≤ M) (x : E) (t : ℝ) :
    HasDerivAt (flow A x) (A t (flow A x t)) t := by
  let R : ℝ := |t|+1
  have hR : 0 < R := by dsimp [R]; positivity
  have hu : Summable (fun n => (‖x‖*M)*(M*R)^n/(n.factorial:ℝ)) := by
    simpa only [mul_div_assoc] using
      (Real.summable_pow_div_factorial (M*R)).mul_left (‖x‖*M)
  have hbound (n : ℕ) (y : ℝ) (hy : y ∈ Set.Ioo (-R) R) :
      ‖A y (term A x n y)‖ ≤ (‖x‖*M)*(M*R)^n/(n.factorial:ℝ) := by
    have hay : |y| ≤ R := abs_le.2 ⟨hy.1.le, hy.2.le⟩
    calc
      _ ≤ ‖A y‖ * ‖term A x n y‖ := (A y).le_opNorm _
      _ ≤ M * (‖x‖*M^n*|y|^n/(n.factorial:ℝ)) :=
        mul_le_mul (hb y) (term_bound hA hM hb x n y) (norm_nonneg _) hM
      _ ≤ M * (‖x‖*M^n*R^n/(n.factorial:ℝ)) := by
        gcongr
      _ = _ := by rw [mul_pow]; ring
  have hzero : Summable (fun n => term A x (n+1) 0) := by simp only [term_zero]; exact summable_zero
  have ht : t ∈ Set.Ioo (-R) R := by
    dsimp [R]
    constructor <;> linarith [le_abs_self t, neg_abs_le t]
  have hd := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo isPreconnected_Ioo
    (fun n y _ => term_succ_hasDerivAt hA x n y) hbound
    (show (0:ℝ) ∈ Set.Ioo (-R) R by constructor <;> linarith) hzero ht
  have hmap := (A t).map_tsum (term_summable hA hM hb x t)
  change A t (flow A x t) = _ at hmap
  rw [← hmap] at hd
  have he : flow A x = fun y => x + ∑' n, term A x (n+1) y :=
    funext (flow_eq hA hM hb x)
  have hh := hd.const_add x
  rw [← he] at hh
  exact hh

lemma flow_smooth {A : ℝ → E →L[ℝ] E} (hA : ContDiff ℝ ∞ A) {M : ℝ}
    (hM : 0 ≤ M) (hb : ∀ s, ‖A s‖ ≤ M) (x : E) : ContDiff ℝ ∞ (flow A x) := by
  have hd := flow_hasDerivAt hA.continuous hM hb x
  have hder : deriv (flow A x) = fun t => A t (flow A x t) := funext fun t => (hd t).deriv
  apply contDiff_infty.2
  intro n
  induction n with
  | zero => exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun t => (hd t).continuousAt)
  | succ n ih =>
    rw [show ((n+1:ℕ) : WithTop ℕ∞) = (n:WithTop ℕ∞)+1 by simp, contDiff_succ_iff_deriv]
    refine ⟨fun t => (hd t).differentiableAt, by simp, ?_⟩
    rw [hder]
    exact ((contDiff_infty.1 hA) n).clm_apply ih


omit [CompleteSpace E] in
lemma solution_unique {A : ℝ → E →L[ℝ] E} {M : ℝ}
    (hM : 0 ≤ M) (hb : ∀ s, ‖A s‖ ≤ M) {f g : ℝ → E} {t₀ : ℝ}
    (hf : ∀ t, HasDerivAt f (A t (f t)) t)
    (hg : ∀ t, HasDerivAt g (A t (g t)) t) (he : f t₀ = g t₀) : f = g := by
  apply ODE_solution_unique_univ (s := fun _ => Set.univ) (K := ⟨M,hM⟩)
    (fun t => ((A t).lipschitzWith.weaken (hb t)).lipschitzOnWith)
    (fun t => ⟨hf t, Set.mem_univ _⟩) (fun t => ⟨hg t, Set.mem_univ _⟩) he

lemma flow_injective {A : ℝ → E →L[ℝ] E} (hA : Continuous A) {M : ℝ}
    (hM : 0 ≤ M) (hb : ∀ s, ‖A s‖ ≤ M) (t : ℝ) :
    Function.Injective (fun x => flow A x t) := by
  intro x y he
  have hh := solution_unique hM hb (flow_hasDerivAt hA hM hb x)
    (flow_hasDerivAt hA hM hb y) he
  have hzero := congrFun hh 0
  simpa only [flow_initial] using hzero

lemma flow_add {A : ℝ → E →L[ℝ] E} (hA : Continuous A) {M : ℝ}
    (hM : 0 ≤ M) (hb : ∀ s, ‖A s‖ ≤ M) (x y : E) (t : ℝ) :
    flow A (x+y) t = flow A x t + flow A y t := by
  have hd (s : ℝ) : HasDerivAt (fun s => flow A x s + flow A y s)
      (A s (flow A x s + flow A y s)) s := by
    simpa only [map_add, Pi.add_def] using (flow_hasDerivAt hA hM hb x s).add
      (flow_hasDerivAt hA hM hb y s)
  have hh := solution_unique hM hb (flow_hasDerivAt hA hM hb (x+y)) hd
    (t₀ := 0) (by simp only [flow_initial])
  exact congrFun hh t

lemma flow_smul {A : ℝ → E →L[ℝ] E} (hA : Continuous A) {M : ℝ}
    (hM : 0 ≤ M) (hb : ∀ s, ‖A s‖ ≤ M) (c : ℝ) (x : E) (t : ℝ) :
    flow A (c • x) t = c • flow A x t := by
  have hd (s : ℝ) : HasDerivAt (fun s => c • flow A x s)
      (A s (c • flow A x s)) s := by
    simpa only [map_smul, Pi.smul_def] using (flow_hasDerivAt hA hM hb x s).const_smul c
  have hh := solution_unique hM hb (flow_hasDerivAt hA hM hb (c • x)) hd
    (t₀ := 0) (by simp only [flow_initial])
  exact congrFun hh t

/-- Actual initial-data linearity, later used for independence of harmonic columns. -/
def flowLinear (A : ℝ → E →L[ℝ] E) (hA : Continuous A) (M : ℝ)
    (hM : 0 ≤ M) (hb : ∀ s, ‖A s‖ ≤ M) (t : ℝ) : E →ₗ[ℝ] E where
  toFun x := flow A x t
  map_add' x y := flow_add hA hM hb x y t
  map_smul' c x := flow_smul hA hM hb c x t

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set

namespace HarmonicCounterexample.LinearODE
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def block (A : ℝ → E →L[ℝ] E) (b : ℝ → ℝ) (t : ℝ) : E×E →L[ℝ] E×E :=
  (ContinuousLinearMap.snd ℝ E E).prod
    ((A t).comp (ContinuousLinearMap.fst ℝ E E) - b t • ContinuousLinearMap.snd ℝ E E)

lemma block_apply (A : ℝ → E →L[ℝ] E) (b : ℝ → ℝ) (t : ℝ) (v : E×E) :
    block A b t v = (v.2, A t v.1 - b t • v.2) := rfl

lemma block_eq (A : ℝ → E →L[ℝ] E) (b : ℝ → ℝ) (t : ℝ) :
    block A b t = (ContinuousLinearMap.inl ℝ E E).comp (ContinuousLinearMap.snd ℝ E E) +
      (ContinuousLinearMap.inr ℝ E E).comp
        ((A t).comp (ContinuousLinearMap.fst ℝ E E) - b t • ContinuousLinearMap.snd ℝ E E) := by
  ext v <;> simp [block]

lemma block_continuous {A : ℝ → E →L[ℝ] E} {b : ℝ → ℝ}
    (hA : Continuous A) (hb : Continuous b) : Continuous (block A b) := by
  simp only [funext (block_eq A b)]
  exact continuous_const.add (continuous_const.clm_comp
    ((hA.clm_comp continuous_const).sub (hb.smul continuous_const)))

lemma block_smooth {A : ℝ → E →L[ℝ] E} {b : ℝ → ℝ}
    (hA : ContDiff ℝ ∞ A) (hb : ContDiff ℝ ∞ b) : ContDiff ℝ ∞ (block A b) := by
  simp only [funext (block_eq A b)]
  exact contDiff_const.add (contDiff_const.clm_comp
    ((hA.clm_comp contDiff_const).sub (hb.smul contDiff_const)))

lemma block_bound {A : ℝ → E →L[ℝ] E} {b : ℝ → ℝ} {MA Mb : ℝ}
    (hMA : 0 ≤ MA) (hMb : 0 ≤ Mb)
    (hA : ∀ t, ‖A t‖ ≤ MA) (hb : ∀ t, |b t| ≤ Mb) (t : ℝ) :
    ‖block A b t‖ ≤ 1+MA+Mb := by
  rw [block, ContinuousLinearMap.opNorm_prod, Prod.norm_def]
  apply max_le
  · exact (ContinuousLinearMap.norm_snd_le ℝ E E).trans (by linarith)
  · calc
      _ ≤ ‖(A t).comp (ContinuousLinearMap.fst ℝ E E)‖ +
            ‖b t • ContinuousLinearMap.snd ℝ E E‖ := norm_sub_le _ _
      _ ≤ ‖A t‖ * ‖ContinuousLinearMap.fst ℝ E E‖ +
            |b t| * ‖ContinuousLinearMap.snd ℝ E E‖ := by
          rw [norm_smul, Real.norm_eq_abs]
          exact add_le_add (ContinuousLinearMap.opNorm_comp_le (A t) (ContinuousLinearMap.fst ℝ E E)) le_rfl
      _ ≤ MA*1+Mb*1 := by
        exact add_le_add
          (mul_le_mul (hA t) (ContinuousLinearMap.norm_fst_le ℝ E E) (norm_nonneg _) hMA)
          (mul_le_mul (hb t) (ContinuousLinearMap.norm_snd_le ℝ E E) (norm_nonneg _) hMb)
      _ ≤ _ := by linarith

def phase (A : ℝ → E →L[ℝ] E) (b : ℝ → ℝ) (l : ℝ) (x : E) (t : ℝ) : E×E :=
  flow (block A b) (x,l • x) t

def value (A : ℝ → E →L[ℝ] E) (b : ℝ → ℝ) (l : ℝ) (x : E) (t : ℝ) : E :=
  (phase A b l x t).1

def velocity (A : ℝ → E →L[ℝ] E) (b : ℝ → ℝ) (l : ℝ) (x : E) (t : ℝ) : E :=
  (phase A b l x t).2

lemma value_initial (A : ℝ → E →L[ℝ] E) (b : ℝ → ℝ) (l : ℝ) (x : E) :
    value A b l x 0 = x := by simp [value, phase, flow_initial]

lemma velocity_initial (A : ℝ → E →L[ℝ] E) (b : ℝ → ℝ) (l : ℝ) (x : E) :
    velocity A b l x 0 = l • x := by simp [velocity, phase, flow_initial]

variable [CompleteSpace E]

lemma value_deriv {A : ℝ → E →L[ℝ] E} {b : ℝ → ℝ}
    (hA : Continuous A) (hb : Continuous b) {MA Mb : ℝ}
    (hMA : 0 ≤ MA) (hMb : 0 ≤ Mb)
    (hAn : ∀ t, ‖A t‖ ≤ MA) (hbn : ∀ t, |b t| ≤ Mb) (l : ℝ) (x : E) (t : ℝ) :
    HasDerivAt (value A b l x) (velocity A b l x t) t := by
  have hd := flow_hasDerivAt (block_continuous hA hb) (by positivity : 0 ≤ 1+MA+Mb)
    (block_bound hMA hMb hAn hbn) (x,l • x) t
  exact (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt t hd

lemma velocity_deriv {A : ℝ → E →L[ℝ] E} {b : ℝ → ℝ}
    (hA : Continuous A) (hb : Continuous b) {MA Mb : ℝ}
    (hMA : 0 ≤ MA) (hMb : 0 ≤ Mb)
    (hAn : ∀ t, ‖A t‖ ≤ MA) (hbn : ∀ t, |b t| ≤ Mb) (l : ℝ) (x : E) (t : ℝ) :
    HasDerivAt (velocity A b l x)
      (A t (value A b l x t) - b t • velocity A b l x t) t := by
  have hd := flow_hasDerivAt (block_continuous hA hb) (by positivity : 0 ≤ 1+MA+Mb)
    (block_bound hMA hMb hAn hbn) (x,l • x) t
  exact (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivAt t hd

lemma value_smooth {A : ℝ → E →L[ℝ] E} {b : ℝ → ℝ}
    (hA : ContDiff ℝ ∞ A) (hb : ContDiff ℝ ∞ b) {MA Mb : ℝ}
    (hMA : 0 ≤ MA) (hMb : 0 ≤ Mb)
    (hAn : ∀ t, ‖A t‖ ≤ MA) (hbn : ∀ t, |b t| ≤ Mb) (l : ℝ) (x : E) :
    ContDiff ℝ ∞ (value A b l x) := by
  exact (ContinuousLinearMap.fst ℝ E E).contDiff.comp
    (flow_smooth (block_smooth hA hb) (by positivity : 0 ≤ 1+MA+Mb)
      (block_bound hMA hMb hAn hbn) (x,l • x))

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set

namespace HarmonicCounterexample.LinearODE
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Exact matching to the regular Euclidean solution on the entire negative
logarithmic half-line, obtained by uniqueness rather than an asymptotic ansatz. -/
theorem phase_euclidean_tail {A : ℝ → E →L[ℝ] E} {b : ℝ → ℝ}
    (hA : Continuous A) (hb : Continuous b) {MA Mb : ℝ}
    (hMA : 0 ≤ MA) (hMb : 0 ≤ Mb)
    (hAn : ∀ t, ‖A t‖ ≤ MA) (hbn : ∀ t, |b t| ≤ Mb)
    {l B : ℝ} (hAi : ∀ t ≤ 0, ∀ v, A t v = (l*(l+B)) • v)
    (hbi : ∀ t ≤ 0, b t = B) (x : E) {t : ℝ} (ht : t ≤ 0) :
    phase A b l x t = Real.exp (l*t) • (x,l • x) := by
  let f : ℝ → E×E := fun s => Real.exp (l*s) • (x,l • x)
  have hd (s : ℝ) : HasDerivAt (phase A b l x)
      (block A b s (phase A b l x s)) s :=
    flow_hasDerivAt (block_continuous hA hb) (by positivity : 0 ≤ 1+MA+Mb)
      (block_bound hMA hMb hAn hbn) (x,l • x) s
  have hf (s : ℝ) : HasDerivAt f ((Real.exp (l*s)*l) • (x,l • x)) s := by
    change HasDerivAt (fun s => Real.exp (l*s) • (x,l • x)) _ s
    convert (((hasDerivAt_id s).const_mul l).exp).smul_const (x,l • x) using 1 <;> first | rfl | simp only [id_eq, mul_one]
  have hfode (s : ℝ) (hs : s ≤ 0) : HasDerivAt f (block A b s (f s)) s := by
    convert hf s using 1
    rw [block_apply]
    dsimp only [f, Prod.smul_fst, Prod.smul_snd]
    rw [hAi s hs, hbi s hs]
    apply Prod.ext
    · simp only [Prod.smul_fst, smul_smul]
    · simp only [Prod.smul_snd, smul_smul]
      module
  have hunique := ODE_solution_unique_of_mem_Icc_left
    (s := fun _ => Set.univ) (K := ⟨1+MA+Mb, by positivity⟩)
    (a := t) (b := 0)
    (fun s _ => ((block A b s).lipschitzWith.weaken (block_bound hMA hMb hAn hbn s)).lipschitzOnWith)
    (continuous_iff_continuousAt.2 (fun s => (hd s).continuousAt)).continuousOn
    (fun s _ => (hd s).hasDerivWithinAt) (fun _ _ => Set.mem_univ _)
    (continuous_iff_continuousAt.2 (fun s => (hf s).continuousAt)).continuousOn
    (fun s hs => (hfode s hs.2).hasDerivWithinAt) (fun _ _ => Set.mem_univ _)
    (show phase A b l x 0 = f 0 by simp [phase, f, flow_initial])
  exact hunique ⟨le_rfl,ht⟩

lemma value_euclidean_tail {A : ℝ → E →L[ℝ] E} {b : ℝ → ℝ}
    (hA : Continuous A) (hb : Continuous b) {MA Mb : ℝ}
    (hMA : 0 ≤ MA) (hMb : 0 ≤ Mb)
    (hAn : ∀ t, ‖A t‖ ≤ MA) (hbn : ∀ t, |b t| ≤ Mb)
    {l B : ℝ} (hAi : ∀ t ≤ 0, ∀ v, A t v = (l*(l+B)) • v)
    (hbi : ∀ t ≤ 0, b t = B) (x : E) {t : ℝ} (ht : t ≤ 0) :
    value A b l x t = Real.exp (l*t) • x := by
  exact congrArg Prod.fst (phase_euclidean_tail hA hb hMA hMb hAn hbn hAi hbi x ht)

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set

namespace HarmonicCounterexample.LinearODE

def integratingWeight (b : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (∫ s in (0:ℝ)..t, b s)

lemma integratingWeight_pos (b : ℝ → ℝ) (t : ℝ) : 0 < integratingWeight b t :=
  Real.exp_pos _

lemma integratingWeight_initial (b : ℝ → ℝ) : integratingWeight b 0 = 1 := by
  simp [integratingWeight]

lemma integratingWeight_deriv {b : ℝ → ℝ} (hb : Continuous b) (t : ℝ) :
    HasDerivAt (integratingWeight b) (integratingWeight b t*b t) t := by
  exact (intervalIntegral.integral_hasDerivAt_right (hb.intervalIntegrable 0 t)
    hb.stronglyMeasurable.stronglyMeasurableAtFilter hb.continuousAt).exp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
open scoped InnerProductSpace

/-- Exact weighted energy identity; no invertibility of the value block is assumed. -/
lemma weighted_energy_deriv {A : ℝ → E →L[ℝ] E} {b : ℝ → ℝ}
    (hb : Continuous b) {y z : ℝ → E} {t : ℝ}
    (hy : HasDerivAt y (z t) t)
    (hz : HasDerivAt z (A t (y t)-b t • z t) t) :
    HasDerivAt (fun t => integratingWeight b t * ⟪y t,z t⟫_ℝ)
      (integratingWeight b t*(⟪y t,A t (y t)⟫_ℝ+‖z t‖^2)) t := by
  have hd := (integratingWeight_deriv hb t).fun_mul (hy.inner ℝ hz)
  convert hd using 1; first | rfl |
    (simp only [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq]; ring)

lemma weighted_energy_monotone {A : ℝ → E →L[ℝ] E} {b : ℝ → ℝ}
    (hb : Continuous b) (hAp : ∀ t v, 0 ≤ ⟪v,A t v⟫_ℝ) {y z : ℝ → E}
    (hy : ∀ t, HasDerivAt y (z t) t)
    (hz : ∀ t, HasDerivAt z (A t (y t)-b t • z t) t) :
    Monotone (fun t => integratingWeight b t * ⟪y t,z t⟫_ℝ) := by
  exact monotone_of_hasDerivAt_nonneg (fun t => weighted_energy_deriv hb (hy t) (hz t))
    (fun t => mul_nonneg (integratingWeight_pos b t).le (add_nonneg (hAp t _) (sq_nonneg _)))

/-- Center-regular initial data have a strictly positive pairing for all t≥0.
This rules out conjugate zeros and produces the value-block injectivity. -/
lemma regular_pairing_positive {A : ℝ → E →L[ℝ] E} {b : ℝ → ℝ}
    (hb : Continuous b) (hAp : ∀ t v, 0 ≤ ⟪v,A t v⟫_ℝ) {y z : ℝ → E}
    (hy : ∀ t, HasDerivAt y (z t) t)
    (hz : ∀ t, HasDerivAt z (A t (y t)-b t • z t) t)
    {l : ℝ} (hl : 0 < l) (hinit : z 0 = l • y 0) (hne : y 0 ≠ 0)
    {t : ℝ} (ht : 0 ≤ t) : 0 < ⟪y t,z t⟫_ℝ := by
  have hm := weighted_energy_monotone hb hAp hy hz ht
  dsimp only at hm
  rw [integratingWeight_initial, one_mul, hinit, inner_smul_right,
    real_inner_self_eq_norm_sq] at hm
  have hnorm : 0 < ‖y 0‖^2 := sq_pos_of_pos (norm_pos_iff.2 hne)
  exact (mul_pos_iff_of_pos_left (integratingWeight_pos b t)).1 ((mul_pos hl hnorm).trans_le hm)

variable [CompleteSpace E]

lemma value_nonzero_of_nonnegative {A : ℝ → E →L[ℝ] E} {b : ℝ → ℝ}
    (hA : Continuous A) (hb : Continuous b) {MA Mb : ℝ}
    (hMA : 0 ≤ MA) (hMb : 0 ≤ Mb)
    (hAn : ∀ t, ‖A t‖ ≤ MA) (hbn : ∀ t, |b t| ≤ Mb)
    (hAp : ∀ t v, 0 ≤ ⟪v,A t v⟫_ℝ) {l : ℝ} (hl : 0 < l)
    {x : E} (hx : x ≠ 0) {t : ℝ} (ht : 0 ≤ t) : value A b l x t ≠ 0 := by
  have he := regular_pairing_positive hb hAp
    (value_deriv hA hb hMA hMb hAn hbn l x)
    (velocity_deriv hA hb hMA hMb hAn hbn l x) hl
    (by simp only [value_initial, velocity_initial])
    (by simpa only [value_initial] using hx) ht
  intro hh
  rw [hh, inner_zero_left] at he
  exact lt_irrefl _ he

lemma value_linear {A : ℝ → E →L[ℝ] E} {b : ℝ → ℝ}
    (hA : Continuous A) (hb : Continuous b) {MA Mb : ℝ}
    (hMA : 0 ≤ MA) (hMb : 0 ≤ Mb)
    (hAn : ∀ t, ‖A t‖ ≤ MA) (hbn : ∀ t, |b t| ≤ Mb) (l t : ℝ) :
    IsLinearMap ℝ (fun x => value A b l x t) := by
  refine ⟨?_, ?_⟩
  · intro x y
    change (flow (block A b) (x+y,l • (x+y)) t).1 = _
    rw [show (x+y,l • (x+y)) = (x,l • x)+(y,l • y) by simp [smul_add],
      flow_add (block_continuous hA hb) (by positivity : 0 ≤ 1+MA+Mb)
        (block_bound hMA hMb hAn hbn)]
    rfl
  · intro c x
    change (flow (block A b) (c • x,l • (c • x)) t).1 = _
    rw [show (c • x,l • (c • x)) = c • (x,l • x) by simp [smul_comm l c],
      flow_smul (block_continuous hA hb) (by positivity : 0 ≤ 1+MA+Mb)
        (block_bound hMA hMb hAn hbn)]
    rfl

lemma value_injective_of_nonnegative {A : ℝ → E →L[ℝ] E} {b : ℝ → ℝ}
    (hA : Continuous A) (hb : Continuous b) {MA Mb : ℝ}
    (hMA : 0 ≤ MA) (hMb : 0 ≤ Mb)
    (hAn : ∀ t, ‖A t‖ ≤ MA) (hbn : ∀ t, |b t| ≤ Mb)
    (hAp : ∀ t v, 0 ≤ ⟪v,A t v⟫_ℝ) {l : ℝ} (hl : 0 < l)
    {t : ℝ} (ht : 0 ≤ t) : Function.Injective (fun x => value A b l x t) := by
  let F : E →ₗ[ℝ] E := (value_linear hA hb hMA hMb hAn hbn l t).mk'
  apply F.ker_eq_bot.1
  rw [LinearMap.ker_eq_bot']
  intro x hx
  by_contra hne
  exact value_nonzero_of_nonnegative hA hb hMA hMb hAn hbn hAp hl hne ht hx

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set

namespace HarmonicCounterexample.LinearODE
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
open scoped InnerProductSpace

/-- Symplectic flux cancellation for two actual center-regular solutions. -/
lemma weighted_wronskian_deriv {A : ℝ → E →L[ℝ] E} {b : ℝ → ℝ}
    (hb : Continuous b) {u v p q : ℝ → E} {t : ℝ}
    (hA : ∀ x y, ⟪A t x,y⟫_ℝ = ⟪x,A t y⟫_ℝ)
    (hu : HasDerivAt u (v t) t) (hv : HasDerivAt v (A t (u t)-b t • v t) t)
    (hp : HasDerivAt p (q t) t) (hq : HasDerivAt q (A t (p t)-b t • q t) t) :
    HasDerivAt (fun t => integratingWeight b t*(⟪u t,q t⟫_ℝ-⟪v t,p t⟫_ℝ)) 0 t := by
  have hd := (integratingWeight_deriv hb t).fun_mul ((hu.inner ℝ hq).fun_sub (hv.inner ℝ hp))
  convert hd using 1; first | rfl |
    (simp only [inner_sub_right,inner_sub_left,inner_smul_right,inner_smul_left,starRingEnd_apply,star_trivial,hA]; ring)

lemma weighted_wronskian_constant {A : ℝ → E →L[ℝ] E} {b : ℝ → ℝ}
    (hb : Continuous b) (hA : ∀ t x y, ⟪A t x,y⟫_ℝ = ⟪x,A t y⟫_ℝ)
    {u v p q : ℝ → E}
    (hu : ∀ t, HasDerivAt u (v t) t) (hv : ∀ t, HasDerivAt v (A t (u t)-b t • v t) t)
    (hp : ∀ t, HasDerivAt p (q t) t) (hq : ∀ t, HasDerivAt q (A t (p t)-b t • q t) t)
    {l : ℝ} (hvi : v 0 = l • u 0) (hqi : q 0 = l • p 0) (t : ℝ) :
    ⟪u t,q t⟫_ℝ = ⟪v t,p t⟫_ℝ := by
  have hc := is_const_of_deriv_eq_zero (fun s =>
    (weighted_wronskian_deriv hb (hA s) (hu s) (hv s) (hp s) (hq s)).differentiableAt)
    (fun s => (weighted_wronskian_deriv hb (hA s) (hu s) (hv s) (hp s) (hq s)).deriv)
  have he := hc t 0
  rw [hvi,hqi,inner_smul_right,inner_smul_left,starRingEnd_apply,star_trivial,sub_self,mul_zero] at he
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (integratingWeight_pos b t).ne')

variable [CompleteSpace E]

lemma regular_wronskian_zero {A : ℝ → E →L[ℝ] E} {b : ℝ → ℝ}
    (hA : Continuous A) (hb : Continuous b) {MA Mb : ℝ}
    (hMA : 0 ≤ MA) (hMb : 0 ≤ Mb)
    (hAn : ∀ t, ‖A t‖ ≤ MA) (hbn : ∀ t, |b t| ≤ Mb)
    (hAs : ∀ t x y, ⟪A t x,y⟫_ℝ = ⟪x,A t y⟫_ℝ)
    (l : ℝ) (x y : E) (t : ℝ) :
    ⟪value A b l x t,velocity A b l y t⟫_ℝ =
      ⟪velocity A b l x t,value A b l y t⟫_ℝ := by
  exact weighted_wronskian_constant (l := l) hb hAs
    (value_deriv hA hb hMA hMb hAn hbn l x) (velocity_deriv hA hb hMA hMb hAn hbn l x)
    (value_deriv hA hb hMA hMb hAn hbn l y) (velocity_deriv hA hb hMA hMb hAn hbn l y)
    (by simp only [velocity_initial,value_initial]) (by simp only [velocity_initial,value_initial]) t

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set

namespace HarmonicCounterexample.LinearODE
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Left composition lifts a bounded coefficient to the Banach space of operators. -/
def leftAction (A : ℝ → E →L[ℝ] E) (t : ℝ) : (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) :=
  ContinuousLinearMap.compL ℝ E E E (A t)

lemma leftAction_continuous {A : ℝ → E →L[ℝ] E} (hA : Continuous A) : Continuous (leftAction A) :=
  (ContinuousLinearMap.compL ℝ E E E).continuous.comp hA

lemma leftAction_smooth {A : ℝ → E →L[ℝ] E} (hA : ContDiff ℝ ∞ A) : ContDiff ℝ ∞ (leftAction A) :=
  (ContinuousLinearMap.compL ℝ E E E).contDiff.comp hA

lemma leftAction_norm_le (A : ℝ → E →L[ℝ] E) (t : ℝ) : ‖leftAction A t‖ ≤ ‖A t‖ := by
  apply le_trans ((ContinuousLinearMap.compL ℝ E E E).le_opNorm (A t))
  exact (mul_le_mul_of_nonneg_right (ContinuousLinearMap.norm_compL_le ℝ E E E) (norm_nonneg _)).trans_eq (one_mul _)

variable [CompleteSpace E]

def operatorValue (A : ℝ → E →L[ℝ] E) (b : ℝ → ℝ) (l : ℝ) (t : ℝ) : E →L[ℝ] E :=
  value (leftAction A) b l (ContinuousLinearMap.id ℝ E) t

def operatorVelocity (A : ℝ → E →L[ℝ] E) (b : ℝ → ℝ) (l : ℝ) (t : ℝ) : E →L[ℝ] E :=
  velocity (leftAction A) b l (ContinuousLinearMap.id ℝ E) t

lemma operatorValue_deriv {A : ℝ → E →L[ℝ] E} {b : ℝ → ℝ}
    (hA : Continuous A) (hb : Continuous b) {MA Mb : ℝ}
    (hMA : 0 ≤ MA) (hMb : 0 ≤ Mb)
    (hAn : ∀ t, ‖A t‖ ≤ MA) (hbn : ∀ t, |b t| ≤ Mb) (l t : ℝ) :
    HasDerivAt (operatorValue A b l) (operatorVelocity A b l t) t :=
  value_deriv (leftAction_continuous hA) hb hMA hMb
    (fun t => (leftAction_norm_le A t).trans (hAn t)) hbn l (ContinuousLinearMap.id ℝ E) t

lemma operatorVelocity_deriv {A : ℝ → E →L[ℝ] E} {b : ℝ → ℝ}
    (hA : Continuous A) (hb : Continuous b) {MA Mb : ℝ}
    (hMA : 0 ≤ MA) (hMb : 0 ≤ Mb)
    (hAn : ∀ t, ‖A t‖ ≤ MA) (hbn : ∀ t, |b t| ≤ Mb) (l t : ℝ) :
    HasDerivAt (operatorVelocity A b l)
      (A t * operatorValue A b l t - b t • operatorVelocity A b l t) t :=
  velocity_deriv (leftAction_continuous hA) hb hMA hMb
    (fun t => (leftAction_norm_le A t).trans (hAn t)) hbn l (ContinuousLinearMap.id ℝ E) t

lemma operatorValue_smooth {A : ℝ → E →L[ℝ] E} {b : ℝ → ℝ}
    (hA : ContDiff ℝ ∞ A) (hb : ContDiff ℝ ∞ b) {MA Mb : ℝ}
    (hMA : 0 ≤ MA) (hMb : 0 ≤ Mb)
    (hAn : ∀ t, ‖A t‖ ≤ MA) (hbn : ∀ t, |b t| ≤ Mb) (l : ℝ) :
    ContDiff ℝ ∞ (operatorValue A b l) :=
  value_smooth (leftAction_smooth hA) hb hMA hMb
    (fun t => (leftAction_norm_le A t).trans (hAn t)) hbn l (ContinuousLinearMap.id ℝ E)

lemma operatorValue_apply_deriv {A : ℝ → E →L[ℝ] E} {b : ℝ → ℝ}
    (hA : Continuous A) (hb : Continuous b) {MA Mb : ℝ}
    (hMA : 0 ≤ MA) (hMb : 0 ≤ Mb)
    (hAn : ∀ t, ‖A t‖ ≤ MA) (hbn : ∀ t, |b t| ≤ Mb) (l : ℝ) (x : E) (s : ℝ) :
    HasDerivAt (fun s => operatorValue A b l s x) (operatorVelocity A b l s x) s := by
  simpa only [add_zero,map_zero] using
    (operatorValue_deriv hA hb hMA hMb hAn hbn l s).clm_apply (hasDerivAt_const s x)

lemma operatorVelocity_apply_deriv {A : ℝ → E →L[ℝ] E} {b : ℝ → ℝ}
    (hA : Continuous A) (hb : Continuous b) {MA Mb : ℝ}
    (hMA : 0 ≤ MA) (hMb : 0 ≤ Mb)
    (hAn : ∀ t, ‖A t‖ ≤ MA) (hbn : ∀ t, |b t| ≤ Mb) (l : ℝ) (x : E) (s : ℝ) :
    HasDerivAt (fun s => operatorVelocity A b l s x)
      (A s (operatorValue A b l s x)-b s • operatorVelocity A b l s x) s := by
  simpa only [add_zero,map_zero,sub_apply,smul_apply,mul_apply_eq_comp] using
    (operatorVelocity_deriv hA hb hMA hMb hAn hbn l s).clm_apply (hasDerivAt_const s x)

lemma operatorPhase_deriv {A : ℝ → E →L[ℝ] E} {b : ℝ → ℝ}
    (hA : Continuous A) (hb : Continuous b) {MA Mb : ℝ}
    (hMA : 0 ≤ MA) (hMb : 0 ≤ Mb)
    (hAn : ∀ t, ‖A t‖ ≤ MA) (hbn : ∀ t, |b t| ≤ Mb) (l : ℝ) (x : E) (s : ℝ) :
    HasDerivAt (fun s => (operatorValue A b l s x,operatorVelocity A b l s x))
      (block A b s (operatorValue A b l s x,operatorVelocity A b l s x)) s := by
  exact (operatorValue_apply_deriv hA hb hMA hMb hAn hbn l x s).prodMk
    (operatorVelocity_apply_deriv hA hb hMA hMb hAn hbn l x s)

omit [CompleteSpace E] in
lemma operatorPhase_initial (A : ℝ → E →L[ℝ] E) (b : ℝ → ℝ) (l : ℝ) (x : E) :
    (operatorValue A b l 0 x,operatorVelocity A b l 0 x) = (x,l • x) := by
  simp only [operatorValue,operatorVelocity,value_initial,velocity_initial,
    ContinuousLinearMap.id_apply,smul_apply]

lemma operatorPhase_apply {A : ℝ → E →L[ℝ] E} {b : ℝ → ℝ}
    (hA : Continuous A) (hb : Continuous b) {MA Mb : ℝ}
    (hMA : 0 ≤ MA) (hMb : 0 ≤ Mb)
    (hAn : ∀ t, ‖A t‖ ≤ MA) (hbn : ∀ t, |b t| ≤ Mb) (l : ℝ) (x : E) (t : ℝ) :
    (operatorValue A b l t x,operatorVelocity A b l t x) = phase A b l x t := by
  have hh : (fun t => (operatorValue A b l t x,operatorVelocity A b l t x)) =
      flow (block A b) (x,l • x) :=
    solution_unique (E := E×E) (A := block A b)
      (f := fun t => (operatorValue A b l t x,operatorVelocity A b l t x))
      (g := flow (block A b) (x,l • x)) (by positivity : 0 ≤ 1+MA+Mb) (block_bound hMA hMb hAn hbn)
      (operatorPhase_deriv hA hb hMA hMb hAn hbn l x)
      (flow_hasDerivAt (block_continuous hA hb) (by positivity : 0 ≤ 1+MA+Mb)
        (block_bound hMA hMb hAn hbn) (x,l • x))
      (t₀ := 0) (by rw [flow_initial]; exact operatorPhase_initial A b l x)
  exact congrFun hh t

lemma operatorValue_apply {A : ℝ → E →L[ℝ] E} {b : ℝ → ℝ}
    (hA : Continuous A) (hb : Continuous b) {MA Mb : ℝ}
    (hMA : 0 ≤ MA) (hMb : 0 ≤ Mb)
    (hAn : ∀ t, ‖A t‖ ≤ MA) (hbn : ∀ t, |b t| ≤ Mb) (l : ℝ) (x : E) (t : ℝ) :
    operatorValue A b l t x = value A b l x t :=
  congrArg Prod.fst (operatorPhase_apply hA hb hMA hMb hAn hbn l x t)

lemma operatorVelocity_apply {A : ℝ → E →L[ℝ] E} {b : ℝ → ℝ}
    (hA : Continuous A) (hb : Continuous b) {MA Mb : ℝ}
    (hMA : 0 ≤ MA) (hMb : 0 ≤ Mb)
    (hAn : ∀ t, ‖A t‖ ≤ MA) (hbn : ∀ t, |b t| ≤ Mb) (l : ℝ) (x : E) (t : ℝ) :
    operatorVelocity A b l t x = velocity A b l x t :=
  congrArg Prod.snd (operatorPhase_apply hA hb hMA hMb hAn hbn l x t)

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set

namespace HarmonicCounterexample.LinearODE
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The logarithmic derivative of the actual center-regular value operator. -/
def slope (A : ℝ → E →L[ℝ] E) (b : ℝ → ℝ) (l t : ℝ) : E →L[ℝ] E :=
  operatorVelocity A b l t * Ring.inverse (operatorValue A b l t)

lemma operatorValue_isUnit [FiniteDimensional ℝ E]
    {A : ℝ → E →L[ℝ] E} {b : ℝ → ℝ}
    (hA : Continuous A) (hb : Continuous b) {MA Mb : ℝ}
    (hMA : 0 ≤ MA) (hMb : 0 ≤ Mb)
    (hAn : ∀ t, ‖A t‖ ≤ MA) (hbn : ∀ t, |b t| ≤ Mb)
    (hAp : ∀ t v, 0 ≤ ⟪v,A t v⟫_ℝ) {l : ℝ} (hl : 0 < l)
    {t : ℝ} (ht : 0 ≤ t) : IsUnit (operatorValue A b l t) := by
  have hi : Function.Injective (operatorValue A b l t) := by
    intro x y hxy
    apply value_injective_of_nonnegative hA hb hMA hMb hAn hbn hAp hl ht
    simpa only [operatorValue_apply hA hb hMA hMb hAn hbn] using hxy
  exact ContinuousLinearMap.isUnit_iff_bijective.2
    ⟨hi, LinearMap.surjective_of_injective hi⟩

omit [CompleteSpace E] in
lemma slope_value {A : ℝ → E →L[ℝ] E} {b : ℝ → ℝ} {l t : ℝ}
    (hV : IsUnit (operatorValue A b l t)) (x : E) :
    slope A b l t (operatorValue A b l t x) = operatorVelocity A b l t x := by
  change ((operatorVelocity A b l t * Ring.inverse (operatorValue A b l t)) *
    operatorValue A b l t) x = _
  rw [mul_assoc,Ring.inverse_mul_cancel _ hV,mul_one]

omit [CompleteSpace E] in
lemma slope_initial (A : ℝ → E →L[ℝ] E) (b : ℝ → ℝ) (l : ℝ) :
    slope A b l 0 = l • (1 : E →L[ℝ] E) := by
  simp only [slope,operatorValue,operatorVelocity,value_initial,velocity_initial]
  change (l • (1 : E →L[ℝ] E)) * Ring.inverse 1 = _
  simp

lemma slope_symmetric {A : ℝ → E →L[ℝ] E} {b : ℝ → ℝ}
    (hA : Continuous A) (hb : Continuous b) {MA Mb : ℝ}
    (hMA : 0 ≤ MA) (hMb : 0 ≤ Mb)
    (hAn : ∀ t, ‖A t‖ ≤ MA) (hbn : ∀ t, |b t| ≤ Mb)
    (hAs : ∀ t x y, ⟪A t x,y⟫_ℝ = ⟪x,A t y⟫_ℝ) (l t : ℝ)
    (hV : IsUnit (operatorValue A b l t)) : (slope A b l t).IsSymmetric := by
  intro x y
  obtain ⟨u,rfl⟩ := (ContinuousLinearMap.isUnit_iff_bijective.1 hV).2 x
  obtain ⟨v,rfl⟩ := (ContinuousLinearMap.isUnit_iff_bijective.1 hV).2 y
  change ⟪slope A b l t (operatorValue A b l t u),operatorValue A b l t v⟫_ℝ =
    ⟪operatorValue A b l t u,slope A b l t (operatorValue A b l t v)⟫_ℝ
  rw [slope_value hV,slope_value hV]
  simp only [operatorValue_apply hA hb hMA hMb hAn hbn,
    operatorVelocity_apply hA hb hMA hMb hAn hbn]
  exact (regular_wronskian_zero hA hb hMA hMb hAn hbn hAs l u v t).symm

lemma slope_nonnegative {A : ℝ → E →L[ℝ] E} {b : ℝ → ℝ}
    (hA : Continuous A) (hb : Continuous b) {MA Mb : ℝ}
    (hMA : 0 ≤ MA) (hMb : 0 ≤ Mb)
    (hAn : ∀ t, ‖A t‖ ≤ MA) (hbn : ∀ t, |b t| ≤ Mb)
    (hAp : ∀ t v, 0 ≤ ⟪v,A t v⟫_ℝ) {l t : ℝ} (hl : 0 < l) (ht : 0 ≤ t)
    (hV : IsUnit (operatorValue A b l t)) (x : E) : 0 ≤ ⟪x,slope A b l t x⟫_ℝ := by
  obtain ⟨u,rfl⟩ := (ContinuousLinearMap.isUnit_iff_bijective.1 hV).2 x
  rw [slope_value hV]
  simp only [operatorValue_apply hA hb hMA hMb hAn hbn,
    operatorVelocity_apply hA hb hMA hMb hAn hbn]
  by_cases hu : u = 0
  · subst u
    have hv := (value_linear hA hb hMA hMb hAn hbn l t).mk'.map_zero
    change value A b l 0 t = 0 at hv
    rw [hv,inner_zero_left]
  · exact (regular_pairing_positive hb hAp
      (value_deriv hA hb hMA hMb hAn hbn l u)
      (velocity_deriv hA hb hMA hMb hAn hbn l u) hl
      (by simp only [value_initial,velocity_initial])
      (by simpa only [value_initial] using hu) ht).le

lemma clm_inverse_deriv {V : ℝ → E →L[ℝ] E} {W : E →L[ℝ] E} {t : ℝ}
    (hV : IsUnit (V t)) (hD : HasDerivAt V W t) :
    HasDerivAt (fun s => Ring.inverse (V s))
      (-(Ring.inverse (V t) * W * Ring.inverse (V t))) t := by
  obtain ⟨v,hv⟩ := hV
  have hf : HasFDerivAt Ring.inverse
      (-ContinuousLinearMap.mulLeftRight ℝ (E →L[ℝ] E) (↑v⁻¹) (↑v⁻¹)) (V t) :=
    hv ▸ hasFDerivAt_ringInverse (𝕜 := ℝ) v
  have hd := hf.comp_hasDerivAt t hD
  simpa only [Function.comp_def,neg_apply,
    ContinuousLinearMap.mulLeftRight_apply,← hv,Ring.inverse_unit] using hd

lemma slope_deriv {A : ℝ → E →L[ℝ] E} {b : ℝ → ℝ}
    (hA : Continuous A) (hb : Continuous b) {MA Mb : ℝ}
    (hMA : 0 ≤ MA) (hMb : 0 ≤ Mb)
    (hAn : ∀ t, ‖A t‖ ≤ MA) (hbn : ∀ t, |b t| ≤ Mb) (l t : ℝ)
    (hV : IsUnit (operatorValue A b l t)) :
    HasDerivAt (slope A b l)
      (A t - b t • slope A b l t - slope A b l t * slope A b l t) t := by
  have hd := (operatorVelocity_deriv hA hb hMA hMb hAn hbn l t).mul
    (clm_inverse_deriv hV (operatorValue_deriv hA hb hMA hMb hAn hbn l t))
  have he : (A t * operatorValue A b l t - b t • operatorVelocity A b l t) *
      Ring.inverse (operatorValue A b l t) + operatorVelocity A b l t *
      -(Ring.inverse (operatorValue A b l t) * operatorVelocity A b l t *
        Ring.inverse (operatorValue A b l t)) =
      A t - b t • slope A b l t - slope A b l t * slope A b l t := by
    rw [sub_mul,smul_mul_assoc,mul_assoc,Ring.mul_inverse_cancel _ hV,mul_one]
    simp only [slope,mul_neg,mul_assoc,sub_eq_add_neg]
  exact he ▸ hd

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set

namespace HarmonicCounterexample.LinearODE
open Set

/-- A genuine integrating-factor comparison on the half-line. -/
lemma integrating_factor_nonnegative (p f f' : ℝ → ℝ) (hp : Continuous p)
    (hf : ∀ t,HasDerivAt f (f' t) t) (h0 : 0 ≤ f 0)
    (hineq : ∀ t,0 ≤ t → 0 ≤ f' t+p t*f t) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ f t := by
  let Q := fun s => ∫ u in (0:ℝ)..s,p u
  have hQ (s : ℝ) : HasDerivAt Q (p s) s :=
    intervalIntegral.integral_hasDerivAt_right (hp.intervalIntegrable 0 s)
      hp.stronglyMeasurable.stronglyMeasurableAtFilter hp.continuousAt
  have hd (s : ℝ) : HasDerivAt (fun u => f u*Real.exp (Q u))
      ((f' s+p s*f s)*Real.exp (Q s)) s := by
    apply ((hf s).mul (hQ s).exp).congr_deriv
    ring
  have hm : MonotoneOn (fun u => f u*Real.exp (Q u)) (Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (continuous_iff_continuousAt.2 (fun s => (hd s).continuousAt)).continuousOn
      (fun s _ => (hd s).hasDerivWithinAt)
      (fun s hs => mul_nonneg (hineq s (interior_subset hs)) (Real.exp_pos _).le)
  have h := hm (show (0:ℝ) ∈ Ici 0 by simp) ht ht
  have hQ0 : Q 0=0 := by simp [Q]
  change f 0*Real.exp (Q 0) ≤ f t*Real.exp (Q t) at h
  rw [hQ0,Real.exp_zero,mul_one] at h
  exact nonneg_of_mul_nonneg_left (h0.trans h) (Real.exp_pos _)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- Energy comparison proves the lower Riccati barrier directly for actual
second-order solutions, without presupposing a global Riccati solution. -/
lemma solution_energy_lower (A : ℝ → E →L[ℝ] E) (b : ℝ → ℝ)
    (y v : ℝ → E) (hb : Continuous b) (hy : ∀ t,HasDerivAt y (v t) t)
    (hv : ∀ t,HasDerivAt v (A t (y t)-b t • v t) t) (c : ℝ)
    (h0 : c*⟪y 0,y 0⟫ ≤ ⟪y 0,v 0⟫)
    (hA : ∀ t,0 ≤ t → ∀ z, (b t*c+c^2)*⟪z,z⟫ ≤ ⟪z,A t z⟫)
    {t : ℝ} (ht : 0 ≤ t) : c*⟪y t,y t⟫ ≤ ⟪y t,v t⟫ := by
  let F := fun s => ⟪y s,v s⟫-c*⟪y s,y s⟫
  let F' := fun s => ⟪y s,A s (y s)-b s • v s⟫+⟪v s,v s⟫-
    c*(⟪y s,v s⟫+⟪v s,y s⟫)
  have hd (s : ℝ) : HasDerivAt F (F' s) s :=
    ((hy s).inner ℝ (hv s)).sub (((hy s).inner ℝ (hy s)).const_mul c)
  have he (s : ℝ) : F' s+b s*F s =
      ⟪v s-c • y s,v s-c • y s⟫+⟪y s,A s (y s)⟫-
        (b s*c+c^2)*⟪y s,y s⟫ := by
    dsimp [F,F']
    simp only [inner_sub_left,inner_sub_right,inner_smul_left,inner_smul_right,
      conj_trivial,real_inner_comm (v s) (y s)]
    ring
  have hp := integrating_factor_nonnegative b F F' hb hd (sub_nonneg.2 h0)
    (fun s hs => by rw [he]; linarith [show 0 ≤ ⟪v s-c • y s,v s-c • y s⟫ by rw [real_inner_self_eq_norm_sq]; positivity,hA s hs (y s)]) ht
  exact sub_nonneg.1 hp

/-- Value vectors cannot vanish: the center-regular norm is nondecreasing. -/
lemma solution_norm_lower (A : ℝ → E →L[ℝ] E) (b : ℝ → ℝ)
    (y v : ℝ → E) (hb : Continuous b) (hy : ∀ t,HasDerivAt y (v t) t)
    (hv : ∀ t,HasDerivAt v (A t (y t)-b t • v t) t)
    (h0 : 0 ≤ ⟪y 0,v 0⟫)
    (hA : ∀ t,0 ≤ t → ∀ z,0 ≤ ⟪z,A t z⟫)
    {t : ℝ} (ht : 0 ≤ t) : ‖y 0‖ ≤ ‖y t‖ := by
  have hp (s : ℝ) (hs : 0 ≤ s) : 0 ≤ ⟪y s,v s⟫ := by
    simpa using solution_energy_lower A b y v hb hy hv 0 (by simpa using h0)
      (by simpa using hA) hs
  have hd (s : ℝ) : HasDerivAt (fun u => ⟪y u,y u⟫) (2*⟪y s,v s⟫) s := by
    apply ((hy s).inner ℝ (hy s)).congr_deriv
    rw [real_inner_comm (v s) (y s)]; ring
  have hm := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (0:ℝ))
    (continuous_iff_continuousAt.2 (fun s => (hd s).continuousAt)).continuousOn
    (fun s _ => (hd s).hasDerivWithinAt)
    (fun s hs => mul_nonneg (by norm_num) (hp s (interior_subset hs)))
  have h := hm (show (0:ℝ) ∈ Ici 0 by simp) ht ht
  change ⟪y 0,y 0⟫ ≤ ⟪y t,y t⟫ at h
  rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (y 0),norm_nonneg (y t)]

variable [CompleteSpace E]

/-- Actual center-regular value flow is norm-expanding for all nonnegative times. -/
theorem value_norm_lower {A : ℝ → E →L[ℝ] E} {b : ℝ → ℝ}
    (hA : Continuous A) (hb : Continuous b) {MA Mb : ℝ}
    (hMA : 0 ≤ MA) (hMb : 0 ≤ Mb)
    (hAn : ∀ t,‖A t‖ ≤ MA) (hbn : ∀ t,|b t| ≤ Mb)
    {l : ℝ} (hl : 0 ≤ l) (hpos : ∀ t,0 ≤ t → ∀ z,0 ≤ ⟪z,A t z⟫)
    (x : E) {t : ℝ} (ht : 0 ≤ t) : ‖x‖ ≤ ‖value A b l x t‖ := by
  have hi : 0 ≤ ⟪value A b l x 0,velocity A b l x 0⟫ := by
    rw [value_initial,velocity_initial,inner_smul_right]
    rw [real_inner_self_eq_norm_sq]
    exact mul_nonneg hl (sq_nonneg _)
  simpa only [value_initial] using solution_norm_lower A b (value A b l x) (velocity A b l x)
    hb (value_deriv hA hb hMA hMb hAn hbn l x)
    (velocity_deriv hA hb hMA hMb hAn hbn l x) hi hpos ht

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set

namespace HarmonicCounterexample.LinearODE
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
open scoped RealInnerProductSpace

/-- Uniform strictly positive lower barrier for the already constructed ACTUAL
center-regular global Riccati slope. No Riccati existence is an assumption. -/
theorem slope_quadratic_lower {A : ℝ → E →L[ℝ] E} {b : ℝ → ℝ}
    (hA : Continuous A) (hb : Continuous b) {MA Mb : ℝ}
    (hMA : 0 ≤ MA) (hMb : 0 ≤ Mb)
    (hAn : ∀ t,‖A t‖ ≤ MA) (hbn : ∀ t,|b t| ≤ Mb)
    {l c t : ℝ} (hc : c ≤ l) (ht : 0 ≤ t)
    (hpos : ∀ s,0 ≤ s → ∀ z,(b s*c+c^2)*(inner ℝ z z) ≤ (inner ℝ z (A s z)))
    (hV : IsUnit (operatorValue A b l t)) (x : E) :
    c*‖x‖^2 ≤ (inner ℝ x (slope A b l t x)) := by
  obtain ⟨u,rfl⟩ := (ContinuousLinearMap.isUnit_iff_bijective.1 hV).2 x
  rw [slope_value hV]
  simp only [operatorValue_apply hA hb hMA hMb hAn hbn,
    operatorVelocity_apply hA hb hMA hMb hAn hbn]
  have hi : c*(inner ℝ (value A b l u 0) (value A b l u 0)) ≤
      (inner ℝ (value A b l u 0) (velocity A b l u 0)) := by
    rw [value_initial,velocity_initial,inner_smul_right,real_inner_self_eq_norm_sq]
    exact mul_le_mul_of_nonneg_right hc (sq_nonneg _)
  simpa only [real_inner_self_eq_norm_sq] using
    solution_energy_lower A b (value A b l u) (velocity A b l u) hb
      (value_deriv hA hb hMA hMb hAn hbn l u)
      (velocity_deriv hA hb hMA hMb hAn hbn l u) c hi hpos ht

end HarmonicCounterexample.LinearODE

end

end OAI
