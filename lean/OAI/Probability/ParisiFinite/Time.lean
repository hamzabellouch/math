import Mathlib

namespace OAI

/-! Time. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal
open MeasureTheory Filter Function Set
open scoped Topology NNReal
namespace ParisiPath

abbrev Time := Icc (0 : ℝ) 1
abbrev Path := C(Time, ℝ)

def extend (X : Path) (t : ℝ) : ℝ := X (projIcc 0 1 zero_le_one t)

lemma continuous_extend (X : Path) : Continuous (extend X) :=
  X.continuous.comp continuous_projIcc

lemma extend_of_mem (X : Path) {t : ℝ} (ht : t ∈ Icc 0 1) :
    extend X t = X ⟨t,ht⟩ := by
  simp only [extend, projIcc_of_mem zero_le_one ht]

structure Drift (K M : ℝ≥0) where
  val : ℝ → ℝ → ℝ
  measurable : Measurable (uncurry val)
  bound : ∀ t x, ‖val t x‖ ≤ M
  lipschitz : ∀ t, LipschitzWith K (val t)

variable {K M : ℝ≥0}

lemma integrable_comp (b : Drift K M) (X : Path) (a c : ℝ) :
    IntervalIntegrable (fun t => b.val t (extend X t)) volume a c := by
  refine (intervalIntegrable_const (c := (M : ℝ))).mono_fun' ?_ ?_
  · exact (b.measurable.comp (measurable_id.prodMk
      (continuous_extend X).measurable)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t => b.bound t _

def next (b : Drift K M) (W X : Path) : Path where
  toFun t := W t + ∫ s in (0 : ℝ)..(t : ℝ), b.val s (extend X s)
  continuous_toFun := W.continuous.add <|
    (intervalIntegral.continuous_primitive (integrable_comp b X) 0).comp continuous_subtype_val

@[simp] lemma next_apply (b : Drift K M) (W X : Path) (t : Time) :
    next b W X t = W t + ∫ s in (0 : ℝ)..(t : ℝ), b.val s (extend X s) := rfl

lemma dist_iterate_apply (b : Drift K M) (W X Y : Path) (n : ℕ) (t : Time) :
    dist (((next b W)^[n]) X t) (((next b W)^[n]) Y t) ≤
      (K : ℝ)^n * (t : ℝ)^n / n.factorial * dist X Y := by
  induction n generalizing t with
  | zero => simpa using ContinuousMap.dist_apply_le_dist (f := X) (g := Y) t
  | succ n ih =>
    rw [iterate_succ_apply', iterate_succ_apply', dist_eq_norm, next_apply, next_apply,
      add_sub_add_left_eq_sub, ← intervalIntegral.integral_sub
        (integrable_comp b _ _ _) (integrable_comp b _ _ _)]
    calc
      _ ≤ ∫ s in (0 : ℝ)..(t : ℝ),
          (K : ℝ)^(n+1) * s^n / n.factorial * dist X Y := by
        apply intervalIntegral.norm_integral_le_of_norm_le t.property.1
        · exact Filter.Eventually.of_forall fun s hs => by
            have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2.trans t.property.2⟩
            rw [← dist_eq_norm, extend_of_mem _ hs', extend_of_mem _ hs']
            calc
              _ ≤ K * dist (((next b W)^[n]) X ⟨s,hs'⟩)
                  (((next b W)^[n]) Y ⟨s,hs'⟩) := (b.lipschitz s).dist_le_mul _ _
              _ ≤ K * ((K : ℝ)^n * s^n / n.factorial * dist X Y) :=
                mul_le_mul_of_nonneg_left (ih ⟨s,hs'⟩) K.coe_nonneg
              _ = _ := by ring
        · exact (by fun_prop : Continuous (fun s : ℝ =>
            (K : ℝ)^(n+1) * s^n / n.factorial * dist X Y)).intervalIntegrable _ _
      _ = (K : ℝ)^(n+1) * (t : ℝ)^(n+1) / (n+1).factorial * dist X Y := by
        rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_div,
          intervalIntegral.integral_const_mul, integral_pow]
        simp only [zero_pow (Nat.succ_ne_zero n), sub_zero, Nat.factorial_succ,
          Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        field_simp

lemma dist_iterate (b : Drift K M) (W X Y : Path) (n : ℕ) :
    dist (((next b W)^[n]) X) (((next b W)^[n]) Y) ≤
      (K : ℝ)^n / n.factorial * dist X Y := by
  apply (ContinuousMap.dist_le (by positivity)).mpr
  intro t
  calc
    _ ≤ (K : ℝ)^n * (t : ℝ)^n / n.factorial * dist X Y := dist_iterate_apply b W X Y n t
    _ ≤ (K : ℝ)^n * 1^n / n.factorial * dist X Y := by
      gcongr
      · exact t.property.1
      · exact t.property.2
    _ = _ := by simp

lemma exists_contracting_iterate (b : Drift K M) :
    ∃ (n : ℕ) (C : ℝ≥0), ∀ W : Path, ContractingWith C (next b W)^[n] := by
  obtain ⟨n,hn⟩ := (FloorSemiring.tendsto_pow_div_factorial_atTop (K : ℝ)).eventually
    (gt_mem_nhds zero_lt_one) |>.exists
  refine ⟨n,⟨(K : ℝ)^n / n.factorial, by positivity⟩,fun W => ?_⟩
  exact ⟨hn, LipschitzWith.of_dist_le_mul fun X Y => dist_iterate b W X Y n⟩

lemma exists_solution (b : Drift K M) (W : Path) :
    ∃ X : Path, ∀ t : Time,
      X t = W t + ∫ s in (0 : ℝ)..(t : ℝ), b.val s (extend X s) := by
  obtain ⟨n,C,h⟩ := exists_contracting_iterate b
  refine ⟨(h W).fixedPoint, fun t => ?_⟩
  exact (congrArg (fun X : Path => X t) (h W).isFixedPt_fixedPoint_iterate).symm

lemma isFixedPt_iff (b : Drift K M) (W X : Path) :
    IsFixedPt (next b W) X ↔ ∀ t : Time,
      X t = W t + ∫ s in (0 : ℝ)..(t : ℝ), b.val s (extend X s) := by
  constructor
  · intro h t
    exact (congrArg (fun Y : Path => Y t) h).symm
  · intro h
    ext t
    exact (h t).symm

def solution (b : Drift K M) (W : Path) : Path := (exists_solution b W).choose

lemma solution_eq (b : Drift K M) (W : Path) (t : Time) :
    solution b W t = W t + ∫ s in (0 : ℝ)..(t : ℝ),
      b.val s (extend (solution b W) s) := (exists_solution b W).choose_spec t

lemma solution_fixed (b : Drift K M) (W : Path) :
    IsFixedPt (next b W) (solution b W) :=
  (isFixedPt_iff b W _).mpr (solution_eq b W)

lemma solution_unique (b : Drift K M) (W X : Path)
    (hX : ∀ t : Time, X t = W t + ∫ s in (0 : ℝ)..(t : ℝ), b.val s (extend X s)) :
    X = solution b W := by
  obtain ⟨n,C,h⟩ := exists_contracting_iterate b
  exact (h W).fixedPoint_unique' ((isFixedPt_iff b W X).mpr hX |>.iterate n)
    ((solution_fixed b W).iterate n)

@[simp] lemma solution_zero (b : Drift K M) (W : Path) :
    solution b W ⟨0,by simp⟩ = W ⟨0,by simp⟩ := by
  rw [solution_eq]
  simp

lemma dist_next_driver (b : Drift K M) (W V X : Path) :
    dist (next b W X) (next b V X) ≤ dist W V := by
  apply (ContinuousMap.dist_le dist_nonneg).mpr
  intro t
  simpa only [next_apply, dist_add_right] using
    ContinuousMap.dist_apply_le_dist (f := W) (g := V) t

lemma dist_next (b : Drift K M) (W V X Y : Path) :
    dist (next b W X) (next b V Y) ≤ dist W V + K * dist X Y := by
  calc
    _ ≤ dist (next b W X) (next b V X) + dist (next b V X) (next b V Y) :=
      dist_triangle _ _ _
    _ ≤ dist W V + K * dist X Y := add_le_add (dist_next_driver b W V X)
      (by simpa using dist_iterate b V X Y 1)

def amplification (K : ℝ≥0) : ℕ → ℝ≥0
  | 0 => 0
  | n+1 => 1 + K * amplification K n

lemma dist_iterate_drivers (b : Drift K M) (W V X : Path) (n : ℕ) :
    dist ((next b W)^[n] X) ((next b V)^[n] X) ≤
      amplification K n * dist W V := by
  induction n with
  | zero => simp [amplification]
  | succ n ih =>
    rw [iterate_succ_apply',iterate_succ_apply']
    calc
      _ ≤ dist W V + K * dist ((next b W)^[n] X) ((next b V)^[n] X) :=
        dist_next b W V _ _
      _ ≤ dist W V + K * (amplification K n * dist W V) := by gcongr
      _ = amplification K (n+1) * dist W V := by
        simp only [amplification,NNReal.coe_add,NNReal.coe_one,NNReal.coe_mul]
        ring

lemma exists_lipschitz_solution (b : Drift K M) :
    ∃ L : ℝ≥0, LipschitzWith L (solution b) := by
  obtain ⟨n,C,h⟩ := exists_contracting_iterate b
  have hC : (C : ℝ) < 1 := (h (0 : Path)).1
  let L : ℝ≥0 := ⟨(amplification K n : ℝ) / (1-C), by positivity⟩
  refine ⟨L, LipschitzWith.of_dist_le_mul fun W V => ?_⟩
  calc
    _ ≤ dist (solution b W) ((next b V)^[n] (solution b W)) / (1-C) :=
      (h V).dist_le_of_fixedPoint _ ((solution_fixed b V).iterate n)
    _ = dist ((next b W)^[n] (solution b W))
        ((next b V)^[n] (solution b W)) / (1-C) := by
      rw [(solution_fixed b W).iterate n]
    _ ≤ (amplification K n * dist W V) / (1-C) :=
      div_le_div_of_nonneg_right (dist_iterate_drivers b W V _ n) (by linarith)
    _ = (L : ℝ) * dist W V := by
      change _ = ((amplification K n : ℝ) / (1-(C : ℝ))) * dist W V
      ring

lemma continuous_solution (b : Drift K M) : Continuous (solution b) :=
  (exists_lipschitz_solution b).choose_spec.continuous

 
lemma iterate_agree_until (b : Drift K M) (W V X : Path) (T : ℝ)
    (hWV : ∀ t : Time, (t : ℝ) ≤ T → W t = V t) (n : ℕ)
    (t : Time) (ht : (t : ℝ) ≤ T) :
    (next b W)^[n] X t = (next b V)^[n] X t := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply',iterate_succ_apply',next_apply,next_apply,hWV t ht]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le t.property.1] at hs
    have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1,hs.2.trans t.property.2⟩
    dsimp only
    rw [extend_of_mem _ hs',extend_of_mem _ hs',ih ⟨s,hs'⟩ (hs.2.trans ht)]

 
lemma solution_agree_until (b : Drift K M) (W V : Path) (T : ℝ)
    (hWV : ∀ t : Time, (t : ℝ) ≤ T → W t = V t)
    (t : Time) (ht : (t : ℝ) ≤ T) :
    solution b W t = solution b V t := by
  have hh (n : ℕ) : dist (solution b W t) (solution b V t) ≤
      (K : ℝ)^n / n.factorial * dist (solution b W) (solution b V) := by
    have heq : (next b W)^[n] (solution b V) t = solution b V t := by
      rw [iterate_agree_until b W V _ T hWV n t ht, (solution_fixed b V).iterate n]
    have h := (ContinuousMap.dist_apply_le_dist
      (f := (next b W)^[n] (solution b W))
      (g := (next b W)^[n] (solution b V)) t).trans
      (dist_iterate b W (solution b W) (solution b V) n)
    rwa [(solution_fixed b W).iterate n,heq] at h
  apply dist_le_zero.mp
  have hlim := (FloorSemiring.tendsto_pow_div_factorial_atTop (K : ℝ)).mul_const
    (dist (solution b W) (solution b V))
  exact ge_of_tendsto (by simpa using hlim) (Filter.Eventually.of_forall hh)

lemma norm_solution_sub_driver (b : Drift K M) (W : Path) (t : Time) :
    ‖solution b W t - W t‖ ≤ M * (t : ℝ) := by
  rw [solution_eq,add_sub_cancel_left]
  simpa only [sub_zero,abs_of_nonneg t.property.1] using
    (intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := (t : ℝ))
      (C := (M : ℝ)) (fun s _ => b.bound s (extend (solution b W) s)))

 

lemma tendsto_iterate_solution (b : Drift K M) (W X : Path) :
    Tendsto (fun n => (next b W)^[n] X) atTop (𝓝 (solution b W)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (g := fun n => (K : ℝ)^n / n.factorial * dist X (solution b W))
    (fun n => dist_nonneg)
  · intro n
    have h := dist_iterate b W X (solution b W) n
    rwa [(solution_fixed b W).iterate n] at h
  · simpa using (FloorSemiring.tendsto_pow_div_factorial_atTop (K : ℝ)).mul_const
      (dist X (solution b W))

lemma measurable_extend_family {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → Path) (hX : ∀ t : Time, Measurable (fun ω => X ω t)) :
    Measurable (fun q : Ω × ℝ => extend (X q.1) q.2) := by
  have h := measurable_uncurry_of_continuous_of_measurable
    (u := fun s ω => extend (X ω) s) (fun ω => continuous_extend (X ω))
    (fun s => hX (projIcc 0 1 zero_le_one s))
  exact h.comp measurable_swap

lemma measurable_next_eval {Ω : Type*} [MeasurableSpace Ω]
    (b : Drift K M) (W X : Ω → Path)
    (hW : ∀ t : Time, Measurable (fun ω => W ω t))
    (hX : ∀ t : Time, Measurable (fun ω => X ω t)) (t : Time) :
    Measurable (fun ω => next b (W ω) (X ω) t) := by
  have hm : Measurable (fun q : Ω × ℝ => b.val q.2 (extend (X q.1) q.2)) :=
    b.measurable.comp (measurable_snd.prodMk (measurable_extend_family X hX))
  simp only [next_apply, intervalIntegral.integral_of_le t.property.1]
  exact (hW t).add hm.stronglyMeasurable.integral_prod_right'.measurable

 

lemma measurable_solution_eval {Ω : Type*} [MeasurableSpace Ω]
    (b : Drift K M) (W : Ω → Path)
    (hW : ∀ t : Time, Measurable (fun ω => W ω t)) (t : Time) :
    Measurable (fun ω => solution b (W ω) t) := by
  have hm (n : ℕ) : ∀ t : Time, Measurable (fun ω => (next b (W ω))^[n] 0 t) := by
    induction n with
    | zero => intro t; exact measurable_const
    | succ n ih =>
      intro t
      simp only [iterate_succ_apply']
      exact measurable_next_eval b W _ hW ih t
  apply measurable_of_tendsto_metrizable (fun n => hm n t)
  refine tendsto_pi_nhds.mpr fun ω => ?_
  exact (by fun_prop : Continuous (fun X : Path => X t)).continuousAt.tendsto.comp
    (tendsto_iterate_solution b (W ω) 0)

lemma measurable_solution_family {Ω : Type*} [MeasurableSpace Ω]
    (b : Drift K M) (W : Ω → Path)
    (hW : ∀ t : Time, Measurable (fun ω => W ω t)) :
    Measurable (fun q : Ω × ℝ => extend (solution b (W q.1)) q.2) :=
  measurable_extend_family _ (measurable_solution_eval b W hW)

 

lemma aemeasurable_solution_eval {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (b : Drift K M) (W : Ω → Path)
    (hW : ∀ t : Time, AEMeasurable (fun ω => W ω t) P) (t : Time) :
    AEMeasurable (fun ω => solution b (W ω) t) P := by
  have h : @Measurable (NullMeasurableSpace Ω P) ℝ _ _
      (fun ω => solution b (W ω) t) :=
    @measurable_solution_eval K M (NullMeasurableSpace Ω P)
      NullMeasurableSpace.instMeasurableSpace b W
      (fun t => (hW t).nullMeasurable.measurable') t
  exact (show NullMeasurable (fun ω => solution b (W ω) t) P from h).aemeasurable

 

def mesh (n : ℕ) : ℝ := 1/(n+1:ℕ)
def grid (n k : ℕ) : ℝ := (k:ℝ)*mesh n

def euler (b : Drift K M) (W : Path) (n : ℕ) : ℕ → ℝ
  | 0 => extend W 0
  | k+1 => euler b W n k + (extend W (grid n (k+1))-extend W (grid n k)) +
      mesh n * b.val (grid n k) (euler b W n k)

lemma mesh_pos (n : ℕ) : 0 < mesh n := by dsimp [mesh]; positivity
lemma grid_zero (n : ℕ) : grid n 0 = 0 := by simp [grid]
lemma grid_succ (n k : ℕ) : grid n (k+1)=grid n k+mesh n := by
  simp only [grid,Nat.cast_add,Nat.cast_one]; ring
lemma grid_end (n : ℕ) : grid n (n+1)=1 := by
  dsimp [grid,mesh]
  field_simp
lemma grid_mono (n : ℕ) : Monotone (grid n) := by
  intro k l h
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast h) (mesh_pos n).le
lemma grid_mem (n k : ℕ) (hk : k ≤ n+1) : grid n k ∈ Icc (0:ℝ) 1 := by
  refine ⟨mul_nonneg (Nat.cast_nonneg _) (mesh_pos n).le,?_⟩
  simpa only [grid_end] using grid_mono n hk

def freeze (n : ℕ) (t : ℝ) : ℝ := grid n ⌊t*(n+1:ℕ)⌋₊

lemma measurable_freeze (n : ℕ) : Measurable (freeze n) := by
  unfold freeze grid
  fun_prop

lemma freeze_tendsto {t : ℝ} (ht : 0 ≤ t) : Tendsto (fun n => freeze n t) atTop (𝓝 t) := by
  have h : Tendsto (fun n : ℕ => (n+1:ℕ):ℕ → ℝ) atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  simpa only [freeze,grid,mesh,div_eq_mul_inv,Function.comp_def,one_mul] using
    (tendsto_nat_floor_mul_div_atTop ht).comp h

lemma freeze_on_cell (n k : ℕ) {t : ℝ}
    (ht : t ∈ Ico (grid n k) (grid n (k+1))) : freeze n t = grid n k := by
  have hn : (0:ℝ)<(n+1:ℕ) := by positivity
  have hk : (k:ℝ) ≤ t*(n+1:ℕ) := by
    have hh := ht.1
    dsimp [grid,mesh] at hh
    rw [mul_one_div,div_le_iff₀ hn] at hh
    exact hh
  have hk' : t*(n+1:ℕ) < (k+1:ℕ) := by
    have hh := ht.2
    dsimp [grid,mesh] at hh
    rwa [mul_one_div,lt_div_iff₀ hn] at hh
  unfold freeze
  rw [(Nat.floor_eq_iff (show 0 ≤ t*(n+1:ℕ) by linarith)).mpr ⟨hk,by simpa only [Nat.cast_add,Nat.cast_one] using hk'⟩]

 
def residual (b : Drift K M) (X : Path) (n : ℕ) (t : ℝ) : ℝ :=
  ‖b.val t (extend X t)-b.val (freeze n t) (extend X (freeze n t))‖

def totalResidual (b : Drift K M) (X : Path) (n : ℕ) : ℝ :=
  ∫ t in (0:ℝ)..1,residual b X n t

lemma measurable_reference (b : Drift K M) (X : Path) :
    Measurable (fun t => b.val t (extend X t)) :=
  b.measurable.comp (measurable_id.prodMk (continuous_extend X).measurable)

lemma measurable_residual (b : Drift K M) (X : Path) (n : ℕ) :
    Measurable (residual b X n) :=
  ((measurable_reference b X).sub ((measurable_reference b X).comp (measurable_freeze n))).norm

lemma residual_bound (b : Drift K M) (X : Path) (n : ℕ) (t : ℝ) :
    residual b X n t ≤ 2*(M:ℝ) := by
  have h1 := b.bound t (extend X t)
  have h2 := b.bound (freeze n t) (extend X (freeze n t))
  exact (norm_sub_le _ _).trans (by linarith)

lemma integrable_residual (b : Drift K M) (X : Path) (n : ℕ) (a c : ℝ) :
    IntervalIntegrable (residual b X n) volume a c := by
  apply (intervalIntegrable_const (c := 2*(M:ℝ))).mono_fun'
    (measurable_residual b X n).aestronglyMeasurable
  exact Eventually.of_forall fun t => by simpa only [residual,norm_norm] using residual_bound b X n t

lemma totalResidual_nonneg (b : Drift K M) (X : Path) (n : ℕ) :
    0 ≤ totalResidual b X n :=
  intervalIntegral.integral_nonneg zero_le_one (fun _ _ => norm_nonneg _)

 

lemma totalResidual_tendsto_zero (b : Drift K M) (X : Path)
    (hc : ∀ᵐ t ∂volume, t ∈ Icc (0:ℝ) 1 → ContinuousAt (fun s => b.val s (extend X s)) t) :
    Tendsto (totalResidual b X) atTop (𝓝 0) := by
  have h := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (a := (0:ℝ)) (b := 1) (μ := volume) (l := atTop) (F := residual b X) (f := fun _ => (0:ℝ))
    (fun _ => 2*(M:ℝ))
    (Eventually.of_forall fun n => (measurable_residual b X n).aestronglyMeasurable.restrict)
    (Eventually.of_forall fun n => ae_of_all _ fun t _ => by
      simpa only [residual,norm_norm] using residual_bound b X n t)
    (intervalIntegrable_const) ?_
  · change Tendsto (fun n => ∫ t in (0:ℝ)..1, residual b X n t) atTop (𝓝 0)
    simpa only [intervalIntegral.integral_zero] using h
  · filter_upwards [hc] with t ht hmem
    rw [uIoc_of_le zero_le_one] at hmem
    have hh := (ht ⟨hmem.1.le,hmem.2⟩).tendsto.comp (freeze_tendsto hmem.1.le)
    simpa only [residual,Function.comp_def,sub_self,norm_zero] using ((tendsto_const_nhds (x := b.val t (extend X t))).sub hh).norm

lemma finite_discrete_gronwall {u r : ℕ → ℝ} {c : ℝ} {N : ℕ}
    (hu0 : ∀ k,0 ≤ u k) (hr : ∀ k,0 ≤ r k) (hc : 0 ≤ c)
    (hs : ∀ k<N,u (k+1) ≤ (1+c)*u k+r k) {k : ℕ} (hk : k ≤ N) :
    u k ≤ (u 0+∑ j ∈ Finset.range k,r j)*Real.exp ((k:ℝ)*c) := by
  let v (j : ℕ) := if j ≤ N then u j else 0
  have hv (j : ℕ) : 0 ≤ v j := by
    dsimp [v]
    split_ifs
    · exact hu0 j
    · exact le_rfl
  have ht (j : ℕ) (_ : 0 ≤ j) : v (j+1) ≤ (1+c)*v j+r j := by
    by_cases hj : j<N
    · simpa only [v,ite_eq_left (by omega : j+1 ≤ N),ite_eq_left (by omega : j ≤ N)] using hs j hj
    · rw [show v (j+1)=0 by simp only [v,ite_eq_right (by omega : ¬j+1 ≤ N)]]
      exact add_nonneg (mul_nonneg (by linarith) (hv j)) (hr j)
  have hh := discrete_gronwall (hv 0) ht (fun j _ => hc) (fun j _ => hr j) (Nat.zero_le k)
  simpa only [v,ite_eq_left hk,ite_eq_left (Nat.zero_le N),Nat.Ico_zero_eq_range,
    Finset.sum_const,Finset.card_range,nsmul_eq_mul] using hh

lemma solution_increment (b : Drift K M) (W : Path) {t s : ℝ}
    (ht : t ∈ Icc (0:ℝ) 1) (hs : s ∈ Icc (0:ℝ) 1) :
    extend (solution b W) s-extend (solution b W) t =
      extend W s-extend W t+∫ r in t..s,b.val r (extend (solution b W) r) := by
  have h0 := solution_eq b W ⟨t,ht⟩
  have h1 := solution_eq b W ⟨s,hs⟩
  have hi := intervalIntegral.integral_add_adjacent_intervals
    (integrable_comp b (solution b W) 0 t) (integrable_comp b (solution b W) t s)
  rw [extend_of_mem _ ht,extend_of_mem _ hs,extend_of_mem _ ht,extend_of_mem _ hs]
  linarith

def localResidual (b : Drift K M) (X : Path) (n k : ℕ) : ℝ :=
  ∫ s in (grid n k)..(grid n (k+1)),
    ‖b.val s (extend X s)-b.val (grid n k) (extend X (grid n k))‖

lemma localResidual_nonneg (b : Drift K M) (X : Path) (n k : ℕ) :
    0 ≤ localResidual b X n k :=
  intervalIntegral.integral_nonneg (grid_mono n (Nat.le_succ k)) (fun _ _ => norm_nonneg _)

lemma localResidual_eq_integral (b : Drift K M) (X : Path) (n k : ℕ) :
    localResidual b X n k = ∫ s in (grid n k)..(grid n (k+1)),residual b X n s := by
  have hnot : ∀ᵐ s ∂volume,s ≠ grid n (k+1) := by simp [ae_iff,measure_singleton]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hnot] with s hs hmem
  rw [uIoc_of_le (grid_mono n (Nat.le_succ k))] at hmem
  have hf := freeze_on_cell n k ⟨hmem.1.le,hmem.2.lt_of_ne hs⟩
  simp only [residual,hf]

lemma sum_localResidual (b : Drift K M) (X : Path) (n : ℕ) :
    (∑ k ∈ Finset.range (n+1),localResidual b X n k)=totalResidual b X n := by
  simp_rw [localResidual_eq_integral]
  rw [intervalIntegral.sum_integral_adjacent_intervals (fun k _ => integrable_residual b X n _ _),
    grid_zero,grid_end]
  rfl

lemma euler_error_step (b : Drift K M) (W : Path) (n k : ℕ) (hk : k<n+1) :
    ‖euler b W n (k+1)-extend (solution b W) (grid n (k+1))‖ ≤
      (1+(K:ℝ)*mesh n)*‖euler b W n k-extend (solution b W) (grid n k)‖+
        localResidual b (solution b W) n k := by
  let X := solution b W
  have hi := solution_increment b W (grid_mem n k (by omega)) (grid_mem n (k+1) (by omega))
  have hint := (integrable_comp b X (grid n k) (grid n (k+1))).sub
    (intervalIntegrable_const (c := b.val (grid n k) (extend X (grid n k))))
  have he : (∫ s in (grid n k)..(grid n (k+1)),
      b.val s (extend X s)-b.val (grid n k) (extend X (grid n k))) =
      (∫ s in (grid n k)..(grid n (k+1)),b.val s (extend X s))-
        mesh n*b.val (grid n k) (extend X (grid n k)) := by
    rw [intervalIntegral.integral_sub (integrable_comp b X _ _) intervalIntegrable_const,
      intervalIntegral.integral_const,grid_succ]
    simp
  have hn := intervalIntegral.norm_integral_le_integral_norm
    (f := fun s => b.val s (extend X s)-b.val (grid n k) (extend X (grid n k)))
    (μ := volume) (grid_mono n (Nat.le_succ k))
  rw [he] at hn
  have hb := (b.lipschitz (grid n k)).dist_le_mul (euler b W n k) (extend X (grid n k))
  simp only [dist_eq_norm] at hb
  have heq : euler b W n (k+1)-extend X (grid n (k+1)) =
      (euler b W n k-extend X (grid n k))+
        mesh n*(b.val (grid n k) (euler b W n k)-b.val (grid n k) (extend X (grid n k)))-
        ((∫ s in (grid n k)..(grid n (k+1)),b.val s (extend X s))-
          mesh n*b.val (grid n k) (extend X (grid n k))) := by
    dsimp only [euler]
    dsimp only [X] at *
    linarith
  change _ ≤ (1+(K:ℝ)*mesh n)*‖euler b W n k-extend X (grid n k)‖+_
  rw [heq]
  have hn' := norm_add_le (euler b W n k-extend X (grid n k))
    (mesh n*(b.val (grid n k) (euler b W n k)-b.val (grid n k) (extend X (grid n k))))
  have hn'' := norm_sub_le
    ((euler b W n k-extend X (grid n k))+
      mesh n*(b.val (grid n k) (euler b W n k)-b.val (grid n k) (extend X (grid n k))))
    ((∫ s in (grid n k)..(grid n (k+1)),b.val s (extend X s))-
      mesh n*b.val (grid n k) (extend X (grid n k)))
  rw [norm_mul,Real.norm_of_nonneg (mesh_pos n).le] at hn'
  change _ ≤ localResidual b X n k at hn
  nlinarith [mul_le_mul_of_nonneg_left hb (mesh_pos n).le]

 

lemma euler_error_bound (b : Drift K M) (W : Path) (n k : ℕ) (hk : k ≤ n+1) :
    ‖euler b W n k-extend (solution b W) (grid n k)‖ ≤
      totalResidual b (solution b W) n * Real.exp (K:ℝ) := by
  have hz : ‖euler b W n 0-extend (solution b W) (grid n 0)‖ = 0 := by
    simp only [euler,grid_zero,extend_of_mem _ (show (0:ℝ) ∈ Icc (0:ℝ) 1 by simp),
      solution_zero,sub_self,norm_zero]
  have h := finite_discrete_gronwall (N := n+1)
    (u := fun k => ‖euler b W n k-extend (solution b W) (grid n k)‖)
    (r := localResidual b (solution b W) n) (c := (K:ℝ)*mesh n)
    (fun _ => norm_nonneg _) (localResidual_nonneg b (solution b W) n)
    (mul_nonneg K.coe_nonneg (mesh_pos n).le) (fun j hj => euler_error_step b W n j hj) hk
  rw [hz,zero_add] at h
  have hsum : (∑ j ∈ Finset.range k,localResidual b (solution b W) n j) ≤
      totalResidual b (solution b W) n := by
    rw [← sum_localResidual]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk)
      (fun j _ _ => localResidual_nonneg b (solution b W) n j)
  have hexp : Real.exp ((k:ℝ)*((K:ℝ)*mesh n)) ≤ Real.exp (K:ℝ) := by
    apply Real.exp_le_exp.mpr
    have ht := (grid_mem n k hk).2
    dsimp only [grid] at ht
    nlinarith [mul_le_mul_of_nonneg_left ht K.coe_nonneg]
  exact h.trans (mul_le_mul hsum hexp (Real.exp_pos _).le
    (totalResidual_nonneg b (solution b W) n))

lemma euler_terminal_tendsto (b : Drift K M) (W : Path)
    (hc : ∀ᵐ t ∂volume, t ∈ Icc (0:ℝ) 1 →
      ContinuousAt (fun s => b.val s (extend (solution b W) s)) t) :
    Tendsto (fun n => euler b W n (n+1)) atTop (𝓝 (extend (solution b W) 1)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => by simpa only [grid_end] using euler_error_bound b W n (n+1) le_rfl)
  simpa only [zero_mul] using (totalResidual_tendsto_zero b (solution b W) hc).mul_const
    (Real.exp (K:ℝ))

 
def scaledDrift (b : Drift K M) (T : ℝ≥0) : Drift (T*K) (T*M) where
  val t x := (T:ℝ)*b.val ((T:ℝ)*t) x
  measurable := (b.measurable.comp ((measurable_fst.const_mul (T:ℝ)).prodMk
    measurable_snd)).const_mul (T:ℝ)
  bound t x := by
    rw [norm_mul,Real.norm_of_nonneg T.coe_nonneg,NNReal.coe_mul]
    exact mul_le_mul_of_nonneg_left (b.bound _ _) T.coe_nonneg
  lipschitz t := LipschitzWith.of_dist_le_mul fun x y => by
    rw [dist_eq_norm,← mul_sub,norm_mul,Real.norm_of_nonneg T.coe_nonneg,NNReal.coe_mul]
    simpa only [dist_eq_norm,mul_assoc] using
      mul_le_mul_of_nonneg_left ((b.lipschitz ((T:ℝ)*t)).dist_le_mul x y) T.coe_nonneg

def scaledPath (T : ℝ≥0) (X : Path) : Path where
  toFun t := extend X ((T:ℝ)*(t:ℝ))
  continuous_toFun := (continuous_extend X).comp (continuous_const.mul continuous_subtype_val)

lemma extend_scaledPath (T : ℝ≥0) (X : Path) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    extend (scaledPath T X) t = extend X ((T:ℝ)*t) := by
  rw [extend_of_mem _ ht]
  rfl

lemma scaled_time_mem {T : ℝ≥0} (hT : T ≤ 1) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    (T:ℝ)*t ∈ Icc (0:ℝ) 1 := by
  refine ⟨mul_nonneg T.coe_nonneg ht.1,?_⟩
  exact (mul_le_mul_of_nonneg_left ht.2 T.coe_nonneg).trans (by simpa only [mul_one] using (show (T:ℝ) ≤ 1 from NNReal.coe_le_coe.mpr hT))

lemma solution_scaled (b : Drift K M) (W : Path) {T : ℝ≥0} (hT : T ≤ 1) :
    solution (scaledDrift b T) (scaledPath T W) = scaledPath T (solution b W) := by
  symm
  apply solution_unique
  intro t
  change extend (solution b W) ((T:ℝ)*(t:ℝ)) = extend W ((T:ℝ)*(t:ℝ)) +
    ∫ s in (0:ℝ)..(t:ℝ),(T:ℝ)*b.val ((T:ℝ)*s) (extend (scaledPath T (solution b W)) s)
  have he : (∫ s in (0:ℝ)..(t:ℝ),(T:ℝ)*b.val ((T:ℝ)*s)
      (extend (scaledPath T (solution b W)) s)) =
      ∫ s in (0:ℝ)..((T:ℝ)*(t:ℝ)),b.val s (extend (solution b W) s) := by
    calc
      _ = ∫ s in (0:ℝ)..(t:ℝ),(T:ℝ)*b.val ((T:ℝ)*s)
          (extend (solution b W) ((T:ℝ)*s)) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le t.property.1] at hs
        dsimp only
        rw [extend_scaledPath T _ ⟨hs.1,hs.2.trans t.property.2⟩]
      _ = _ := by
        rw [intervalIntegral.integral_const_mul]
        simpa only [smul_eq_mul,mul_zero] using
          intervalIntegral.smul_integral_comp_mul_left
            (fun s => b.val s (extend (solution b W) s)) (a := (0:ℝ)) (b := (t:ℝ)) (T:ℝ)
  rw [he,extend_of_mem _ (scaled_time_mem hT t.property),
    extend_of_mem _ (scaled_time_mem hT t.property)]
  exact solution_eq b W _

 
def horizonEuler (b : Drift K M) (W : Path) (T : ℝ≥0) (n k : ℕ) : ℝ :=
  euler (scaledDrift b T) (scaledPath T W) n k

lemma horizonEuler_zero (b : Drift K M) (W : Path) (T : ℝ≥0) (n : ℕ) :
    horizonEuler b W T n 0 = extend W 0 := by
  simp only [horizonEuler,euler,extend_scaledPath _ _ (show (0:ℝ) ∈ Icc (0:ℝ) 1 by simp),mul_zero]

lemma horizonEuler_succ (b : Drift K M) (W : Path) (T : ℝ≥0) (n k : ℕ) (hk : k<n+1) :
    horizonEuler b W T n (k+1) = horizonEuler b W T n k +
      (extend W ((T:ℝ)*grid n (k+1))-extend W ((T:ℝ)*grid n k)) +
      ((T:ℝ)*mesh n)*b.val ((T:ℝ)*grid n k) (horizonEuler b W T n k) := by
  simp only [horizonEuler,euler,scaledDrift,
    extend_scaledPath _ _ (grid_mem n (k+1) (by omega)),
    extend_scaledPath _ _ (grid_mem n k (by omega))]
  ring

lemma horizonEuler_terminal_tendsto (b : Drift K M) (W : Path) {T : ℝ≥0} (hT : T ≤ 1)
    (hc : ∀ᵐ t ∂volume, t ∈ Icc (0:ℝ) 1 →
      ContinuousAt (fun s => (scaledDrift b T).val s
        (extend (solution (scaledDrift b T) (scaledPath T W)) s)) t) :
    Tendsto (fun n => horizonEuler b W T n (n+1)) atTop
      (𝓝 (extend (solution b W) T)) := by
  have h := euler_terminal_tendsto (scaledDrift b T) (scaledPath T W) hc
  rw [solution_scaled b W hT,extend_scaledPath T _ (show (1:ℝ) ∈ Icc (0:ℝ) 1 by simp),mul_one] at h
  exact h

lemma norm_euler_sub_driver (b : Drift K M) (W : Path) (n k : ℕ) :
    ‖euler b W n k-extend W (grid n k)‖ ≤ (k:ℝ)*mesh n*(M:ℝ) := by
  induction k with
  | zero => simp [euler,grid_zero]
  | succ k ih =>
    have he : euler b W n (k+1)-extend W (grid n (k+1)) =
        (euler b W n k-extend W (grid n k))+mesh n*b.val (grid n k) (euler b W n k) := by
      rw [euler]
      ring
    rw [he]
    calc
      _ ≤ ‖euler b W n k-extend W (grid n k)‖+
          ‖mesh n*b.val (grid n k) (euler b W n k)‖ := norm_add_le _ _
      _ ≤ (k:ℝ)*mesh n*(M:ℝ)+mesh n*(M:ℝ) := by
        rw [norm_mul,Real.norm_of_nonneg (mesh_pos n).le]
        exact add_le_add ih (mul_le_mul_of_nonneg_left (b.bound _ _) (mesh_pos n).le)
      _ = _ := by simp only [Nat.cast_add,Nat.cast_one]; ring

lemma euler_error_uniform_bound (b : Drift K M) (W : Path) (n k : ℕ) (hk : k ≤ n+1) :
    ‖euler b W n k-extend (solution b W) (grid n k)‖ ≤ 2*(M:ℝ) := by
  have h1 := norm_euler_sub_driver b W n k
  have h2 := norm_solution_sub_driver b W ⟨grid n k,grid_mem n k hk⟩
  rw [← extend_of_mem _ (grid_mem n k hk),← extend_of_mem _ (grid_mem n k hk)] at h2
  have he : euler b W n k-extend (solution b W) (grid n k) =
      (euler b W n k-extend W (grid n k))-
        (extend (solution b W) (grid n k)-extend W (grid n k)) := by ring
  rw [he]
  have ht := (grid_mem n k hk).2
  have hn := norm_sub_le (euler b W n k-extend W (grid n k))
    (extend (solution b W) (grid n k)-extend W (grid n k))
  change _ ≤ (M:ℝ)*grid n k at h2
  change _ ≤ grid n k*(M:ℝ) at h1
  nlinarith [mul_le_mul_of_nonneg_left ht M.coe_nonneg]

lemma aemeasurable_euler {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (b : Drift K M) (W : Ω → Path)
    (hW : ∀ t : Time,AEMeasurable (fun ω => W ω t) P) (n k : ℕ) :
    AEMeasurable (fun ω => euler b (W ω) n k) P := by
  have hw (t : ℝ) : AEMeasurable (fun ω => extend (W ω) t) P :=
    hW (projIcc 0 1 zero_le_one t)
  induction k with
  | zero => exact hw 0
  | succ k ih =>
    exact (ih.add ((hw _).sub (hw _))).add
      (((b.measurable.comp (measurable_const.prodMk measurable_id)).comp_aemeasurable ih).const_mul _)

lemma aemeasurable_scaledPath_eval {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (W : Ω → Path) (hW : ∀ t : Time,AEMeasurable (fun ω => W ω t) P)
    (T : ℝ≥0) (t : Time) : AEMeasurable (fun ω => scaledPath T (W ω) t) P :=
  hW (projIcc 0 1 zero_le_one ((T:ℝ)*(t:ℝ)))

end ParisiPath

end

end OAI
