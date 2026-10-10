import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.MachineTorus
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.ChartExpressions

namespace OAI

noncomputable section
namespace VelocityDetection.Effective
open Set Filter Function
open scoped Topology BigOperators ContDiff
open VelocityDetection.Effective.Expr ArrayRecipe JointCalculus

def residualCode (a : Fin 2 → Code) (i : Fin 2) : Code :=
  letI := neZeroTwo
  letI := neZeroFive
  (a i).diff 1 + a 0*(a i).diff 2 + a 1*(a i).diff 3 -
    .var 0*((((a i).diff 2).diff 2)+(((a i).diff 3).diff 3))

theorem valid_residualCode (a : Fin 2 → Code) {x : Fin 5 → ℝ} (ha : ∀ i, (a i).Valid x) (i) :
    (residualCode a i).Valid x := by
  simp only [residualCode,valid_sub,valid_add,valid_mul,valid_var,true_and]
  exact ⟨⟨⟨valid_diff _ (ha i) _,ha 0,valid_diff _ (ha i) _⟩,ha 1,valid_diff _ (ha i) _⟩,
    valid_diff _ (valid_diff _ (ha i) _) _,valid_diff _ (valid_diff _ (ha i) _) _⟩

theorem eval_residualCode (a : Fin 2 → Code) (f : ℝ → VectorField 2)
    (hf : ∀ ν > 0, ContDiff ℝ ∞ (uncurry (f ν))) {x : Fin 5 → ℝ} (hx : 0 < x 0)
    (ha : ∀ i, (a i).Valid x)
    (he : ∀ i, (fun y => (a i).eval y) =ᶠ[𝓝 x]
      pull (fun ν p => f ν p.1 p.2 i)) (i) :
    (residualCode a i).eval x = residual (x 0) (uncurry (f (x 0))) (point x) i := by
  have hi (ν : ℝ) (hν : 0 < ν) (k : Fin 2) : ContDiff ℝ ∞ (fun p : ℝ × Coord 2 => f ν p.1 p.2 k) :=
    (contDiff_apply ℝ ℝ k).comp (hf ν hν)
  have hd (j : Fin 3) : ((a i).diff (axis j)).eval x =
      dAlong (direction j) (fun p : ℝ × Coord 2 => f (x 0) p.1 p.2 i) (point x) := by
    rw [← coordinateD_eval _ (ha i),coordinateD_congr (he i)]
    exact coordinateD_pull _ _ (hi _ hx i) j
  have hdd (j : Fin 3) : (((a i).diff (axis j)).diff (axis j)).eval x =
      dAlong (direction j) (dAlong (direction j) (fun p : ℝ × Coord 2 => f (x 0) p.1 p.2 i)) (point x) := by
    calc
      _ = mixedD [axis j,axis j] (fun y => (a i).eval y) x := (mixedD_eval _ (ha i) _).symm
      _ = mixedD [axis j,axis j] (pull (fun ν p => f ν p.1 p.2 i)) x := mixedD_congr (he i) _
      _ = _ := coordinateDD_pull _ _ hx (fun ν hν => hi ν hν i) j
  have h1 := hd 0
  have h2 := hd 1
  have h3 := hd 2
  have h22 := hdd 1
  have h33 := hdd 2
  simp [axis,direction] at h1 h2 h3 h22 h33
  simp only [residualCode,eval_sub,eval_add,eval_mul,eval_var,h1,h2,h3,h22,h33]
  have h0 : (a 0).eval x = pull (fun ν p => f ν p.1 p.2 0) x := (he 0).self_of_nhds
  have hv1 : (a 1).eval x = pull (fun ν p => f ν p.1 p.2 1) x := (he 1).self_of_nhds
  rw [h0,hv1]
  rfl

end VelocityDetection.Effective
end

noncomputable section
namespace VelocityDetection.Effective.ArrayRecipe
open Set Filter Function Turing
open scoped Topology BigOperators ContDiff
open VelocityDetection.Effective.Expr ArrayRecipe JointCalculus

def initialCode (N b m q : ℕ) : Fin 2 → Code :=
  ![spacing N b m 0 * .rat q,-spacing N b m 0]

def source (N b m q : ℕ) : Code :=
  letI := neZeroFive
  Recipe.impulse (.var 1) (initialCode N b m q) ![.var 2,.var 3]

@[simp] theorem eval_initialCode (N b m q : ℕ) (x : Fin 5 → ℝ) (i) :
    (initialCode N b m q i).eval x =
      ![Expanding.spacing (x 0) (HistoryRouting.K N b m) (HistoryRouting.D N b) 0*q,
        -Expanding.spacing (x 0) (HistoryRouting.K N b m) (HistoryRouting.D N b) 0] i := by
  fin_cases i <;> simp [initialCode]

@[simp] theorem eval_source (N b m q : ℕ) (x : Fin 5 → ℝ) :
    (source N b m q).eval x = SmoothProfiles.impulse
      ![Expanding.spacing (x 0) (HistoryRouting.K N b m) (HistoryRouting.D N b) 0*q,
        -Expanding.spacing (x 0) (HistoryRouting.K N b m) (HistoryRouting.D N b) 0]
      (x 1) ![x 2,x 3] := by
  simp only [source,Recipe.eval_impulse,eval_initialCode,eval_var]
  rfl

theorem valid_source (N b m q : ℕ) (x : Fin 5 → ℝ) : (source N b m q).Valid x := by
  apply Recipe.valid_impulse
  · trivial
  · intro i; fin_cases i <;> simp [initialCode]
  · intro i; fin_cases i <;> trivial

end VelocityDetection.Effective.ArrayRecipe
end

noncomputable section
namespace VelocityDetection.Effective
open Set Filter Function Turing
open scoped Topology BigOperators ContDiff
open VelocityDetection.Effective.Expr ArrayRecipe JointCalculus

noncomputable def forceFunction (f : ℝ → VectorField 3) (i : Fin 3) (x : Fin 5 → ℝ) : ℝ :=
  letI := neZeroFive
  f (x 0) (x 1) ![x 2,x 3,x 4] i

end VelocityDetection.Effective
end

noncomputable section
namespace VelocityDetection.Effective.MachineRecipe
open Set Filter Function Turing
open scoped Topology BigOperators ContDiff
open VelocityDetection.Effective.Expr ArrayRecipe JointCalculus
variable {b N : ℕ} [NeZero b] [NeZero N]

inductive Domain where | torus | cylinder
  deriving DecidableEq, Repr

def field (d : Domain) (B R L : ℕ) (M : TM0.Machine (Fin b) (Fin N))
    (w : List (Fin b)) (i : Fin 2) : Code := match d with
  | .torus => ChartRecipe.field (NeZero.pos b) (MachineHistory.table M) w.length B R L i
  | .cylinder => ArrayRecipe.field (NeZero.pos b) (MachineHistory.table M) w.length L i

def source (d : Domain) (B R L : ℕ) (w : List (Fin b)) : Code := match d with
  | .torus => ChartRecipe.source (N+1) b w.length B (MachineTorus.initialAddress (N:=N) w) R L
  | .cylinder => ArrayRecipe.source (N+1) b w.length (MachineTorus.initialAddress (N:=N) w)

def force (d : Domain) (B R L : ℕ) (M : TM0.Machine (Fin b) (Fin N))
    (w : List (Fin b)) (i : Fin 3) : Code :=
  letI := neZeroTwo
  ![residualCode (field d B R L M w) 0,residualCode (field d B R L M w) 1,
    source (N:=N) d B R L w] i

noncomputable def analyticField (d : Domain) (ν : ℝ) (M : TM0.Machine (Fin b) (Fin N))
    (w : List (Fin b)) : VectorField 2 := match d with
  | .torus => BurstTotal.field (MachineTorus.data M w) ν
  | .cylinder => RoutingArray.field (MachineCylinder.data M w) ν

noncomputable def analyticForce (d : Domain) (ν : ℝ) (M : TM0.Machine (Fin b) (Fin N))
    (w : List (Fin b)) : VectorField 3 := match d with
  | .torus => MachineTorus.force ν M w
  | .cylinder => MachineCylinder.force ν M w

def Good (d : Domain) (R L : ℕ) (x : Fin 5 → ℝ) : Prop :=
  0 < x 0 ∧ x 1 < L ∧ (d = .torus → ‖![x 2,x 3]‖+1 < R)

theorem good_open (d : Domain) (R L : ℕ) : IsOpen {x | Good d R L x} := by
  have hs : Continuous (fun x : Fin 5 → ℝ => (![x 2,x 3] : Coord 2)) := by
    apply continuous_pi; intro i; fin_cases i <;> fun_prop
  by_cases hd : d = .torus
  · subst d
    simp only [Good,true_implies]
    exact (isOpen_lt continuous_const (continuous_apply 0)).inter
      ((isOpen_lt (continuous_apply 1) continuous_const).inter
        (isOpen_lt (hs.norm.add_const 1) continuous_const))
  · simp only [Good,hd,false_implies,and_true]
    exact (isOpen_lt continuous_const (continuous_apply 0)).inter
      (isOpen_lt (continuous_apply 1) continuous_const)

theorem valid_field (d : Domain) (R L : ℕ) (M : TM0.Machine (Fin b) (Fin N))
    (w : List (Fin b)) {x : Fin 5 → ℝ} (hx : 0 < x 0) (i) :
    (field d SmoothBump.bound R L M w i).Valid x := by
  cases d
  · exact ChartRecipe.valid_field (by omega : 0 < N+1) _ _ _ _ _ hx.le i
  · exact ArrayRecipe.valid_field (by omega : 0 < N+1) _ _ _ _ hx i

theorem valid_source (d : Domain) (R L : ℕ) (M : TM0.Machine (Fin b) (Fin N))
    (w : List (Fin b)) {x : Fin 5 → ℝ} (hx : 0 < x 0) :
    (source (N:=N) d SmoothBump.bound R L w).Valid x := by
  cases d
  · exact ChartRecipe.valid_source (by omega : 0 < N+1) (NeZero.pos b) (MachineHistory.table M) _ _ _ _ hx.le
  · exact ArrayRecipe.valid_source _ _ _ _ x

theorem valid_force (d : Domain) (R L : ℕ) (M : TM0.Machine (Fin b) (Fin N))
    (w : List (Fin b)) {x : Fin 5 → ℝ} (hx : 0 < x 0) (i) :
    (force d SmoothBump.bound R L M w i).Valid x := by
  fin_cases i
  · exact valid_residualCode _ (valid_field d R L M w hx) 0
  · exact valid_residualCode _ (valid_field d R L M w hx) 1
  · exact valid_source d R L M w hx

theorem eval_field (d : Domain) (R L : ℕ) (M : TM0.Machine (Fin b) (Fin N))
    (w : List (Fin b)) {x : Fin 5 → ℝ} (hx : Good d R L x) (i) :
    (field d SmoothBump.bound R L M w i).eval x =
      analyticField d (x 0) M w (x 1) ![x 2,x 3] i := by
  cases d
  · exact ChartRecipe.eval_field (by omega : 0 < N+1) _ _ _ R L hx.1.le hx.2.1 (hx.2.2 rfl) i
  · exact ArrayRecipe.eval_field (by omega : 0 < N+1) _ _ _ L hx.1 hx.2.1 i

theorem field_germ (d : Domain) (R L : ℕ) (M : TM0.Machine (Fin b) (Fin N))
    (w : List (Fin b)) {x : Fin 5 → ℝ} (hx : Good d R L x) (i) :
    (fun y => (field d SmoothBump.bound R L M w i).eval y) =ᶠ[𝓝 x]
      pull (fun ν p => analyticField d ν M w p.1 p.2 i) :=
  (show ∀ᶠ y in 𝓝 x, Good d R L y from (good_open d R L).mem_nhds hx).mono (fun _ hy => eval_field d R L M w hy i)

theorem eval_source (d : Domain) (R L : ℕ) (M : TM0.Machine (Fin b) (Fin N))
    (w : List (Fin b)) {x : Fin 5 → ℝ} (hx : Good d R L x) :
    (source (N:=N) d SmoothBump.bound R L w).eval x =
      analyticForce d (x 0) M w (x 1) ![x 2,x 3,x 4] 2 := by
  cases d
  · let tr := MachineTorus.correctnessTrace M w
    exact ChartRecipe.eval_source (by omega : 0 < N+1) (NeZero.pos b) (MachineHistory.table M) w.length
      _ R L (tr.instruction 0 (MachineTorus.trace_active M w))
      (tr.source_eq 0 (MachineTorus.trace_active M w)) hx.1.le hx.2.1 (hx.2.2 rfl)
  · exact ArrayRecipe.eval_source _ _ _ _ x

theorem eval_force (d : Domain) (R L : ℕ) (M : TM0.Machine (Fin b) (Fin N))
    (w : List (Fin b)) {x : Fin 5 → ℝ} (hx : Good d R L x) (i) :
    (force d SmoothBump.bound R L M w i).eval x =
      forceFunction (fun ν => analyticForce d ν M w) i x := by
  have hh (ν : ℝ) (hν : 0 < ν) : ContDiff ℝ ∞ (uncurry (analyticField d ν M w)) := by
    cases d
    · exact BurstTotal.contDiff_field _ ν hν.le
    · exact RoutingArray.contDiff_field _ ν hν
  have he (j : Fin 2) := eval_residualCode (field d SmoothBump.bound R L M w)
    (fun ν => analyticField d ν M w) hh hx.1 (valid_field d R L M w hx.1)
    (field_germ d R L M w hx) j
  fin_cases i
  · change (residualCode _ 0).eval x = _
    rw [he 0]
    cases d <;> simp only [forceFunction,analyticForce,analyticField,MachineTorus.force,MachineCylinder.force,
      BurstTotal.force,RoutingArray.force,JointCalculus.lift,JointCalculus.projection_apply,horizontal,point,
      Matrix.cons_val_zero,Matrix.cons_val_one] <;> rfl
  · change (residualCode _ 1).eval x = _
    rw [he 1]
    cases d <;> simp only [forceFunction,analyticForce,analyticField,MachineTorus.force,MachineCylinder.force,
      BurstTotal.force,RoutingArray.force,JointCalculus.lift,JointCalculus.projection_apply,horizontal,point,
      Matrix.cons_val_zero,Matrix.cons_val_one] <;> rfl
  · exact eval_source d R L M w hx

theorem force_germ (d : Domain) (R L : ℕ) (M : TM0.Machine (Fin b) (Fin N))
    (w : List (Fin b)) {x : Fin 5 → ℝ} (hx : Good d R L x) (i) :
    (fun y => (force d SmoothBump.bound R L M w i).eval y) =ᶠ[𝓝 x]
      forceFunction (fun ν => analyticForce d ν M w) i :=
  (show ∀ᶠ y in 𝓝 x, Good d R L y from (good_open d R L).mem_nhds hx).mono (fun _ hy => eval_force d R L M w hy i)

end VelocityDetection.Effective.MachineRecipe
end

noncomputable section
namespace VelocityDetection.Effective.MachineRecipe
open Set Filter Function Turing
open scoped Topology ContDiff BigOperators
variable {b N : ℕ} [NeZero b] [NeZero N]

def timeCutoff (q : Fin 5 → ℕ → ℚ) : ℕ :=
  letI := neZeroFive
  ⌈q 1 0+2⌉₊

def spaceCutoff (q : Fin 5 → ℕ → ℚ) : ℕ :=
  letI := neZeroFive
  ⌈|q 2 0|+|q 3 0|+3⌉₊

theorem cutoffs_good (d : Domain) {q : Fin 5 → ℕ → ℚ} {x : Fin 5 → ℝ}
    (hq : Names q x) (hν : 0 < x 0) : Good d (spaceCutoff q) (timeCutoff q) x := by
  have h (i) : |x i-(q i 0:ℝ)| ≤ 1 := by simpa [accuracy] using hq i 0
  have ht : (q 1 0:ℝ)+2 ≤ timeCutoff q := by
    exact_mod_cast (Nat.le_ceil (q 1 0+2))
  have hR : |(q 2 0:ℝ)|+|(q 3 0:ℝ)|+3 ≤ spaceCutoff q := by
    exact_mod_cast (Nat.le_ceil (|q 2 0|+|q 3 0|+3))
  refine ⟨hν,by linarith [(abs_le.mp (h 1)).2],fun _ => ?_⟩
  have hi (i) : |x i| ≤ |(q i 0:ℝ)|+1 := by
    have hh := abs_add_le (x i-(q i 0:ℝ)) (q i 0:ℝ)
    simp only [sub_add_cancel] at hh
    linarith [h i]
  have hn : ‖(![x 2,x 3] : Coord 2)‖ ≤ |(q 2 0:ℝ)|+|(q 3 0:ℝ)|+1 := by
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro i; fin_cases i <;> simp only [Real.norm_eq_abs] <;> change |x _| ≤ _
    · linarith [hi 2,abs_nonneg (q 3 0:ℝ)]
    · linarith [hi 3,abs_nonneg (q 2 0:ℝ)]
  linarith

def runTrial (d : Domain) (B : ℕ) (M : TM0.Machine (Fin b) (Fin N))
    (w : List (Fin b)) (i : Fin 3) (is : List (Fin 5)) (q : Fin 5 → ℕ → ℚ)
    (ε : ℚ) (k : ℕ) : Option ℚ :=
  trial (force d B (spaceCutoff q) (timeCutoff q) M w i) is q ε k

theorem runTrial_correct (d : Domain) (M : TM0.Machine (Fin b) (Fin N))
    (w : List (Fin b)) (i : Fin 3) (is : List (Fin 5))
    {q : Fin 5 → ℕ → ℚ} {x : Fin 5 → ℝ} (hq : Names q x) (hν : 0 < x 0)
    (ε : ℚ) (k : ℕ) {r : ℚ} (hr : runTrial d SmoothBump.bound M w i is q ε k = some r) :
    |mixedD is (forceFunction (fun ν => analyticForce d ν M w) i) x-(r:ℝ)| ≤ (ε:ℝ) := by
  have hg := cutoffs_good d hq hν
  rw [← mixedD_congr (force_germ d _ _ M w hg i) is]
  exact trial_correct _ is hq (valid_force d _ _ M w hν i) ε k hr

theorem runTrial_terminates (d : Domain) (M : TM0.Machine (Fin b) (Fin N))
    (w : List (Fin b)) (i : Fin 3) (is : List (Fin 5))
    {q : Fin 5 → ℕ → ℚ} {x : Fin 5 → ℝ} (hq : Names q x) (hν : 0 < x 0)
    {ε : ℚ} (hε : 0 < ε) : ∃ k r, runTrial d SmoothBump.bound M w i is q ε k = some r :=
  trial_terminates _ is hq (valid_force d _ _ M w hν i) hε

end VelocityDetection.Effective.MachineRecipe
end

noncomputable section
namespace VelocityDetection.Effective
open Set Filter Function
open scoped Topology BigOperators

theorem flatRound_radius_tendsto_precision (p : Poly) {q : ℕ → ℚ} {x : ℝ}
    {κ : ℕ → ℕ} (hκ : Tendsto κ atTop atTop)
    (hq : Tendsto (fun n => (q n:ℝ)) atTop (𝓝 x)) :
    Tendsto (fun n => ((flatRound p (q n) (κ n)).radius:ℝ)) atTop (𝓝 0) := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have he := hq.eventually_lt_const hx
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with n hn
    rw [flatRound_nonpos p (by exact_mod_cast hn.le)]
    norm_num
  · apply squeeze_zero (fun n => by exact_mod_cast flatRound_radius_nonneg p (q n) (κ n))
      (g := fun n => (polyBound (nextPoly p):ℝ)*|(q n:ℝ)|)
      (fun n => by exact_mod_cast flatRound_small_bound p (q n) (κ n))
    simpa using hq.abs.const_mul (polyBound (nextPoly p):ℝ)
  · have hi := hq.inv₀ (ne_of_gt hx)
    have hi_abs : Tendsto (fun n => |((q n)⁻¹:ℚ)|.cast) atTop (𝓝 |x⁻¹|) := by
      simpa only [Rat.cast_inv,Rat.cast_abs] using hi.abs
    have hb := hi_abs.eventually_lt_const (show |x⁻¹| < |x⁻¹|+1 by linarith)
    have hp := hq.eventually_const_lt hx
    let C : ℝ := |x⁻¹|+1
    have hC : 0 ≤ C := by dsimp [C]; positivity
    have hf : Tendsto (fun n : ℕ => C^(κ n)/((κ n).factorial:ℝ)) atTop (𝓝 0) :=
      (FloorSemiring.tendsto_pow_div_factorial_atTop C).comp hκ
    have he : Tendsto (fun n => (expError (-(q n)⁻¹) (κ n):ℝ)) atTop (𝓝 0) := by
      apply squeeze_zero' (g := fun n : ℕ => C^(κ n)/((κ n).factorial:ℝ)*2)
        (Filter.Eventually.of_forall (fun n => by exact_mod_cast expError_nonneg (-(q n)⁻¹) (κ n)))
        (by
          filter_upwards [hb] with n hn
          simp only [expError,Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_abs,
            Rat.cast_inv,Rat.cast_natCast,Rat.cast_ofNat,abs_neg]
          gcongr
          simpa only [Rat.cast_abs,Rat.cast_inv] using hn.le)
        (by simpa using hf.mul_const 2)
    have hv : Tendsto (fun n => (polyEval p (q n)⁻¹:ℝ)) atTop (𝓝 ((poly p).eval x⁻¹)) := by
      simpa only [cast_polyEval,Rat.cast_inv,Function.comp_def] using ((poly p).continuous.tendsto x⁻¹).comp hi
    have he' : Tendsto (fun n => (|polyEval p (q n)⁻¹| *expError (-(q n)⁻¹) (κ n):ℝ)) atTop (𝓝 0) := by
      simpa only [Rat.cast_mul,Rat.cast_abs,mul_zero] using hv.abs.mul he
    have hden : Tendsto (fun n : ℕ => (κ n+1:ℝ)) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.comp hκ)
    have hr : Tendsto (fun n : ℕ => C/(κ n+1:ℝ)) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv,mul_zero,Function.comp_def] using
        (tendsto_inv_atTop_zero.comp hden).const_mul C
    have hs := hr.eventually_lt_const (show (0:ℝ)<1/2 by norm_num)
    apply squeeze_zero' (g := fun n => (|polyEval p (q n)⁻¹| *expError (-(q n)⁻¹) (κ n):ℝ))
      (Filter.Eventually.of_forall (fun n => by exact_mod_cast flatRound_radius_nonneg p (q n) (κ n)))
      (by
        filter_upwards [hp,hb,hs] with n hpn hbn hsn
        have hrn : |(q n)⁻¹|/(κ n+1) ≤ (1/2:ℚ) := by
          have hd : (0:ℝ) < (κ n:ℝ)+1 := by positivity
          have hh : ((|(q n)⁻¹|/(κ n+1):ℚ):ℝ) < ((1/2:ℚ):ℝ) := by
            simpa only [Rat.cast_div,Rat.cast_add,Rat.cast_natCast,Rat.cast_one,Rat.cast_ofNat]
              using (div_le_div_of_nonneg_right hbn.le hd.le).trans_lt hsn
          exact Rat.cast_le.mp hh.le
        exact_mod_cast flatRound_exp_bound p (by exact_mod_cast hpn) (κ n) hrn)
      he'

end VelocityDetection.Effective
end

noncomputable section
namespace VelocityDetection.Effective.Ball
open Set Filter Function
open scoped Topology BigOperators

theorem converges_flat_precision (p : Poly) {a : ℕ → Ball} {x : ℝ} (ha : Converges a x)
    {κ : ℕ → ℕ} (hκ : Tendsto κ atTop atTop) :
    Converges (fun k => (a k).flat p (κ k)) (Effective.flat p x) := by
  have hr := flatRound_radius_tendsto_precision p hκ ha.1
  have hf : Tendsto (fun k => Effective.flat p ((a k).center:ℝ)) atTop (𝓝 (Effective.flat p x)) :=
    (contDiff_flat p).continuous.continuousAt.tendsto.comp ha.1
  have hc : Tendsto (fun k => ((flatRound p (a k).center (κ k)).center:ℝ)) atTop (𝓝 (Effective.flat p x)) := by
    apply tendsto_of_tendsto_of_dist hf
    apply squeeze_zero (fun k => dist_nonneg) (fun k => ?_) hr
    simpa only [Real.dist_eq] using (flatRound_certifies p (a k).center (κ k)).2
  refine ⟨hc,?_⟩
  simpa only [flat,Rat.cast_add,Rat.cast_mul,mul_zero,zero_add] using
    (hr.add (ha.2.const_mul (polyBound (nextPoly p):ℝ)))

end VelocityDetection.Effective.Ball
end

noncomputable section
namespace VelocityDetection.Effective.Expr
open Set Filter Function
open scoped Topology BigOperators
variable {n : ℕ}

theorem round_converges_precision (e : Expr n) {a : ℕ → Fin n → Ball} {x : Fin n → ℝ}
    (ha : ∀ i, Ball.Converges (fun k => a k i) (x i)) (hv : e.Valid x)
    {κ : ℕ → ℕ} (hκ : Tendsto κ atTop atTop) :
    Ball.Converges (fun k => e.round (a k) (κ k)) (e.eval x) ∧
      ∀ᶠ k in atTop, e.safe (a k) (κ k) = true := by
  induction e with
  | rat q => exact ⟨Ball.converges_atom q,Eventually.of_forall (fun _ => rfl)⟩
  | var i => exact ⟨ha i,Eventually.of_forall (fun _ => rfl)⟩
  | add e f he hf | mul e f he hf =>
    obtain ⟨hec,hes⟩ := he hv.1
    obtain ⟨hfc,hfs⟩ := hf hv.2
    constructor
    · first | exact Ball.converges_add hec hfc | exact Ball.converges_mul hec hfc
    · filter_upwards [hes,hfs] with k hk hk'
      exact Bool.and_eq_true_iff.mpr ⟨hk,hk'⟩
  | neg e he =>
    obtain ⟨hc,hs⟩ := he hv
    exact ⟨Ball.converges_neg hc,hs⟩
  | flat p e he =>
    obtain ⟨hc,hs⟩ := he hv
    exact ⟨Ball.converges_flat_precision p hc hκ,hs⟩
  | inv e he =>
    obtain ⟨hc,hs⟩ := he hv.1
    refine ⟨Ball.converges_inv hc hv.2,?_⟩
    filter_upwards [hs,Ball.eventually_invSafe hc hv.2] with k hk hk'
    exact Bool.and_eq_true_iff.mpr ⟨hk,hk'⟩

end VelocityDetection.Effective.Expr
end

noncomputable section
namespace VelocityDetection.Effective
open Set Filter Function
open scoped Topology BigOperators

structure RationalBox (n : ℕ) where
  lower : Fin n → ℚ
  upper : Fin n → ℚ
  ordered : ∀ i, lower i ≤ upper i

end VelocityDetection.Effective
end

noncomputable section
namespace VelocityDetection.Effective.RationalBox
open Set Filter Function
open scoped Topology BigOperators
variable {n : ℕ} (Q : RationalBox n)

def carrier : Set (Fin n → ℝ) := Icc (fun i => (Q.lower i:ℝ)) (fun i => (Q.upper i:ℝ))

theorem compact_carrier : IsCompact Q.carrier := isCompact_Icc

def cell (k : ℕ) (j : Fin n → Fin (k+2)) (i : Fin n) : Ball :=
  ⟨Q.lower i+(Q.upper i-Q.lower i)*((j i:ℕ):ℚ)/(k+1),
    (Q.upper i-Q.lower i)/(k+1)⟩

theorem cell_nonneg (k : ℕ) (j : Fin n → Fin (k+2)) (i) : 0 ≤ (Q.cell k j i).radius :=
  div_nonneg (sub_nonneg.mpr (Q.ordered i)) (by positivity)

theorem center_mem (k : ℕ) (j : Fin n → Fin (k+2)) :
    (fun i => ((Q.cell k j i).center:ℝ)) ∈ Q.carrier := by
  have hj (i) : (0:ℝ) ≤ (j i:ℕ) ∧ (j i:ℕ) ≤ (k:ℝ)+1 :=
    ⟨Nat.cast_nonneg _,by exact_mod_cast (show (j i:ℕ) ≤ k+1 by omega)⟩
  have ho (i) : (Q.lower i:ℝ) ≤ (Q.upper i:ℝ) := by exact_mod_cast Q.ordered i
  constructor <;> intro i <;> simp only [cell,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_sub,
    Rat.cast_natCast,Rat.cast_one] <;> have hk : (0:ℝ) < (k:ℝ)+1 := by positivity
  · exact le_add_of_nonneg_right (div_nonneg (mul_nonneg (sub_nonneg.mpr (ho i)) (hj i).1) hk.le)
  · have hh := mul_le_mul_of_nonneg_left (hj i).2 (sub_nonneg.mpr (ho i))
    have hh' := (div_le_iff₀ hk).mpr hh
    linarith

theorem covers (k : ℕ) {x : Fin n → ℝ} (hx : x ∈ Q.carrier) :
    ∃ j : Fin n → Fin (k+2), ∀ i, (Q.cell k j i).Certifies (x i) := by
  have hlocal (i : Fin n) : ∃ j : Fin (k+2),
      |x i-((Q.lower i+(Q.upper i-Q.lower i)*(j:ℕ)/(k+1):ℚ):ℝ)| ≤
        ((Q.upper i-Q.lower i)/(k+1):ℚ) := by
    have hlo := hx.1 i
    have hhi := hx.2 i
    have hk : (0:ℝ) < (k:ℝ)+1 := by positivity
    by_cases he : Q.lower i = Q.upper i
    · refine ⟨0,?_⟩
      have hx' : x i = (Q.lower i:ℝ) := le_antisymm (by simpa [he] using hhi) hlo
      simp [he,hx']
    have hd : (0:ℝ) < (Q.upper i:ℝ)-(Q.lower i:ℝ) := by
      exact_mod_cast sub_pos.mpr (lt_of_le_of_ne (Q.ordered i) he)
    let a : ℝ := (x i-(Q.lower i:ℝ))*((k:ℝ)+1)/((Q.upper i:ℝ)-(Q.lower i:ℝ))
    have ha0 : 0 ≤ a := div_nonneg (mul_nonneg (sub_nonneg.mpr hlo) hk.le) hd.le
    have ha : a ≤ (k:ℝ)+1 := by
      dsimp only [a]
      rw [div_le_iff₀ hd]
      nlinarith
    have hj : ⌊a⌋₊ < k+2 := by
      rw [Nat.floor_lt ha0]
      push_cast
      linarith
    refine ⟨⟨⌊a⌋₊,hj⟩,?_⟩
    have hfloor := Nat.floor_le ha0
    have hceil := Nat.lt_floor_add_one a
    have heq : a*((Q.upper i:ℝ)-(Q.lower i:ℝ)) =
        (x i-(Q.lower i:ℝ))*((k:ℝ)+1) := by dsimp [a]; field_simp
    simp only [Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_sub,Rat.cast_natCast,Rat.cast_one]
    apply abs_le.mpr
    constructor
    · have hcenter : ((Q.upper i:ℝ)-(Q.lower i:ℝ))*(⌊a⌋₊:ℝ)/((k:ℝ)+1) ≤ x i-(Q.lower i:ℝ) := by
        apply (div_le_iff₀ hk).mpr
        nlinarith [mul_le_mul_of_nonneg_right hfloor hd.le]
      have hr : 0 ≤ ((Q.upper i:ℝ)-(Q.lower i:ℝ))/((k:ℝ)+1) := div_nonneg hd.le hk.le
      linarith
    · apply (le_div_iff₀ hk).mpr
      nlinarith [mul_lt_mul_of_pos_right hceil hd,
        (div_mul_cancel₀ (((Q.upper i:ℝ)-(Q.lower i:ℝ))*(⌊a⌋₊:ℝ)) hk.ne')]
  choose j hj using hlocal
  exact ⟨j,fun i => ⟨Q.cell_nonneg k j i,hj i⟩⟩

theorem radius_tendsto {κ : ℕ → ℕ} (hκ : Tendsto κ atTop atTop)
    (j : ∀ k, Fin n → Fin (κ k+2)) (i) :
    Tendsto (fun k => ((Q.cell (κ k) (j k) i).radius:ℝ)) atTop (𝓝 0) := by
  have hden : Tendsto (fun k => (κ k:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.comp hκ)
  simpa only [cell,Rat.cast_div,Rat.cast_sub,Rat.cast_add,Rat.cast_natCast,Rat.cast_one,
    Rat.cast_mul,Rat.cast_inv,div_eq_mul_inv,mul_zero,Function.comp_def] using
      (tendsto_inv_atTop_zero.comp hden).const_mul ((Q.upper i:ℝ)-(Q.lower i:ℝ))

end VelocityDetection.Effective.RationalBox
end

end OAI
