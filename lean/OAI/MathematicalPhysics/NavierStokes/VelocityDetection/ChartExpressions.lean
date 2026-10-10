import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.RationalEvaluation
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.BurstTotal
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.ExpressionAlgebra

namespace OAI

noncomputable section
namespace VelocityDetection.Effective.ChartRecipe
open Set Function ArrayRecipe
open scoped BigOperators Topology
open VelocityDetection.Effective.Expr
variable {N b : ℕ} (hN : 0 < N) (hb : 0 < b)
  (table : Fin N → Fin b → Option (Stacks.Rule (Fin N) b)) (m : ℕ)

@[simp] theorem cast_scale (P : ℕ) :
    (scale N b m P : ℝ) = ChartRouting.scale (HistoryRouting.data hN hb table m) P := by
  simp [scale,ChartRouting.scale,HistoryRouting.data,Expanding.count,K,D,HistoryRouting.K,HistoryRouting.D]

def radius (N b m P : ℕ) : ℚ := scale N b m P/16

@[simp] theorem cast_radius (P : ℕ) :
    (radius N b m P : ℝ) = ChartRouting.radius (HistoryRouting.data hN hb table m) P := by
  simp [radius,cast_scale hN hb table,ChartRouting.radius]

def targetHeight (P n : ℕ) (c : Instruction hb table m n) : ℚ :=
  if ArrayRecipe.sign hb table (History.target hb table c) = 1 then -(7/16) else -scale N b m P

@[simp] theorem cast_targetHeight (P n : ℕ) (c : Instruction hb table m n) :
    (targetHeight hb table m P n c : ℝ) =
      ChartRouting.targetHeight (HistoryRouting.data hN hb table m) P n c := by
  have hh : (ArrayRecipe.sign hb table (History.target hb table c):ℚ) = 1 ↔
      HistoryRouting.sign hb table (History.target hb table c) = 1 := by
    rw [← ArrayRecipe.eval_sign]
    simpa only [Rat.cast_one] using (Rat.cast_inj (α := ℝ)
      (p := ArrayRecipe.sign hb table (History.target hb table c)) (q := 1)).symm
  unfold targetHeight ChartRouting.targetHeight
  change ((if ArrayRecipe.sign hb table (History.target hb table c) = 1 then -(7/16) else
    -scale N b m P : ℚ) : ℝ) =
    if HistoryRouting.sign hb table (History.target hb table c) = 1 then -(7/16) else
      -ChartRouting.scale (HistoryRouting.data hN hb table m) P
  by_cases hs : HistoryRouting.sign hb table (History.target hb table c) = 1
  · simp [hh.mpr hs,hs]
  · simp [mt hh.mp hs,hs,cast_scale hN hb table]

def path (P n : ℕ) (c : Instruction hb table m n) : Fin 2 → Code :=
  letI := neZeroFive
  fun i =>
    .rat (![1/4,1/2] i) + Recipe.center (.rat n) 1 (.rat (scale N b m P)) (.rat (scale N b m P))
      (.rat (targetHeight hb table m P n c/scale N b m P))
      (History.sourceAddress hb table c) (History.targetAddress hb table c) (.var 1) i

@[simp] theorem eval_path (P n : ℕ) (c : Instruction hb table m n) (x : Fin 5 → ℝ) (i) :
    (path hb table m P n c i).eval x = ChartRouting.path (HistoryRouting.data hN hb table m) P n c (x 1) i := by
  simp only [path,eval_add,eval_rat,Recipe.eval_center,eval_lit1,eval_var,Rat.cast_natCast,Rat.cast_div,
    cast_scale hN hb table,cast_targetHeight hN hb table,ChartRouting.path,Pi.add_apply,HistoryRouting.data]
  congr 1
  fin_cases i <;> norm_num [ChartRouting.origin]

theorem valid_path (P n : ℕ) (c : Instruction hb table m n) (x : Fin 5 → ℝ) (i) :
    (path hb table m P n c i).Valid x := by
  refine ⟨trivial,?_⟩
  apply Recipe.valid_center <;> simp

theorem eval_velocity (P n : ℕ) (c : Instruction hb table m n) (x : Fin 5 → ℝ) (i) :
    ((path hb table m P n c i).diff 1).eval x =
      deriv (ChartRouting.path (HistoryRouting.data hN hb table m) P n c) (x 1) i := by
  rw [Expr.eval_diff_curve _ (valid_path hb table m P n c x i) 1
    (fun s => ChartRouting.path (HistoryRouting.data hN hb table m) P n c s i) (by
      intro s; simp [eval_path hN])]
  rw [deriv_pi]
  intro j
  exact (differentiable_pi.mp ((ChartRouting.contDiff_path _ _ _ _).differentiable (by norm_num)) j).differentiableAt

def gate (P n : ℕ) (c : Instruction hb table m n) : Fin 2 → Code :=
  letI := neZeroFive
  Recipe.gate (.rat (radius N b m P)) (path hb table m P n c)
    (fun i => (path hb table m P n c i).diff 1) ![.var 2,.var 3]

theorem eval_gate (P n : ℕ) (c : Instruction hb table m n) (x : Fin 5 → ℝ) (i) :
    (gate hb table m P n c i).eval x = TranslationGates.field
      (ChartRouting.radius (HistoryRouting.data hN hb table m) P)
      (ChartRouting.path (HistoryRouting.data hN hb table m) P n c (x 1))
      (deriv (ChartRouting.path (HistoryRouting.data hN hb table m) P n c) (x 1)) ![x 2,x 3] i := by
  simp only [gate,Recipe.eval_gate,eval_rat,cast_radius hN hb table,eval_path hN,eval_velocity hN]
  congr 1; funext j; fin_cases j <;> rfl

include hN hb table in

theorem valid_gate (P n : ℕ) (c : Instruction hb table m n) (x : Fin 5 → ℝ) (i) :
    (gate hb table m P n c i).Valid x := by
  apply Recipe.valid_gate
  · trivial
  · exact valid_path hb table m P n c x
  · exact fun j => Expr.valid_diff _ (valid_path hb table m P n c x j) 1
  · intro j; fin_cases j <;> trivial
  · simpa only [eval_rat,cast_radius hN hb table] using (ChartRouting.radius_pos (HistoryRouting.data hN hb table m) P).ne'

def stage (P n : ℕ) (i : Fin 2) : Code :=
  activeSum hb table (fun c : Instruction hb table m n => gate hb table m P n c i)

theorem eval_stage (P n : ℕ) (x : Fin 5 → ℝ) (i) :
    (stage hb table m P n i).eval x = ChartRouting.stage (HistoryRouting.data hN hb table m) P n (x 1) ![x 2,x 3] i := by
  simp only [stage,eval_activeSum,eval_gate hN,ChartRouting.stage,Finset.sum_apply]
  rfl

include hN hb table in

theorem valid_stage (P n : ℕ) (x : Fin 5 → ℝ) (i) :
    (stage hb table m P n i).Valid x := valid_activeSum _ _ _ (fun c => valid_gate hN hb table m P n c x i)

def prefixCode (P : ℕ) (i : Fin 2) : Code := sumFin P (fun n => stage hb table m P n i)

theorem eval_prefix (P : ℕ) (x : Fin 5 → ℝ) (i) :
    (prefixCode hb table m P i).eval x = ChartRouting.finiteField (HistoryRouting.data hN hb table m) P (x 1) ![x 2,x 3] i := by
  simp only [prefixCode,eval_sumFin,eval_stage hN,ChartRouting.finiteField,Finset.sum_apply]
  exact Fin.sum_univ_eq_sum_range (fun n => ChartRouting.stage (HistoryRouting.data hN hb table m) P n (x 1) ![x 2,x 3] i) P

include hN hb table in

theorem valid_prefix (P : ℕ) (x : Fin 5 → ℝ) (i) :
    (prefixCode hb table m P i).Valid x := valid_sumFin _ _ (fun _ => valid_stage hN hb table m P _ x i)

def duration (N b m B k : ℕ) : Code :=
  letI := neZeroFive
  .rat ((1/16)*(1/2:ℚ)^k) /
    (3*(1+.var 0*.rat (2*(B:ℚ)/(radius N b m (k+1))^2)))

@[simp] theorem eval_duration (k : ℕ) (x : Fin 5 → ℝ) :
    (duration N b m SmoothBump.bound k).eval x = BurstSchedule.duration (HistoryRouting.data hN hb table m) (x 0) k := by
  simp [duration,BurstSchedule.duration,BurstSchedule.error,BurstSchedule.lapBound,cast_radius hN hb table]

include hN hb table in

theorem valid_duration (k : ℕ) {x : Fin 5 → ℝ} (hx : 0 ≤ x 0) :
    (duration N b m SmoothBump.bound k).Valid x := by
  have hh := BurstSchedule.lapBound_pos (HistoryRouting.data hN hb table m) k
  dsimp only [BurstSchedule.lapBound] at hh
  simp only [duration,valid_div,valid_mul,valid_add,valid_rat,valid_lit1,valid_lit3,valid_var,
    eval_mul,eval_add,eval_rat,eval_var,eval_lit1,eval_lit3,Rat.cast_div,Rat.cast_mul,Rat.cast_pow,
    Rat.cast_natCast,Rat.cast_ofNat,cast_radius hN hb table,true_and]
  positivity

def localTime (N b m B k : ℕ) : Code :=
  letI := neZeroFive
  (.var 1-.rat (k+1))/duration N b m B k

def weight (N b m B k : ℕ) : Code :=
  Recipe.step (8*localTime N b m B k)-Recipe.step (8*localTime N b m B k-.rat 7)

def clock (N b m B k : ℕ) : Code := .rat (k+1)*
  (Recipe.step (8*localTime N b m B k-1)-Recipe.step (8*localTime N b m B k-.rat 5))

@[simp] theorem eval_localTime (k : ℕ) (x : Fin 5 → ℝ) :
    (localTime N b m SmoothBump.bound k).eval x = BurstSchedule.localTime (HistoryRouting.data hN hb table m) (x 0) k (x 1) := by
  simp [localTime,BurstSchedule.localTime,eval_duration hN hb table]

@[simp] theorem eval_weight (k : ℕ) (x : Fin 5 → ℝ) :
    (weight N b m SmoothBump.bound k).eval x = BurstSchedule.weight (HistoryRouting.data hN hb table m) (x 0) k (x 1) := by
  simp [weight,BurstSchedule.weight,BurstSchedule.amplitude,eval_localTime hN hb table]

@[simp] theorem eval_clock (k : ℕ) (x : Fin 5 → ℝ) :
    (clock N b m SmoothBump.bound k).eval x = BurstSchedule.clock (HistoryRouting.data hN hb table m) (x 0) k (x 1) := by
  simp [clock,BurstSchedule.clock,BurstSchedule.phase,eval_localTime hN hb table]

include hN hb table in

theorem valid_localTime (k : ℕ) {x : Fin 5 → ℝ} (hx : 0 ≤ x 0) :
    (localTime N b m SmoothBump.bound k).Valid x :=
  ⟨⟨trivial,trivial⟩,valid_duration hN hb table m k hx,by
    simpa [eval_duration hN hb table] using (BurstSchedule.duration_pos (HistoryRouting.data hN hb table m) (x 0) hx k).ne'⟩

include hN hb table in

theorem valid_weight (k : ℕ) {x : Fin 5 → ℝ} (hx : 0 ≤ x 0) :
    (weight N b m SmoothBump.bound k).Valid x := by
  have ht := valid_localTime hN hb table m k hx
  exact ⟨Recipe.valid_step _ ⟨trivial,ht⟩,Recipe.valid_step _ ⟨⟨trivial,ht⟩,trivial⟩⟩

include hN hb table in

theorem valid_clock (k : ℕ) {x : Fin 5 → ℝ} (hx : 0 ≤ x 0) :
    (clock N b m SmoothBump.bound k).Valid x := by
  have ht := valid_localTime hN hb table m k hx
  exact ⟨trivial,Recipe.valid_step _ ⟨⟨trivial,ht⟩,trivial⟩,Recipe.valid_step _ ⟨⟨trivial,ht⟩,trivial⟩⟩

theorem eval_weightD (k : ℕ) {x : Fin 5 → ℝ} (hx : 0 ≤ x 0) :
    ((weight N b m SmoothBump.bound k).diff 1).eval x =
      deriv (BurstSchedule.weight (HistoryRouting.data hN hb table m) (x 0) k) (x 1) := by
  apply Expr.eval_diff_curve _ (valid_weight hN hb table m k hx) 1
  intro s; simp [eval_weight hN hb table]

theorem eval_clockD (k : ℕ) {x : Fin 5 → ℝ} (hx : 0 ≤ x 0) :
    ((clock N b m SmoothBump.bound k).diff 1).eval x =
      deriv (BurstSchedule.clock (HistoryRouting.data hN hb table m) (x 0) k) (x 1) := by
  apply Expr.eval_diff_curve _ (valid_clock hN hb table m k hx) 1
  intro s; simp [eval_clock hN hb table]

def rawField (B k : ℕ) (i : Fin 2) : Code :=
  letI := neZeroFive
  (clock N b m B k).diff 1 * (prefixCode hb table m (k+1) i).subst
    ![.var 0,clock N b m B k,.var 2,.var 3,.var 4]

theorem eval_rawField (k : ℕ) {x : Fin 5 → ℝ} (hx : 0 ≤ x 0) (i) :
    (rawField hb table m SmoothBump.bound k i).eval x =
      BurstBlock.rawField (HistoryRouting.data hN hb table m) (x 0) k (x 1) ![x 2,x 3] i := by
  simp [rawField,eval_clockD hN hb table m _ hx,eval_prefix hN,eval_clock hN hb table,
    BurstBlock.rawField,smul_eq_mul]

include hN hb table in

theorem valid_rawField (k : ℕ) {x : Fin 5 → ℝ} (hx : 0 ≤ x 0) (i) :
    (rawField hb table m SmoothBump.bound k i).Valid x := by
  refine ⟨Expr.valid_diff _ (valid_clock hN hb table m k hx) 1,?_⟩
  apply Expr.valid_subst
  · intro j; fin_cases j <;> try {exact True.intro}
    exact valid_clock hN hb table m k hx
  · exact valid_prefix hN hb table m _ _ _

def initial (N b m P q : ℕ) : Fin 2 → Code :=
  ![.rat (1/4+scale N b m P*q),.rat (1/2-scale N b m P)]

@[simp] theorem eval_initial (P q : ℕ) (x : Fin 5 → ℝ) (i) :
    (initial N b m P q i).eval x = BurstBlock.initial (HistoryRouting.data hN hb table m) P q i := by
  fin_cases i <;> simp [initial,BurstBlock.initial,ChartRouting.origin,cast_scale hN hb table,sub_eq_add_neg]

def rawSource (B q k : ℕ) : Code :=
  letI := neZeroFive
  (weight N b m B k).diff 1 *
    Recipe.packet (.rat (radius N b m (k+1)))
      (fun i => (![.var 2,.var 3] i)-initial N b m (k+1) q i)

theorem eval_rawSource (q k : ℕ) {x : Fin 5 → ℝ} (hx : 0 ≤ x 0) :
    (rawSource (N:=N) (b:=b) m SmoothBump.bound q k).eval x =
      BurstBlock.rawSource (HistoryRouting.data hN hb table m) (x 0) q k (x 1) ![x 2,x 3] := by
  simp only [rawSource,eval_mul,eval_weightD hN hb table m _ hx,Recipe.eval_packet,
    eval_rat,cast_radius hN hb table,eval_sub,eval_initial hN hb table,BurstBlock.rawSource]
  congr 2; funext j; fin_cases j <;> rfl

include hN hb table in

theorem valid_rawSource (q k : ℕ) {x : Fin 5 → ℝ} (hx : 0 ≤ x 0) :
    (rawSource (N:=N) (b:=b) m SmoothBump.bound q k).Valid x := by
  refine ⟨Expr.valid_diff _ (valid_weight hN hb table m k hx) 1,?_⟩
  apply Recipe.valid_packet
  · trivial
  · intro j; fin_cases j <;> exact ⟨trivial,trivial⟩
  · simpa only [eval_rat,cast_radius hN hb table] using (ChartRouting.radius_pos (HistoryRouting.data hN hb table m) (k+1)).ne'

end VelocityDetection.Effective.ChartRecipe
end

noncomputable section
namespace VelocityDetection.Effective
open Set Function
open scoped Topology BigOperators
open VelocityDetection.Effective.Expr ArrayRecipe

def latticeIndex (R : ℕ) (j : Fin (2*R+1) × Fin (2*R+1)) : Fin 2 → ℤ :=
  ![(j.1:ℕ)-(R:ℤ),(j.2:ℕ)-(R:ℤ)]

theorem latticeIndex_mem (R : ℕ) (j : Fin (2*R+1) × Fin (2*R+1)) :
    latticeIndex R j ∈ Periodization.box R := by
  have h1 := j.1.isLt
  have h2 := j.2.isLt
  apply Finset.mem_Icc.mpr
  constructor <;> intro i <;> fin_cases i <;> dsimp [latticeIndex] <;> omega

theorem latticeIndex_injective (R : ℕ) : Function.Injective (latticeIndex R) := by
  intro a b h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  dsimp [latticeIndex] at h0 h1
  apply Prod.ext <;> apply Fin.ext <;> omega

theorem latticeIndex_surjective (R : ℕ) (k : Fin 2 → ℤ)
    (hk : k ∈ Periodization.box R) : ∃ j, latticeIndex R j = k := by
  obtain ⟨hl,hu⟩ := Finset.mem_Icc.mp hk
  have hn (i) : 0 ≤ k i+(R:ℤ) := by have := hl i; dsimp at this; omega
  have hu' (i) : (k i+(R:ℤ)).toNat < 2*R+1 := by
    have := hu i; dsimp at this; omega
  refine ⟨(⟨(k 0+R).toNat,hu' 0⟩,⟨(k 1+R).toNat,hu' 1⟩),?_⟩
  funext i
  fin_cases i <;> dsimp [latticeIndex] <;> rw [Int.toNat_of_nonneg (hn _)] <;> omega

theorem sum_lattice {E : Type*} [AddCommMonoid E] (R : ℕ) (g : (Fin 2 → ℤ) → E) :
    (∑ i : Fin (2*R+1), ∑ j : Fin (2*R+1), g (latticeIndex R (i,j))) =
      ∑ k ∈ Periodization.box R, g k := by
  classical
  trans ∑ j : Fin (2*R+1) × Fin (2*R+1), g (latticeIndex R j)
  · exact (Fintype.sum_prod_type (fun j => g (latticeIndex R j))).symm
  apply Finset.sum_bij (fun j _ => latticeIndex R j)
  · exact fun j _ => latticeIndex_mem R j
  · exact fun _ _ _ _ h => latticeIndex_injective R h
  · intro k hk
    obtain ⟨j,hj⟩ := latticeIndex_surjective R k hk
    exact ⟨j,Finset.mem_univ _,hj⟩
  · intro _ _; rfl

def periodize (R : ℕ) (e : Code) : Code :=
  letI := neZeroFive
  sumFin (2*R+1) (fun i => sumFin (2*R+1) (fun j =>
    e.subst ![.var 0,.var 1,.var 2-.rat ((i:ℚ)-R),.var 3-.rat ((j:ℚ)-R),.var 4]))

def shifted (x : Fin 5 → ℝ) (k : Fin 2 → ℤ) : Fin 5 → ℝ :=
  ![x 0,x 1,x 2-k 0,x 3-k 1,x 4]

theorem eval_periodize (R : ℕ) (e : Code) (x : Fin 5 → ℝ) :
    (periodize R e).eval x = ∑ k ∈ Periodization.box R, e.eval (shifted x k) := by
  simp only [periodize,eval_sumFin,eval_subst]
  rw [← sum_lattice]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  funext r; fin_cases r <;> simp [shifted,latticeIndex]

theorem valid_periodize (R : ℕ) (e : Code) (x : Fin 5 → ℝ)
    (he : ∀ k : Fin 2 → ℤ, e.Valid (shifted x k)) : (periodize R e).Valid x := by
  apply valid_sumFin
  intro i
  apply valid_sumFin
  intro j
  apply valid_subst
  · intro r; fin_cases r <;> simp
  · convert he (latticeIndex R (i,j)) using 1
    funext r; fin_cases r <;> simp [shifted,latticeIndex]

end VelocityDetection.Effective
end

noncomputable section
namespace VelocityDetection.Effective.ChartRecipe
open Set Function
open scoped Topology BigOperators
open VelocityDetection.Effective.Expr ArrayRecipe
variable {N b : ℕ} (hN : 0 < N) (hb : 0 < b)
  (table : Fin N → Fin b → Option (Stacks.Rule (Fin N) b)) (m : ℕ)

def fieldBlock (B R k : ℕ) (i : Fin 2) : Code := periodize R (rawField hb table m B k i)

def sourceBlock (N b m B q R k : ℕ) : Code := periodize R (rawSource (N:=N) (b:=b) m B q k)

private theorem chartBound {X : Coord 2} (hX : X ∈ ChartRouting.chartSet) (i) : |X i| ≤ 1 := by
  obtain ⟨h0,h1⟩ := ChartRouting.chartSet_interior hX i
  rw [abs_of_pos h0]; exact h1.le

theorem eval_fieldBlock (R k : ℕ) {x : Fin 5 → ℝ} (hx : 0 ≤ x 0)
    (hR : ‖![x 2,x 3]‖+1 < R) (i : Fin 2) :
    (fieldBlock hb table m SmoothBump.bound R k i).eval x =
      BurstBlock.field (HistoryRouting.data hN hb table m) (x 0) k (x 1) ![x 2,x 3] i := by
  have hf : ∀ t X, ChartRouting.finiteField (HistoryRouting.data hN hb table m) (k+1) t X ≠ 0 →
      ∀ j, |X j| ≤ 1 := fun t X h => chartBound (ChartRouting.prefix_support _ _ t X h)
  have he := Periodization.extend_finite hf hR
    (BurstSchedule.clock (HistoryRouting.data hN hb table m) (x 0) k (x 1))
  simp only [fieldBlock,eval_periodize]
  simp only [BurstBlock.field,ChartRouting.periodicPrefix,he,Finset.smul_sum,Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro l _
  rw [eval_rawField hN hb table m k (by simpa [shifted] using hx)]
  rfl

theorem eval_sourceBlock (q R k : ℕ) (c : Instruction hb table m 0)
    (hc : History.sourceAddress hb table c = q) {x : Fin 5 → ℝ} (hx : 0 ≤ x 0)
    (hR : ‖![x 2,x 3]‖+1 < R) :
    (sourceBlock N b m SmoothBump.bound q R k).eval x =
      BurstBlock.source (HistoryRouting.data hN hb table m) (x 0) q k (x 1) ![x 2,x 3] := by
  have hf : ∀ t X, BurstBlock.rawSource (HistoryRouting.data hN hb table m) (x 0) q k t X ≠ 0 →
      ∀ j, |X j| ≤ 1 := fun t X h => chartBound (BurstBlock.rawSource_support _ _ q k c hc t X h)
  rw [sourceBlock,eval_periodize,BurstBlock.source,Periodization.extend_finite hf hR]
  apply Finset.sum_congr rfl
  intro l _
  rw [eval_rawSource hN hb table m q k (by simpa [shifted] using hx)]
  congr 1
  funext r; fin_cases r <;> rfl

include hN in

theorem valid_fieldBlock (R k : ℕ) {x : Fin 5 → ℝ} (hx : 0 ≤ x 0) (i) :
    (fieldBlock hb table m SmoothBump.bound R k i).Valid x := by
  apply valid_periodize
  intro l
  exact valid_rawField hN hb table m k (by simpa [shifted] using hx) i

include hN hb table in

theorem valid_sourceBlock (q R k : ℕ) {x : Fin 5 → ℝ} (hx : 0 ≤ x 0) :
    (sourceBlock N b m SmoothBump.bound q R k).Valid x := by
  apply valid_periodize
  intro l
  exact valid_rawSource hN hb table m q k (by simpa [shifted] using hx)

def field (B R L : ℕ) (i : Fin 2) : Code := sumFin L (fun k => fieldBlock hb table m B R k i)

def source (N b m B q R L : ℕ) : Code := sumFin L (fun k => sourceBlock N b m B q R k)

theorem eval_field (R L : ℕ) {x : Fin 5 → ℝ} (hx : 0 ≤ x 0) (ht : x 1 < L)
    (hR : ‖![x 2,x 3]‖+1 < R) (i : Fin 2) :
    (field hb table m SmoothBump.bound R L i).eval x =
      BurstTotal.field (HistoryRouting.data hN hb table m) (x 0) (x 1) ![x 2,x 3] i := by
  have he := congrFun (TimeBlocks.eq_finite
    (BurstTotal.fieldFamily (HistoryRouting.data hN hb table m) (x 0) hx)
    (by linarith : x 1 ≤ (L:ℝ)+1)) ![x 2,x 3]
  change BurstTotal.field _ _ _ _ = _ at he
  rw [he]
  simp only [field,eval_sumFin,eval_fieldBlock hN hb table m _ _ hx hR,TimeBlocks.finiteSum,Finset.sum_apply]
  exact Fin.sum_univ_eq_sum_range (fun k => BurstBlock.field (HistoryRouting.data hN hb table m)
    (x 0) k (x 1) ![x 2,x 3] i) L

theorem eval_source (q R L : ℕ) (c : Instruction hb table m 0)
    (hc : History.sourceAddress hb table c = q) {x : Fin 5 → ℝ} (hx : 0 ≤ x 0) (ht : x 1 < L)
    (hR : ‖![x 2,x 3]‖+1 < R) :
    (source N b m SmoothBump.bound q R L).eval x =
      BurstTotal.source (HistoryRouting.data hN hb table m) (x 0) q (x 1) ![x 2,x 3] := by
  have he := congrFun (TimeBlocks.eq_finite
    (BurstTotal.sourceFamily (HistoryRouting.data hN hb table m) (x 0) hx q)
    (by linarith : x 1 ≤ (L:ℝ)+1)) ![x 2,x 3]
  change BurstTotal.source _ _ _ _ _ = _ at he
  rw [he]
  simp only [source,eval_sumFin,eval_sourceBlock hN hb table m q _ _ c hc hx hR,TimeBlocks.finiteSum]
  exact Fin.sum_univ_eq_sum_range (fun k => BurstBlock.source (HistoryRouting.data hN hb table m)
    (x 0) q k (x 1) ![x 2,x 3]) L

include hN in

theorem valid_field (R L : ℕ) {x : Fin 5 → ℝ} (hx : 0 ≤ x 0) (i) :
    (field hb table m SmoothBump.bound R L i).Valid x :=
  valid_sumFin _ _ (fun _ => valid_fieldBlock hN hb table m _ _ hx i)

include hN hb table in

theorem valid_source (q R L : ℕ) {x : Fin 5 → ℝ} (hx : 0 ≤ x 0) :
    (source N b m SmoothBump.bound q R L).Valid x :=
  valid_sumFin _ _ (fun _ => valid_sourceBlock hN hb table m _ _ _ hx)

end VelocityDetection.Effective.ChartRecipe
end

noncomputable section
namespace VelocityDetection.Effective
open Set Filter Function
open scoped Topology BigOperators ContDiff
open VelocityDetection.Effective.Expr ArrayRecipe JointCalculus

def axis (j : Fin 3) : Fin 5 := ![1,2,3] j

noncomputable def direction (j : Fin 3) : ℝ × Coord 2 :=
  ![(1,0),(0,Pi.single 0 1),(0,Pi.single 1 1)] j

noncomputable def point (x : Fin 5 → ℝ) : ℝ × Coord 2 := (x 1,![x 2,x 3])

noncomputable def pull (f : ℝ → (ℝ × Coord 2) → ℝ) (x : Fin 5 → ℝ) : ℝ := f (x 0) (point x)

@[simp] theorem axis_ne_zero (j : Fin 3) : axis j ≠ 0 := by fin_cases j <;> decide

@[simp] theorem update_axis_zero (x : Fin 5 → ℝ) (j : Fin 3) (s : ℝ) :
    update x (axis j) s 0 = x 0 := by rw [update_of_ne (Ne.symm (axis_ne_zero j))]

theorem point_hasDerivAt (x : Fin 5 → ℝ) (j : Fin 3) :
    HasDerivAt (fun s => point (update x (axis j) s)) (direction j) (x (axis j)) := by
  fin_cases j
  · simpa [point,axis,direction] using
      ((hasDerivAt_id (x 1)).prodMk (hasDerivAt_const (x 1) ![x 2,x 3]))
  · convert (hasDerivAt_const (x 2) (x 1)).prodMk (hasDerivAt_update ![x 2,x 3] 0 (x 2)) using 1
    funext s
    apply Prod.ext
    · simp [point,axis]
    · ext i; fin_cases i <;> simp [point,axis]
    · rfl
    · rfl
  · convert (hasDerivAt_const (x 3) (x 1)).prodMk (hasDerivAt_update ![x 2,x 3] 1 (x 3)) using 1
    funext s
    apply Prod.ext
    · simp [point,axis]
    · ext i; fin_cases i <;> simp [point,axis]
    · rfl
    · rfl

theorem coordinateD_pull (f : ℝ → (ℝ × Coord 2) → ℝ) (x : Fin 5 → ℝ)
    (hf : ContDiff ℝ ∞ (f (x 0))) (j : Fin 3) :
    coordinateD (axis j) (pull f) x = dAlong (direction j) (f (x 0)) (point x) := by
  have hd := (hf.differentiable (by simp) (point (update x (axis j) (x (axis j))))).hasFDerivAt.comp_hasDerivAt (x (axis j))
    (point_hasDerivAt x j)
  simpa only [coordinateD,pull,update_axis_zero,comp_def,dAlong,update_eq_self] using hd.deriv

theorem coordinateDD_pull (f : ℝ → (ℝ × Coord 2) → ℝ) (x : Fin 5 → ℝ)
    (hx : 0 < x 0) (hf : ∀ ν > 0, ContDiff ℝ ∞ (f ν)) (j : Fin 3) :
    coordinateD (axis j) (coordinateD (axis j) (pull f)) x =
      dAlong (direction j) (dAlong (direction j) (f (x 0))) (point x) := by
  have hh : coordinateD (axis j) (pull f) =ᶠ[𝓝 x]
      pull (fun ν => dAlong (direction j) (f ν)) := by
    have hp : ∀ᶠ y : Fin 5 → ℝ in 𝓝 x, 0 < y 0 :=
      (isOpen_lt continuous_const (continuous_apply 0)).mem_nhds hx
    exact hp.mono (fun y hy => coordinateD_pull f y (hf (y 0) hy) j)
  rw [coordinateD_congr hh]
  exact coordinateD_pull _ x (contDiff_dAlong _ (hf (x 0) hx)) j

end VelocityDetection.Effective
end

end OAI
