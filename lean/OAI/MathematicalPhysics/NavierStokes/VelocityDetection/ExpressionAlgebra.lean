import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.HistoryRouting
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.SmoothExpressions
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.SmoothBump

namespace OAI

noncomputable section
namespace VelocityDetection.Effective.Expr
open Set Function Filter
open scoped Topology BigOperators
variable {n m : ℕ}

instance : Add (Expr n) := ⟨Expr.add⟩

instance : Neg (Expr n) := ⟨Expr.neg⟩

instance : Sub (Expr n) := ⟨fun a b => .add a (.neg b)⟩

instance : Mul (Expr n) := ⟨Expr.mul⟩

instance : Inv (Expr n) := ⟨Expr.inv⟩

instance : Div (Expr n) := ⟨fun a b => .mul a (.inv b)⟩

instance (k : ℕ) : OfNat (Expr n) k := ⟨.rat k⟩

@[simp] theorem eval_add (a b : Expr n) (x) : (a+b).eval x = a.eval x+b.eval x := rfl

@[simp] theorem eval_neg (a : Expr n) (x) : (-a).eval x = -a.eval x := rfl

@[simp] theorem eval_sub (a b : Expr n) (x) : (a-b).eval x = a.eval x-b.eval x := rfl

@[simp] theorem eval_mul (a b : Expr n) (x) : (a*b).eval x = a.eval x*b.eval x := rfl

@[simp] theorem eval_inv (a : Expr n) (x) : (a⁻¹).eval x = (a.eval x)⁻¹ := rfl

@[simp] theorem eval_div (a b : Expr n) (x) : (a/b).eval x = a.eval x/b.eval x := rfl

@[simp] theorem eval_rat (q : ℚ) (x : Fin n → ℝ) : (rat q).eval x = q := rfl

@[simp] theorem eval_var (i : Fin n) (x) : (var i).eval x = x i := rfl

@[simp] theorem eval_nat (k : ℕ) (x : Fin n → ℝ) : (OfNat.ofNat k : Expr n).eval x = k := by
  change ((k:ℚ):ℝ) = k
  simp

@[simp] theorem valid_add (a b : Expr n) (x) : (a+b).Valid x ↔ a.Valid x ∧ b.Valid x := Iff.rfl

@[simp] theorem valid_neg (a : Expr n) (x) : (-a).Valid x ↔ a.Valid x := Iff.rfl

@[simp] theorem valid_sub (a b : Expr n) (x) : (a-b).Valid x ↔ a.Valid x ∧ b.Valid x := Iff.rfl

@[simp] theorem valid_mul (a b : Expr n) (x) : (a*b).Valid x ↔ a.Valid x ∧ b.Valid x := Iff.rfl

@[simp] theorem valid_inv (a : Expr n) (x) : a⁻¹.Valid x ↔ a.Valid x ∧ a.eval x ≠ 0 := Iff.rfl

@[simp] theorem valid_div (a b : Expr n) (x) : (a/b).Valid x ↔ a.Valid x ∧ b.Valid x ∧ b.eval x ≠ 0 := Iff.rfl

@[simp] theorem valid_rat (q : ℚ) (x : Fin n → ℝ) : (rat q).Valid x := trivial

@[simp] theorem valid_var (i : Fin n) (x) : (var i).Valid x := trivial

@[simp] theorem valid_nat (k : ℕ) (x : Fin n → ℝ) : (OfNat.ofNat k : Expr n).Valid x := trivial

@[simp] theorem eval_lit0 (x : Fin n → ℝ) : (0 : Expr n).eval x = 0 := by change ((0:ℚ):ℝ) = 0; norm_num

@[simp] theorem valid_lit0 (x : Fin n → ℝ) : (0 : Expr n).Valid x := trivial

@[simp] theorem eval_lit1 (x : Fin n → ℝ) : (1 : Expr n).eval x = 1 := by change ((1:ℚ):ℝ) = 1; norm_num

@[simp] theorem valid_lit1 (x : Fin n → ℝ) : (1 : Expr n).Valid x := trivial

@[simp] theorem eval_lit2 (x : Fin n → ℝ) : (2 : Expr n).eval x = 2 := rfl

@[simp] theorem valid_lit2 (x : Fin n → ℝ) : (2 : Expr n).Valid x := trivial

@[simp] theorem eval_lit3 (x : Fin n → ℝ) : (3 : Expr n).eval x = 3 := rfl

@[simp] theorem valid_lit3 (x : Fin n → ℝ) : (3 : Expr n).Valid x := trivial

@[simp] theorem eval_lit8 (x : Fin n → ℝ) : (8 : Expr n).eval x = 8 := rfl

@[simp] theorem valid_lit8 (x : Fin n → ℝ) : (8 : Expr n).Valid x := trivial

@[simp] theorem eval_lit16 (x : Fin n → ℝ) : (16 : Expr n).eval x = 16 := rfl

@[simp] theorem valid_lit16 (x : Fin n → ℝ) : (16 : Expr n).Valid x := trivial

@[simp] theorem eval_lit1024 (x : Fin n → ℝ) : (1024 : Expr n).eval x = 1024 := rfl

@[simp] theorem valid_lit1024 (x : Fin n → ℝ) : (1024 : Expr n).Valid x := trivial

@[simp] theorem eval_lit3000 (x : Fin n → ℝ) : (3000 : Expr n).eval x = 3000 := rfl

@[simp] theorem valid_lit3000 (x : Fin n → ℝ) : (3000 : Expr n).Valid x := trivial

def subst (v : Fin m → Expr n) : Expr m → Expr n :=
  Expr.rec (motive := fun _ => Expr n)
    Expr.rat v
    (fun _ _ a b => .add a b)
    (fun _ a => .neg a)
    (fun _ _ a b => .mul a b)
    (fun _ a => .inv a)
    (fun p _ a => .flat p a)

@[simp] theorem eval_subst (e : Expr m) (v : Fin m → Expr n) (x) :
    (e.subst v).eval x = e.eval (fun i => (v i).eval x) := by
  induction e <;> simp_all [subst,eval]

theorem valid_subst (e : Expr m) (v : Fin m → Expr n) {x}
    (hv : ∀ i, (v i).Valid x) (he : e.Valid (fun i => (v i).eval x)) :
    (e.subst v).Valid x := by
  induction e with
  | rat => trivial
  | var => exact hv _
  | add a b ha hb | mul a b ha hb => exact ⟨ha he.1,hb he.2⟩
  | neg a ha | flat p a ha => exact ha he
  | inv a ha =>
    refine ⟨ha he.1, ?_⟩
    change (a.subst v).eval x ≠ 0
    simpa only [eval_subst] using he.2

def sumList : List (Expr n) → Expr n
  | [] => 0
  | e::es => e + sumList es

@[simp] theorem eval_sumList (es : List (Expr n)) (x) :
    (sumList es).eval x = (es.map (fun e => e.eval x)).sum := by
  induction es with
  | nil => simp [sumList]
  | cons e es ih => simp [sumList,ih]

theorem valid_sumList (es : List (Expr n)) {x} (h : ∀ e ∈ es, e.Valid x) :
    (sumList es).Valid x := by
  induction es with
  | nil => trivial
  | cons e es ih => exact ⟨h _ (by simp),ih (fun _ he => h _ (by simp [he]))⟩

def sumFin (k : ℕ) (f : Fin k → Expr n) : Expr n := sumList (List.ofFn f)

@[simp] theorem eval_sumFin (k : ℕ) (f : Fin k → Expr n) (x) :
    (sumFin k f).eval x = ∑ i : Fin k, (f i).eval x := by
  simp [sumFin,List.map_ofFn,List.sum_ofFn]

theorem valid_sumFin (k : ℕ) (f : Fin k → Expr n) {x} (h : ∀ i, (f i).Valid x) :
    (sumFin k f).Valid x := by
  apply valid_sumList
  intro e he
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
  exact h i

def unaryD (e : Expr 1) (a : Expr n) : Expr n := (e.diff 0).subst (fun _ => a)

theorem eval_unaryD (e : Expr 1) (a : Expr n) {x}
    (h : e.Valid (fun _ => a.eval x)) :
    (e.unaryD a).eval x = deriv (fun s => e.eval (fun _ => s)) (a.eval x) := by
  rw [unaryD,eval_subst]
  symm
  convert (e.hasDerivAt_eval h 0).deriv using 1
  congr 1
  funext s
  congr 1
  funext i
  fin_cases i
  simp

theorem valid_unaryD (e : Expr 1) (a : Expr n) {x} (ha : a.Valid x)
    (he : e.Valid (fun _ => a.eval x)) : (e.unaryD a).Valid x :=
  (e.diff 0).valid_subst _ (fun _ => ha) (e.valid_diff he 0)

theorem eval_diff_curve (e : Expr n) {x} (h : e.Valid x) (i : Fin n)
    (f : ℝ → ℝ) (hf : ∀ s, e.eval (update x i s) = f s) :
    (e.diff i).eval x = deriv f (x i) := by
  rw [← (e.hasDerivAt_eval h i).deriv]
  congr 1
  funext s
  exact hf s

end VelocityDetection.Effective.Expr
end

noncomputable section
namespace VelocityDetection.Effective.Recipe
open Set Function Filter
open scoped Topology BigOperators
open _root_.OAI.VelocityDetection.Effective.Expr
variable {n : ℕ}

def glue (a : Expr n) : Expr n := .flat [(0,1)] a

@[simp] theorem eval_glue (a : Expr n) (x) : (glue a).eval x = expNegInvGlue (a.eval x) := by
  simp [glue,Expr.eval,Effective.flat,poly]

@[simp] theorem valid_glue (a : Expr n) (x) : (glue a).Valid x ↔ a.Valid x := Iff.rfl

def step (a : Expr n) : Expr n := glue a/(glue a+glue (1-a))

@[simp] theorem eval_step (a : Expr n) (x) :
    (step a).eval x = SmoothProfiles.step (a.eval x) := by
  simp [step,Real.smoothTransition,SmoothProfiles.step]

theorem valid_step (a : Expr n) {x} (ha : a.Valid x) : (step a).Valid x := by
  simp only [step,valid_div,valid_add,valid_glue,valid_sub,ha,true_and,
    eval_add,eval_glue,eval_sub,eval_lit1,valid_lit1]
  exact (Real.smoothTransition.pos_denom (a.eval x)).ne'

def pulse (a : Expr n) : Expr n := (step (.var 0 : Expr 1)).unaryD a

@[simp] theorem eval_pulse (a : Expr n) (x) :
    (pulse a).eval x = SmoothProfiles.pulse (a.eval x) := by
  rw [pulse,eval_unaryD _ _ (valid_step _ (valid_var _ _))]
  simp only [eval_step,eval_var,SmoothProfiles.pulse]

theorem valid_pulse (a : Expr n) {x} (ha : a.Valid x) : (pulse a).Valid x :=
  valid_unaryD _ _ ha (valid_step _ (valid_var _ _))

def window (a : Expr n) : Expr n := step (a+3)*step (3-a)

def windowD (a : Expr n) : Expr n := pulse (a+3)*step (3-a)-step (a+3)*pulse (3-a)

@[simp] theorem eval_window (a : Expr n) (x) :
    (window a).eval x = TranslationGates.window (a.eval x) := by
  simp [window,TranslationGates.window]

@[simp] theorem eval_windowD (a : Expr n) (x) :
    (windowD a).eval x = TranslationGates.windowD (a.eval x) := by
  simp [windowD,TranslationGates.windowD]

theorem valid_window (a : Expr n) {x} (ha : a.Valid x) : (window a).Valid x :=
  ⟨valid_step _ ⟨ha,trivial⟩,valid_step _ ⟨trivial,ha⟩⟩

theorem valid_windowD (a : Expr n) {x} (ha : a.Valid x) : (windowD a).Valid x :=
  ⟨⟨valid_pulse _ ⟨ha,trivial⟩,valid_step _ ⟨trivial,ha⟩⟩,
    ⟨valid_step _ ⟨ha,trivial⟩,valid_pulse _ ⟨trivial,ha⟩⟩⟩

def theta (a T : Expr n) (j : ℕ) (t : Expr n) : Expr n :=
  step (2*(3*(t-a)/T-.rat j)-.rat (1/2))

@[simp] theorem eval_theta (a T : Expr n) (j : ℕ) (t : Expr n) (x) :
    (theta a T j t).eval x = CenterPaths.theta (a.eval x) (T.eval x) j (t.eval x) := by
  simp [theta,CenterPaths.theta,CenterPaths.ramp]

theorem valid_theta (a T : Expr n) (j : ℕ) (t : Expr n) {x}
    (ha : a.Valid x) (hT : T.Valid x) (ht : t.Valid x) (h : T.eval x ≠ 0) :
    (theta a T j t).Valid x := by
  apply valid_step
  simp [ha,hT,ht,h]

def center (a T S S' σ : Expr n) (k l : ℕ) (t : Expr n) : Fin 2 → Expr n :=
  ![(1-theta a T 1 t)*S*.rat k+theta a T 1 t*S'*.rat l,
    -(1-theta a T 0 t)*S+(theta a T 0 t-theta a T 2 t)*(-(.rat k+2)*S)+
      theta a T 2 t*σ*S']

@[simp] theorem eval_center (a T S S' σ : Expr n) (k l : ℕ) (t : Expr n) (x) (i) :
    (center a T S S' σ k l t i).eval x =
      CenterPaths.center (a.eval x) (T.eval x) (S.eval x) (S'.eval x) (σ.eval x) k l (t.eval x) i := by
  fin_cases i <;> simp [center,CenterPaths.center,CenterPaths.privateRow]

theorem valid_center (a T S S' σ : Expr n) (k l : ℕ) (t : Expr n) {x}
    (ha : a.Valid x) (hT : T.Valid x) (hS : S.Valid x) (hS' : S'.Valid x)
    (hσ : σ.Valid x) (ht : t.Valid x) (h : T.eval x ≠ 0) (i) :
    (center a T S S' σ k l t i).Valid x := by
  have hh := fun j => valid_theta a T j t ha hT ht h
  fin_cases i <;> simp [center,hh,hS,hS',hσ]

def gate (R : Expr n) (c G X : Fin 2 → Expr n) : Fin 2 → Expr n :=
  letI := neZeroTwo
  ![window ((X 0-c 0)/R)*(windowD ((X 1-c 1)/R)/R)*
      (G 0*(X 1-c 1)-G 1*(X 0-c 0))+
      window ((X 0-c 0)/R)*window ((X 1-c 1)/R)*G 0,
    window ((X 0-c 0)/R)*window ((X 1-c 1)/R)*G 1-
      (windowD ((X 0-c 0)/R)/R*window ((X 1-c 1)/R))*
        (G 0*(X 1-c 1)-G 1*(X 0-c 0))]

@[simp] theorem eval_gate (R : Expr n) (c G X : Fin 2 → Expr n) (x) (i) :
    (gate R c G X i).eval x = TranslationGates.field (R.eval x)
      (fun j => (c j).eval x) (fun j => (G j).eval x) (fun j => (X j).eval x) i := by
  fin_cases i <;> simp [gate,TranslationGates.field_apply_zero,TranslationGates.field_apply_one]

theorem valid_gate (R : Expr n) (c G X : Fin 2 → Expr n) {x}
    (hR : R.Valid x) (hc : ∀ i, (c i).Valid x) (hG : ∀ i, (G i).Valid x)
    (hX : ∀ i, (X i).Valid x) (h : R.eval x ≠ 0) (i) :
    (gate R c G X i).Valid x := by
  have ha : ∀ i, ((X i-c i)/R).Valid x := fun i => ⟨⟨hX i,hc i⟩,hR,h⟩
  have hw := fun i => valid_window _ (ha i)
  have hd := fun i => valid_windowD _ (ha i)
  fin_cases i <;> simp [gate,hw,hd,hG,hR,h,hX,hc]

def impulse (t : Expr n) (p X : Fin 2 → Expr n) : Expr n :=
  letI := neZeroTwo
  pulse t*pulse (X 0-p 0+.rat (1/2))*pulse (X 1-p 1+.rat (1/2))

@[simp] theorem eval_impulse (t : Expr n) (p X : Fin 2 → Expr n) (x) :
    (impulse t p X).eval x = SmoothProfiles.impulse (fun i => (p i).eval x)
      (t.eval x) (fun i => (X i).eval x) := by
  simp [impulse,SmoothProfiles.impulse,SmoothProfiles.spatialPulse,Fin.prod_univ_two,mul_assoc]

theorem valid_impulse (t : Expr n) (p X : Fin 2 → Expr n) {x}
    (ht : t.Valid x) (hp : ∀ i, (p i).Valid x) (hX : ∀ i, (X i).Valid x) :
    (impulse t p X).Valid x :=
  ⟨⟨valid_pulse _ ht,valid_pulse _ ⟨⟨hX 0,hp 0⟩,trivial⟩⟩,
    valid_pulse _ ⟨⟨hX 1,hp 1⟩,trivial⟩⟩

def packet (R : Expr n) (X : Fin 2 → Expr n) : Expr n :=
  letI := neZeroTwo
  window (3*(X 0/R))*window (3*(X 1/R))

@[simp] theorem eval_packet (R : Expr n) (X : Fin 2 → Expr n) (x) :
    (packet R X).eval x = SmoothBump.packet (R.eval x) (fun i => (X i).eval x) := by
  simp [packet,SmoothBump.packet,SmoothBump.profile]

theorem valid_packet (R : Expr n) (X : Fin 2 → Expr n) {x} (hR : R.Valid x)
    (hX : ∀ i, (X i).Valid x) (h : R.eval x ≠ 0) : (packet R X).Valid x :=
  ⟨valid_window _ ⟨trivial,hX 0,hR,h⟩,valid_window _ ⟨trivial,hX 1,hR,h⟩⟩

end VelocityDetection.Effective.Recipe
end

noncomputable section
namespace VelocityDetection.Effective.Expr
open Set Function
open scoped BigOperators Topology
variable {n : ℕ}

def activeSum {N b B H : ℕ} (hb : 0 < b)
    (table : Fin N → Fin b → Option (Stacks.Rule (Fin N) b))
    (f : History.Active hb table B H → Expr n) : Expr n :=
  sumFin N (fun s => sumFin B (fun l => sumFin B (fun r => sumFin H (fun h =>
    if hp : (Stacks.lookup hb table (History.config (s,l,r,h)).tape).isSome then
      f ⟨(s,l,r,h),hp⟩ else 0))))

theorem eval_activeSum {N b B H : ℕ} (hb : 0 < b)
    (table : Fin N → Fin b → Option (Stacks.Rule (Fin N) b))
    (f : History.Active hb table B H → Expr n) (x) :
    (activeSum hb table f).eval x = ∑ c : History.Active hb table B H, (f c).eval x := by
  classical
  let g : History.Box N B H → ℝ := fun c =>
    if hp : (Stacks.lookup hb table (History.config c).tape).isSome then
      (f ⟨c,hp⟩).eval x else 0
  have he (c : History.Box N B H) :
      (if hp : (Stacks.lookup hb table (History.config c).tape).isSome then
        f ⟨c,hp⟩ else 0).eval x = g c := by
    dsimp [g]; split_ifs <;> simp
  simp only [activeSum,eval_sumFin,he]
  trans ∑ c : History.Box N B H, g c
  · simp only [Fintype.sum_prod_type]
  exact Finset.sum_congr_set {c | (Stacks.lookup hb table (History.config c).tape).isSome}
    g (fun c => (f c).eval x) (fun c hc => by exact dite_eq_left hc) (fun c hc => by exact dite_eq_right hc)

theorem valid_activeSum {N b B H : ℕ} (hb : 0 < b)
    (table : Fin N → Fin b → Option (Stacks.Rule (Fin N) b))
    (f : History.Active hb table B H → Expr n) {x} (hf : ∀ c, (f c).Valid x) :
    (activeSum hb table f).Valid x := by
  apply valid_sumFin; intro s
  apply valid_sumFin; intro l
  apply valid_sumFin; intro r
  apply valid_sumFin; intro h
  split_ifs
  · exact hf _
  · trivial

end VelocityDetection.Effective.Expr
end

noncomputable section
namespace VelocityDetection.Effective.ArrayRecipe
open Set Function
open scoped BigOperators Topology
open _root_.OAI.VelocityDetection.Effective.Expr Stacks
variable {N b : ℕ} (hN : 0 < N) (hb : 0 < b)
  (table : Fin N → Fin b → Option (Rule (Fin N) b)) (m : ℕ)

abbrev Code := Expr 5

def K (N b m : ℕ) : ℕ := N * capacity b (m+1) 0 ^ 2

def D (N b : ℕ) : ℕ := b^2 * History.radix N b

def radius (N b m n : ℕ) : Code :=
  .rat (1024*3000*(4*(D N b))*(K N b m*D N b+2)*(4*D N b)^n) * (1+.var 0)

def spacing (N b m n : ℕ) : Code := 16*radius N b m n

def duration (N b m n : ℕ) : Code :=
  spacing N b m (n+1) * .rat (K N b m*D N b^(n+1)+2)

def start (N b m : ℕ) : ℕ → Code
  | 0 => 1
  | n+1 => start N b m n+duration N b m n

@[simp] theorem eval_radius (n : ℕ) (x : Fin 5 → ℝ) :
    (radius N b m n).eval x = Expanding.radius (x 0) (HistoryRouting.K N b m) (HistoryRouting.D N b) n := by
  simp [radius,HistoryRouting.K,HistoryRouting.D,K,D,Expanding.radius,Expanding.initialRadius,
    Expanding.lambda]; ring

@[simp] theorem eval_spacing (n : ℕ) (x : Fin 5 → ℝ) :
    (spacing N b m n).eval x = Expanding.spacing (x 0) (HistoryRouting.K N b m) (HistoryRouting.D N b) n := by
  simp [spacing,Expanding.spacing]

@[simp] theorem eval_duration (n : ℕ) (x : Fin 5 → ℝ) :
    (duration N b m n).eval x = Expanding.duration (x 0) (HistoryRouting.K N b m) (HistoryRouting.D N b) n := by
  simp [duration,Expanding.duration,Expanding.count,HistoryRouting.K,HistoryRouting.D,K,D]

@[simp] theorem eval_start (n : ℕ) (x : Fin 5 → ℝ) :
    (start N b m n).eval x = Expanding.startTime (x 0) (HistoryRouting.K N b m) (HistoryRouting.D N b) n := by
  induction n with
  | zero => simp [start,Expanding.startTime]
  | succ n ih => simp [start,Expanding.startTime,ih]

@[simp] theorem valid_radius (n : ℕ) (x : Fin 5 → ℝ) : (radius N b m n).Valid x := by simp [radius]

@[simp] theorem valid_spacing (n : ℕ) (x : Fin 5 → ℝ) : (spacing N b m n).Valid x := by simp [spacing]

@[simp] theorem valid_duration (n : ℕ) (x : Fin 5 → ℝ) : (duration N b m n).Valid x := by simp [duration]

@[simp] theorem valid_start (n : ℕ) (x : Fin 5 → ℝ) : (start N b m n).Valid x := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨ih,valid_duration _ _ _⟩

def sign (c : History.Configuration N) : ℚ :=
  if (lookup hb table c.tape).isNone then 1 else -1

@[simp] theorem eval_sign (c : History.Configuration N) :
    (sign hb table c : ℝ) = HistoryRouting.sign hb table c := by
  unfold sign HistoryRouting.sign
  cases h : lookup hb table c.tape <;> simp

abbrev Instruction (n : ℕ) := History.Active hb table (capacity b (m+1) n) (History.radix N b^n)

def path (n : ℕ) (c : Instruction hb table m n) : Fin 2 → Code :=
  Recipe.center (start N b m n) (duration N b m n) (spacing N b m n)
    (spacing N b m (n+1)) (.rat (sign hb table (History.target hb table c)))
    (History.sourceAddress hb table c) (History.targetAddress hb table c) (.var 1)

@[simp] theorem eval_path (n : ℕ) (c : Instruction hb table m n) (x : Fin 5 → ℝ) (i) :
    (path hb table m n c i).eval x = RoutingArray.path (HistoryRouting.data hN hb table m) (x 0) n c (x 1) i := by
  simp [path,RoutingArray.path,HistoryRouting.data]

include hN in

theorem valid_path (n : ℕ) (c : Instruction hb table m n) {x : Fin 5 → ℝ} (hx : 0 < x 0) (i) :
    (path hb table m n c i).Valid x := by
  apply Recipe.valid_center <;> try {simp}
  have hh := Expanding.duration_ge_one hx (HistoryRouting.K_nonneg N b m) (HistoryRouting.D_ge_one hN hb) n
  simpa using (show Expanding.duration (x 0) (HistoryRouting.K N b m) (HistoryRouting.D N b) n ≠ 0 by linarith)

theorem eval_velocity (n : ℕ) (c : Instruction hb table m n) {x : Fin 5 → ℝ} (hx : 0 < x 0) (i) :
    ((path hb table m n c i).diff 1).eval x =
      deriv (RoutingArray.path (HistoryRouting.data hN hb table m) (x 0) n c) (x 1) i := by
  rw [Expr.eval_diff_curve _ (valid_path hN hb table m n c hx i) 1
    (fun s => RoutingArray.path (HistoryRouting.data hN hb table m) (x 0) n c s i) (by
      intro s; simp [eval_path hN])]
  rw [deriv_pi]
  intro j
  exact (differentiable_pi.mp ((RoutingArray.contDiff_path _ _ _ _).differentiable (by norm_num)) j).differentiableAt

def gate (n : ℕ) (c : Instruction hb table m n) : Fin 2 → Code :=
  Recipe.gate (radius N b m n) (path hb table m n c)
    (fun i => (path hb table m n c i).diff 1) ![.var 2,.var 3]

theorem eval_gate (n : ℕ) (c : Instruction hb table m n) {x : Fin 5 → ℝ} (hx : 0 < x 0) (i) :
    (gate hb table m n c i).eval x = TranslationGates.field
      (Expanding.radius (x 0) (HistoryRouting.K N b m) (HistoryRouting.D N b) n)
      (RoutingArray.path (HistoryRouting.data hN hb table m) (x 0) n c (x 1))
      (deriv (RoutingArray.path (HistoryRouting.data hN hb table m) (x 0) n c) (x 1))
      ![x 2,x 3] i := by
  simp only [gate,Recipe.eval_gate,eval_radius,eval_path hN,eval_velocity hN hb table m n c hx]
  congr 1
  funext j; fin_cases j <;> rfl

include hN in

theorem valid_gate (n : ℕ) (c : Instruction hb table m n) {x : Fin 5 → ℝ} (hx : 0 < x 0) (i) :
    (gate hb table m n c i).Valid x := by
  apply Recipe.valid_gate
  · simp
  · exact valid_path hN hb table m n c hx
  · exact fun j => Expr.valid_diff _ (valid_path hN hb table m n c hx j) 1
  · intro j; fin_cases j <;> trivial
  · simp only [eval_radius]
    have h := Expanding.radius_ge_one hx (HistoryRouting.K_nonneg N b m) (HistoryRouting.D_ge_one hN hb) n
    linarith

def stage (n : ℕ) (i : Fin 2) : Code :=
  activeSum hb table (fun c : Instruction hb table m n => gate hb table m n c i)

theorem eval_stage (n : ℕ) {x : Fin 5 → ℝ} (hx : 0 < x 0) (i) :
    (stage hb table m n i).eval x = RoutingArray.stage (HistoryRouting.data hN hb table m) (x 0) n (x 1) ![x 2,x 3] i := by
  simp only [stage,eval_activeSum,eval_gate hN hb table m n _ hx,RoutingArray.stage,Finset.sum_apply]
  rfl

include hN in

theorem valid_stage (n : ℕ) {x : Fin 5 → ℝ} (hx : 0 < x 0) (i) :
    (stage hb table m n i).Valid x := valid_activeSum _ _ _ (fun c => valid_gate hN hb table m n c hx i)

def field (L : ℕ) (i : Fin 2) : Code := sumFin L (fun n => stage hb table m n i)

theorem eval_field (L : ℕ) {x : Fin 5 → ℝ} (hx : 0 < x 0) (ht : x 1 < L) (i) :
    (field hb table m L i).eval x = RoutingArray.field (HistoryRouting.data hN hb table m) (x 0) (x 1) ![x 2,x 3] i := by
  rw [RoutingArray.field_eq_finite _ _ hx ht]
  simp only [field,eval_sumFin,eval_stage hN hb table m _ hx,Finset.sum_apply]
  simpa only [Finset.sum_apply] using (Fin.sum_univ_eq_sum_range (fun n =>
    RoutingArray.stage (HistoryRouting.data hN hb table m) (x 0) n (x 1) ![x 2,x 3] i) L)

include hN in

theorem valid_field (L : ℕ) {x : Fin 5 → ℝ} (hx : 0 < x 0) (i) :
    (field hb table m L i).Valid x := valid_sumFin _ _ (fun _ => valid_stage hN hb table m _ hx i)

end VelocityDetection.Effective.ArrayRecipe
end

noncomputable section
namespace VelocityDetection.Effective.ChartRecipe
open Set Function ArrayRecipe
open scoped BigOperators Topology
open VelocityDetection.Effective.Expr
variable {N b : ℕ} (hN : 0 < N) (hb : 0 < b)
  (table : Fin N → Fin b → Option (Stacks.Rule (Fin N) b)) (m : ℕ)

def scale (N b m P : ℕ) : ℚ := (1024*((K N b m:ℚ)*(D N b:ℚ)^(P+1)+4))⁻¹

end VelocityDetection.Effective.ChartRecipe
end

end OAI
