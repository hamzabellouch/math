import Mathlib
import OAI.Combinatorics.KMedianRecovery.Geometry.Nearest

namespace OAI

namespace MetricKMedianRecovery.RationalLinearFeasibility
variable {V R : Type*} [Fintype V] {n : ℕ}

def Form.enumeratedRow (e : Fin n ≃ V) (f : Form V) : Row n :=
  ⟨fun i => f.coeff (e i),-f.constant⟩

lemma Form.enumeratedRow_realHolds (e : Fin n ≃ V) (f : Form V) (x : V → ℝ) :
    (f.enumeratedRow e).RealHolds (fun i => x (e i)) ↔ f.realEval x ≤ 0 := by
  unfold Row.RealHolds Row.realValue Form.enumeratedRow Form.realEval
  rw [e.sum_comp (fun v => (f.coeff v:ℝ)*x v),Rat.cast_neg]
  constructor <;> intro h <;> linarith

lemma Form.enumeratedRow_holds (e : Fin n ≃ V) (f : Form V) (x : Fin n → ℚ) :
    (f.enumeratedRow e).Holds x ↔ f.eval (fun v => x (e.symm v)) ≤ 0 := by
  unfold Row.Holds Row.value Form.enumeratedRow Form.eval
  have he := e.sum_comp (fun v => f.coeff v * x (e.symm v))
  simp only [Equiv.symm_apply_apply] at he
  rw [he]
  constructor <;> intro h <;> linarith

def solveForms (e : Fin n ≃ V) (rows : List R) (f : R → Form V) : Option (V → ℚ) :=
  (solve n (rows.map (fun r => (f r).enumeratedRow e))).map (fun y v => y (e.symm v))

lemma solveForms_sound (e : Fin n ≃ V) (rows : List R) (f : R → Form V)
    (x : V → ℚ) (hx : solveForms e rows f=some x) :
    ∀ r ∈ rows, (f r).eval x ≤ 0 := by
  obtain ⟨y,hy,rfl⟩ := Option.map_eq_some_iff.mp hx
  intro r hr
  exact ((f r).enumeratedRow_holds e y).mp
    (solve_sound n _ y hy _ (List.mem_map.mpr ⟨r,hr,rfl⟩))

lemma solveForms_complete (e : Fin n ≃ V) (rows : List R) (f : R → Form V)
    (x : V → ℝ) (hx : ∀ r ∈ rows, (f r).realEval x ≤ 0) :
    ∃ y, solveForms e rows f=some y := by
  have hh : ∀ q ∈ rows.map (fun r => (f r).enumeratedRow e), q.RealHolds (fun i => x (e i)) := by
    intro q hq
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hq
    exact ((f r).enumeratedRow_realHolds e x).mpr (hx r hr)
  obtain ⟨y,hy⟩ := solve_complete n _ _ hh
  exact ⟨fun v => y (e.symm v),by simp only [solveForms,hy,Option.map_some]⟩

end MetricKMedianRecovery.RationalLinearFeasibility

namespace MetricKMedianRecovery.EffectiveOpenability
open RationalLinearFeasibility RationalOpenability OpenabilityLinearization
variable {D X : Type*} [Fintype D] [DecidableEq D] [DecidableEq X]

def active (d : X → D → ℚ) (v z : ℚ) (W : Finset X) (j : D) : Prop :=
  ∀ f ∈ W, z < (1-3*v)*d f j
instance activeDecidable (d : X → D → ℚ) (v z : ℚ) (W : Finset X) (j : D) :
    Decidable (active d v z W j) := inferInstanceAs (Decidable (∀ f ∈ W, z < (1-3*v)*d f j))

def bid (F : Type*) [DecidableEq F] (j : D) : Form (Variables D F) := Form.coord (.inl j)
def slack (F : Type*) [DecidableEq F] (f : F) (a j : D) : Form (Variables D F) := Form.coord (.inr (f,a,j))

def payment (d : X → D → ℚ) (F W : Finset X) (v z : ℚ) (i : X) : Form (Variables D F) :=
  Form.sum (fun j => if active d v z W j then
    if d i j ≤ v*z then (bid F j).sub (Form.const ((1-3*v)*d i j))
    else Form.const (max (z-(1-3*v)*d i j) 0)
    else Form.const (max ((1-3*v)*nearest d W j-(1-3*v)*d i j) 0))

def dual (d : X → D → ℚ) (F W : Finset X) (v z : ℚ) (f : F) (a j : D) : Form (Variables D F) :=
  if active d v z W j then (bid F j).sub (Form.const (d f j))
  else (bid F a).sub (Form.const (2*d f j+d f a))

def forms (d : X → D → ℚ) (F W : Finset X) (v z lam eta : ℚ) (i : X) :
    Kind D W F → Form (Variables D F)
  | .lower j => if active d v z W j then (Form.const z).sub (bid F j) else Form.const 0
  | .upper j => if active d v z W j then (bid F j).sub (Form.const ((1+v^2)*z)) else Form.const 0
  | .cap j f => if active d v z W j then (bid F j).sub (Form.const ((1-3*v)*d f j)) else Form.const 0
  | .far j => if active d v z W j ∧ v*z<d i j then (bid F j).sub (Form.const z) else Form.const 0
  | .payment => (Form.const (lam-(Fintype.card D:ℚ)*eta)).sub (payment d F W v z i)
  | .slackZero f a j => if active d v z W a then (Form.const 0).sub (slack F f a j) else Form.const 0
  | .slackTerm f a j => if active d v z W a then (dual d F W v z f a j).sub (slack F f a j) else Form.const 0
  | .dual f a => if active d v z W a then (Form.sum (fun j => slack F f a j)).sub (Form.const lam) else Form.const 0

omit [Fintype D] [DecidableEq D] [DecidableEq X] in
lemma active_iff [PseudoMetricSpace X] (loc : D → X) (d : X → D → ℚ)
    (hd : ∀ f j, (d f j:ℝ)=dist f (loc j)) (v z : ℚ) (W : Finset X) (j : D) :
    active d v z W j ↔ activeAt loc (1-3*(v:ℝ)) (z:ℝ) W j := by
  have hh (f : X) : (((1-3*v)*d f j:ℚ):ℝ)=(1-3*(v:ℝ))*dist (loc j) f := by
    push_cast
    rw [hd,dist_comm]
  simp only [active,activeAt,←hh,Rat.cast_lt]

omit [Fintype D] in
lemma bid_eq (F : Type*) [DecidableEq F] (j : D) : bid F j=RationalOpenability.bid F j := by
  unfold bid RationalOpenability.bid
  exact congrArg (fun de : DecidableEq (Variables D F) => @Form.coord (Variables D F) de (.inl j))
    (Subsingleton.elim _ _)
omit [Fintype D] in
lemma slack_eq (F : Type*) [DecidableEq F] (f : F) (a j : D) : slack F f a j=RationalOpenability.slack f a j := by
  unfold slack RationalOpenability.slack
  exact congrArg (fun de : DecidableEq (Variables D F) => @Form.coord (Variables D F) de (.inr (f,a,j)))
    (Subsingleton.elim _ _)

lemma forms_eq [PseudoMetricSpace X] (loc : D → X) (d : X → D → ℚ)
    (hd : ∀ f j, (d f j:ℝ)=dist f (loc j)) (F W : Finset X) (v z lam eta : ℚ) (i : X) :
    forms d F W v z lam eta i=system loc d F W v z lam eta i := by
  classical
  have ha (j : D) := active_iff loc d hd v z W j
  have hn (j : D) : d i j ≤ v*z ↔ dist i (loc j) ≤ (v:ℝ)*(z:ℝ) := by
    rw [←hd,←Rat.cast_mul]
    exact Rat.cast_le.symm
  have hf (j : D) : v*z<d i j ↔ (v:ℝ)*(z:ℝ)<dist i (loc j) := by
    rw [←hd,←Rat.cast_mul]
    exact Rat.cast_lt.symm
  have hp : payment d F W v z i=paymentForm loc d F W v z i := by
    simp only [payment,paymentForm,ha,hn,bid_eq]
  have hdu (f : F) (a j : D) : dual d F W v z f a j=dualForm loc d F W v z f a j := by
    simp only [dual,dualForm,ha,bid_eq]
  funext k
  cases k <;> simp only [forms,system,ha,hf,hp,hdu,bid_eq,slack_eq]

def solveOpening (d : X → D → ℚ) (F W : Finset X) (v z lam eta : ℚ) (i : X)
    {n : ℕ} (e : Fin n ≃ Variables D F) (rows : List (Kind D W F)) : Option (Variables D F → ℚ) :=
  solveForms e rows (forms d F W v z lam eta i)

lemma solveOpening_sound [PseudoMetricSpace X] (loc : D → X) (d : X → D → ℚ)
    (hd : ∀ f j, (d f j:ℝ)=dist f (loc j)) (F W : Finset X) (v z lam eta : ℚ) (i : X)
    {n : ℕ} (e : Fin n ≃ Variables D F) (rows : List (Kind D W F)) (hrows : ∀ k, k ∈ rows)
    (x : Variables D F → ℚ) (hx : solveOpening d F W v z lam eta i e rows=some x) :
    Feasible loc F W (v:ℝ) (z:ℝ) (lam:ℝ) (eta:ℝ) i
      (fun j => (x (.inl j):ℝ)) (fun f a j => (x (.inr (f,a,j)):ℝ)) := by
  apply (system_iff loc d hd F W v z lam eta i (fun v => (x v:ℝ))).mp
  intro k
  rw [←forms_eq loc d hd F W v z lam eta i,Form.realEval_cast]
  exact_mod_cast solveForms_sound e rows (forms d F W v z lam eta i) x hx k (hrows k)

lemma solveOpening_complete [PseudoMetricSpace X] (loc : D → X) (d : X → D → ℚ)
    (hd : ∀ f j, (d f j:ℝ)=dist f (loc j)) (F W : Finset X) (v z lam eta : ℚ) (i : X)
    {n : ℕ} (e : Fin n ≃ Variables D F) (rows : List (Kind D W F))
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) (hz : (0:ℝ)≤(z:ℝ))
    (h : etaOpenable loc F W (1-3*(v:ℝ)) (1+(v:ℝ)^2) (v:ℝ) (z:ℝ) (lam:ℝ) (eta:ℝ) i) :
    ∃ x, solveOpening d F W v z lam eta i e rows=some x := by
  obtain ⟨tau,y,hf⟩ := (openable_iff_linear_feasible loc F W (v:ℝ) (z:ℝ)
    (lam:ℝ) (eta:ℝ) i hv hv1 hz).mp h
  let x : Variables D F → ℝ := Sum.elim tau (fun p => y p.1 p.2.1 p.2.2)
  apply solveForms_complete e rows (forms d F W v z lam eta i) x
  intro k _
  rw [forms_eq loc d hd F W v z lam eta i]
  exact (system_iff loc d hd F W v z lam eta i x).mpr hf k

end MetricKMedianRecovery.EffectiveOpenability

end OAI
