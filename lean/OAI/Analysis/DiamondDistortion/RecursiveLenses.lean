import OAI.Analysis.DiamondDistortion.Backward

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace RecursiveApplications
open Midpoint
variable {X ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def c6 : ℝ := 2*Real.exp (-(Real.exp 1-1))/(4:ℝ)^6
def c3 : ℝ := (6*Real.exp 1)⁻¹^3

def q6 (ε : ℝ) : ℝ := Real.sqrt (1-c6*ε^6/512)
def theta (ε : ℝ) : ℝ := Real.sqrt (1-c3*ε^3/(2*Real.sqrt 2))

lemma c6_pos : 0 < c6 := by unfold c6; positivity
lemma c6_le_one : c6 ≤ 1 := by
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hl : Real.exp (-(Real.exp 1-1)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  simp only [neg_sub] at hl
  unfold c6
  norm_num
  linarith
lemma c3_pos : 0 < c3 := by unfold c3; positivity
lemma c3_le_one : c3 ≤ 1 := by
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hi : (6*Real.exp 1)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).mpr (by linarith)
  exact pow_le_one₀ (by positivity) hi

/-- Polynomial form of the homogeneous power input, used only as an intermediate
    algebraic rewrite of the displayed sixth and cubic estimates. -/
def PowerInput (A : Heads ι X) (n m : ℕ) (c : ℝ) : Prop :=
  ∀ (H : ι) (p y : X) (R : ℝ),A.projection H p=p → A.projection H y=0 →
    0 < R → ‖p+y‖ ≤ R → ‖p-y‖ ≤ R →
    R^m*‖p‖^2+c*‖y‖^n ≤ R^(m+2)

lemma power_lens (A : Heads ι X) {n m : ℕ} {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 < ε)
    (hinput : PowerInput A n m c) :
    Diamond.UnitLensBound X ε (Real.sqrt (1-c*(ε/2)^n)) := by
  intro x z hp hm hs
  have hh := positive_limit_le
    (fun η => (1+2*η)^m*(max (‖x‖-η) 0)^2+c*(max (ε/2-η) 0)^n)
    (fun η => (1+2*η)^(m+2)) (by fun_prop) (by fun_prop) (fun η hη => by
      obtain ⟨H,p,y,hP,hY,hpL,hyL,hpR,hmR⟩ := A.pure_pair z hη hp hm hs
      have h := hinput H p y (1+2*η) hP hY (by positivity) hpR hmR
      have hp' := (sq_le_sq₀ (le_max_right _ _) (norm_nonneg _)).mpr
        (max_le hpL (norm_nonneg _))
      have hy' := pow_le_pow_left₀ (le_max_right (ε/2-η) 0)
        (max_le hyL (norm_nonneg y)) n
      exact (add_le_add
        (mul_le_mul_of_nonneg_left hp' (by positivity : 0 ≤ (1+2*η)^m))
        (mul_le_mul_of_nonneg_left hy' hc)).trans h)
  simp only [mul_zero,add_zero,sub_zero,one_pow,one_mul,
    max_eq_left (norm_nonneg x),max_eq_left (half_pos hε).le] at hh
  have hrad : 0 ≤ 1-c*(ε/2)^n := by nlinarith [sq_nonneg ‖x‖]
  exact (Real.le_sqrt (norm_nonneg _) hrad).mpr (by linarith)

/-- The exact finite-head sixth input. The S=0 convention is represented by
    real division, for which the entire right side is zero when S=0. -/
def SixthInput (A : Heads ι X) : Prop :=
  ∀ (H : ι) (p y : X),A.projection H p=p → A.projection H y=0 →
    let S := ‖p+y‖^2+‖p-y‖^2
    c6*‖y‖^6/S^2 ≤ S-2*‖p‖^2

lemma sixth_to_power (A : Heads ι X) (hinput : SixthInput A) : PowerInput A 6 4 (c6/8) := by
  intro H p y R hP hY hR hp hm
  let S := ‖p+y‖^2+‖p-y‖^2
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hcap : S ≤ 2*R^2 := by
    have hp2 := (sq_le_sq₀ (norm_nonneg _) hR.le).mpr hp
    have hm2 := (sq_le_sq₀ (norm_nonneg _) hR.le).mpr hm
    dsimp [S]
    linarith
  by_cases hzero : S=0
  · have hplus : ‖p+y‖=0 := by
      have he : ‖p+y‖^2+‖p-y‖^2=0 := hzero
      nlinarith [sq_nonneg ‖p-y‖,norm_nonneg (p+y)]
    have hminus : ‖p-y‖=0 := by
      have he : ‖p+y‖^2+‖p-y‖^2=0 := hzero
      nlinarith [sq_nonneg ‖p+y‖,norm_nonneg (p-y)]
    have hp0 := Diamond.norm_center_le (le_of_eq hplus) (le_of_eq hminus)
    have hy0 := Diamond.norm_deviation_le (le_of_eq hplus) (le_of_eq hminus)
    have hpn : ‖p‖=0 := le_antisymm hp0 (norm_nonneg _)
    have hyn : ‖y‖=0 := le_antisymm hy0 (norm_nonneg _)
    rw [hpn,hyn]
    simpa using (pow_nonneg hR.le 6)
  have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hzero)
  have hh := hinput H p y hP hY
  change c6*‖y‖^6/S^2 ≤ S-2*‖p‖^2 at hh
  have henergy : c6*‖y‖^6 ≤ (S-2*‖p‖^2)*S^2 :=
    (div_le_iff₀ (sq_pos_of_pos hSpos)).mp hh
  have hdef : 0 ≤ S-2*‖p‖^2 :=
    (by have := c6_pos; positivity : 0 ≤ c6*‖y‖^6/S^2).trans hh
  have hS2 : S^2 ≤ (2*R^2)^2 := (sq_le_sq₀ hS (by positivity)).mpr hcap
  have hmul := mul_le_mul_of_nonneg_left hS2 hdef
  have hmul2 := mul_le_mul_of_nonneg_right
    (show S-2*‖p‖^2 ≤ 2*R^2-2*‖p‖^2 by linarith) (sq_nonneg (2*R^2))
  have hfin := henergy.trans (hmul.trans hmul2)
  norm_num
  nlinarith only [hfin]

lemma q6_range {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) : 0 ≤ q6 ε ∧ q6 ε < 1 := by
  have hp : 0 < c6*ε^6/512 := by have := c6_pos; positivity
  have hpow : ε^6 ≤ 1 := pow_le_one₀ hε.le hε1
  have hl : c6*ε^6 ≤ 1 := (mul_le_of_le_one_left (by positivity) c6_le_one).trans hpow
  have hrad : 0 ≤ 1-c6*ε^6/512 := by linarith
  have hsq := Real.sq_sqrt hrad
  constructor
  · exact Real.sqrt_nonneg _
  · unfold q6
    nlinarith [Real.sqrt_nonneg (1-c6*ε^6/512)]

theorem sixth_lens (A : Heads ι X) (hinput : SixthInput A) {ε : ℝ} (hε : 0 < ε)
    (_hε1 : ε ≤ 1) : Diamond.UnitLensBound X ε (q6 ε) := by
  have h := power_lens A (show 0 ≤ c6/8 by have := c6_pos; positivity) hε (sixth_to_power A hinput)
  have he : 1-(c6/8)*(ε/2)^6=1-c6*ε^6/512 := by ring
  simpa only [he,q6] using h

theorem sixth_depth (A : Heads ι X) (hinput : SixthInput A) {D s : ℝ}
    (k : ℕ) (f : Diamond.Vertex k → X) (hf : Diamond.HasDistortion k f D s) :
    D⁻¹ ≤ (q6 D⁻¹)^k := by
  have hD : 0 < D := lt_of_lt_of_le (by norm_num) hf.1
  have hα : 0 < D⁻¹ := inv_pos.mpr hD
  have hα1 : D⁻¹ ≤ 1 := (inv_le_one₀ hD).mpr hf.1
  have hlens : Diamond.UnitLensBound X (2*D⁻¹) (q6 D⁻¹) := by
    intro x z hp hm hs
    exact sixth_lens A hinput hα hα1 x z hp hm
      (fun i j hij => (by linarith : D⁻¹ ≤ 2*D⁻¹).trans (hs i j hij))
  have hnorm := Diamond.upper_one_normalization f hf
  obtain ⟨hq,hq1⟩ := q6_range hα hα1
  exact Diamond.backward hα hα1 hq hq1 hlens k (fun v => (D*s)⁻¹ • f v)
    (fun u v => (hnorm u v).1) (fun u v => (hnorm u v).2)

/-- Exact finite-head cubic inequality, with its positive radius denominator. -/
def CubicInput (A : Heads ι X) : Prop :=
  ∀ (H : ι) (p y : X) (R : ℝ),A.projection H p=p → A.projection H y=0 →
    0 < R → ‖p+y‖ ≤ R → ‖p-y‖ ≤ R →
    ‖p‖^2+c3/(2*Real.sqrt 2*R)*‖y‖^3 ≤ R^2

lemma cubic_to_power (A : Heads ι X) (hinput : CubicInput A) :
    PowerInput A 3 1 (c3/(2*Real.sqrt 2)) := by
  intro H p y R hP hY hR hp hm
  have h := mul_le_mul_of_nonneg_left (hinput H p y R hP hY hR hp hm) hR.le
  have he : R*(‖p‖^2+c3/(2*Real.sqrt 2*R)*‖y‖^3)=
      R*‖p‖^2+c3/(2*Real.sqrt 2)*‖y‖^3 := by field_simp
  rw [he] at h
  simpa only [pow_one,show (1+2:ℕ)=3 from rfl,show R*R^2=R^3 by ring] using h

lemma theta_range {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) : 0 ≤ theta ε ∧ theta ε < 1 := by
  have hsqrt : 1 ≤ Real.sqrt 2 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hp : 0 < c3*ε^3/(2*Real.sqrt 2) := by have := c3_pos; positivity
  have hpow : ε^3 ≤ 1 := pow_le_one₀ hε.le hε1
  have hl : c3*ε^3 ≤ 1 := (mul_le_of_le_one_left (by positivity) c3_le_one).trans hpow
  have hratio : c3*ε^3/(2*Real.sqrt 2) ≤ 1 :=
    (div_le_one₀ (by positivity)).mpr (by linarith)
  have hrad : 0 ≤ 1-c3*ε^3/(2*Real.sqrt 2) := by linarith
  have hsq := Real.sq_sqrt hrad
  constructor
  · exact Real.sqrt_nonneg _
  · unfold theta
    nlinarith [Real.sqrt_nonneg (1-c3*ε^3/(2*Real.sqrt 2))]

/-- The cubic graph application can also use finite-dimensional paired tails
    directly; dual separability is unnecessary for this stronger transfer from
    the same displayed pure-head estimate. The weak-null clause is proved below. -/
theorem cubic_depth (A : Heads ι X) (hinput : CubicInput A) {D s : ℝ}
    (k : ℕ) (f : Diamond.Vertex k → X) (hf : Diamond.HasDistortion k f D s) :
    1 ≤ D*(theta D⁻¹)^k := by
  have hD : 0 < D := lt_of_lt_of_le (by norm_num) hf.1
  have hα : 0 < D⁻¹ := inv_pos.mpr hD
  have hα1 : D⁻¹ ≤ 1 := (inv_le_one₀ hD).mpr hf.1
  have hpow := power_lens A (show 0 ≤ c3/(2*Real.sqrt 2) by have := c3_pos; positivity)
    (show 0 < 2*D⁻¹ by positivity) (cubic_to_power A hinput)
  have he : 1-c3/(2*Real.sqrt 2)*(2*D⁻¹/2)^3=1-c3*(D⁻¹)^3/(2*Real.sqrt 2) := by ring
  have hlens : Diamond.UnitLensBound X (2*D⁻¹) (theta D⁻¹) := by simpa only [he,theta] using hpow
  have hnorm := Diamond.upper_one_normalization f hf
  obtain ⟨hθ,hθ1⟩ := theta_range hα hα1
  have h := Diamond.backward hα hα1 hθ hθ1 hlens k (fun v => (D*s)⁻¹ • f v)
    (fun u v => (hnorm u v).1) (fun u v => (hnorm u v).2)
  have hh := mul_le_mul_of_nonneg_left h hD.le
  simpa only [mul_inv_cancel₀ hD.ne'] using hh

def ZeroRootInput (A : Heads ι X) : Prop :=
  ∀ (H : ι) (p y : X),A.projection H p=p → A.projection H y=0 → y ≠ 0 →
    ‖p‖+‖y‖^3/(8*(2*‖p‖+‖y‖)^2) ≤ (‖p+y‖+‖p-y‖)/2

lemma zero_root_parent (A : Heads ι X) (hinput : ZeroRootInput A)
    {α R : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (_hR : 0 ≤ R) (hR1 : R ≤ 1)
    {x : X} (z : ℕ → X) (hp : ∀ i,‖x+z i‖ ≤ R) (hm : ∀ i,‖x-z i‖ ≤ R)
    (hs : ∀ i j,i ≠ j → 2*α ≤ ‖z i-z j‖) : ‖x‖ ≤ R-α^3/4608 := by
  let c : ℝ := α^3/2304
  let η : ℝ := c/6
  have hc : 0 < c := by dsimp [c]; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  have hα2 : α^2 ≤ 1 := pow_le_one₀ hα.le hα1
  have hα3 : α^3 ≤ α := by nlinarith [mul_le_mul_of_nonneg_left hα2 hα.le]
  have hηα : η ≤ α/2 := by dsimp [η,c]; nlinarith
  have hηhalf : η ≤ 1/2 := hηα.trans (by linarith)
  obtain ⟨H,p,y,hP,hY,hpL,hyL,hpR,hmR⟩ := A.pure_pair z hη hp hm hs
  have hy : α/2 ≤ ‖y‖ := by linarith
  have hypos : 0 < ‖y‖ := (half_pos hα).trans_le hy
  have hy0 : y ≠ 0 := norm_pos_iff.mp hypos
  have hp2 : ‖p‖ ≤ 2 := (Diamond.norm_center_le hpR hmR).trans (by linarith)
  have hy2 : ‖y‖ ≤ 2 := (Diamond.norm_deviation_le hpR hmR).trans (by linarith)
  have hdenpos : 0 < 8*(2*‖p‖+‖y‖)^2 := by positivity
  have hden : 8*(2*‖p‖+‖y‖)^2 ≤ 288 := by
    have hsum : 2*‖p‖+‖y‖ ≤ 6 := by linarith
    have hsq := (sq_le_sq₀ (by positivity : 0 ≤ 2*‖p‖+‖y‖) (by norm_num : (0:ℝ) ≤ 6)).mpr hsum
    linarith
  have hy3 := pow_le_pow_left₀ (half_pos hα).le hy 3
  have hgain : c ≤ ‖y‖^3/(8*(2*‖p‖+‖y‖)^2) := by
    apply (le_div_iff₀ hdenpos).mpr
    have hm := mul_le_mul_of_nonneg_left hden hc.le
    dsimp [c] at hm ⊢
    nlinarith only [hm,hy3]
  have hi := hinput H p y hP hY hy0
  have hu : (‖p+y‖+‖p-y‖)/2 ≤ R+2*η := by linarith
  have hchain := hi.trans hu
  dsimp [η,c] at hchain hpL hgain
  linarith

theorem zero_root_depth (A : Heads ι X) (hinput : ZeroRootInput A) {D s : ℝ}
    (k : ℕ) (f : Diamond.Vertex k → X) (hf : Diamond.HasDistortion k f D s) :
    (k:ℝ) ≤ 4608*D^3*(1-D⁻¹) := by
  have hD : 0 < D := lt_of_lt_of_le (by norm_num) hf.1
  have hα : 0 < D⁻¹ := inv_pos.mpr hD
  have hα1 : D⁻¹ ≤ 1 := (inv_le_one₀ hD).mpr hf.1
  have hnorm := Diamond.upper_one_normalization f hf
  have hstep : ∀ (x : X) (z : ℕ → X) (R : ℝ),0 ≤ R → R ≤ 1 → D⁻¹ ≤ ‖x‖ →
      (∀ i,‖x+z i‖ ≤ R) → (∀ i,‖x-z i‖ ≤ R) →
      (∀ i j,i ≠ j → 2*D⁻¹ ≤ ‖z i-z j‖) → ‖x‖ ≤ R-(D⁻¹)^3/4608 := by
    intro x z R hR hR1 hx hp hm hs
    exact zero_root_parent A hinput hα hα1 hR hR1 z hp hm hs
  have hi := Diamond.iterate_additive (show 0 ≤ (D⁻¹)^3/4608 by positivity) hstep k
    (fun v => (D*s)⁻¹ • f v) (by norm_num : (0:ℝ) ≤ 1) le_rfl
    (fun u v => (hnorm u v).1)
    (fun e => Diamond.slope_upper _ (fun u v => by simpa using (hnorm u v).2) e)
  have hfin : (k:ℝ)*(D⁻¹)^3/4608 ≤ 1-D⁻¹ := by linarith
  have hm := mul_le_mul_of_nonneg_right hfin (show 0 ≤ 4608*D^3 by positivity)
  have he : ((k:ℝ)*(D⁻¹)^3/4608)*(4608*D^3)=(k:ℝ) := by field_simp
  rw [he] at hm
  simpa only [mul_comm] using hm

end RecursiveApplications

end DiamondDistortion

end

end OAI
