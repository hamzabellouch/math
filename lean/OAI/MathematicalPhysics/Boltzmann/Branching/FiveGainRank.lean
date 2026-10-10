import OAI.MathematicalPhysics.Boltzmann.Branching.CompactParameterConvergence
import OAI.MathematicalPhysics.Boltzmann.Collision.AxialJointAnalytic
import OAI.MathematicalPhysics.Boltzmann.Jets.JetBarrierKinetic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Algebra.Module.FiniteDimension

namespace OAI

section

/-! # The explicit nondegenerate five-collision configuration

These algebraic witnesses allow arbitrary axial cold velocities. The first
three increments are independent; after the fourth increment the final two
collision normals are not parallel. Derivative and analytic-null-set arguments
are separate from these algebraic statements.
-/

noncomputable section

open Matrix
open scoped Matrix

namespace BoltzmannNonuniqueness.FiveGainWitness

abbrev V := Fin 3 → ℝ

def transverseSquare (R : ℝ) : ℝ := (R+1)^2+(1-R)^2

def smallFactor (R b : ℝ) : ℝ := (2*(1+b^2+transverseSquare R))⁻¹

def first : V := ![0,1,0]
def second (R : ℝ) : V := ![1,-R,0]
def third (R b : ℝ) : V :=
  ![-smallFactor R b*b*(R+1),-smallFactor R b*b*(1-R),
    smallFactor R b*transverseSquare R]

def afterThirdX (R b : ℝ) : ℝ := (1-smallFactor R b*b)*(R+1)
def afterThirdY (R b : ℝ) : ℝ := (1-smallFactor R b*b)*(1-R)

theorem transverseSquare_pos (R : ℝ) : 0 < transverseSquare R := by
  unfold transverseSquare
  nlinarith [sq_nonneg R]

theorem smallFactor_pos (R b : ℝ) : 0 < smallFactor R b := by
  unfold smallFactor
  have := transverseSquare_pos R
  positivity

theorem transverse_factor_pos (R b : ℝ) : 0 < 1-smallFactor R b*b := by
  have hD : 0 < 2*(1+b^2+transverseSquare R) := by
    have := transverseSquare_pos R
    positivity
  have hB : b < 2*(1+b^2+transverseSquare R) := by
    have := transverseSquare_pos R
    nlinarith [sq_nonneg (b-1)]
  have h := (div_lt_one hD).mpr hB
  unfold smallFactor
  rw [mul_comm,← div_eq_mul_inv]
  linarith

theorem first_perpendicular (R b : ℝ) : ![R,0,b] ⬝ᵥ first = 0 := by
  simp [first]

theorem second_perpendicular (R b : ℝ) : ![R,1,b] ⬝ᵥ second R = 0 := by
  simp [second]

theorem third_perpendicular (R b : ℝ) : ![R+1,1-R,b] ⬝ᵥ third R b = 0 := by
  rw [vec3_dotProduct]
  dsimp [third,Matrix.cons_val]
  unfold transverseSquare
  ring

theorem first_three_det (R b : ℝ) :
    det (Matrix.of ![first,second R,third R b]) = -smallFactor R b*transverseSquare R := by
  rw [det_fin_three]
  simp [first,second,third,Matrix.of_apply,Matrix.cons_val]

theorem first_three_det_ne_zero (R b : ℝ) : det (Matrix.of ![first,second R,third R b]) ≠ 0 := by
  rw [first_three_det]
  exact mul_ne_zero (neg_ne_zero.mpr (smallFactor_pos R b).ne') (transverseSquare_pos R).ne'

theorem afterThird_transverse_pos (R b : ℝ) :
    0 < afterThirdX R b ^ 2+afterThirdY R b ^ 2 := by
  have h : 0 < (1-smallFactor R b*b)^2 * transverseSquare R :=
    mul_pos (sq_pos_of_pos (transverse_factor_pos R b)) (transverseSquare_pos R)
  convert h using 1
  unfold afterThirdX afterThirdY transverseSquare
  ring

theorem last_normals_cross_ne_zero (R b a₄ a₅ : ℝ) :
    ![afterThirdX R b,afterThirdY R b,a₄] ⨯₃
      ![afterThirdX R b-afterThirdY R b,afterThirdY R b+afterThirdX R b,a₅] ≠ 0 := by
  intro hz
  have h := congrFun hz 2
  change afterThirdX R b*(afterThirdY R b+afterThirdX R b)-
    afterThirdY R b*(afterThirdX R b-afterThirdY R b) = 0 at h
  have := afterThird_transverse_pos R b
  nlinarith

/-- Every perpendicular increment is produced by a redundant angular parameter. -/
theorem cross_represents {n k : V} (hn : n ≠ 0) (hk : n ⬝ᵥ k = 0) :
    n ⨯₃ ((-(n ⬝ᵥ n)⁻¹) • (n ⨯₃ k)) = k := by
  have hd : n ⬝ᵥ n ≠ 0 := fun h => hn (dotProduct_self_eq_zero.mp h)
  rw [map_smul,cross_cross_eq_smul_sub_smul',hk,zero_smul,zero_sub,smul_neg,
    ← neg_smul,neg_neg,smul_smul,inv_mul_cancel₀ hd,one_smul]

end BoltzmannNonuniqueness.FiveGainWitness

end

end

section

/-! # The actual recursive five-gain characteristic map -/

noncomputable section

open Matrix
open scoped Matrix
open BoltzmannNonuniqueness.AxialFlow BoltzmannNonuniqueness.AxialAnalytic

namespace BoltzmannNonuniqueness.FiveGainMap

abbrev V := Fin 3 → ℝ
abbrev State := ℝ × (V × V)
abbrev Parameters := (Fin 5 → ℝ) × (Fin 5 → V)

def axis (a : ℝ) : V := ![0,0,a]

def step (σ α γ s t : ℝ) (L : V) (z : State) : State :=
  let x := z.2.1-(z.1-t) • z.2.2
  let n := z.2.2-axis (velocity σ α γ s t (x 2))
  (t,x,z.2.2+n ⨯₃ L)

/-- Only the first five stages change the state. -/
def path (σ s : Fin 5 → ℝ) (α γ : ℝ) (z : State) (q : Parameters) : ℕ → State
  | 0 => z
  | k+1 => if h : k < 5 then
      step (σ ⟨k,h⟩) α γ (s ⟨k,h⟩) (q.1 ⟨k,h⟩) (q.2 ⟨k,h⟩)
        (path σ s α γ z q k)
    else path σ s α γ z q k

def map (σ s : Fin 5 → ℝ) (α γ : ℝ) (z : State) (q : Parameters) : State :=
  path σ s α γ z q 5

section Analytic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cross_analytic {f g : E → V} {q : E}
    (hf : AnalyticAt ℝ f q) (hg : AnalyticAt ℝ g q) :
    AnalyticAt ℝ (fun y => f y ⨯₃ g y) q := by
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact ((analyticAt_pi_iff.mp hf 1).mul (analyticAt_pi_iff.mp hg 2)).sub
      ((analyticAt_pi_iff.mp hf 2).mul (analyticAt_pi_iff.mp hg 1))
  · exact ((analyticAt_pi_iff.mp hf 2).mul (analyticAt_pi_iff.mp hg 0)).sub
      ((analyticAt_pi_iff.mp hf 0).mul (analyticAt_pi_iff.mp hg 2))
  · exact ((analyticAt_pi_iff.mp hf 0).mul (analyticAt_pi_iff.mp hg 1)).sub
      ((analyticAt_pi_iff.mp hf 1).mul (analyticAt_pi_iff.mp hg 0))

theorem axis_analytic {f : E → ℝ} {q : E} (hf : AnalyticAt ℝ f q) :
    AnalyticAt ℝ (fun y => axis (f y)) q := by
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact analyticAt_const
  · exact analyticAt_const
  · exact hf

theorem step_analytic {σ α γ s : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s)
    {t : E → ℝ} {L : E → V} {z : E → State} {q : E}
    (ht : AnalyticAt ℝ t q) (hL : AnalyticAt ℝ L q) (hz : AnalyticAt ℝ z q)
    (htpos : 0 < t q) :
    AnalyticAt ℝ (fun y => step σ α γ s (t y) (L y) (z y)) q := by
  have hztime : AnalyticAt ℝ (fun y => (z y).1) q := analyticAt_fst.comp hz
  have hzx : AnalyticAt ℝ (fun y => (z y).2.1) q :=
    analyticAt_fst.comp (analyticAt_snd.comp hz)
  have hzv : AnalyticAt ℝ (fun y => (z y).2.2) q :=
    analyticAt_snd.comp (analyticAt_snd.comp hz)
  let x : E → V := fun y => (z y).2.1-((z y).1-t y) • (z y).2.2
  have hx : AnalyticAt ℝ x q := hzx.sub ((hztime.sub ht).smul hzv)
  have hp : AnalyticAt ℝ (fun y => ((s,t y),x y 2)) q :=
    (analyticAt_const.prod ht).prod (analyticAt_pi_iff.mp hx 2)
  have hv := (jointVelocity_analytic (σ := σ) hα hγ ((s,t q),x q 2) hs htpos).comp
    (f := fun y => ((s,t y),x y 2)) hp
  exact ht.prod (hx.prod (hzv.add (cross_analytic (hzv.sub (axis_analytic hv)) hL)))

end Analytic

theorem path_analytic {σ s : Fin 5 → ℝ} {α γ : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : ∀ i, 0 < s i) (z : State) (q : Parameters) (ht : ∀ i, 0 < q.1 i) (k : ℕ) :
    AnalyticAt ℝ (fun y => path σ s α γ z y k) q := by
  induction k with
  | zero => exact analyticAt_const
  | succ k ih =>
    by_cases hk : k < 5
    · simp only [path,dite_eq_left hk]
      apply step_analytic hα hγ (hs ⟨k,hk⟩) _ _ ih (ht ⟨k,hk⟩)
      · exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 5 => ℝ)
          ⟨k,hk⟩).analyticAt _).comp analyticAt_fst
      · exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 5 => V)
          ⟨k,hk⟩).analyticAt _).comp analyticAt_snd
    · simpa only [path,dite_eq_right hk] using ih

theorem map_analytic {σ s : Fin 5 → ℝ} {α γ : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : ∀ i, 0 < s i) (z : State) (q : Parameters) (ht : ∀ i, 0 < q.1 i) :
    AnalyticAt ℝ (map σ s α γ z) q := path_analytic hα hγ hs z q ht 5

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # The thermal collision map, including the zero-width limit -/

noncomputable section

open Matrix
open scoped Matrix
open BoltzmannNonuniqueness.AxialFlow BoltzmannNonuniqueness.AxialAnalytic

namespace BoltzmannNonuniqueness.FiveGainMap

def thermalCenter (σ α γ s d t : ℝ) (x w : V) : V :=
  ![d*w 0,d*w 1,JetCoreMap.axialMap σ α γ s d t (x 2) (w 2)]

def thermalStep (σ α γ s d t : ℝ) (L w : V) (z : State) : State :=
  let x := z.2.1-(z.1-t) • z.2.2
  (t,x,z.2.2+(z.2.2-thermalCenter σ α γ s d t x w) ⨯₃ L)

theorem thermalCenter_zero (σ α γ s t : ℝ) (x w : V) :
    thermalCenter σ α γ s 0 t x w = axis (velocity σ α γ s t (x 2)) := by
  simp [thermalCenter,JetCoreMap.axialMap,axis]

theorem thermalStep_zero (σ α γ s t : ℝ) (L w : V) (z : State) :
    thermalStep σ α γ s 0 t L w z = step σ α γ s t L z := by
  simp only [thermalStep,thermalCenter_zero,step]

section Analytic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem thermalCenter_analytic {σ α γ : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    {s d t : E → ℝ} {x w : E → V} {q : E}
    (hs : AnalyticAt ℝ s q) (hd : AnalyticAt ℝ d q) (ht : AnalyticAt ℝ t q)
    (hx : AnalyticAt ℝ x q) (hw : AnalyticAt ℝ w q)
    (hspos : 0 < s q) (htpos : 0 < t q) :
    AnalyticAt ℝ (fun y => thermalCenter σ α γ (s y) (d y) (t y) (x y) (w y)) q := by
  have hw₂ := analyticAt_pi_iff.mp hw 2
  have hshift := (analyticAt_pi_iff.mp hx 2).sub (ht.mul (hd.mul hw₂))
  have hp := (hs.prod ht).prod hshift
  have hu := (jointVelocity_analytic (σ := σ) hα hγ
    ((s q,t q),x q 2-t q*(d q*w q 2)) hspos htpos).comp
    (f := fun y => ((s y,t y),x y 2-t y*(d y*w y 2))) hp
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact hd.mul (analyticAt_pi_iff.mp hw 0)
  · exact hd.mul (analyticAt_pi_iff.mp hw 1)
  · have h := (hd.mul hw₂).add hu
    change AnalyticAt ℝ (fun y => d y*w y 2+
      velocity σ α γ (s y) (t y) (x y 2-t y*d y*w y 2)) q
    change AnalyticAt ℝ (fun y => d y*w y 2+
      velocity σ α γ (s y) (t y) (x y 2-t y*(d y*w y 2))) q at h
    simpa only [mul_assoc] using h

theorem thermalStep_analytic {σ α γ : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    {s d t : E → ℝ} {L w : E → V} {z : E → State} {q : E}
    (hs : AnalyticAt ℝ s q) (hd : AnalyticAt ℝ d q) (ht : AnalyticAt ℝ t q)
    (hL : AnalyticAt ℝ L q) (hw : AnalyticAt ℝ w q) (hz : AnalyticAt ℝ z q)
    (hspos : 0 < s q) (htpos : 0 < t q) :
    AnalyticAt ℝ (fun y => thermalStep σ α γ (s y) (d y) (t y) (L y) (w y) (z y)) q := by
  have hztime : AnalyticAt ℝ (fun y => (z y).1) q := analyticAt_fst.comp hz
  have hzx : AnalyticAt ℝ (fun y => (z y).2.1) q :=
    analyticAt_fst.comp (analyticAt_snd.comp hz)
  have hzv : AnalyticAt ℝ (fun y => (z y).2.2) q :=
    analyticAt_snd.comp (analyticAt_snd.comp hz)
  let x : E → V := fun y => (z y).2.1-((z y).1-t y) • (z y).2.2
  have hx : AnalyticAt ℝ x q := hzx.sub ((hztime.sub ht).smul hzv)
  have hc := thermalCenter_analytic (σ := σ) hα hγ hs hd ht hx hw hspos htpos
  exact ht.prod (hx.prod (hzv.add (cross_analytic (hzv.sub hc) hL)))

end Analytic

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Joint analytic dependence of the five thermal collision steps -/

noncomputable section

namespace BoltzmannNonuniqueness.FiveGainMap

abbrev ThermalEnvironment := (Fin 5 → ℝ) × ((Fin 5 → ℝ) × State)
abbrev ThermalControls := Parameters × (Fin 5 → V)
abbrev ThermalInput := ThermalEnvironment × ThermalControls

def thermalPath (σ : Fin 5 → ℝ) (α γ : ℝ) (env : ThermalEnvironment)
    (q : ThermalControls) : ℕ → State
  | 0 => env.2.2
  | k+1 => if h : k < 5 then
      thermalStep (σ ⟨k,h⟩) α γ (env.1 ⟨k,h⟩) (env.2.1 ⟨k,h⟩)
        (q.1.1 ⟨k,h⟩) (q.1.2 ⟨k,h⟩) (q.2 ⟨k,h⟩)
        (thermalPath σ α γ env q k)
    else thermalPath σ α γ env q k

def thermalMap (σ : Fin 5 → ℝ) (α γ : ℝ) (p : ThermalInput) : State :=
  thermalPath σ α γ p.1 p.2 5

theorem thermalPath_zero (σ s : Fin 5 → ℝ) (α γ : ℝ) (z : State)
    (q : Parameters) (w : Fin 5 → V) (k : ℕ) :
    thermalPath σ α γ (s,0,z) (q,w) k = path σ s α γ z q k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    by_cases hk : k < 5
    · simpa only [thermalPath,path,dite_eq_left hk,Pi.zero_apply,thermalStep_zero] using
        congrArg (thermalStep (σ ⟨k,hk⟩) α γ (s ⟨k,hk⟩) 0
          (q.1 ⟨k,hk⟩) (q.2 ⟨k,hk⟩) (w ⟨k,hk⟩)) ih
    · simpa only [thermalPath,path,dite_eq_right hk] using ih

theorem thermalMap_zero (σ s : Fin 5 → ℝ) (α γ : ℝ) (z : State)
    (q : Parameters) (w : Fin 5 → V) :
    thermalMap σ α γ ((s,0,z),(q,w)) = map σ s α γ z q :=
  thermalPath_zero σ s α γ z q w 5

theorem thermalPath_analytic {σ : Fin 5 → ℝ} {α γ : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (p : ThermalInput)
    (hs : ∀ i, 0 < p.1.1 i) (ht : ∀ i, 0 < p.2.1.1 i) (k : ℕ) :
    AnalyticAt ℝ (fun y : ThermalInput => thermalPath σ α γ y.1 y.2 k) p := by
  have hsc : AnalyticAt ℝ (fun y : ThermalInput => y.1.1) p :=
    analyticAt_fst.comp analyticAt_fst
  have hd : AnalyticAt ℝ (fun y : ThermalInput => y.1.2.1) p :=
    analyticAt_fst.comp (analyticAt_snd.comp analyticAt_fst)
  have hz : AnalyticAt ℝ (fun y : ThermalInput => y.1.2.2) p :=
    analyticAt_snd.comp (analyticAt_snd.comp analyticAt_fst)
  have htime : AnalyticAt ℝ (fun y : ThermalInput => y.2.1.1) p :=
    analyticAt_fst.comp (analyticAt_fst.comp analyticAt_snd)
  have hL : AnalyticAt ℝ (fun y : ThermalInput => y.2.1.2) p :=
    analyticAt_snd.comp (analyticAt_fst.comp analyticAt_snd)
  have hw : AnalyticAt ℝ (fun y : ThermalInput => y.2.2) p :=
    analyticAt_snd.comp analyticAt_snd
  induction k with
  | zero => exact hz
  | succ k ih =>
    by_cases hk : k < 5
    · simp only [thermalPath,dite_eq_left hk]
      exact thermalStep_analytic hα hγ (analyticAt_pi_iff.mp hsc ⟨k,hk⟩)
        (analyticAt_pi_iff.mp hd ⟨k,hk⟩) (analyticAt_pi_iff.mp htime ⟨k,hk⟩)
        (analyticAt_pi_iff.mp hL ⟨k,hk⟩) (analyticAt_pi_iff.mp hw ⟨k,hk⟩) ih
        (hs ⟨k,hk⟩) (ht ⟨k,hk⟩)
    · simpa only [thermalPath,dite_eq_right hk] using ih

theorem thermalMap_analytic {σ : Fin 5 → ℝ} {α γ : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (p : ThermalInput)
    (hs : ∀ i, 0 < p.1.1 i) (ht : ∀ i, 0 < p.2.1.1 i) :
    AnalyticAt ℝ (thermalMap σ α γ) p := thermalPath_analytic hα hγ p hs ht 5

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Compact C1 convergence of the actual thermal five-gain maps -/

noncomputable section

open Filter Set
open scoped Topology

namespace BoltzmannNonuniqueness.FiveGainMap

attribute [local irreducible] thermalMap

abbrev PositiveEnvironment := {e : ThermalEnvironment // ∀ i, 0 < e.1 i}

def controlDerivative (σ : Fin 5 → ℝ) (α γ : ℝ) (p : ThermalInput) :
    ThermalControls →L[ℝ] State :=
  (fderiv ℝ (thermalMap σ α γ) p).comp (ContinuousLinearMap.inr ℝ _ _)

theorem thermalControl_hasFDerivAt {σ : Fin 5 → ℝ} {α γ : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (env : PositiveEnvironment)
    (q : ThermalControls) (ht : ∀ i, 0 < q.1.1 i) :
    HasFDerivAt (fun u => thermalMap σ α γ (env.val,u))
      (controlDerivative σ α γ (env.val,q)) q := by
  have hd := (thermalMap_analytic (σ := σ) hα hγ (env.val,q) env.property ht).hasStrictFDerivAt.hasFDerivAt
  have hi := (hasFDerivAt_const (𝕜 := ℝ) env.val q).prodMk (hasFDerivAt_id (𝕜 := ℝ) q)
  exact hd.comp q hi

theorem thermalMap_compact_tendsto {σ : Fin 5 → ℝ} {α γ : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) {env : ℕ → PositiveEnvironment}
    {env₀ : PositiveEnvironment} (henv : Tendsto env atTop (𝓝 env₀))
    {K : Set ThermalControls} (hK : IsCompact K)
    (hT : ∀ q ∈ K, ∀ i, 0 < q.1.1 i) :
    TendstoUniformlyOn (fun n q => thermalMap σ α γ ((env n).val,q))
      (fun q => thermalMap σ α γ (env₀.val,q)) atTop K := by
  let F : PositiveEnvironment × K → State :=
    fun p => thermalMap σ α γ (p.1.val,p.2.val)
  have hc : Continuous (fun p : PositiveEnvironment × K => (p.1.val,p.2.val)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)
  have hM : ContinuousOn (thermalMap σ α γ)
      (Set.range (fun r : PositiveEnvironment × K => (r.1.val,r.2.val))) := by
    rintro _ ⟨p,rfl⟩
    exact (thermalMap_analytic (σ := σ) hα hγ (p.1.val,p.2.val) p.1.property
      (hT p.2.val p.2.property)).continuousAt.continuousWithinAt
  have hF : Continuous F := hM.comp_continuous hc (fun p => Set.mem_range_self p)
  exact GainPullback.uniform_on_compact_of_joint_restriction
    (F := fun p : PositiveEnvironment × ThermalControls => thermalMap σ α γ (p.1.val,p.2))
    hK hF henv

theorem thermalDerivative_compact_tendsto {σ : Fin 5 → ℝ} {α γ : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) {env : ℕ → PositiveEnvironment}
    {env₀ : PositiveEnvironment} (henv : Tendsto env atTop (𝓝 env₀))
    {K : Set ThermalControls} (hK : IsCompact K)
    (hT : ∀ q ∈ K, ∀ i, 0 < q.1.1 i) :
    TendstoUniformlyOn (fun n q => controlDerivative σ α γ ((env n).val,q))
      (fun q => controlDerivative σ α γ (env₀.val,q)) atTop K := by
  let F : PositiveEnvironment × K → ThermalControls →L[ℝ] State :=
    fun p => controlDerivative σ α γ (p.1.val,p.2.val)
  have hc : Continuous (fun p : PositiveEnvironment × K => (p.1.val,p.2.val)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)
  have hD : Continuous (fun p : PositiveEnvironment × K =>
      fderiv ℝ (thermalMap σ α γ) (p.1.val,p.2.val)) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact (thermalMap_analytic (σ := σ) hα hγ (p.1.val,p.2.val) p.1.property
      (hT p.2.val p.2.property)).fderiv.continuousAt.comp (f := fun r : PositiveEnvironment × K => (r.1.val,r.2.val))
        hc.continuousAt
  have hF : Continuous F := hD.clm_comp_const (ContinuousLinearMap.inr ℝ _ _)
  exact GainPullback.uniform_on_compact_of_joint_restriction
    (F := fun p : PositiveEnvironment × ThermalControls => controlDerivative σ α γ (p.1.val,p.2))
    hK hF henv

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Exact reduction of the five-gain map at equal collision times -/

noncomputable section

open Matrix
open scoped Matrix
open BoltzmannNonuniqueness.AxialFlow

namespace BoltzmannNonuniqueness.FiveGainMap

def velocityStep (a : ℝ) (L v : V) : V := v+(v-axis a) ⨯₃ L

def velocityPath (a : Fin 5 → ℝ) (L : Fin 5 → V) (v : V) : ℕ → V
  | 0 => v
  | k+1 => if h : k < 5 then velocityStep (a ⟨k,h⟩) (L ⟨k,h⟩)
      (velocityPath a L v k) else velocityPath a L v k

def commonPosition (τ : ℝ) (z : State) : V := z.2.1-(z.1-τ) • z.2.2

def equalTimeSpeeds (σ s : Fin 5 → ℝ) (α γ τ : ℝ) (z : State) : Fin 5 → ℝ :=
  fun i => velocity (σ i) α γ (s i) τ (commonPosition τ z 2)

theorem step_same_time (σ α γ s τ : ℝ) (L x v : V) :
    step σ α γ s τ L (τ,x,v) =
      (τ,x,velocityStep (velocity σ α γ s τ (x 2)) L v) := by
  simp only [step,sub_self,zero_smul,sub_zero,velocityStep]

theorem path_equal_time (σ s : Fin 5 → ℝ) (α γ τ : ℝ) (z : State)
    (L : Fin 5 → V) {k : ℕ} (hk : 0 < k) (hk5 : k ≤ 5) :
    path σ s α γ z ((fun _ => τ),L) k =
      (τ,commonPosition τ z,
        velocityPath (equalTimeSpeeds σ s α γ τ z) L z.2.2 k) := by
  induction k with
  | zero => omega
  | succ k ih =>
    have hlt : k < 5 := by omega
    rw [path,velocityPath,dite_eq_left hlt,dite_eq_left hlt]
    cases k with
    | zero => rfl
    | succ k =>
      rw [ih (by omega) (by omega),step_same_time]
      rfl

theorem map_equal_time (σ s : Fin 5 → ℝ) (α γ τ : ℝ) (z : State)
    (L : Fin 5 → V) :
    map σ s α γ z ((fun _ => τ),L) =
      (τ,commonPosition τ z,
        velocityPath (equalTimeSpeeds σ s α γ τ z) L z.2.2 5) :=
  path_equal_time σ s α γ τ z L (by decide) (by decide)

theorem map_equal_time_position (σ s : Fin 5 → ℝ) (α γ τ : ℝ) (z : State)
    (L : Fin 5 → V) :
    (map σ s α γ z ((fun _ => τ),L)).2.1 = commonPosition τ z := by
  rw [map_equal_time]

theorem map_equal_time_position_derivative (σ s : Fin 5 → ℝ) (α γ τ : ℝ)
    (z : State) (L : Fin 5 → V) :
    HasFDerivAt (fun M : Fin 5 → V => (map σ s α γ z ((fun _ => τ),M)).2.1)
      (0 : (Fin 5 → V) →L[ℝ] V) L := by
  have he : (fun M : Fin 5 → V => (map σ s α γ z ((fun _ => τ),M)).2.1) =
      (fun _ => commonPosition τ z) := funext (map_equal_time_position σ s α γ τ z)
  rw [he]
  exact hasFDerivAt_const _ _

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Position derivatives at the equal-time five-collision configuration -/

noncomputable section

open Matrix

namespace BoltzmannNonuniqueness.FiveGainWitness

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

def endPosition (t₀ : ℝ) (x₀ v₀ : W) (t : Fin 5 → ℝ) (v : Fin 4 → W) : W :=
  x₀-(t₀-t 0) • v₀-∑ i : Fin 4, (t i.castSucc-t i.succ) • v i

def positionDirection (v₀ : W) (dt : Fin 5 → ℝ) (v : Fin 4 → W) : W :=
  dt 0 • v₀-∑ i : Fin 4, (dt i.castSucc-dt i.succ) • v i

theorem endPosition_equal_time (t₀ τ : ℝ) (x₀ v₀ : W) (v : Fin 4 → W) :
    endPosition t₀ x₀ v₀ (fun _ => τ) v = x₀-(t₀-τ) • v₀ := by
  simp [endPosition]

/-- Dependence of the velocities contributes zero to the position derivative
when all formal free-flight durations vanish. -/
theorem endPosition_hasDerivAt (t₀ τ : ℝ) (x₀ v₀ : W)
    {t : ℝ → Fin 5 → ℝ} {v : ℝ → Fin 4 → W}
    {dt : Fin 5 → ℝ} {dv : Fin 4 → W}
    (ht : ∀ i, HasDerivAt (fun r => t r i) (dt i) 0)
    (hv : ∀ i, HasDerivAt (fun r => v r i) (dv i) 0)
    (heq : ∀ i, t 0 i = τ) :
    HasDerivAt (fun r => endPosition t₀ x₀ v₀ (t r) (v r))
      (positionDirection v₀ dt (v 0)) 0 := by
  have hs (i : Fin 4) : HasDerivAt
      (fun r => (t r i.castSucc-t r i.succ) • v r i)
      ((dt i.castSucc-dt i.succ) • v 0 i) 0 := by
    have h := ((ht i.castSucc).sub (ht i.succ)).smul (hv i)
    change HasDerivAt (fun r => (t r i.castSucc-t r i.succ) • v r i)
      ((t 0 i.castSucc-t 0 i.succ) • dv i +
        (dt i.castSucc-dt i.succ) • v 0 i) 0 at h
    simpa only [heq,sub_self,zero_smul,zero_add] using h
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hs i)
  have hfirst := ((hasDerivAt_const 0 t₀).sub (ht 0)).smul_const v₀
  have h := ((hasDerivAt_const 0 x₀).sub hfirst).sub hsum
  change HasDerivAt (fun r => endPosition t₀ x₀ v₀ (t r) (v r))
    (0-(0-dt 0) • v₀-∑ i, (dt i.castSucc-dt i.succ) • v 0 i) 0 at h
  simpa only [positionDirection,zero_sub,neg_smul,neg_neg] using h

theorem direction_first (v₀ : W) (v : Fin 4 → W) :
    positionDirection v₀ ![1,0,0,0,0] v = v₀-v 0 := by
  simp [positionDirection,Fin.sum_univ_succ]

theorem direction_second (v₀ : W) (v : Fin 4 → W) :
    positionDirection v₀ ![0,1,0,0,0] v = v 0-v 1 := by
  simp [positionDirection,Fin.sum_univ_succ]
  abel

theorem direction_third (v₀ : W) (v : Fin 4 → W) :
    positionDirection v₀ ![0,0,1,0,0] v = v 1-v 2 := by
  simp [positionDirection,Fin.sum_univ_succ]
  abel

end BoltzmannNonuniqueness.FiveGainWitness

end

end

section

/-! # Position formula and time derivatives for the actual collision path -/

noncomputable section

open Matrix
open BoltzmannNonuniqueness.FiveGainWitness

namespace BoltzmannNonuniqueness.FiveGainMap

theorem path_succ_time (σ s : Fin 5 → ℝ) (α γ : ℝ) (z : State)
    (q : Parameters) (k : ℕ) (hk : k < 5) :
    (path σ s α γ z q (k+1)).1 = q.1 ⟨k,hk⟩ := by
  simp only [path,dite_eq_left hk,step]

theorem path_succ_position (σ s : Fin 5 → ℝ) (α γ : ℝ) (z : State)
    (q : Parameters) (k : ℕ) (hk : k < 5) :
    (path σ s α γ z q (k+1)).2.1 = (path σ s α γ z q k).2.1-
      ((path σ s α γ z q k).1-q.1 ⟨k,hk⟩) • (path σ s α γ z q k).2.2 := by
  simp only [path,dite_eq_left hk,step]

theorem map_position (σ s : Fin 5 → ℝ) (α γ : ℝ) (z : State) (q : Parameters) :
    (map σ s α γ z q).2.1 = endPosition z.1 z.2.1 z.2.2 q.1
      (fun i : Fin 4 => (path σ s α γ z q (i.val+1)).2.2) := by
  unfold map endPosition
  rw [path_succ_position σ s α γ z q 4 (by decide),
    path_succ_position σ s α γ z q 3 (by decide),
    path_succ_position σ s α γ z q 2 (by decide),
    path_succ_position σ s α γ z q 1 (by decide),
    path_succ_position σ s α γ z q 0 (by decide),
    path_succ_time σ s α γ z q 3 (by decide),
    path_succ_time σ s α γ z q 2 (by decide),
    path_succ_time σ s α γ z q 1 (by decide),
    path_succ_time σ s α γ z q 0 (by decide)]
  rw [show path σ s α γ z q 0 = z from rfl]
  simp only [Fin.sum_univ_succ,Fin.val_zero,Fin.val_succ,Fin.castSucc_zero,
    Fin.succ_zero_eq_one,Nat.zero_add,Finset.univ_eq_empty,Finset.sum_empty,add_zero,
    Nat.reduceAdd]
  abel

theorem map_position_hasDerivAt {σ s : Fin 5 → ℝ} {α γ τ : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : ∀ i, 0 < s i) (hτ : 0 < τ)
    (z : State) {q : ℝ → Parameters} {dq : Parameters}
    (hq : HasDerivAt q dq 0) (ht : ∀ i, (q 0).1 i = τ) :
    HasDerivAt (fun r => (map σ s α γ z (q r)).2.1)
      (positionDirection z.2.2 dq.1
        (fun i : Fin 4 => (path σ s α γ z (q 0) (i.val+1)).2.2)) 0 := by
  have ha (i : Fin 4) := path_analytic (σ := σ) hα hγ hs z (q 0)
    (fun j => by rw [ht]; exact hτ) (i.val+1)
  have hv (i : Fin 4) := ((ha i).hasStrictFDerivAt.hasFDerivAt.snd.snd).comp_hasDerivAt 0 hq
  have ht' (i : Fin 5) := ((ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin 5 => ℝ) i).hasFDerivAt).comp_hasDerivAt
    0 hq.fst
  have h := endPosition_hasDerivAt z.1 τ z.2.1 z.2.2 ht' hv ht
  change HasDerivAt (fun r => endPosition z.1 z.2.1 z.2.2 (q r).1
    (fun i : Fin 4 => (path σ s α γ z (q r) (i.val+1)).2.2))
    (positionDirection z.2.2 dq.1
      (fun i : Fin 4 => (path σ s α γ z (q 0) (i.val+1)).2.2)) 0 at h
  simpa only [map_position] using h

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Rotations about the cold velocity axis -/

noncomputable section

open Matrix
open scoped Matrix

namespace BoltzmannNonuniqueness.FiveGainMap

def rotationLinear (c s : ℝ) : V →ₗ[ℝ] V where
  toFun v := ![c*v 0-s*v 1,s*v 0+c*v 1,v 2]
  map_add' v w := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' a v := by
    ext i
    fin_cases i <;> simp <;> ring

def rotation (c s : ℝ) : V →L[ℝ] V := (rotationLinear c s).toContinuousLinearMap

theorem rotation_apply (c s : ℝ) (v : V) :
    rotation c s v = ![c*v 0-s*v 1,s*v 0+c*v 1,v 2] := rfl

@[simp] theorem rotation_axis (c s a : ℝ) : rotation c s (axis a) = axis a := by
  ext i
  fin_cases i <;> simp [rotation_apply,axis]

@[simp] theorem rotation_axial (c s : ℝ) (v : V) : rotation c s v 2 = v 2 := rfl

theorem rotation_cross {c s : ℝ} (hcs : c^2+s^2 = 1) (v w : V) :
    rotation c s (v ⨯₃ w) = rotation c s v ⨯₃ rotation c s w := by
  ext i
  fin_cases i
  · simp [rotation_apply,cross_apply]
    ring
  · simp [rotation_apply,cross_apply]
    ring
  · simp [rotation_apply,cross_apply]
    linear_combination -(v 0*w 1-v 1*w 0)*hcs

theorem rotation_inverse {c s : ℝ} (hcs : c^2+s^2 = 1) (v : V) :
    rotation c (-s) (rotation c s v) = v := by
  ext i
  fin_cases i
  · simp [rotation_apply]
    linear_combination v 0*hcs
  · simp [rotation_apply]
    linear_combination v 1*hcs
  · rfl

theorem rotation_surjective {c s : ℝ} (hcs : c^2+s^2 = 1) :
    Function.Surjective (rotation c s) := by
  intro v
  refine ⟨rotation c (-s) v,?_⟩
  have hn : c^2+(-s)^2 = 1 := by simpa using hcs
  simpa only [neg_neg] using rotation_inverse hn v

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Covariance of the actual five-gain map under axial rotations -/

noncomputable section

namespace BoltzmannNonuniqueness.FiveGainMap

def rotateAngles (c s : ℝ) : (Fin 5 → V) →L[ℝ] (Fin 5 → V) :=
  ContinuousLinearMap.pi (fun i => (rotation c s).comp (ContinuousLinearMap.proj i))

def rotateParameters (c s : ℝ) : Parameters →L[ℝ] Parameters :=
  (ContinuousLinearMap.id ℝ (Fin 5 → ℝ)).prodMap (rotateAngles c s)

def rotateState (c s : ℝ) : State →L[ℝ] State :=
  (ContinuousLinearMap.id ℝ ℝ).prodMap ((rotation c s).prodMap (rotation c s))

theorem rotateParameters_apply (c s : ℝ) (q : Parameters) :
    rotateParameters c s q = (q.1,fun i => rotation c s (q.2 i)) := rfl

theorem rotateState_apply (c s : ℝ) (z : State) :
    rotateState c s z = (z.1,rotation c s z.2.1,rotation c s z.2.2) := rfl

theorem rotateState_surjective {c s : ℝ} (hcs : c^2+s^2 = 1) :
    Function.Surjective (rotateState c s) := by
  rintro ⟨t,x,v⟩
  obtain ⟨x',hx'⟩ := rotation_surjective hcs x
  obtain ⟨v',hv'⟩ := rotation_surjective hcs v
  exact ⟨(t,x',v'),by simp only [rotateState_apply,hx',hv']⟩

theorem step_rotation {c s : ℝ} (hcs : c^2+s^2 = 1)
    (σ α γ μ t : ℝ) (L : V) (z : State) :
    step σ α γ μ t (rotation c s L) (rotateState c s z) =
      rotateState c s (step σ α γ μ t L z) := by
  let x := z.2.1-(z.1-t) • z.2.2
  have hx : rotation c s z.2.1-(z.1-t) • rotation c s z.2.2 = rotation c s x := by
    simp only [x,map_sub,map_smul]
  have hn (a : ℝ) : rotation c s z.2.2-axis a = rotation c s (z.2.2-axis a) := by
    simp only [map_sub,rotation_axis]
  simp only [step,rotateState_apply,hx,rotation_axial]
  refine Prod.ext rfl ?_
  refine Prod.ext rfl ?_
  rw [hn,← rotation_cross hcs,← map_add]

theorem path_rotation {c s : ℝ} (hcs : c^2+s^2 = 1)
    (σ μ : Fin 5 → ℝ) (α γ : ℝ) (z : State) (q : Parameters) (k : ℕ) :
    path σ μ α γ (rotateState c s z) (rotateParameters c s q) k =
      rotateState c s (path σ μ α γ z q k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    by_cases hk : k < 5
    · simp only [path,dite_eq_left hk]
      change step (σ ⟨k,hk⟩) α γ (μ ⟨k,hk⟩) (q.1 ⟨k,hk⟩)
        (rotation c s (q.2 ⟨k,hk⟩))
        (path σ μ α γ (rotateState c s z) (rotateParameters c s q) k) = _
      rw [ih,step_rotation hcs]
    · simpa only [path,dite_eq_right hk] using ih

theorem map_rotation {c s : ℝ} (hcs : c^2+s^2 = 1)
    (σ μ : Fin 5 → ℝ) (α γ : ℝ) (z : State) (q : Parameters) :
    map σ μ α γ (rotateState c s z) (rotateParameters c s q) =
      rotateState c s (map σ μ α γ z q) :=
  path_rotation hcs σ μ α γ z q 5

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # The connected positive-time domain of the five-gain map -/

noncomputable section

open Set

namespace BoltzmannNonuniqueness.FiveGainMap

def positiveDomain : Set Parameters := {q | ∀ i, 0 < q.1 i}

def timeProjection (i : Fin 5) : Parameters →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ _ _)

theorem positiveDomain_eq : positiveDomain = ⋂ i : Fin 5, {q | 0 < timeProjection i q} := by
  ext q
  simp [positiveDomain,timeProjection]

theorem positiveDomain_open : IsOpen positiveDomain := by
  rw [positiveDomain_eq]
  exact isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const (timeProjection i).continuous)

theorem positiveDomain_convex : Convex ℝ positiveDomain := by
  rw [positiveDomain_eq]
  apply convex_iInter
  intro i
  exact (convex_Ioi (0 : ℝ)).linear_preimage (timeProjection i).toLinearMap

theorem positiveDomain_preconnected : IsPreconnected positiveDomain :=
  positiveDomain_convex.isPreconnected

theorem map_analyticOnNhd {σ s : Fin 5 → ℝ} {α γ : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : ∀ i, 0 < s i) (z : State) :
    AnalyticOnNhd ℝ (map σ s α γ z) positiveDomain :=
  fun q hq => map_analytic hα hγ hs z q hq

theorem map_derivative_analyticOnNhd {σ s : Fin 5 → ℝ} {α γ : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : ∀ i, 0 < s i) (z : State) :
    AnalyticOnNhd ℝ (fderiv ℝ (map σ s α γ z)) positiveDomain :=
  (map_analyticOnNhd hα hγ hs z).fderiv

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # The two final angular blocks span all three velocity directions -/

noncomputable section

open Matrix Function
open scoped Matrix

namespace BoltzmannNonuniqueness.FiveGainWitness

theorem angular_pair_surjective {X Y : ℝ} (hXY : 0 < X^2+Y^2) (a b : ℝ) :
    Surjective (fun L : V × V =>
      ![X,Y,a] ⨯₃ L.1 + ![X-Y,Y+X,b] ⨯₃ L.2) := by
  intro w
  have hD : X^2+Y^2 ≠ 0 := hXY.ne'
  by_cases hX : X = 0
  · have hY : Y ≠ 0 := by
      intro hY
      simp [hX,hY] at hXY
    let v := w 1+a*w 2/Y
    refine ⟨(![-w 2/Y,0,(w 0-v)/Y],![0,0,v/Y]),?_⟩
    funext i
    fin_cases i <;> simp [cross_apply,Matrix.cons_val,hX,v] <;>
      field_simp [hY] <;> ring
  · let u := w 0+a*w 2/X
    let c := ((Y-X)*u-(X+Y)*w 1)/(X^2+Y^2)
    let d := (X*u+Y*w 1)/(X^2+Y^2)
    refine ⟨(![0,w 2/X,c],![0,0,d]),?_⟩
    funext i
    fin_cases i <;> simp [cross_apply,Matrix.cons_val,u,c,d] <;>
      field_simp [hX,hD] <;> ring

theorem final_angular_surjective (R b a₄ a₅ : ℝ) :
    Surjective (fun L : V × V =>
      ![afterThirdX R b,afterThirdY R b,a₄] ⨯₃ L.1 +
      ![afterThirdX R b-afterThirdY R b,afterThirdY R b+afterThirdX R b,a₅] ⨯₃ L.2) :=
  angular_pair_surjective (afterThird_transverse_pos R b) a₄ a₅

end BoltzmannNonuniqueness.FiveGainWitness

end

end

section

/-! # Angular parameters realizing the nondegenerate five-collision path -/

noncomputable section

open Matrix
open scoped Matrix
open BoltzmannNonuniqueness.FiveGainWitness

namespace BoltzmannNonuniqueness.FiveGainMap

def witnessVelocities (R z b : ℝ) : Fin 6 → V :=
  ![![R,0,z], ![R,1,z], ![R+1,1-R,z],
    ![afterThirdX R b,afterThirdY R b,z+smallFactor R b*transverseSquare R],
    ![afterThirdX R b-afterThirdY R b,afterThirdY R b+afterThirdX R b,
      z+smallFactor R b*transverseSquare R],
    ![afterThirdX R b-afterThirdY R b,afterThirdY R b+afterThirdX R b,
      z+smallFactor R b*transverseSquare R]]

def witnessNormal (R z : ℝ) (a : Fin 5 → ℝ) (i : Fin 5) : V :=
  witnessVelocities R z (z-a 2) i.castSucc-axis (a i)

def witnessIncrement (R z : ℝ) (a : Fin 5 → ℝ) (i : Fin 5) : V :=
  witnessVelocities R z (z-a 2) i.succ-witnessVelocities R z (z-a 2) i.castSucc

def witnessAngles (R z : ℝ) (a : Fin 5 → ℝ) (i : Fin 5) : V :=
  (-(witnessNormal R z a i ⬝ᵥ witnessNormal R z a i)⁻¹) •
    (witnessNormal R z a i ⨯₃ witnessIncrement R z a i)

theorem witnessNormal_ne_zero {R : ℝ} (hR : 0 < R) (z : ℝ) (a : Fin 5 → ℝ)
    (i : Fin 5) : witnessNormal R z a i ≠ 0 := by
  have hX : 0 < afterThirdX R (z-a 2) :=
    mul_pos (transverse_factor_pos R _) (by linarith)
  have hXY : 0 < afterThirdX R (z-a 2)-afterThirdY R (z-a 2) := by
    have h := mul_pos (transverse_factor_pos R (z-a 2)) hR
    unfold afterThirdX afterThirdY
    nlinarith
  intro he
  have h0 := congrFun he 0
  fin_cases i <;>
    simp [witnessNormal,witnessVelocities,axis,Matrix.cons_val] at h0
  all_goals linarith

theorem witness_perpendicular (R z : ℝ) (a : Fin 5 → ℝ) (i : Fin 5) :
    witnessNormal R z a i ⬝ᵥ witnessIncrement R z a i = 0 := by
  fin_cases i <;>
    simp [witnessNormal,witnessIncrement,witnessVelocities,axis,
      Matrix.cons_val,afterThirdX,afterThirdY,transverseSquare] <;> ring

theorem witnessAngles_realize {R : ℝ} (hR : 0 < R) (z : ℝ) (a : Fin 5 → ℝ)
    (i : Fin 5) :
    witnessNormal R z a i ⨯₃ witnessAngles R z a i = witnessIncrement R z a i :=
  cross_represents (witnessNormal_ne_zero hR z a i) (witness_perpendicular R z a i)

theorem witnessAngles_last (R z : ℝ) (a : Fin 5 → ℝ) :
    witnessAngles R z a 4 = 0 := by
  simp [witnessAngles,witnessIncrement,witnessVelocities]

theorem witness_velocityPath {R : ℝ} (hR : 0 < R) (z : ℝ) (a : Fin 5 → ℝ)
    (k : ℕ) (hk : k ≤ 5) :
    velocityPath a (witnessAngles R z a) ![R,0,z] k =
      witnessVelocities R z (z-a 2) ⟨k,by omega⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hlt : k < 5 := by omega
    rw [velocityPath,dite_eq_left hlt,ih (by omega)]
    change witnessVelocities R z (z-a 2) (⟨k,hlt⟩ : Fin 5).castSucc +
      witnessNormal R z a ⟨k,hlt⟩ ⨯₃ witnessAngles R z a ⟨k,hlt⟩ = _
    rw [witnessAngles_realize hR]
    unfold witnessIncrement
    abel

theorem map_at_witness {R : ℝ} (hR : 0 < R) (z t₀ τ α γ : ℝ) (x₀ : V)
    (σ s : Fin 5 → ℝ) :
    let a := equalTimeSpeeds σ s α γ τ (t₀,x₀,![R,0,z])
    map σ s α γ (t₀,x₀,![R,0,z]) ((fun _ => τ),witnessAngles R z a) =
      (τ,commonPosition τ (t₀,x₀,![R,0,z]),witnessVelocities R z (z-a 2) 5) := by
  dsimp only
  rw [map_equal_time,witness_velocityPath hR z _ 5 (by decide)]
  rfl

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # The last two angular derivatives of the actual equal-time collision path -/

noncomputable section

open Matrix
open scoped Matrix

namespace BoltzmannNonuniqueness.FiveGainMap

theorem cross_hasDerivAt {f g : ℝ → V} {f' g' : V} {r : ℝ}
    (hf : HasDerivAt f f' r) (hg : HasDerivAt g g' r) :
    HasDerivAt (fun y => f y ⨯₃ g y) (f' ⨯₃ g r+f r ⨯₃ g') r := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · change HasDerivAt (fun y => f y 1*g y 2-f y 2*g y 1)
      (f' 1*g r 2-f' 2*g r 1+(f r 1*g' 2-f r 2*g' 1)) r
    convert ((hasDerivAt_pi.mp hf 1).mul (hasDerivAt_pi.mp hg 2)).sub
      ((hasDerivAt_pi.mp hf 2).mul (hasDerivAt_pi.mp hg 1)) using 1
    ring
  · change HasDerivAt (fun y => f y 2*g y 0-f y 0*g y 2)
      (f' 2*g r 0-f' 0*g r 2+(f r 2*g' 0-f r 0*g' 2)) r
    convert ((hasDerivAt_pi.mp hf 2).mul (hasDerivAt_pi.mp hg 0)).sub
      ((hasDerivAt_pi.mp hf 0).mul (hasDerivAt_pi.mp hg 2)) using 1
    ring
  · change HasDerivAt (fun y => f y 0*g y 1-f y 1*g y 0)
      (f' 0*g r 1-f' 1*g r 0+(f r 0*g' 1-f r 1*g' 0)) r
    convert ((hasDerivAt_pi.mp hf 0).mul (hasDerivAt_pi.mp hg 1)).sub
      ((hasDerivAt_pi.mp hf 1).mul (hasDerivAt_pi.mp hg 0)) using 1
    ring

def finalVelocity (a₄ a₅ : ℝ) (v₃ L₄ L₅ : V) : V :=
  let v₄ := velocityStep a₄ L₄ v₃
  velocityStep a₅ L₅ v₄

theorem finalVelocity_hasDerivAt (a₄ a₅ : ℝ) (v₃ L₄ A B : V) :
    HasDerivAt (fun r : ℝ => finalVelocity a₄ a₅ v₃ (L₄+r • A) (r • B))
      ((v₃-axis a₄) ⨯₃ A + (velocityStep a₄ L₄ v₃-axis a₅) ⨯₃ B) 0 := by
  have hL : HasDerivAt (fun r : ℝ => L₄+r • A) A 0 := by
    have h := (hasDerivAt_const (0 : ℝ) L₄).add
      ((hasDerivAt_id (0 : ℝ)).smul_const A)
    change HasDerivAt (fun r : ℝ => L₄+r • A) (0+1 • A) 0 at h
    simpa only [zero_add,one_smul] using h
  have h₄ : HasDerivAt (fun r : ℝ => velocityStep a₄ (L₄+r • A) v₃)
      ((v₃-axis a₄) ⨯₃ A) 0 := by
    have h := (hasDerivAt_const (0 : ℝ) v₃).add
      (cross_hasDerivAt (hasDerivAt_const (0 : ℝ) (v₃-axis a₄)) hL)
    change HasDerivAt (fun r : ℝ => velocityStep a₄ (L₄+r • A) v₃)
      (0+(0 ⨯₃ (L₄+0 • A)+(v₃-axis a₄) ⨯₃ A)) 0 at h
    simpa only [map_zero,LinearMap.zero_apply,zero_add] using h
  have hB : HasDerivAt (fun r : ℝ => r • B) B 0 := by
    have h := (hasDerivAt_id (0 : ℝ)).smul_const B
    change HasDerivAt (fun r : ℝ => r • B) (1 • B) 0 at h
    simpa only [one_smul] using h
  have h := h₄.add (cross_hasDerivAt (h₄.sub_const (axis a₅)) hB)
  change HasDerivAt (fun r : ℝ => finalVelocity a₄ a₅ v₃ (L₄+r • A) (r • B))
    ((v₃-axis a₄) ⨯₃ A+(((v₃-axis a₄) ⨯₃ A) ⨯₃ (0 • B)+
      (velocityStep a₄ (L₄+0 • A) v₃-axis a₅) ⨯₃ B)) 0 at h
  simpa only [zero_smul,add_zero,map_zero,zero_add] using h

def varyLastTwo (L : Fin 5 → V) (A B : V) (r : ℝ) : Fin 5 → V :=
  ![L 0,L 1,L 2,L 3+r • A,r • B]

theorem velocityPath_varyLastTwo (a : Fin 5 → ℝ) (L : Fin 5 → V) (v A B : V) (r : ℝ) :
    velocityPath a (varyLastTwo L A B r) v 5 =
      finalVelocity (a 3) (a 4) (velocityPath a L v 3) (L 3+r • A) (r • B) := by
  simp only [velocityPath,varyLastTwo,finalVelocity]
  rfl

theorem map_last_angular_hasDerivAt (σ s : Fin 5 → ℝ) (α γ τ : ℝ) (z : State)
    (L : Fin 5 → V) (A B : V) :
    let a := equalTimeSpeeds σ s α γ τ z
    let v₃ := velocityPath a L z.2.2 3
    HasDerivAt (fun r : ℝ => (map σ s α γ z
      ((fun _ => τ),varyLastTwo L A B r)).2.2)
      ((v₃-axis (a 3)) ⨯₃ A + (velocityStep (a 3) (L 3) v₃-axis (a 4)) ⨯₃ B) 0 := by
  dsimp only
  simpa only [map_equal_time,velocityPath_varyLastTwo] using
    finalVelocity_hasDerivAt (equalTimeSpeeds σ s α γ τ z 3)
      (equalTimeSpeeds σ s α γ τ z 4)
      (velocityPath (equalTimeSpeeds σ s α γ τ z) L z.2.2 3) (L 3) A B

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Derivative blocks of the actual five-gain map -/

noncomputable section

open Matrix
open scoped Matrix
open BoltzmannNonuniqueness.FiveGainWitness

namespace BoltzmannNonuniqueness.FiveGainMap

theorem map_time (σ s : Fin 5 → ℝ) (α γ : ℝ) (z : State) (q : Parameters) :
    (map σ s α γ z q).1 = q.1 4 := path_succ_time σ s α γ z q 4 (by decide)

theorem affineParameter_derivative (q d : Parameters) :
    HasDerivAt (fun r : ℝ => q+r • d) d 0 := by
  have h := (hasDerivAt_const (0 : ℝ) q).add ((hasDerivAt_id (0 : ℝ)).smul_const d)
  change HasDerivAt (fun r : ℝ => q+r • d) (0+1 • d) 0 at h
  simpa only [zero_add,one_smul] using h

theorem apply_eq_of_line {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Parameters → F} {D : Parameters →L[ℝ] F} {q d : Parameters} {v : F}
    (hf : HasFDerivAt f D q) (hl : HasDerivAt (fun r : ℝ => f (q+r • d)) v 0) :
    D d = v := by
  have h := hf.comp_hasDerivAt_of_eq 0 (affineParameter_derivative q d) (by simp)
  exact h.unique hl

theorem map_derivative_time {σ s : Fin 5 → ℝ} {α γ : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : ∀ i, 0 < s i)
    (z : State) (q d : Parameters) (ht : ∀ i, 0 < q.1 i) :
    (fderiv ℝ (map σ s α γ z) q d).1 = d.1 4 := by
  have hq := affineParameter_derivative q d
  have hd := (map_analytic (σ := σ) hα hγ hs z q ht).hasStrictFDerivAt.hasFDerivAt
  have hm := hd.fst.comp_hasDerivAt_of_eq 0 hq (by simp)
  have hqfst := (hasFDerivAt_fst (𝕜 := ℝ) (p := q+0 • d)).comp_hasDerivAt 0 hq
  have ht' := hasDerivAt_pi.mp hqfst 4
  change HasDerivAt (fun r => (map σ s α γ z (q+r • d)).1)
    (fderiv ℝ (map σ s α γ z) q d).1 0 at hm
  simp only [map_time] at hm
  exact hm.unique ht'

theorem map_derivative_position {σ s : Fin 5 → ℝ} {α γ τ : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : ∀ i, 0 < s i) (hτ : 0 < τ)
    (z : State) (q d : Parameters) (ht : ∀ i, q.1 i = τ) :
    (fderiv ℝ (map σ s α γ z) q d).2.1 =
      positionDirection z.2.2 d.1
        (fun i : Fin 4 => (path σ s α γ z q (i.val+1)).2.2) := by
  have hq := affineParameter_derivative q d
  have hpos := map_position_hasDerivAt (σ := σ) hα hγ hs hτ z hq (by simpa using ht)
  simp only [zero_smul,add_zero] at hpos
  have hd := (map_analytic (σ := σ) hα hγ hs z q
    (fun i => by rw [ht]; exact hτ)).hasStrictFDerivAt.hasFDerivAt
  exact apply_eq_of_line hd.snd.fst hpos

def lastAngularDirection (A B : V) : Parameters := (0,![0,0,0,A,B])

theorem varyLastTwo_eq {L : Fin 5 → V} (hL : L 4 = 0) (A B : V) (r : ℝ) :
    ((fun _ => (0 : ℝ)),varyLastTwo L A B r) =
      ((fun _ => (0 : ℝ)),L)+r • lastAngularDirection A B := by
  apply Prod.ext
  · ext i
    simp [lastAngularDirection]
  · ext i j
    fin_cases i <;> simp [varyLastTwo,lastAngularDirection,vecHead,vecTail,hL]

theorem map_derivative_last_angular {σ s : Fin 5 → ℝ} {α γ τ : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : ∀ i, 0 < s i) (hτ : 0 < τ)
    (z : State) (L : Fin 5 → V) (hL : L 4 = 0) (A B : V) :
    let a := equalTimeSpeeds σ s α γ τ z
    let v₃ := velocityPath a L z.2.2 3
    (fderiv ℝ (map σ s α γ z) ((fun _ => τ),L) (lastAngularDirection A B)).2.2 =
      (v₃-axis (a 3)) ⨯₃ A+(velocityStep (a 3) (L 3) v₃-axis (a 4)) ⨯₃ B := by
  dsimp only
  let q : Parameters := ((fun _ => τ),L)
  have hd := (map_analytic (σ := σ) hα hγ hs z q
    (fun _ => hτ)).hasStrictFDerivAt.hasFDerivAt
  have he (r : ℝ) : q+r • lastAngularDirection A B =
      ((fun _ => τ),varyLastTwo L A B r) := by
    apply Prod.ext
    · ext i
      simp [q,lastAngularDirection]
    · exact (congrArg Prod.snd (varyLastTwo_eq hL A B r)).symm
  have hl := map_last_angular_hasDerivAt σ s α γ τ z L A B
  simp only [← he] at hl
  exact apply_eq_of_line hd.snd.snd hl

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # The first three time directions span all positions at the witness -/

noncomputable section

open Matrix Function
open scoped Matrix
open BoltzmannNonuniqueness.FiveGainWitness

namespace BoltzmannNonuniqueness.FiveGainMap

def firstTimeDirection (c : V) : Parameters := (![c 0,c 1,c 2,0,0],0)

def witnessPosition (R b : ℝ) (c : V) : V :=
  -(c 0 • first+c 1 • second R+c 2 • third R b)

theorem witnessPosition_surjective (R b : ℝ) : Surjective (witnessPosition R b) := by
  let M := Matrix.of ![first,second R,third R b]
  have hM : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).mpr
    (isUnit_iff_ne_zero.mpr (first_three_det_ne_zero R b))
  have hs := (Matrix.vecMul_surjective_iff_isUnit (A := M)).mpr hM
  intro w
  obtain ⟨c,hc⟩ := hs (-w)
  refine ⟨c,?_⟩
  have he : c 0 • first+c 1 • second R+c 2 • third R b = -w := by
    rw [← hc]
    ext i
    simp [Matrix.vecMul,dotProduct,Fin.sum_univ_succ,M]
    ring
  simp only [witnessPosition,he,neg_neg]

theorem positionDirection_at_witness (R z : ℝ) (a : Fin 5 → ℝ) (c : V) :
    positionDirection ![R,0,z] (firstTimeDirection c).1
      (fun i : Fin 4 => witnessVelocities R z (z-a 2) ⟨i.val+1,by omega⟩) =
      witnessPosition R (z-a 2) c := by
  ext i
  fin_cases i <;>
    simp [positionDirection,firstTimeDirection,witnessVelocities,witnessPosition,
      first,second,third,afterThirdX,afterThirdY,Fin.sum_univ_succ] <;> ring

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Combining the time, position, and angular derivative blocks -/

noncomputable section

open Function
open scoped Matrix

namespace BoltzmannNonuniqueness.FiveGainMap

theorem surjective_of_blocks (T : Parameters →L[ℝ] State)
    (ht : ∀ d, (T d).1 = d.1 4)
    (hp : Surjective (fun c => (T (firstTimeDirection c)).2.1))
    (hz : ∀ A B, (T (lastAngularDirection A B)).2.1 = 0)
    (hv : Surjective (fun p : V × V => (T (lastAngularDirection p.1 p.2)).2.2)) :
    Surjective T := by
  rintro ⟨t,x,v⟩
  let e : Parameters := (![0,0,0,0,1],0)
  let base := t • e
  obtain ⟨c,hc⟩ := hp (x-(T base).2.1)
  change (T (firstTimeDirection c)).2.1 = x-(T base).2.1 at hc
  let q := base+firstTimeDirection c
  obtain ⟨⟨A,B⟩,hAB⟩ := hv (v-(T q).2.2)
  change (T (lastAngularDirection A B)).2.2 = v-(T q).2.2 at hAB
  refine ⟨q+lastAngularDirection A B,?_⟩
  apply Prod.ext
  · rw [ht]
    simp [q,base,e,firstTimeDirection,lastAngularDirection]
  · apply Prod.ext
    · change (T (q+lastAngularDirection A B)).2.1 = x
      rw [map_add]
      change (T q).2.1+(T (lastAngularDirection A B)).2.1 = x
      rw [hz,add_zero]
      change (T (base+firstTimeDirection c)).2.1 = x
      rw [map_add]
      change (T base).2.1+(T (firstTimeDirection c)).2.1 = x
      rw [hc]
      abel
    · rw [map_add]
      change (T q).2.2+(T (lastAngularDirection A B)).2.2 = v
      rw [hAB]
      abel

end BoltzmannNonuniqueness.FiveGainMap

end

end

end OAI
