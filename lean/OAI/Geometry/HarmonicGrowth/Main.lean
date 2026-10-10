import OAI.Geometry.HarmonicGrowth.Growth

namespace OAI

noncomputable section


namespace HarmonicCounterexample.Angular
open Module Matrix Berger Cartesian LinearODE
open scoped ContDiff Topology
variable {n l : ℕ} {ι : Type*} [Fintype ι]

/-- The genuine center-regular ODE solution in the actual angular polynomial space. -/
def regularValue (J : ℝ → ComplexStructure (Fin n)) (l : ℕ)
    (c q d : ℝ → ℝ) (P : harmonicPolynomials n l) (t : ℝ) : harmonicPolynomials n l :=
  value (fun t => angularOperator (J t) l (c t) (q t)) d l P t

/-- Evaluating the actual global flow as a function on R^n. -/
def regularHarmonic (B : Basis ι ℝ (harmonicPolynomials n l))
    (J : ℝ → ComplexStructure (Fin n)) (c q d : ℝ → ℝ)
    (P : harmonicPolynomials n l) : Space n → ℝ :=
  synthesized l (fun i => evaluate (B i : PolynomialSpace n))
    (fun t => coordinates B (regularValue J l c q d P t))

variable {J : ℝ → ComplexStructure (Fin n)} {c q d : ℝ → ℝ}
variable (hA : ContDiff ℝ ∞ (fun t => angularOperator (J t) l (c t) (q t)))
  (hd : ContDiff ℝ ∞ d) {MA Md : ℝ} (hMA : 0 ≤ MA) (hMd : 0 ≤ Md)
  (hAn : ∀ t, ‖angularOperator (J t) l (c t) (q t)‖ ≤ MA)
  (hdn : ∀ t, |d t| ≤ Md)
  (hc : ∀ t ≤ 0,c t = 1) (hq : ∀ t ≤ 0,q t = 1)
  (hdi : ∀ t ≤ 0,d t = (n:ℝ)-2)

include hA hd hMA hMd hAn hdn hc hq hdi in
lemma regularValue_core (P : harmonicPolynomials n l) {t : ℝ} (ht : t ≤ 0) :
    regularValue J l c q d P t = Real.exp ((l:ℝ)*t) • P := by
  apply value_euclidean_tail hA.continuous hd.continuous hMA hMd hAn hdn _ hdi P ht
  intro s hs v
  rw [hc s hs,hq s hs,angularOperator_round]
  simp only [inv_one,one_mul,_root_.smul_apply,one_apply_eq_self,roundEigenvalue]
  congr 1; ring

include hA hd hMA hMd hAn hdn hc hq hdi in
lemma regularHarmonic_core (B : Basis ι ℝ (harmonicPolynomials n l))
    (P : harmonicPolynomials n l) {x : Space n} (hx : squareRadius x < 1) :
    regularHarmonic B J c q d P x = evaluate (P : PolynomialSpace n) x := by
  have hh (t : ℝ) (ht : t ≤ 0) :
      coordinates B (regularValue J l c q d P t) = Real.exp ((l:ℝ)*t) • coordinates B P := by
    rw [regularValue_core hA hd hMA hMd hAn hdn hc hq hdi P ht,map_smul]
  rw [regularHarmonic,synthesized_core_eq hh hx,evaluate_sum]
  simpa only [evaluate_smul] using basis_evaluate B P x

include hA hd hMA hMd hAn hdn hc hq hdi in
lemma regularHarmonic_smooth (B : Basis ι ℝ (harmonicPolynomials n l))
    (P : harmonicPolynomials n l) : ContDiff ℝ ∞ (regularHarmonic B J c q d P) := by
  apply synthesized_smooth (fun i => evaluate_smooth _)
  · exact (coordinates B).contDiff.comp (value_smooth hA hd hMA hMd hAn hdn l P)
  · intro t ht
    rw [regularValue_core hA hd hMA hMd hAn hdn hc hq hdi P ht,map_smul]

include hA hd hMA hMd hAn hdn hc hq hdi in
lemma regularHarmonic_injective (B : Basis ι ℝ (harmonicPolynomials n l)) :
    Function.Injective (regularHarmonic B J c q d) := by
  intro P Q h
  apply Subtype.ext
  apply evaluate_eq_of_core
  intro x hx
  rw [← regularHarmonic_core hA hd hMA hMd hAn hdn hc hq hdi B P hx,
    ← regularHarmonic_core hA hd hMA hMd hAn hdn hc hq hdi B Q hx,h]

include hA hd hMA hMd hAn hdn hc hq hdi in
lemma regularHarmonic_harmonic (B : Basis ι ℝ (harmonicPolynomials n l))
    (P : harmonicPolynomials n l) (g : SmoothMetric n)
    (hg0 : ∀ᶠ x in 𝓝 0,g.coeff x = 1)
    (hc0 : ∀ t,c t ≠ 0) (hq0 : ∀ t,q t ≠ 0) (u v : ℝ → ℝ)
    (hdv : ∀ t,d t = (n:ℝ)-2+((n:ℝ)-1)*u t+v t)
    (hginv : ∀ x, x ≠ 0 → (g.coeff x)⁻¹ =
      polarTensor (J (logRadius x)) x (c (logRadius x))⁻¹ (c (logRadius x)*q (logRadius x))⁻¹)
    (hgcon : ∀ x,x ≠ 0 → ∀ k i j,christoffel g x k i j =
      normalizedConnectionCoeff (J (logRadius x)) x (c (logRadius x)) (q (logRadius x))
        (u (logRadius x)) (v (logRadius x)) k i j) :
    ∀ x,laplaceBeltrami g (regularHarmonic B J c q d P) x = 0 := by
  intro x
  by_cases hx : x = 0
  · subst x
    apply synthesized_harmonic_at_zero g hg0 (fun i => B i)
    intro t ht
    rw [regularValue_core hA hd hMA hMd hAn hdn hc hq hdi P ht,map_smul]
  · let A := fun t => angularOperator (J t) l (c t) (q t)
    let Y := fun t => coordinates B (regularValue J l c q d P t)
    let Y1 := fun t => coordinates B (velocity A d l P t)
    let Y2 := fun t => coordinates B (A t (value A d l P t)-d t • velocity A d l P t)
    let heval (i : ι) : (harmonicPolynomials n l →L[ℝ] ℝ) :=
      (ContinuousLinearMap.proj i).comp (coordinates B).toContinuousLinearMap
    have hY (t : ℝ) (i : ι) : HasDerivAt (fun s => Y s i) (Y1 t i) t :=
      (heval i).hasFDerivAt.comp_hasDerivAt t
        (value_deriv hA.continuous hd.continuous hMA hMd hAn hdn l P t)
    have hY1 (t : ℝ) (i : ι) : HasDerivAt (fun s => Y1 s i) (Y2 t i) t :=
      (heval i).hasFDerivAt.comp_hasDerivAt t
        (velocity_deriv hA.continuous hd.continuous hMA hMd hAn hdn l P t)
    apply synthesized_harmonic_at_ne_zero g (J (logRadius x)) hY hY1
      (fun i => evaluate_smooth _) (fun i => harmonicPolynomials_euler (B i))
      (fun i => harmonicPolynomials_harmonic (B i)) hx (hc0 _) (hq0 _)
      (u (logRadius x)) (v (logRadius x)) (hginv x hx) (hgcon x hx)
      (fun i j => coordinates B ((rotationCLM (J (logRadius x)) l*
        rotationCLM (J (logRadius x)) l) (B i)) j)
      (fun i => square_rotation_basis_evaluate B (J (logRadius x)) i x)
    intro i
    change coordinates B (A (logRadius x) (value A d l P (logRadius x))-
      d (logRadius x) • velocity A d l P (logRadius x)) i + _ = _
    simp only [map_sub,map_smul,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    rw [angularOperator_basis_coordinates,hdv,roundEigenvalue]
    dsimp only [Y1,Y,regularValue,A]
    rw [_root_.mul_inv_rev]
    ring

end HarmonicCounterexample.Angular

end

noncomputable section


namespace HarmonicCounterexample.GlobalGrowth

/-- Smoothness cannot by itself be substituted for the all-point growth bound.
This compact absorption lemma supplies the missing uniform constant. -/
theorem absorb_compact {E : Type*} [TopologicalSpace E]
    (u r : E → ℝ) (hu : Continuous u) (hr : ∀ x, 0 ≤ r x)
    (hcompact : ∀ R, IsCompact {x | r x ≤ R}) (k : ℕ)
    {D R : ℝ} (houtside : ∀ x, R ≤ r x → |u x| ≤ D * (1+r x)^k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |u x| ≤ C * (1+r x)^k := by
  obtain ⟨B, hB⟩ := (hcompact R).exists_bound_of_continuousOn hu.continuousOn
  refine ⟨max 0 (max B D), le_max_left _ _, ?_⟩
  intro x
  have hpow : 1 ≤ (1+r x)^k := one_le_pow₀ (by linarith [hr x])
  have hC : 0 ≤ max 0 (max B D) := le_max_left _ _
  by_cases hx : R ≤ r x
  · exact (houtside x hx).trans (mul_le_mul_of_nonneg_right
      ((le_max_right B D).trans (le_max_right 0 (max B D))) (by positivity))
  · have hb : |u x| ≤ B := by
      simpa only [Real.norm_eq_abs] using hB x (le_of_not_ge hx)
    calc
      |u x| ≤ B := hb
      _ ≤ max 0 (max B D) := (le_max_left B D).trans (le_max_right 0 (max B D))
      _ ≤ max 0 (max B D) * (1+r x)^k := by nlinarith

/-- The finite-dimensional angular norm estimate is uniform over the entire
compact link, not just at a finite set of angles. -/
theorem angular_bound {ι X : Type*} [Fintype ι] [TopologicalSpace X]
    (K : Set X) (hK : IsCompact K) (φ : ι → X → ℝ)
    (hφ : ∀ i, ContinuousOn (φ i) K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : ι → ℝ) (x : X), x ∈ K →
      |∑ i, y i * φ i x| ≤ C * ‖y‖ := by
  classical
  choose B hB using fun i => hK.exists_bound_of_continuousOn (hφ i)
  refine ⟨∑ i, max 0 (B i), Finset.sum_nonneg (fun i _ => le_max_left _ _), ?_⟩
  intro y x hx
  calc
    |∑ i, y i * φ i x| ≤ ∑ i, |y i * φ i x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, max 0 (B i) * ‖y‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      have hb : |φ i x| ≤ max 0 (B i) := by
        simpa only [Real.norm_eq_abs] using (hB i x hx).trans (le_max_right 0 (B i))
      have hy : |y i| ≤ ‖y‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm y i
      calc
        |y i| * |φ i x| ≤ ‖y‖ * max 0 (B i) :=
          mul_le_mul hy hb (abs_nonneg _) (norm_nonneg _)
        _ = max 0 (B i) * ‖y‖ := mul_comm _ _
    _ = (∑ i, max 0 (B i)) * ‖y‖ := (Finset.sum_mul ..).symm

/-- Independence of restrictions implies independence of actual global
functions; equality only on a fixed sphere suffices. -/
theorem independent_of_restriction {ι X Y : Type*} (f : Y → X)
    (u : ι → X → ℝ) (h : LinearIndependent ℝ (fun i => u i ∘ f)) :
    LinearIndependent ℝ u := by
  let T : (X → ℝ) →ₗ[ℝ] (Y → ℝ) :=
    { toFun := fun v => v ∘ f
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact LinearIndependent.of_comp T h

end HarmonicCounterexample.GlobalGrowth

end

noncomputable section


namespace HarmonicCounterexample.Angular
open Module Matrix Berger Cartesian LinearODE
open scoped ContDiff
variable {n l : ℕ} {ι : Type*} [Fintype ι]

lemma normalized_point_norm {x : Space n} (hx : x ≠ 0) :
    ‖(radius x)⁻¹ • x‖ ≤ 1 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (radius_pos hx))]
  calc
    (radius x)⁻¹ * ‖x‖ ≤ (radius x)⁻¹ * radius x :=
      mul_le_mul_of_nonneg_left (norm_le_radius x) (inv_nonneg.2 (radius_nonneg x))
    _ = 1 := inv_mul_cancel₀ (radius_pos hx).ne'

lemma synthesized_normalized (B : Basis ι ℝ (harmonicPolynomials n l))
    (Y : ℝ → ι → ℝ) {x : Space n} (hx : x ≠ 0) :
    synthesized l (fun i => evaluate (B i : PolynomialSpace n)) Y x =
      ∑ i, Y (logRadius x) i * evaluate (B i : PolynomialSpace n) ((radius x)⁻¹ • x) := by
  apply Finset.sum_congr rfl
  intro i _
  rw [evaluate_homogeneous (B i).property.1]
  have he : Real.exp (-(l:ℝ)*logRadius x) = ((radius x)⁻¹)^l := by
    rw [neg_mul,Real.exp_neg,Real.exp_nat_mul,exp_logRadius hx,inv_pow]
  simp only [regularCoefficient,he]
  ring

/-- A true uniform sphere estimate for every time of the actual polynomial
synthesis, not a finite sampling of directions. -/
lemma synthesized_angular_bound (B : Basis ι ℝ (harmonicPolynomials n l)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Y : ℝ → ι → ℝ) (x : Space n), x ≠ 0 →
      |synthesized l (fun i => evaluate (B i : PolynomialSpace n)) Y x| ≤
        C * ‖Y (logRadius x)‖ := by
  obtain ⟨C,hC,h⟩ := GlobalGrowth.angular_bound (Metric.closedBall (0 : Space n) 1)
    (isCompact_closedBall _ _) (fun i => evaluate (B i : PolynomialSpace n))
    (fun i => (evaluate_smooth _).continuous.continuousOn)
  refine ⟨C,hC,?_⟩
  intro Y x hx
  rw [synthesized_normalized B Y hx]
  apply h
  simpa only [Metric.mem_closedBall,dist_zero_right] using normalized_point_norm hx

/-- The all-point polynomial bound from a genuine coefficient-flow bound.
The compact core is absorbed using the actual smooth global function. -/
lemma synthesized_growth (B : Basis ι ℝ (harmonicPolynomials n l))
    (Y : ℝ → ι → ℝ) (k : ℕ)
    (hs : Continuous (synthesized l (fun i => evaluate (B i : PolynomialSpace n)) Y))
    {D T : ℝ} (hD : 0 ≤ D)
    (hY : ∀ t, T ≤ t → ‖Y t‖ ≤ D*Real.exp ((k:ℝ)*t)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      |synthesized l (fun i => evaluate (B i : PolynomialSpace n)) Y x| ≤
        C*(1+radius x)^k := by
  obtain ⟨A,hA,ha⟩ := synthesized_angular_bound B
  apply GlobalGrowth.absorb_compact _ radius hs radius_nonneg radius_sublevel_compact k
    (D := A*D) (R := Real.exp T)
  intro x hx
  have hr : 0 < radius x := (Real.exp_pos T).trans_le hx
  have hx0 : x ≠ 0 := by intro h; subst x; simp [radius] at hr
  have ht : T ≤ logRadius x := by
    rw [logRadius_eq_log_radius x,Real.le_log_iff_exp_le hr]
    exact hx
  calc
    _ ≤ A*‖Y (logRadius x)‖ := ha Y x hx0
    _ ≤ A*(D*Real.exp ((k:ℝ)*logRadius x)) := mul_le_mul_of_nonneg_left (hY _ ht) hA
    _ = A*D*(radius x)^k := by rw [Real.exp_nat_mul,exp_logRadius hx0]; ring
    _ ≤ A*D*(1+radius x)^k := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (radius_nonneg x) (by linarith) k) (mul_nonneg hA hD)

end HarmonicCounterexample.Angular

end

noncomputable section


namespace HarmonicCounterexample.Angular
open MvPolynomial Cartesian
open scoped BigOperators
variable {n : ℕ}

/-- Independence in distinct homogeneous degrees, retaining all coefficients. -/
lemma independent_homogeneous_family {δ : Type*} [Fintype δ]
    {ι : δ → Type*} [∀ d,Fintype (ι d)] (degree : δ → ℕ)
    (hdegree : Function.Injective degree)
    (P : (d : δ) → ι d → PolynomialSpace n)
    (hP : ∀ d j,P d j ∈ homogeneousSubmodule (Fin n) ℝ (degree d))
    (hli : ∀ d,LinearIndependent ℝ (P d)) :
    LinearIndependent ℝ (fun i : Sigma ι => P i.1 i.2) := by
  classical
  apply Fintype.linearIndependent_iff.2
  intro c hc i
  obtain ⟨d,i⟩ := i
  have he := congrArg (homogeneousComponent (degree d)) hc
  simp only [map_sum,map_smul,map_zero] at he
  simp_rw [homogeneousComponent_of_mem (hP _ _),hdegree.eq_iff] at he
  rw [Fintype.sum_sigma] at he
  have he' : ∑ j,c ⟨d,j⟩ • P d j = 0 := by simpa using he
  exact Fintype.linearIndependent_iff.1 (hli d) _ he' i

/-- Evaluation on the whole open flat core, as an actual function space. -/
def coreEvaluation : PolynomialSpace n →ₗ[ℝ]
    ({x : Space n // squareRadius x < 1} → ℝ) where
  toFun P x := evaluate P x.1
  map_add' P Q := by ext x; simp [evaluate]
  map_smul' c P := by ext x; simp [evaluate]

lemma coreEvaluation_injective : Function.Injective (coreEvaluation (n := n)) := by
  intro P Q h
  apply evaluate_eq_of_core
  intro x hx
  exact congrFun h ⟨x,hx⟩

def coreRestriction : (Space n → ℝ) →ₗ[ℝ]
    ({x : Space n // squareRadius x < 1} → ℝ) where
  toFun f x := f x.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Core independence proves independence of the global functions. No unproved
unique-continuation principle is used. -/
lemma independent_of_core {ι : Type*} (P : ι → PolynomialSpace n)
    (hP : LinearIndependent ℝ P) (f : ι → Space n → ℝ)
    (hf : ∀ i x,squareRadius x < 1 → f i x = evaluate (P i) x) :
    LinearIndependent ℝ f := by
  have hi := hP.map' coreEvaluation (LinearMap.ker_eq_bot.2 coreEvaluation_injective)
  have he : coreRestriction ∘ f = coreEvaluation ∘ P := by
    funext i x
    exact hf i x.1 x.2
  exact LinearIndependent.of_comp coreRestriction (he ▸ hi)

/-- The complete finite-family independence bridge for the degree-by-degree
center-regular harmonic producer in the manuscript. -/
theorem independent_across_degrees {δ : Type*} [Fintype δ]
    {ι : δ → Type*} [∀ d,Fintype (ι d)] (degree : δ → ℕ)
    (hdegree : Function.Injective degree)
    (P : (d : δ) → ι d → harmonicPolynomials n (degree d))
    (hP : ∀ d,LinearIndependent ℝ (P d))
    (f : Sigma ι → Space n → ℝ)
    (hf : ∀ i x,squareRadius x < 1 → f i x = evaluate (P i.1 i.2) x) :
    LinearIndependent ℝ f := by
  apply independent_of_core (fun i => (P i.1 i.2 : PolynomialSpace n)) _ f hf
  apply independent_homogeneous_family degree hdegree (fun d j => (P d j : PolynomialSpace n))
  · exact fun d j => (P d j).property.1
  · intro d
    exact (hP d).map' (harmonicPolynomials n (degree d)).subtype (LinearMap.ker_eq_bot.2 Subtype.val_injective)

end HarmonicCounterexample.Angular

end

noncomputable section


namespace HarmonicCounterexample.Construction
open Filter Set Schedule LinearODE Cycling Angular Berger Cartesian Matrix Pulses
open scoped Topology ContDiff InnerProductSpace

namespace Stream
variable (F:Stream L cycleTarget)

lemma drift_core (t:ℝ) (ht:t≤0) : drift t=(16:ℝ)-2 := by
  rw [drift_center t ht]
  norm_num

lemma trajectory_regularValue (l:Fin L) (i:SelectedIndex l) (t:ℝ) :
    F.trajectory l i t=regularValue F.J (l.val+2) F.c F.q drift (F.initialPolynomial l i) t := by
  rw [trajectory,operatorValue_apply (F.A_smooth l).continuous drift_smooth.continuous
    (F.bound_nonneg l) (show (0:ℝ)≤14 by norm_num) (F.A_bound l) (fun t=>(drift_bounds t).2)]
  rw [F.A_eq l,degree_cast l]
  rfl

def harmonic (l:Fin L) (i:SelectedIndex l) : Space 16→ℝ :=
  regularHarmonic (basis l.val).toBasis F.J F.c F.q drift (F.initialPolynomial l i)

lemma harmonic_core (l:Fin L) (i:SelectedIndex l) {x:Space 16} (hx:squareRadius x<1) :
    F.harmonic l i x=evaluate (F.initialPolynomial l i : PolynomialSpace 16) x :=
  regularHarmonic_core (F.angular_smooth l) drift_smooth (F.bound_nonneg l) (by norm_num)
    (F.angular_bound l) (fun t=>(drift_bounds t).2) F.c_center F.q_center drift_core
    (basis l.val).toBasis (F.initialPolynomial l i) hx

lemma harmonic_smooth (l:Fin L) (i:SelectedIndex l) : ContDiff ℝ ∞ (F.harmonic l i) :=
  regularHarmonic_smooth (F.angular_smooth l) drift_smooth (F.bound_nonneg l) (by norm_num)
    (F.angular_bound l) (fun t=>(drift_bounds t).2) F.c_center F.q_center drift_core
    (basis l.val).toBasis (F.initialPolynomial l i)

lemma metric_locally_one : ∀ᶠ x:Space 16 in 𝓝 0,F.metric.coeff x=1 := by
  have he : ∀ᶠ x:Space 16 in 𝓝 0, radius x<Real.exp 0 :=
    (radius_continuous.tendsto 0).eventually (eventually_lt_nhds (by simp))
  exact he.mono (fun x hx=>rawCoefficient_euclidean F.c F.q F.J F.c_center F.q_center hx)

lemma metric_inverse (x:Space 16) (hx:x≠0) : (F.metric.coeff x)⁻¹=
    polarTensor (F.J (logRadius x)) x (F.c (logRadius x))⁻¹ (F.c (logRadius x)*F.q (logRadius x))⁻¹ := by
  have he : F.metric.coeff x=polarTensor (F.J (logRadius x)) x (F.c (logRadius x))
      (F.c (logRadius x)*F.q (logRadius x)) := by
    change rawCoefficient F.c F.q F.J x=_
    rw [rawCoefficient,ite_eq_right hx]
    ext i j
    rw [tensor_eq_rawPolar (F.J (logRadius x)) hx (fun y=>F.c (logRadius y)) (fun y=>F.q (logRadius y))]
    simp only [rawPolarEntry,polarTensor,Matrix.add_apply,Matrix.smul_apply,Matrix.vecMulVec_apply,smul_eq_mul]
    ring
  rw [he,polarTensor_inverse _ (squareRadius_pos hx).ne' (F.c_pos _).ne'
    (mul_ne_zero (F.c_pos _).ne' (F.q_pos _).ne')]

lemma metric_connection (x:Space 16) (hx:x≠0) (k i j:Fin 16) :
    christoffel F.metric x k i j=normalizedConnectionCoeff (F.J (logRadius x)) x
      (F.c (logRadius x)) (F.q (logRadius x))
      (horizontalSlope mu F.q (logRadius x)) (logSlope F.q (logRadius x)) k i j := by
  apply christoffel_logProfiles F.metric (F.J (logRadius x)) hx
    (rawCoefficient_locally_fixed F.c F.q F.J F.J_local hx)
  · exact horizontalScale_hasDeriv (F.q_smooth.differentiable (by simp)) F.q_pos mu _
  · exact logSlope_hasDeriv (F.q_smooth.differentiable (by simp)) F.q_pos _
  · exact (F.c_pos _).ne'
  · exact (F.q_pos _).ne'

lemma harmonic_laplace (l:Fin L) (i:SelectedIndex l) (x:Space 16) :
    laplaceBeltrami F.metric (F.harmonic l i) x=0 := by
  apply regularHarmonic_harmonic (F.angular_smooth l) drift_smooth
    (F.bound_nonneg l) (by norm_num) (F.angular_bound l) (fun t=>(drift_bounds t).2)
    F.c_center F.q_center drift_core (basis l.val).toBasis (F.initialPolynomial l i)
    F.metric F.metric_locally_one (fun t=>(F.c_pos t).ne') (fun t=>(F.q_pos t).ne')
    (horizontalSlope mu F.q) (logSlope F.q) _ F.metric_inverse F.metric_connection x
  intro t
  convert F.drift_eq t using 1
  norm_num

lemma harmonic_growth (l:Fin L) (i:SelectedIndex l) :
    ∃C:ℝ,0≤C ∧ ∀x,|F.harmonic l i x|≤C*(1+radius x)^50000 := by
  obtain ⟨T,hT⟩:=F.trajectory_exp_growth l i
  let C := (coordinates (basis l.val).toBasis).toContinuousLinearMap
  apply synthesized_growth (basis l.val).toBasis _ 50000 (F.harmonic_smooth l i).continuous
    (D:=‖C‖) (T:=T) (norm_nonneg C)
  intro t ht
  change ‖C (regularValue F.J (l.val+2) F.c F.q drift (F.initialPolynomial l i) t)‖≤_
  rw [← F.trajectory_regularValue l i t]
  exact (C.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hT t ht) (norm_nonneg C))

lemma harmonic_member (l:Fin L) (i:SelectedIndex l) : HarmonicGrowth F.metric 50000 (F.harmonic l i) := by
  refine ⟨F.harmonic_smooth l i,F.harmonic_laplace l i,?_⟩
  obtain ⟨C,hC,h⟩:=F.harmonic_growth l i
  refine ⟨C,hC,?_⟩
  intro x
  rw [F.geometry_main.2.2.2 x]
  exact h x

lemma harmonic_independent : LinearIndependent ℝ (fun i:Sigma SelectedIndex=>F.harmonic i.1 i.2) := by
  apply independent_across_degrees (fun l:Fin L=>l.val+2) _ F.initialPolynomial
    F.initialPolynomial_independent (fun i:Sigma SelectedIndex=>F.harmonic i.1 i.2)
    (fun i x hx=>F.harmonic_core i.1 i.2 hx)
  intro l m he
  apply Fin.ext
  exact Nat.add_right_cancel he

end Stream
end HarmonicCounterexample.Construction

end

noncomputable section


namespace HarmonicCounterexample.Construction

lemma selectedFamily_card : euclideanDimension 16 50000 < Fintype.card (Sigma SelectedIndex) := by
  simpa only [Fintype.card_sigma,Fintype.card_fin] using selectionCount_surplus

lemma embedding_of_strict_card {A:Type*} [Fintype A] {d:ℕ}
    (h:d<Fintype.card A) : Nonempty (Fin (d+1) ↪ A) := by
  apply Function.Embedding.nonempty_of_card_le
  simpa only [Fintype.card_fin,Nat.succ_eq_add_one] using Nat.succ_le_of_lt h

def familyEmbedding : Fin (euclideanDimension 16 50000+1) ↪ Sigma SelectedIndex :=
  Classical.choice (embedding_of_strict_card selectedFamily_card)

end HarmonicCounterexample.Construction

end

noncomputable section


namespace HarmonicCounterexample
open Construction

/-- The actual complete Ricci-nonnegative manifold and the actual polynomial-
growth harmonic functions manufactured by the same globally admissible stream.
This proves every clause of the unchanged manuscript main theorem. -/
theorem main : MainClaim := by
  let F := constructedStream
  refine ⟨16,50000,F.metric,by norm_num,by norm_num,by norm_num,
    F.geometry_main.1,F.ricci,F.geometry_main.2.1,F.geometry_main.2.2.1,?_,?_,?_⟩
  · exact fun i=>F.harmonic (familyEmbedding i).1 (familyEmbedding i).2
  · exact F.harmonic_independent.comp familyEmbedding familyEmbedding.injective
  · intro i
    exact F.harmonic_member (familyEmbedding i).1 (familyEmbedding i).2

end HarmonicCounterexample

end

end OAI
