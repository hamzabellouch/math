import OAI.Algebra.Determinantal.Model

namespace OAI

namespace PermanentBorder.PolarAnalysis
open MvPolynomial Filter
open scoped Topology

section PolynomialSystem
variable {σ τ : Type*} [Fintype σ] [Fintype τ]

noncomputable def polynomialSystem (L : τ → Poly σ →ₗ[ℂ] Poly τ)
    (P : Poly σ) (x : τ → ℂ) : τ → ℂ := fun i => MvPolynomial.eval x (L i P)

noncomputable def coefficientSystem (n : ℕ) (L : τ → Poly σ →ₗ[ℂ] Poly τ)
    (u : ((exponentCube (σ := σ) n) → ℂ) × (τ → ℂ)) : τ → ℂ :=
  fun i => ∑ d : exponentCube (σ := σ) n,
    u.1 d * MvPolynomial.eval u.2 (L i (monomial d.val 1))

theorem contDiff_coefficientSystem (n : ℕ) (L : τ → Poly σ →ₗ[ℂ] Poly τ) :
    ContDiff ℂ 1 (coefficientSystem n L) := by
  classical
  apply contDiff_pi.mpr
  intro i
  apply ContDiff.sum
  intro d _
  exact ((contDiff_apply ℂ ℂ d).comp contDiff_fst).mul
    ((contDiff_mvPolynomial_eval _).comp contDiff_snd)

omit [Fintype τ] in
theorem coefficientSystem_eq {n : ℕ} (L : τ → Poly σ →ₗ[ℂ] Poly τ)
    {P : Poly σ} (hP : P.support ⊆ exponentCube n) (x : τ → ℂ) :
    coefficientSystem n L ((fun d => P.coeff d.val),x) = polynomialSystem L P x := by
  classical
  ext i
  change (∑ d : exponentCube n, P.coeff d.val * eval x (L i (monomial d.val 1))) = _
  change _ = eval x (L i P)
  conv_rhs => rw [sum_over_exponentCube hP]
  simp only [map_sum]
  conv_rhs => rw [← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro d _
  rw [show monomial d.val (P.coeff d.val) = P.coeff d.val • monomial d.val (1 : ℂ) by
    simp [smul_monomial], map_smul]
  simp

def SimplePolynomialZero (L : τ → Poly σ →ₗ[ℂ] Poly τ) (P : Poly σ) (x : τ → ℂ) :=
  polynomialSystem L P x = 0 ∧ (fderiv ℂ (polynomialSystem L P) x).IsInvertible

theorem coefficient_limit_simple_zeros {ι : Type*} [Fintype ι]
    (L : τ → Poly σ →ₗ[ℂ] Poly τ) {P : ℕ → Poly σ} {p : Poly σ} {n : ℕ}
    (hP : ∀ j, (P j).support ⊆ exponentCube n)
    (hp : ∀ d, Tendsto (fun j => (P j).coeff d) atTop (𝓝 (p.coeff d)))
    (x : ι → τ → ℂ) (hx : Function.Injective x)
    (hs : ∀ i, SimplePolynomialZero L p (x i)) :
    ∀ᶠ j in atTop, ∃ y : ι → τ → ℂ, Function.Injective y ∧
      ∀ i, SimplePolynomialZero L (P j) (y i) := by
  classical
  let c : exponentCube (σ := σ) n → ℂ := fun d => p.coeff d.val
  let cs : ℕ → exponentCube (σ := σ) n → ℂ := fun j d => (P j).coeff d.val
  have hc : Tendsto cs atTop (𝓝 c) := tendsto_pi_nhds.mpr fun d => hp d.val
  let F := coefficientSystem n L
  have hF : ContDiff ℂ 1 F := contDiff_coefficientSystem n L
  have hp' := support_subset_cube_of_limit hP hp
  have he : (fun x => F (c,x)) = polynomialSystem L p := by
    funext x
    exact coefficientSystem_eq L hp' x
  have hz : ∀ i, F (c,x i) = 0 := by
    intro i
    rw [congrFun he]
    exact (hs i).1
  have hs' : ∀ i, SimpleAt F c (x i) := by
    intro i
    unfold SimpleAt
    rw [← fderiv_slice hF, he]
    exact (hs i).2
  have ht := finite_simple_zeros_persist hF x hx hz hs'
  filter_upwards [hc.eventually ht] with j hj
  obtain ⟨y,hy,hys⟩ := hj
  refine ⟨y,hy,?_⟩
  intro i
  have he' : (fun x => F (cs j,x)) = polynomialSystem L (P j) := by
    funext x
    exact coefficientSystem_eq L (hP j) x
  constructor
  · rw [← congrFun he']
    exact (hys i).1
  · rw [← he', fderiv_slice hF]
    exact (hys i).2

theorem HasBorderDeterminant.exists_simple_approximant {ι : Type*} [Fintype ι]
    {p : Poly σ} {n : ℕ} (h : HasBorderDeterminant n p)
    (L : τ → Poly σ →ₗ[ℂ] Poly τ) (x : ι → τ → ℂ)
    (hx : Function.Injective x) (hs : ∀ i, SimplePolynomialZero L p (x i)) :
    ∃ (A₀ : Matrix (Fin n) (Fin n) ℂ) (A : σ → Matrix (Fin n) (Fin n) ℂ)
      (y : ι → τ → ℂ), Function.Injective y ∧
      ∀ i, SimplePolynomialZero L (affineMatrixPolynomial n A₀ A) (y i) := by
  obtain ⟨hn,A₀,A,hlim⟩ := h
  obtain ⟨j,y,hy,hys⟩ := (coefficient_limit_simple_zeros L
    (fun j => support_subset_exponentCube (degree_affineMatrixPolynomial n (A₀ j) (A j)))
    hlim x hx hs).exists
  exact ⟨A₀ j,A j,y,hy,hys⟩
end PolynomialSystem
end PermanentBorder.PolarAnalysis
namespace PermanentBorder.Polar
open MvPolynomial
open scoped Classical
variable {τ : Type*} [Fintype τ]

noncomputable def affineChartSubstitution
    (e : (PolarVars τ → ℂ) ≃L[ℂ] (PolarVars τ → ℂ)) :
    Poly (PolarVars τ) →ₐ[ℂ] Poly (Option τ) :=
  affineSubstitution (fun j => e.symm (Pi.single none 1) j)
    (fun j i => e.symm (Pi.single (some i) 1) j)

lemma eval_affineChartSubstitution
    (e : (PolarVars τ → ℂ) ≃L[ℂ] (PolarVars τ → ℂ))
    (f : Poly (PolarVars τ)) (z : Option τ → ℂ) :
    eval z (affineChartSubstitution e f) = eval (affineNormChart e z) f := by
  change (aeval z : Poly (Option τ) →ₐ[ℂ] ℂ) (aeval _ f) = _
  rw [comp_aeval_apply]
  apply congrArg (fun g : PolarVars τ → ℂ => aeval g f)
  funext j
  simp only [map_add, map_sum, map_mul, aeval_C, aeval_X, Algebra.algebraMap_self_apply]
  convert (affineNormChart_eq e z j).symm using 1
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  apply congrArg (fun v : PolarVars τ → ℂ => e.symm v j)
  funext v
  simp [Pi.single_apply]

noncomputable def polarOperator (w : τ → PolarVars τ → ℂ) (i : τ) :
    Poly (PolarVars τ) →ₗ[ℂ] Poly (PolarVars τ) :=
  ∑ j, w i j • (pderiv j).toLinearMap

lemma polarOperator_eq (w : τ → PolarVars τ → ℂ) (i : τ) (f : Poly (PolarVars τ)) :
    polarOperator w i f = polarPolynomial w f i := by
  simp [polarOperator, polarPolynomial, smul_eq_C_mul]

noncomputable def affinePolarOperators (w : τ → PolarVars τ → ℂ)
    (e : (PolarVars τ → ℂ) ≃L[ℂ] (PolarVars τ → ℂ)) :
    Option τ → Poly (PolarVars τ) →ₗ[ℂ] Poly (Option τ) :=
  Option.elim' (affineChartSubstitution e).toLinearMap
    (fun i => (affineChartSubstitution e).toLinearMap.comp (polarOperator w i))

lemma polynomialSystem_affinePolarOperators (w : τ → PolarVars τ → ℂ)
    (e : (PolarVars τ → ℂ) ≃L[ℂ] (PolarVars τ → ℂ)) (f : Poly (PolarVars τ)) :
    PolarAnalysis.polynomialSystem (affinePolarOperators w e) f =
      fun z j => eval (affineNormChart e z) (hypersurfacePolars w f j) := by
  funext z j
  cases j with
  | none => exact eval_affineChartSubstitution e f z
  | some i =>
    change eval z (affineChartSubstitution e (polarOperator w i f)) = _
    rw [eval_affineChartSubstitution, polarOperator_eq]
    rfl

theorem HasBorderDeterminant.simple_polar_approximant {n r : ℕ}
    {f : Poly (PolarVars τ)} (hb : HasBorderDeterminant n f)
    (hr : 2 ≤ r) (hh : f.IsHomogeneous r)
    (hs : ∀ y : PolarVars τ → ℂ, eval y f = 0 →
      (∀ j, eval y (pderiv j f) = 0) → y = 0) :
    ∃ w : τ → PolarVars τ → ℂ,
    ∃ e : (PolarVars τ → ℂ) ≃L[ℂ] (PolarVars τ → ℂ),
    ∃ (A₀ : Matrix (Fin n) (Fin n) ℂ) (A : PolarVars τ → Matrix (Fin n) (Fin n) ℂ),
    ∃ x : Fin (r * (r-1)^Fintype.card τ) → Option τ → ℂ,
      Function.Injective x ∧ ∀ i,
        PolarAnalysis.SimplePolynomialZero (affinePolarOperators w e)
          (affineMatrixPolynomial n A₀ A) (x i) := by
  obtain ⟨w,e,x,hx,hsx⟩ := smooth_polar_affine_certificate f hr hh hs
  have hp (i) : PolarAnalysis.SimplePolynomialZero (affinePolarOperators w e) f (x i) := by
    unfold PolarAnalysis.SimplePolynomialZero
    rw [polynomialSystem_affinePolarOperators]
    exact hsx i
  obtain ⟨A₀,A,y,hy,hys⟩ := PolarAnalysis.HasBorderDeterminant.exists_simple_approximant
    hb (affinePolarOperators w e) x hx hp
  exact ⟨w,e,A₀,A,y,hy,hys⟩
end PermanentBorder.Polar

namespace PermanentBorder.Polar
open MvPolynomial Matrix PolarAnalysis KernelBilinear
open scoped Classical
variable {τ : Type} [Fintype τ]

lemma derivative_polar (w : τ → PolarVars τ → ℂ) (f : Poly (PolarVars τ))
    (y : PolarVars τ → ℂ) (i : τ) :
    fderiv ℂ (fun y => eval y f) y (w i) = eval y (polarPolynomial w f i) := by
  rw [(CI.hasFDerivAt_eval f y).fderiv, CI.polynomialDerivative_apply]
  simp [polarPolynomial,mul_comm]

lemma polarPair_polynomialSystem (w : τ → PolarVars τ → ℂ)
    (e : (PolarVars τ → ℂ) ≃L[ℂ] (PolarVars τ → ℂ)) (f : Poly (PolarVars τ)) :
    polarPair (fun y => eval y f) (fun z => affineNormChart e (optionProduct.symm z)) w =
      fun z => optionProduct (polynomialSystem (affinePolarOperators w e) f (optionProduct.symm z)) := by
  funext z
  rw [polynomialSystem_affinePolarOperators]
  apply Prod.ext
  · rfl
  · funext i
    exact derivative_polar w f _ i

omit [Fintype τ] in
lemma affineNormChart_add (e : (PolarVars τ → ℂ) ≃L[ℂ] (PolarVars τ → ℂ))
    (z : Option τ → ℂ) :
    affineNormChart e z = e.symm (Pi.single none 1) +
      (e.symm.toContinuousLinearMap.comp optionInsert) z := by
  change e.symm (Option.elim' 1 z) = e.symm (Pi.single none 1) + e.symm (optionInsert z)
  rw [← map_add]
  apply congrArg e.symm
  funext j
  cases j <;> simp

lemma eval_matrix {σ : Type} [Fintype σ] {n : ℕ}
    (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : σ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (y : σ → ℂ) :
    eval y (affineMatrixPolynomial (n+1) A₀ A) = (affine A₀ A y).det := by
  classical
  let M : Matrix (Fin (n+1)) (Fin (n+1)) (Poly σ) :=
    fun i j => C (A₀ i j) + ∑ v, C (A v i j) * X v
  change eval y M.det = _
  calc
    eval y M.det = ((eval y).mapMatrix M).det := RingHom.map_det (eval y) M
    _ = (affine A₀ A y).det := by
      apply congrArg Matrix.det
      ext i j
      change eval y (M i j) = (affine A₀ A y) i j
      simp [M,affine,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,mul_comm]

lemma simple_conjugate {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W]
    (e : V ≃L[ℂ] W) {F : V → V} {x : V} (hF : DifferentiableAt ℂ F x)
    (hs : (fderiv ℂ F x).IsInvertible) :
    (fderiv ℂ (fun y => e (F (e.symm y))) (e x)).IsInvertible := by
  have hF' : HasFDerivAt F (fderiv ℂ F x) (e.symm (e x)) := by simpa using hF.hasFDerivAt
  have hd := e.hasFDerivAt.comp (e x)
    (hF'.comp (e x) e.symm.hasFDerivAt)
  change (fderiv ℂ (e ∘ F ∘ e.symm) (e x)).IsInvertible
  rw [hd.fderiv]
  exact (show e.toContinuousLinearMap.IsInvertible from ⟨e,rfl⟩).comp
    (hs.comp (show e.symm.toContinuousLinearMap.IsInvertible from ⟨e.symm,rfl⟩))

theorem HasBorderDeterminant.polar_count {n r : ℕ}
    {f : Poly (PolarVars τ)} (hb : HasBorderDeterminant n f)
    (hr : 2 ≤ r) (hh : f.IsHomogeneous r)
    (hs : ∀ y : PolarVars τ → ℂ, eval y f = 0 →
      (∀ j, eval y (pderiv j f) = 0) → y = 0) :
    r * (r-1)^Fintype.card τ ≤
      2^Fintype.card τ * (2*n-1).choose (Fintype.card τ+1) := by
  classical
  cases n with
  | zero => exact False.elim (Nat.not_lt_zero _ hb.1)
  | succ n =>
    obtain ⟨w,e,A₀,A,x,hx,hxs⟩ := HasBorderDeterminant.simple_polar_approximant hb hr hh hs
    let P := affineMatrixPolynomial (n+1) A₀ A
    let Q := polynomialSystem (affinePolarOperators w e) P
    let b := e.symm (Pi.single none 1)
    let L := e.symm.toContinuousLinearMap.comp optionInsert
    have hrel : polarPair (fun y => (affine A₀ A y).det)
        (fun z => b + L (optionProduct.symm z)) w =
          fun z => optionProduct (Q (optionProduct.symm z)) := by
      have heval : (fun y => (affine A₀ A y).det) = (fun y => eval y P) := by
        funext y
        exact (eval_matrix A₀ A y).symm
      have hψ : (fun z => b + L (optionProduct.symm z)) =
          (fun z => affineNormChart e (optionProduct.symm z)) := by
        funext z
        exact (affineNormChart_add e _).symm
      rw [heval,hψ]
      exact polarPair_polynomialSystem w e P
    have hQ (z : Option τ → ℂ) : DifferentiableAt ℂ Q z := by
      apply differentiableAt_pi.mpr
      intro j
      exact ((contDiff_mvPolynomial_eval ((affinePolarOperators w e j) P)).differentiable (by decide)).differentiableAt
    have hcount := affine_polar_count A₀ A b L w (fun j => optionProduct (x j))
      (optionProduct.injective.comp hx)
      (fun j => by
        rw [hrel]
        change optionProduct (Q (optionProduct.symm (optionProduct (x j)))) = 0
        rw [optionProduct.symm_apply_apply]
        have hz : Q (x j) = 0 := (hxs j).1
        rw [hz, map_zero])
      (fun j => by
        rw [hrel]
        exact simple_conjugate optionProduct (hQ (x j)) (hxs j).2)
    have hn : 2*(n+1)-1 = 2*n+1 := by omega
    simpa [hn] using hcount
end PermanentBorder.Polar

namespace PermanentBorder.Polar

 theorem factorial_exp_lower (b : ℕ) : ((b : ℝ) / Real.exp 1)^b ≤ b.factorial := by
  rcases b with _ | b
  · simp
  have hb : (1:ℝ) ≤ b+1 := by linarith [Nat.cast_nonneg (α := ℝ) b]
  have hπ : (1:ℝ) ≤ Real.pi := le_trans (by norm_num) Real.two_le_pi
  have hs : 1 ≤ Real.sqrt (2 * Real.pi * (b+1)) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    nlinarith
  have hn := Stirling.le_factorial_stirling (b+1)
  simp only [Nat.cast_add, Nat.cast_one] at hn ⊢
  exact le_trans (le_mul_of_one_le_left (by positivity) hs) hn

 theorem choose_exp_bound (a b : ℕ) (hb : 0 < b) :
    (a.choose b : ℝ) ≤ (Real.exp 1 * a / b)^b := by
  have hbR : (0:ℝ) < b := by exact_mod_cast hb
  have hfact := factorial_exp_lower b
  have hx : (0:ℝ) < ((b:ℝ)/Real.exp 1)^b := by positivity
  calc
    (a.choose b : ℝ) ≤ (a:ℝ)^b / b.factorial := Nat.choose_le_pow_div b a
    _ ≤ (a:ℝ)^b / ((b:ℝ)/Real.exp 1)^b :=
      div_le_div_of_nonneg_left (by positivity) hx hfact
    _ = (Real.exp 1 * a / b)^b := by rw [← div_pow]; congr 1; field_simp

 theorem smooth_count_numerical_bound (n K r : ℕ) (hn : 0 < n) (hr : 2 ≤ r)
    (hcount : (r:ℝ) * ((r-1:ℕ):ℝ)^K ≤
      2^K * ((2*n-1).choose (K+1) : ℝ)) :
    ((r-1:ℕ):ℝ) * (K+1) / (4 * Real.exp 1) ≤ n := by
  have hr0 : (0:ℝ) < (r-1:ℕ) := by exact_mod_cast (show 0 < r-1 by omega)
  have hrle : ((r-1:ℕ):ℝ) ≤ r := by exact_mod_cast Nat.sub_le r 1
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hK : (0:ℝ) < K+1 := by positivity
  have hchoose := choose_exp_bound (2*n-1) (K+1) (by omega)
  have htwo : ((2*n-1:ℕ):ℝ) ≤ 2*n := by
    exact_mod_cast (Nat.sub_le (2*n) 1)
  have hbase : Real.exp 1 * ((2*n-1:ℕ):ℝ) / ((K+1:ℕ):ℝ) ≤
      (2 * Real.exp 1 * n) / (K+1) := by
    simp only [Nat.cast_add, Nat.cast_one]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [Real.exp_pos (1:ℝ)]
  have hpow : (((r-1:ℕ):ℝ))^(K+1) ≤ (4 * Real.exp 1 * n / (K+1))^(K+1) := by
    calc
      (((r-1:ℕ):ℝ))^(K+1) ≤ (r:ℝ) * ((r-1:ℕ):ℝ)^K := by
        rw [pow_succ, mul_comm]
        exact mul_le_mul_of_nonneg_right hrle (by positivity)
      _ ≤ 2^K * ((2*n-1).choose (K+1) : ℝ) := hcount
      _ ≤ 2^K * (Real.exp 1 * ((2*n-1:ℕ):ℝ) / ((K+1:ℕ):ℝ))^(K+1) :=
        mul_le_mul_of_nonneg_left hchoose (by positivity)
      _ ≤ 2^(K+1) * ((2 * Real.exp 1 * n) / (K+1))^(K+1) := by
        apply mul_le_mul
        · have : (2:ℝ)^K ≤ 2^(K+1) := by rw [pow_succ]; nlinarith [pow_pos (by norm_num : (0:ℝ)<2) K]
          exact this
        · exact pow_le_pow_left₀ (by positivity) hbase _
        · positivity
        · positivity
      _ = (4 * Real.exp 1 * n / (K+1))^(K+1) := by
        rw [← mul_pow]; congr 1; ring
  have hle : ((r-1:ℕ):ℝ) ≤ 4 * Real.exp 1 * n / (K+1) :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by omega : K+1 ≠ 0)).mp hpow
  apply (div_le_iff₀ (by positivity)).mpr
  have := (le_div_iff₀ hK).mp hle
  nlinarith

end PermanentBorder.Polar

namespace PermanentBorder
open MvPolynomial
open scoped Classical

theorem HasBorderDeterminant.rename {σ τ : Type*} [Fintype σ] [Fintype τ]
    {n : ℕ} {f : Poly σ} (h : HasBorderDeterminant n f) (e : σ → τ) :
    HasBorderDeterminant n (MvPolynomial.rename e f) := by
  classical
  let B : σ → τ → ℂ := fun i j => if e i = j then 1 else 0
  have he : PermanentBorder.affineSubstitution (fun _ : σ => 0) B = (MvPolynomial.rename e : Poly σ →ₐ[ℂ] Poly τ) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [PermanentBorder.affineSubstitution,B,eq_comm]
  simpa only [he] using h.affineSubstitution (fun _ => 0) B

namespace Polar

lemma smooth_rename {σ τ : Type} [Fintype σ] [Fintype τ]
    (e : σ ≃ τ) (f : Poly σ)
    (hs : ∀ y : σ → ℂ, eval y f = 0 →
      (∀ j, eval y (pderiv j f) = 0) → y = 0) :
    ∀ y : τ → ℂ, eval y (rename e f) = 0 →
      (∀ j, eval y (pderiv j (rename e f)) = 0) → y = 0 := by
  intro y hy hg
  rw [eval_rename] at hy
  have hgrad (i : σ) : eval (y ∘ e) (pderiv i f) = 0 := by
    have h := hg (e i)
    rw [pderiv_rename e.injective,eval_rename] at h
    exact h
  have hz := hs _ hy hgrad
  funext i
  simpa only [Function.comp_apply,e.apply_symm_apply,Pi.zero_apply] using congrFun hz (e.symm i)

theorem HasBorderDeterminant.smooth_lower_bound {σ : Type} [Fintype σ]
    {n r : ℕ} {f : Poly σ} (hb : HasBorderDeterminant n f)
    (hσ : 2 ≤ Fintype.card σ) (hr : 2 ≤ r) (hh : f.IsHomogeneous r)
    (hs : ∀ y : σ → ℂ, eval y f = 0 →
      (∀ j, eval y (pderiv j f) = 0) → y = 0) :
    ((r-1 : ℕ) : ℝ) * ((Fintype.card σ-1 : ℕ) : ℝ) / (4*Real.exp 1) ≤ n := by
  classical
  let K := Fintype.card σ - 2
  have hc : Fintype.card σ = Fintype.card (PolarVars (Fin K)) := by
    simp only [PolarVars,Fintype.card_option,Fintype.card_fin]
    dsimp [K]
    omega
  let e := Fintype.equivOfCardEq hc
  have hb' := hb.rename e
  have hp := HasBorderDeterminant.polar_count hb' hr (hh.rename_isHomogeneous)
    (smooth_rename e f hs)
  have hcount : (r : ℝ) * ((r-1 : ℕ) : ℝ)^K ≤
      2^K * ((2*n-1).choose (K+1) : ℝ) := by
    simp only [Fintype.card_fin] at hp
    exact_mod_cast hp
  have h := smooth_count_numerical_bound n K r hb.1 hr hcount
  have hk : K+1 = Fintype.card σ-1 := by dsimp [K]; omega
  have hkR : (K : ℝ)+1 = ((Fintype.card σ-1 : ℕ) : ℝ) := by exact_mod_cast hk
  simpa only [hkR] using h
end Polar
end PermanentBorder

end OAI
