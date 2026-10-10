import OAI.Geometry.HarmonicGrowth.Cycling
import OAI.Geometry.HarmonicGrowth.Intrinsic

namespace OAI

noncomputable section
open Filter
open scoped BigOperators Topology ContDiff

namespace HarmonicCounterexample
open Matrix Berger Cartesian
variable {n : ℕ}

lemma laplace_congr (g : SmoothMetric n) {f h : Space n → ℝ} {x : Space n}
    (he : f =ᶠ[𝓝 x] h) : laplaceBeltrami g f x = laplaceBeltrami g h x := by
  have hd (i j : Fin n) : coordDeriv i (coordDeriv j f) x = coordDeriv i (coordDeriv j h) x :=
    coordDeriv_congr (he.eventually_nhds.mono fun _ hy => coordDeriv_congr hy j) i
  simp only [laplaceBeltrami,coordDeriv_congr he,hd]

lemma laplace_eq_euclidean_of_flat (g : SmoothMetric n) {x : Space n}
    (hg : ∀ᶠ y in 𝓝 x, g.coeff y = 1) (f : Space n → ℝ) :
    laplaceBeltrami g f x = euclideanLaplacian f x := by
  have hd (k i j : Fin n) : coordDeriv k (fun y => g.coeff y i j) x = 0 := by
    rw [coordDeriv_congr (hg.mono fun _ hy => congrFun (congrFun hy i) j) k]
    exact coordDeriv_const _ _ _
  have hΓ (k i j : Fin n) : christoffel g x k i j = 0 := by simp [christoffel,hd]
  simp [laplaceBeltrami,hΓ,hg.self_of_nhds,Matrix.one_apply,euclideanLaplacian,hessian,
    Matrix.trace,Matrix.diag]

end HarmonicCounterexample

end

noncomputable section
open Filter
open scoped BigOperators Topology ContDiff

namespace HarmonicCounterexample.Cartesian
open Matrix Berger
variable {n : ℕ} {ι : Type*} [Fintype ι]

lemma synthesized_harmonic_at_ne_zero (g : SmoothMetric n) (J : ComplexStructure (Fin n))
    {l : ℝ} {P : ι → Space n → ℝ} {Y Y1 Y2 : ℝ → ι → ℝ}
    (hY : ∀ t i, HasDerivAt (fun s => Y s i) (Y1 t i) t)
    (hY1 : ∀ t i, HasDerivAt (fun s => Y1 s i) (Y2 t i) t)
    (hP : ∀ i, ContDiff ℝ ∞ (P i)) (hE : ∀ i x, euler (P i) x = l*P i x)
    (hH : ∀ i x, euclideanLaplacian (P i) x = 0) {x : Space n} (hx : x ≠ 0)
    {A q : ℝ} (hA : A ≠ 0) (hq : q ≠ 0) (u v : ℝ)
    (hg : (g.coeff x)⁻¹ = polarTensor J x A⁻¹ (A*q)⁻¹)
    (hΓ : ∀ k i j, christoffel g x k i j = normalizedConnectionCoeff J x A q u v k i j)
    (H : Matrix ι ι ℝ)
    (hW : ∀ i, hopfDerivative J (hopfDerivative J (P i)) x = ∑ j, H i j*P j x)
    (hODE : ∀ i, Y2 (logRadius x) i+((n:ℝ)-2+((n:ℝ)-1)*u+v)*Y1 (logRadius x) i =
      A⁻¹*l*(l+(n:ℝ)-2)*Y (logRadius x) i-
      ((A*q)⁻¹-A⁻¹)*∑ j, H j i*Y (logRadius x) j) :
    laplaceBeltrami g (synthesized l P Y) x = 0 := by
  have hdiff (i : ι) {y : Space n} (hy : y ≠ 0) :
      DifferentiableAt ℝ (fun y => regularCoefficient l Y i (logRadius y)*P i y) y :=
    (logProfile_differentiableAt (fun t => regularCoefficient_deriv (hY t) i) hy).mul
      ((hP i).differentiable (by simp) y)
  have hnd (i : ι) : ∀ᶠ y in 𝓝 x,
      DifferentiableAt ℝ (fun y => regularCoefficient l Y i (logRadius y)*P i y) y :=
    (eventually_ne_nhds hx).mono fun _ hy => hdiff i hy
  have hdd (i : ι) (j : Fin n) : DifferentiableAt ℝ
      (coordDeriv j (fun y => regularCoefficient l Y i (logRadius y)*P i y)) x := by
    exact coordDeriv_product_differentiableAt
      ((eventually_ne_nhds hx).mono fun _ hy =>
        logProfile_differentiableAt (fun t => regularCoefficient_deriv (hY t) i) hy)
      (Filter.Eventually.of_forall ((hP i).differentiable (by simp)))
      (logProfile_coord_differentiableAt (fun t => regularCoefficient_deriv (hY t) i)
        (fun t => regularCoefficient_second (hY t) (hY1 t) i) hx)
      (fun j => (coordDeriv_smooth (hP i) j).differentiable (by simp) x) j
  apply (mul_eq_zero.mp ?_).resolve_left (squareRadius_pos hx).ne'
  change (x ⬝ᵥ x)*laplaceBeltrami g (synthesized l P Y) x = 0
  unfold synthesized
  rw [laplace_sum g hnd hdd,Finset.mul_sum]
  simp only [laplace_regular_term g J hY hY1 (hP _) (hE _) (hH _) hx hA hq u v hg hΓ,
    hODE,hW]
  let d := ((A*q)⁻¹-A⁻¹)
  have he (j : ι) :
      (A⁻¹*l*(l+(n:ℝ)-2)*Y (logRadius x) j-d*(∑ i,H i j*Y (logRadius x) i)-
      A⁻¹*l*(l+(n:ℝ)-2)*Y (logRadius x) j)*P j x+
      d*Y (logRadius x) j*(∑ i,H j i*P i x) =
      d*((∑ i,Y (logRadius x) j*H j i*P i x)-
        ∑ i,Y (logRadius x) i*H i j*P j x) := by
    have h1 : (∑ i,H i j*Y (logRadius x) i)*P j x =
        ∑ i,Y (logRadius x) i*H i j*P j x := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have h2 : Y (logRadius x) j*(∑ i,H j i*P i x) =
        ∑ i,Y (logRadius x) j*H j i*P i x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    calc
      _ = d*(Y (logRadius x) j*(∑ i,H j i*P i x)-
        (∑ i,H i j*Y (logRadius x) i)*P j x) := by ring
      _ = _ := by rw [h1,h2]
  simp only [← show d = ((A*q)⁻¹-A⁻¹) from rfl,he,← Finset.mul_sum,
    Finset.sum_sub_distrib]
  have hs : (∑ j,∑ i,Y (logRadius x) j*H j i*P i x) =
      ∑ j,∑ i,Y (logRadius x) i*H i j*P j x := Finset.sum_comm
  rw [hs,sub_self,mul_zero,mul_zero]

end HarmonicCounterexample.Cartesian

end

noncomputable section
open Filter
open scoped BigOperators Topology ContDiff

namespace HarmonicCounterexample.Angular
open MvPolynomial Matrix Berger Cartesian
variable {n : ℕ}

abbrev evaluate (P : PolynomialSpace n) (x : Space n) : ℝ := MvPolynomial.eval x P

lemma evaluate_smooth (P : PolynomialSpace n) : ContDiff ℝ ∞ (evaluate P) := by
  unfold evaluate
  induction P using MvPolynomial.induction_on with
  | C c => simpa [Angular.evaluate] using (contDiff_const : ContDiff ℝ ∞ (fun _ : Space n => c))
  | add P Q hp hq => simpa only [Angular.evaluate, eval_add] using hp.add hq
  | mul_X P i hp => simpa only [Angular.evaluate, eval_mul, eval_X] using hp.mul (contDiff_apply ℝ ℝ i)

lemma coordDeriv_evaluate (P : PolynomialSpace n) (i : Fin n) :
    coordDeriv i (evaluate P) = evaluate (pderiv i P) := by
  ext x
  unfold evaluate
  induction P using MvPolynomial.induction_on with
  | C c => simp [coordDeriv_const]
  | add P Q hp hq =>
    simp only [eval_add]
    change coordDeriv i (fun y => eval y P+eval y Q) x = _
    rw [coordDeriv_add ((evaluate_smooth P).differentiable (by simp) x)
      ((evaluate_smooth Q).differentiable (by simp) x),hp,hq]
    simp
  | mul_X P j hp =>
    simp only [eval_mul,eval_X]
    change coordDeriv i (fun y => eval y P*y j) x = _
    rw [coordDeriv_mul ((evaluate_smooth P).differentiable (by simp) x)
      (hasFDerivAt_apply j x).differentiableAt,hp,coordDeriv_coordinate]
    simp only [Angular.evaluate,pderiv_mul,pderiv_X,eval_add,eval_mul,eval_X]
    by_cases h : i = j
    · subst j; simp [add_comm,mul_comm]
    · simp [Ne.symm h,mul_comm]

lemma euler_evaluate {P : PolynomialSpace n} {l : ℕ} (hP : P.IsHomogeneous l) (x : Space n) :
    euler (evaluate P) x = (l : ℝ)*evaluate P x := by
  have h := congrArg (eval x) hP.sum_X_mul_pderiv
  simpa only [map_sum,eval_mul,eval_X,map_nsmul,nsmul_eq_mul,map_natCast,
    euler,Berger.gradient,dotProduct,coordDeriv_evaluate,Angular.evaluate] using h

lemma euclideanLaplacian_evaluate (P : PolynomialSpace n) (x : Space n) :
    euclideanLaplacian (evaluate P) x = evaluate (polynomialLaplacian P) x := by
  simp [euclideanLaplacian,hessian,Matrix.trace,Matrix.diag,coordDeriv_evaluate,Angular.evaluate,
    polynomialLaplacian]

lemma harmonicPolynomials_euler {l : ℕ} (P : harmonicPolynomials n l) (x : Space n) :
    euler (evaluate (P : PolynomialSpace n)) x = (l:ℝ)*evaluate (P : PolynomialSpace n) x :=
  euler_evaluate P.property.1 x

lemma harmonicPolynomials_harmonic {l : ℕ} (P : harmonicPolynomials n l) (x : Space n) :
    euclideanLaplacian (evaluate (P : PolynomialSpace n)) x = 0 := by
  rw [euclideanLaplacian_evaluate,show polynomialLaplacian (P : PolynomialSpace n) = 0 from P.property.2]
  simp [Angular.evaluate]

end HarmonicCounterexample.Angular

end

noncomputable section
open Filter
open scoped BigOperators Topology ContDiff

namespace HarmonicCounterexample.Angular
open MvPolynomial Matrix Berger Cartesian
variable {n : ℕ}

lemma evaluate_injective : Function.Injective (evaluate (n := n)) := by
  intro P Q h
  apply MvPolynomial.funext
  intro x
  exact congrFun h x

lemma evaluate_homogeneous {P : PolynomialSpace n} {l : ℕ} (hP : P.IsHomogeneous l)
    (c : ℝ) (x : Space n) : evaluate P (c • x) = c^l*evaluate P x := by
  unfold evaluate
  conv_lhs => rw [P.as_sum]
  conv_rhs => arg 2; rw [P.as_sum]
  simp only [map_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdeg : Finsupp.degree d = l := by
    rw [Finsupp.degree_eq_weight_one]
    exact hP (MvPolynomial.mem_support_iff.1 hd)
  simp only [eval_monomial,Finsupp.prod,Pi.smul_apply,smul_eq_mul,mul_pow,
    Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,← Finsupp.degree_apply,hdeg]
  ring

lemma evaluate_zero_of_pos_degree {P : PolynomialSpace n} {l : ℕ} (hP : P.IsHomogeneous l)
    (hl : 0 < l) : evaluate P 0 = 0 := by
  simpa [zero_pow (Nat.ne_of_gt hl)] using evaluate_homogeneous hP 0 (0 : Space n)

lemma evaluate_sum {ι : Type*} (s : Finset ι) (P : ι → PolynomialSpace n) (x : Space n) :
    evaluate (∑ i ∈ s,P i) x = ∑ i ∈ s,evaluate (P i) x := by simp [Angular.evaluate]

lemma evaluate_smul (c : ℝ) (P : PolynomialSpace n) (x : Space n) :
    evaluate (c • P) x = c*evaluate P x := by simp [Angular.evaluate]

lemma coordinate_radius_smul (c : ℝ) (x : Space n) :
    Cartesian.radius (c • x) = |c| *Cartesian.radius x := by
  simp only [Cartesian.radius,Cartesian.squareRadius,dotProduct,Pi.smul_apply,smul_eq_mul,mul_pow,
    show ∀ a : ℝ, a*a = a^2 from fun a => (pow_two a).symm,← Finset.mul_sum,Real.sqrt_mul (sq_nonneg c),Real.sqrt_sq_eq_abs]

end HarmonicCounterexample.Angular

end

noncomputable section
open Filter
open scoped BigOperators Topology ContDiff

namespace HarmonicCounterexample.Angular
open MvPolynomial Matrix Berger Cartesian
variable {n : ℕ}
lemma hopf_evaluate (J : ComplexStructure (Fin n)) (P : PolynomialSpace n) (x : Space n) :
    hopfDerivative J (evaluate P) x = evaluate (polynomialRotation J.matrix P) x := by
  simp only [hopfDerivative,Berger.gradient,dotProduct,Matrix.mulVec,coordDeriv_evaluate,
    polynomialRotation_apply,evaluate_sum,evaluate_smul,Angular.evaluate,eval_mul,eval_X,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end HarmonicCounterexample.Angular

end

noncomputable section
open Filter
open scoped BigOperators Topology ContDiff

namespace HarmonicCounterexample.Angular
open MvPolynomial Matrix Berger Cartesian
variable {n : ℕ}

lemma evaluate_zero_of_core {P : PolynomialSpace n}
    (hP : ∀ x, squareRadius x < 1 → evaluate P x = 0) : P = 0 := by
  let d : ℝ := 1/((n:ℝ)+1)
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hd : 0 < d := by positivity
  have hnd : (n:ℝ)*d^2 < 1 := by
    dsimp [d]
    rw [div_pow,one_pow,← mul_div_assoc,mul_one,div_lt_one (sq_pos_of_pos (by positivity))]
    nlinarith [sq_nonneg (n:ℝ)]
  apply MvPolynomial.funext_set (fun _ => Set.Ioo (-d) d)
    (fun _ => Set.Ioo_infinite (by linarith))
  intro x hx
  rw [map_zero]
  apply hP
  have hi (i : Fin n) : x i*x i ≤ d^2 := by
    have hh := hx i (Set.mem_univ i)
    nlinarith [hh.1,hh.2]
  have hs : squareRadius x ≤ (n:ℝ)*d^2 := by
    unfold squareRadius dotProduct
    calc
      _ ≤ ∑ i : Fin n,d^2 := Finset.sum_le_sum fun i _ => hi i
      _ = _ := by simp
  linarith

/-- Equality on the flat core determines the actual polynomial, not merely its
restriction to a formal angular vector space. -/
lemma evaluate_eq_of_core {P Q : PolynomialSpace n}
    (h : ∀ x, squareRadius x < 1 → evaluate P x = evaluate Q x) : P = Q := by
  apply sub_eq_zero.mp
  apply evaluate_zero_of_core
  intro x hx
  simp only [Angular.evaluate,eval_sub,h x hx,sub_self]

lemma rotation_evaluate (J : ComplexStructure (Fin n)) (l : ℕ)
    (P : harmonicPolynomials n l) (x : Space n) :
    hopfDerivative J (evaluate (P : PolynomialSpace n)) x =
      evaluate ((rotation J l P) : PolynomialSpace n) x := hopf_evaluate J P x

end HarmonicCounterexample.Angular

end

noncomputable section
open Filter
open scoped BigOperators Topology ContDiff

namespace HarmonicCounterexample.Cartesian
open Matrix Berger Angular MvPolynomial
variable {n : ℕ} {ι : Type*} [Fintype ι]

lemma synthesized_core_eq {l : ℝ} {P : ι → PolynomialSpace n} {Y : ℝ → ι → ℝ}
    {c : ι → ℝ} (hc : ∀ t ≤ 0, Y t = Real.exp (l*t) • c) {x : Space n}
    (hx : squareRadius x < 1) :
    synthesized l (fun i => evaluate (P i)) Y x = evaluate (∑ i,c i • P i) x := by
  have ht : logRadius x ≤ 0 := by
    unfold logRadius
    exact mul_nonpos_of_nonneg_of_nonpos (by norm_num)
      (Real.log_nonpos (squareRadius_nonneg x) hx.le)
  simp only [synthesized,regularCoefficient_core hc ht,evaluate_sum,evaluate_smul]

lemma synthesized_harmonic_at_zero (g : SmoothMetric n)
    (hg : ∀ᶠ x in 𝓝 0, g.coeff x = 1) {l : ℕ}
    (P : ι → harmonicPolynomials n l) {Y : ℝ → ι → ℝ} {c : ι → ℝ}
    (hc : ∀ t ≤ 0, Y t = Real.exp ((l:ℝ)*t) • c) :
    laplaceBeltrami g (synthesized l (fun i => evaluate (P i : PolynomialSpace n)) Y) 0 = 0 := by
  have he : synthesized l (fun i => evaluate (P i : PolynomialSpace n)) Y =ᶠ[𝓝 0]
      evaluate (∑ i,c i • (P i : PolynomialSpace n)) := by
    have hr : ∀ᶠ x : Space n in 𝓝 0,squareRadius x < 1 :=
      squareRadius_smooth.continuous.continuousAt.eventually (eventually_lt_nhds (by simp))
    exact hr.mono fun _ hx => synthesized_core_eq hc hx
  rw [laplace_congr g he,laplace_eq_euclidean_of_flat g hg,euclideanLaplacian_evaluate]
  have hh : polynomialLaplacian (∑ i,c i • (P i : PolynomialSpace n)) = 0 := by
    simp only [map_sum,map_smul,show ∀ i, polynomialLaplacian (P i : PolynomialSpace n) = 0 from
      fun i => (P i).property.2,smul_zero,Finset.sum_const_zero]
  simp only [hh,Angular.evaluate,map_zero]

/-- Global vanishing of synthesized functions forces vanishing of the initial
polynomial. No limiting separation argument, ODE inverse, or unique-continuation
claim is hidden here: the regular flow equals its polynomial on the open core. -/
lemma synthesized_injective_from_core {l : ℝ} {P : ι → PolynomialSpace n}
    {Y : ℝ → ι → ℝ} {c : ι → ℝ}
    (hc : ∀ t ≤ 0, Y t = Real.exp (l*t) • c)
    (hz : synthesized l (fun i => evaluate (P i)) Y = 0) :
    ∑ i,c i • P i = 0 := by
  apply evaluate_zero_of_core
  intro x hx
  rw [← synthesized_core_eq hc hx,hz]
  rfl

end HarmonicCounterexample.Cartesian

end

noncomputable section


namespace HarmonicCounterexample.Angular
open MvPolynomial Matrix Berger
open scoped ContDiff Topology InnerProductSpace
variable {n : ℕ}

/-- The round eigenvalue in degree l on S^(n-1). -/
def roundEigenvalue (n l : ℕ) : ℝ := (l:ℝ)*((l:ℝ)+(n:ℝ)-2)

lemma roundEigenvalue_nonneg {n : ℕ} (hn : 2 ≤ n) (l : ℕ) : 0 ≤ roundEigenvalue n l := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  unfold roundEigenvalue
  exact mul_nonneg (Nat.cast_nonneg l) (by linarith [Nat.cast_nonneg (α := ℝ) l])

/-- The actual negative Berger Laplacian on the genuine harmonic-polynomial
space. Here c is the horizontal metric coefficient and q the squared Hopf stretch (the manuscript q). -/
def angularOperator (J : ComplexStructure (Fin n)) (l : ℕ) (c q : ℝ) :
    harmonicPolynomials n l →L[ℝ] harmonicPolynomials n l :=
  c⁻¹ • (roundEigenvalue n l • (1 : harmonicPolynomials n l →L[ℝ] harmonicPolynomials n l) +
    (1-(q)⁻¹) • (rotationCLM J l*rotationCLM J l))

lemma angularOperator_round (J : ComplexStructure (Fin n)) (l : ℕ) (c : ℝ) :
    angularOperator J l c 1 = (c⁻¹*roundEigenvalue n l) • 1 := by
  ext P
  simp only [angularOperator,inv_one,sub_self,_root_.smul_apply,_root_.add_apply,
    one_apply_eq_self,_root_.zero_smul,_root_.add_zero,_root_.smul_smul]

lemma angularOperator_inner (J : ComplexStructure (Fin n)) (l : ℕ) (c q : ℝ)
    (P : harmonicPolynomials n l) :
    ⟪P,angularOperator J l c q P⟫_ℝ = c⁻¹*(roundEigenvalue n l*‖P‖^2+
      (1-(q)⁻¹)*⟪P,(rotationCLM J l*rotationCLM J l) P⟫_ℝ) := by
  simp only [angularOperator,_root_.smul_apply,_root_.add_apply,
    one_apply_eq_self,_root_.inner_smul_right,_root_.inner_add_right,real_inner_self_eq_norm_sq]

lemma angularOperator_symmetric (J : ComplexStructure (Fin n)) (l : ℕ) (c q : ℝ) :
    (angularOperator J l c q).IsSymmetric := by
  intro P Q
  change ⟪angularOperator J l c q P,Q⟫_ℝ = ⟪P,angularOperator J l c q Q⟫_ℝ
  simp only [angularOperator,_root_.smul_apply,_root_.add_apply,
    one_apply_eq_self,_root_.inner_smul_left,_root_.inner_smul_right,_root_.inner_add_left,_root_.inner_add_right,
    conj_trivial]
  have hs : ⟪(rotationCLM J l*rotationCLM J l) P,Q⟫_ℝ =
      ⟪P,(rotationCLM J l*rotationCLM J l) Q⟫_ℝ := rotationCLM_square_symmetric J l P Q
  rw [hs]

lemma angularOperator_lower (J : ComplexStructure (Fin n)) (l : ℕ) {c q : ℝ}
    (hc : 0 < c) (hq : 1 ≤ q) (P : harmonicPolynomials n l) :
    c⁻¹*(roundEigenvalue n l-(1-(q)⁻¹)*(l:ℝ)^2)*‖P‖^2 ≤
      ⟪P,angularOperator J l c q P⟫_ℝ := by
  have hd : 0 ≤ 1-(q)⁻¹ := sub_nonneg.2 (inv_le_one_of_one_le₀ hq)
  have h := mul_le_mul_of_nonneg_left (rotationCLM_square_lower J l P) hd
  rw [angularOperator_inner]
  have hi : 0 ≤ c⁻¹ := inv_nonneg.2 hc.le
  have hh := mul_le_mul_of_nonneg_left h hi
  nlinarith

lemma angularOperator_nonnegative_of_one_le {n : ℕ} (hn : 2 ≤ n)
    (J : ComplexStructure (Fin n)) (l : ℕ) {c q : ℝ}
    (hc : 0 < c) (hq : 1 ≤ q) (P : harmonicPolynomials n l) :
    0 ≤ ⟪P,angularOperator J l c q P⟫_ℝ := by
  apply le_trans _ (angularOperator_lower J l hc hq P)
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hq' : 0 ≤ (q)⁻¹ := inv_nonneg.2 (le_trans zero_le_one hq)
  have he : roundEigenvalue n l-(1-(q)⁻¹)*(l:ℝ)^2 =
      (l:ℝ)*((n:ℝ)-2)+(q)⁻¹*(l:ℝ)^2 := by unfold roundEigenvalue; ring
  rw [he]
  exact mul_nonneg (mul_nonneg (inv_nonneg.2 hc.le)
    (add_nonneg (mul_nonneg (Nat.cast_nonneg l) (by linarith))
      (mul_nonneg hq' (sq_nonneg _)))) (sq_nonneg _)

lemma angularOperator_positive_lower {n : ℕ} (hn : 2 ≤ n)
    (J : ComplexStructure (Fin n)) (l : ℕ) {c q : ℝ}
    (hc : 0 < c) (hq : 0 < q) (P : harmonicPolynomials n l) :
    c⁻¹*min 1 q⁻¹*(l:ℝ)^2*‖P‖^2 ≤ ⟪P,angularOperator J l c q P⟫_ℝ := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hi : 0 ≤ c⁻¹ := inv_nonneg.2 hc.le
  by_cases h : 1 ≤ q
  · apply le_trans _ (angularOperator_lower J l hc h P)
    have he : roundEigenvalue n l-(1-q⁻¹)*(l:ℝ)^2 =
        (l:ℝ)*((n:ℝ)-2)+q⁻¹*(l:ℝ)^2 := by unfold roundEigenvalue; ring
    rw [min_eq_right (inv_le_one_of_one_le₀ h),he]
    have h0 : 0 ≤ (l:ℝ)*((n:ℝ)-2) := mul_nonneg (Nat.cast_nonneg l) (by linarith)
    have := mul_nonneg (mul_nonneg hi h0) (sq_nonneg ‖P‖)
    nlinarith
  · have hqi : 1 ≤ q⁻¹ := (one_le_inv₀ hq).2 (le_of_not_ge h)
    have hrot := mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 hqi)
      (rotationCLM_square_nonpos J l P)
    rw [min_eq_left hqi,angularOperator_inner]
    have he : (l:ℝ)^2 ≤ roundEigenvalue n l := by
      unfold roundEigenvalue
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) l) (sub_nonneg.2 hn')]
    have hmul := mul_le_mul_of_nonneg_right he (sq_nonneg ‖P‖)
    have hh := mul_le_mul_of_nonneg_left hmul hi
    have hpos := mul_nonneg hi hrot
    nlinarith

lemma angularOperator_nonnegative {n : ℕ} (hn : 2 ≤ n)
    (J : ComplexStructure (Fin n)) (l : ℕ) {c q : ℝ}
    (hc : 0 < c) (hq : 0 < q) (P : harmonicPolynomials n l) :
    0 ≤ ⟪P,angularOperator J l c q P⟫_ℝ := by
  apply le_trans _ (angularOperator_positive_lower hn J l hc hq P)
  positivity

lemma angularOperator_norm_le (J : ComplexStructure (Fin n)) (l : ℕ) (c q : ℝ) :
    ‖angularOperator J l c q‖ ≤ |c⁻¹| *(|roundEigenvalue n l|+|1-(q)⁻¹| *(l:ℝ)^2) := by
  rw [angularOperator,norm_smul,Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  calc
    _ ≤ ‖roundEigenvalue n l • (1 : harmonicPolynomials n l →L[ℝ] harmonicPolynomials n l)‖+
        ‖(1-(q)⁻¹) • (rotationCLM J l*rotationCLM J l)‖ := @norm_add_le (harmonicPolynomials n l →L[ℝ] harmonicPolynomials n l) _ _ _
    _ ≤ |roundEigenvalue n l|+|1-(q)⁻¹| *(l:ℝ)^2 := by
      simp only [norm_smul,Real.norm_eq_abs]
      apply add_le_add
      · exact (mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_id_le) (abs_nonneg _)).trans_eq (mul_one _)
      · apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        calc
          _ ≤ ‖rotationCLM J l‖*‖rotationCLM J l‖ := ContinuousLinearMap.opNorm_comp_le (rotationCLM J l) (rotationCLM J l)
          _ ≤ (l:ℝ)*(l:ℝ) := mul_self_le_mul_self (@norm_nonneg (harmonicPolynomials n l →L[ℝ] harmonicPolynomials n l) _ (rotationCLM J l)) (rotationCLM_opNorm_le J l)
          _ = _ := (sq _).symm

lemma angularOperator_smooth (J : ComplexStructure (Fin n)) (l : ℕ)
    {c q : ℝ → ℝ} (hc : ContDiff ℝ ∞ c) (hq : ContDiff ℝ ∞ q)
    (hc0 : ∀ t,c t ≠ 0) (hq0 : ∀ t,q t ≠ 0) :
    ContDiff ℝ ∞ (fun t => angularOperator J l (c t) (q t)) := by
  let : Module ℝ (harmonicPolynomials n l →L[ℝ] harmonicPolynomials n l) :=
    ContinuousLinearMap.module
  exact (hc.inv hc0).smul (contDiff_const.add
    ((contDiff_const.sub (hq.inv hq0)).smul
      (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => rotationCLM J l*rotationCLM J l))))

/-- Switching the genuine angular rotation on an open round gap is smooth,
although the label itself need not be continuous there. -/
lemma angularOperator_glued_smooth (J : ℝ → ComplexStructure (Fin n)) (l : ℕ)
    {c q : ℝ → ℝ} (hc : ContDiff ℝ ∞ c) (hq : ContDiff ℝ ∞ q)
    (hc0 : ∀ t,c t ≠ 0) (hq0 : ∀ t,q t ≠ 0)
    (hJ : ∀ t,(∀ᶠ s in nhds t,J s = J t) ∨ (∀ᶠ s in nhds t,q s = 1)) :
    ContDiff ℝ ∞ (fun t => angularOperator (J t) l (c t) (q t)) := by
  let : Module ℝ (harmonicPolynomials n l →L[ℝ] harmonicPolynomials n l) :=
    ContinuousLinearMap.module
  rw [contDiff_iff_contDiffAt]
  intro t
  rcases hJ t with hfixed | hround
  · apply ((angularOperator_smooth (J t) l hc hq hc0 hq0).contDiffAt).congr_of_eventuallyEq
    exact hfixed.mono fun s hs => by dsimp only; rw [hs]
  · have hs : ContDiff ℝ ∞ (fun s => ((c s)⁻¹*roundEigenvalue n l) •
        (1 : harmonicPolynomials n l →L[ℝ] harmonicPolynomials n l)) :=
      ((hc.inv hc0).mul (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => roundEigenvalue n l))).smul
        (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ =>
          (1 : harmonicPolynomials n l →L[ℝ] harmonicPolynomials n l)))
    apply hs.contDiffAt.congr_of_eventuallyEq
    exact hround.mono fun s hqs => by dsimp only; rw [hqs,angularOperator_round]

end HarmonicCounterexample.Angular

end

noncomputable section


namespace HarmonicCounterexample.Angular
open Module MvPolynomial Matrix Berger Cartesian
open scoped ContDiff
variable {n l : ℕ} {ι : Type*} [Fintype ι]

/-- Coordinates in a fixed basis of actual harmonic polynomials. -/
def coordinates (b : Basis ι ℝ (harmonicPolynomials n l)) :
    harmonicPolynomials n l ≃L[ℝ] (ι → ℝ) := b.equivFun.toContinuousLinearEquiv

lemma coordinates_sum (b : Basis ι ℝ (harmonicPolynomials n l))
    (P : harmonicPolynomials n l) : ∑ i, coordinates b P i • b i = P := b.sum_equivFun P

lemma basis_evaluate (b : Basis ι ℝ (harmonicPolynomials n l))
    (P : harmonicPolynomials n l) (x : Space n) :
    (∑ i, coordinates b P i*evaluate (b i : PolynomialSpace n) x) =
      evaluate (P : PolynomialSpace n) x := by
  have h := congrArg (fun Q : harmonicPolynomials n l => evaluate (Q : PolynomialSpace n) x)
    (coordinates_sum b P)
  simpa only [Submodule.coe_sum, Submodule.coe_smul,evaluate_sum,evaluate_smul] using h

lemma basis_operator_coordinates (b : Basis ι ℝ (harmonicPolynomials n l))
    (T : harmonicPolynomials n l →L[ℝ] harmonicPolynomials n l)
    (P : harmonicPolynomials n l) (i : ι) :
    coordinates b (T P) i = ∑ j,coordinates b (T (b j)) i*coordinates b P j := by
  have h := congrArg (fun Q => coordinates b (T Q) i) (coordinates_sum b P)
  rw [← h]
  simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma square_rotation_basis_evaluate (b : Basis ι ℝ (harmonicPolynomials n l))
    (J : ComplexStructure (Fin n)) (i : ι) (x : Space n) :
    hopfDerivative J (hopfDerivative J (evaluate (b i : PolynomialSpace n))) x =
      ∑ j,coordinates b ((rotationCLM J l*rotationCLM J l) (b i)) j*
        evaluate (b j : PolynomialSpace n) x := by
  rw [basis_evaluate]
  have he (P : harmonicPolynomials n l) :
      hopfDerivative J (evaluate (P : PolynomialSpace n)) =
        evaluate (rotationCLM J l P : PolynomialSpace n) := funext (rotation_evaluate J l P)
  rw [he,he]
  rfl

lemma angularOperator_basis_coordinates (b : Basis ι ℝ (harmonicPolynomials n l))
    (J : ComplexStructure (Fin n)) (c q : ℝ) (P : harmonicPolynomials n l) (i : ι) :
    coordinates b (angularOperator J l c q P) i =
      c⁻¹*roundEigenvalue n l*coordinates b P i +
      c⁻¹*(1-q⁻¹)*(∑ j,coordinates b ((rotationCLM J l*rotationCLM J l) (b j)) i*
        coordinates b P j) := by
  change coordinates b (c⁻¹ • (roundEigenvalue n l • P +
    (1-q⁻¹) • ((rotationCLM J l*rotationCLM J l) P))) i = _
  simp only [map_smul,map_add,Pi.smul_apply,Pi.add_apply,smul_eq_mul]
  rw [basis_operator_coordinates b (rotationCLM J l*rotationCLM J l) P i]
  ring

end HarmonicCounterexample.Angular

end

noncomputable section


namespace HarmonicCounterexample.Construction
open Filter Set Schedule AngularStream LinearODE Berger Cartesian Pulses
open FiniteControl.SmoothWord
open scoped Topology ContDiff InnerProductSpace

variable (L:ℕ) [NeZero L]

/-- A single constructed infinite history, including the thresholds and exact
whole-period equalities, for any prescribed determinant-one simultaneous target. -/
structure Stream (target:∀l:Fin L,Matrix.SpecialLinearGroup (Index l.val) ℝ) where
  word : PhysicalWord CS
  j0 : ℕ
  s : ℕ→Fin word.n→ℝ
  admissible : ∀j,s j∈word.admissible
  zero : ∀j,j<j0→s j=0
  packet : ∀j,j0≤j→∀t i,packetStretch (s j) (pulse j) t i∈Icc (1/2:ℝ) (3/2)
  d : ℝ→Fin word.n
  selects : ∀t i,i≠d t→bump i (duration word.n*t)=0
  local_round : ∀t,(∀ᶠu in 𝓝 t,d u=d t) ∨
    (∀ᶠu in 𝓝 t,∀a:Fin word.n→ℝ,unitPacketScalar a u=0)
  qbounds : ∀t,scalar s qstar j0 t∈Icc (1/2:ℝ) 2
  curvature : ∀t,let q:=scalar s qstar j0
    let u:=horizontalSlope mu q
    let v:=logSlope q
    0≤radialRicciNumerator 16 (u t) (v t) (deriv u t) (deriv v t) ∧
    0≤horizontalRicciNumerator 16 (horizontalScale mu q t) (q t) (u t) (v t) (deriv u t) ∧
    0≤verticalRicciNumerator 16 (horizontalScale mu q t) (q t) (u t) (v t) (deriv u t) (deriv v t)
  period : ∀j,j0≤j→∀l:Fin L,∃z:ℝ,z∈Ioo (1/2:ℝ) (3/2) ∧
    (geometry L).transmission word.slot s j0 j l=
      (Real.exp (∫t in time j..time j+pulse j,(geometry L).baseline j l t)*z) •
      (((geometry L).legU (fun l=>d0 l.val) j0 j l+
        (theta l.val) • (geometry L).legV (fun l=>d0 l.val) j0 j l)*(target l:Matrix _ _ ℝ))

lemma exists_stream (target:∀l:Fin L,Matrix.SpecialLinearGroup (Index l.val) ℝ) :
    Nonempty (Stream L target) := by
  obtain ⟨w,N,ht⟩ := global_actual_transmission (system L) (geometry L)
    (fun l=>d0 l.val) (fun l=>by convert Dround_diagonal l.val using 1; simp only [system,geometry]) (generator_trace L)
    (generator_full L) target
  let : NeZero w.n := ⟨w.n_ne⟩
  obtain ⟨N',hN'⟩ := scalar_all_curvatures w mu_pos mu_le profile_limit
  let j0 := max N N'
  obtain ⟨s,hs,hzero,hpacket,htrans⟩ := ht j0 (le_max_left _ _)
  obtain ⟨d,hd,hdlocal⟩ := exists_unit_round_gap_selector w.n
  obtain ⟨hqb,hcurv⟩ := hN' j0 (le_max_right _ _) s hs
  refine ⟨⟨w,j0,s,hs,hzero,hpacket,d,(fun t i hi=>(hd t i hi).1),hdlocal,?_,hcurv,?_⟩⟩
  · intro t
    exact ⟨(hqb t).1,(hqb t).2.trans (by norm_num [qstar])⟩
  · intro j hj l
    obtain ⟨D,hD,hDp,z,hz,he⟩ := htrans j hj l
    refine ⟨z,hz,?_⟩
    rw [hD] at he
    exact he

variable {L} {target:∀l:Fin L,Matrix.SpecialLinearGroup (Index l.val) ℝ}
namespace Stream
omit [NeZero L]
variable (F:Stream L target)
instance : NeZero F.word.n := ⟨F.word.n_ne⟩

def q : ℝ→ℝ := scalar F.s qstar F.j0
def c : ℝ→ℝ := horizontalScale mu F.q
def J (t:ℝ) : ComplexStructure (Fin 16) :=
  (globalSlot F.d F.j0 t).elim Jround
    (fun i=>(F.word.slot i).reindex (finSumFinEquiv (m:=8) (n:=8)).symm)

lemma q_pos (t:ℝ) : 0<F.q t := lt_of_lt_of_le (by norm_num) (F.qbounds t).1
lemma q_smooth : ContDiff ℝ ∞ F.q := scalar_smooth F.s qstar F.j0
lemma c_pos (t:ℝ) : 0<F.c t := horizontalScale_pos F.q_pos mu t
lemma c_smooth : ContDiff ℝ ∞ F.c := horizontalScale_smooth F.q_smooth F.q_pos mu
lemma J_local (t:ℝ) : (∀ᶠu in 𝓝 t,F.J u=F.J t) ∨ (∀ᶠu in 𝓝 t,F.q u=1) := by
  rcases globalSlot_local_or_round F.d F.local_round F.s qstar F.j0 t with h|h
  · left;exact h.mono (fun u hu=>by simp only [J,hu])
  · exact Or.inr h
lemma q_center (t:ℝ) (ht:t≤0) : F.q t=1 := scalar_initial F.s (ht.trans (time_pos F.j0).le)
lemma c_center (t:ℝ) (ht:t≤0) : F.c t=1 := horizontalScale_initial F.s F.j0 mu ht

def metric : SmoothMetric 16 := bergerMetric F.c F.q F.J F.c_smooth F.q_smooth
  F.c_pos F.q_pos F.J_local F.c_center F.q_center

lemma geometry_main : Complete F.metric ∧ EuclideanNearOrigin F.metric ∧
    PositiveSubunitAVR F.metric ∧ ∀x,distance F.metric 0 x=radius x :=
  profile_metric_global mu_pos.le F.q_smooth F.qbounds F.J F.J_local
    F.c_center F.q_center profile_limit

lemma ricci : RicciNonnegative F.metric := by
  apply bergerMetric_ricciNonnegative F.c F.q (horizontalSlope mu F.q) (logSlope F.q)
    F.J F.c_smooth F.q_smooth F.c_pos F.q_pos F.J_local F.c_center F.q_center
  · exact horizontalScale_hasDeriv (F.q_smooth.differentiable (by simp)) F.q_pos mu
  · exact logSlope_hasDeriv (F.q_smooth.differentiable (by simp)) F.q_pos
  · exact (horizontalSlope_smooth F.q_smooth F.q_pos mu).differentiable (by simp)
  · exact (logSlope_smooth F.q_smooth F.q_pos).differentiable (by simp)
  · intro t;exact (F.curvature t).1
  · intro t;exact (F.curvature t).2.1
  · intro t;exact (F.curvature t).2.2

lemma drift_eq (t:ℝ) : drift t=14+15*horizontalSlope mu F.q t+logSlope F.q t := by
  unfold drift horizontalSlope;ring

lemma coefficient_eq (l:Fin L) (t:ℝ) :
    (geometry L).coefficient F.word.slot F.s F.j0 l t=
      Angular.angularOperator (F.J t) (l.val+2) (F.c t) (F.q t) := by
  rw [HistoryGeometry.coefficient,angular_globalSlot _ _ _ _ F.d F.selects]
  have hD : ((globalSlot F.d F.j0 t).elim ((geometry L).D₀ l)
      (fun i=>(system L).D l (F.word.slot i)))=
      Angular.rotationCLM (F.J t) (l.val+2)*Angular.rotationCLM (F.J t) (l.val+2) := by
    cases h : globalSlot F.d F.j0 t <;>
      simp only [J,h,Option.elim,system,geometry,Dround,D,Jround]
  rw [hD]
  have hB : (system L).B l=Angular.roundEigenvalue 16 (l.val+2) := by
    simp only [system,B,degree,Angular.roundEigenvalue,Nat.cast_add,Nat.cast_ofNat];ring
  change alpha t • PulseTaylor.angular (1/15) ((system L).B l • 1)
    (Angular.rotationCLM (F.J t) (l.val+2)*Angular.rotationCLM (F.J t) (l.val+2)) (F.q t)=_
  rw [hB]
  have hc : (F.c t)⁻¹=alpha t*(F.q t)^(1/15:ℝ) := by
    rw [c,horizontalScale,_root_.mul_inv_rev,show (-1:ℝ)/15=-(1/15) by ring,Real.rpow_neg (F.q_pos t).le]
    simp only [inv_inv,alpha];ring
  have hr : (F.q t)^(1/15:ℝ)-(F.q t)^((1/15:ℝ)-1)=
      (F.q t)^(1/15:ℝ)*(1-(F.q t)⁻¹) := by
    rw [Real.rpow_sub_one (F.q_pos t).ne'];ring
  rw [PulseTaylor.angular,Angular.angularOperator,hc,hr]
  module

end Stream
end HarmonicCounterexample.Construction

end

end OAI
