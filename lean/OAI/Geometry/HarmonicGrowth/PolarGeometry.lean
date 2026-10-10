import OAI.Geometry.HarmonicGrowth.GlobalControl
import OAI.Geometry.HarmonicGrowth.SpectralSelection

namespace OAI

noncomputable section


namespace HarmonicCounterexample.Construction
open Filter Set Schedule Pulses AngularStream Berger Cartesian
open scoped Topology ContDiff

def horizontalScale (μ : ℝ) (q : ℝ → ℝ) (t : ℝ) : ℝ :=
  (Scale.profile μ t)^2*(q t)^(-1/15:ℝ)

def horizontalSlope (μ : ℝ) (q : ℝ → ℝ) (t : ℝ) : ℝ :=
  Scale.slope μ t-logSlope q t/15

lemma horizontalScale_smooth {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    (hqp : ∀ t,0<q t) (μ : ℝ) : ContDiff ℝ ∞ (horizontalScale μ q) :=
  ((Scale.profile_smooth μ).pow 2).mul (hq.rpow_const_of_ne (fun t => (hqp t).ne'))

lemma horizontalScale_pos {q : ℝ → ℝ} (hqp : ∀ t,0<q t) (μ t : ℝ) :
    0<horizontalScale μ q t :=
  mul_pos (sq_pos_of_pos (Scale.profile_pos μ t)) (Real.rpow_pos_of_pos (hqp t) _)

lemma horizontalSlope_smooth {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    (hqp : ∀ t,0<q t) (μ : ℝ) : ContDiff ℝ ∞ (horizontalSlope μ q) :=
  (contDiff_const.mul Scale.weight_smooth).sub ((logSlope_smooth hq hqp).div_const 15)

lemma logSlope_hasDeriv {q : ℝ → ℝ} (hq : Differentiable ℝ q)
    (hqp : ∀ t,0<q t) (t : ℝ) : HasDerivAt q (2*q t*logSlope q t) t := by
  convert! (hq t).hasDerivAt using 1
  unfold logSlope
  field_simp [(hqp t).ne']

lemma horizontalScale_hasDeriv {q : ℝ → ℝ} (hq : Differentiable ℝ q)
    (hqp : ∀ t,0<q t) (μ t : ℝ) :
    HasDerivAt (horizontalScale μ q) (2*horizontalScale μ q t*horizontalSlope μ q t) t := by
  have hd := ((Scale.profile_hasDerivAt μ t).pow 2).mul
    (((hq t).hasDerivAt).rpow_const (p:=(-1/15:ℝ)) (Or.inl (hqp t).ne'))
  convert! hd using 1
  rw [Real.rpow_sub_one (hqp t).ne']
  unfold horizontalScale horizontalSlope logSlope
  simp only [Pi.pow_apply]
  field_simp
  ring

lemma horizontalSlope_deriv {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    (hqp : ∀ t,0<q t) (μ t : ℝ) :
    deriv (horizontalSlope μ q) t=deriv (Scale.slope μ) t-deriv (logSlope q) t/15 := by
  exact (((contDiff_const.mul Scale.weight_smooth).differentiable (by simp) t).hasDerivAt.sub
    (((logSlope_smooth hq hqp).differentiable (by simp) t).hasDerivAt.div_const 15)).deriv

variable {n : ℕ}
lemma scalar_initial_local (s : ℕ → Fin n → ℝ) (j0 : ℕ) {t : ℝ} (ht : t ≤ time j0) :
    ∀ᶠ u in 𝓝 t,scalar s qstar j0 u=1 := by
  rcases ht.lt_or_eq with ht|ht
  · filter_upwards [eventually_lt_nhds ht] with u hu
    exact scalar_initial s hu.le
  · subst t;exact scalar_start_collar s qstar le_rfl

lemma logSlope_initial_local (s : ℕ → Fin n → ℝ) (j0 : ℕ) {t : ℝ} (ht : t ≤ time j0) :
    logSlope (scalar s qstar j0) t=0 ∧ deriv (logSlope (scalar s qstar j0)) t=0 := by
  have he : scalar s qstar j0 =ᶠ[𝓝 t] (fun _ => (1:ℝ)) := scalar_initial_local s j0 ht
  have hv : logSlope (scalar s qstar j0) =ᶠ[𝓝 t] (fun _ => (0:ℝ)) := by
    filter_upwards [he.deriv] with u hu
    simp only [deriv_const] at hu
    simp only [logSlope,hu,zero_div]
  exact ⟨hv.eq_of_nhds,by simpa only [deriv_const] using hv.deriv_eq⟩

lemma horizontalScale_initial (s : ℕ → Fin n → ℝ) (j0 : ℕ) (μ : ℝ)
    {t : ℝ} (ht : t ≤ 0) : horizontalScale μ (scalar s qstar j0) t=1 := by
  rw [horizontalScale,Scale.profile_initial (by linarith),scalar_initial s (ht.trans (time_pos j0).le)]
  simp

/-- The early round region is handled by exact radial concavity; the late
 threshold controls all periods, for the same q and c used to tune the equation. -/
theorem scalar_all_curvatures {κ : Type*} (w : LinearODE.PhysicalWord κ)
    {μ : ℝ} (hμ : 0<μ) (hμ1 : μ≤1/4) (ha : Tendsto (Scale.profile μ) atTop (𝓝 a)) :
    ∃ J : ℕ,∀ j0,J≤j0 → ∀ s : ℕ → Fin w.n → ℝ,(∀ j,s j ∈ w.admissible) →
      (∀ t,1/2 ≤ scalar s qstar j0 t ∧ scalar s qstar j0 t ≤ qstar+1/2) ∧
      ∀ t,let q:=scalar s qstar j0
        let u:=horizontalSlope μ q
        let v:=logSlope q
        0 ≤ radialRicciNumerator 16 (u t) (v t) (deriv u t) (deriv v t) ∧
        0 ≤ horizontalRicciNumerator 16 (horizontalScale μ q t) (q t) (u t) (v t) (deriv u t) ∧
        0 ≤ verticalRicciNumerator 16 (horizontalScale μ q t) (q t) (u t) (v t) (deriv u t) (deriv v t) := by
  obtain ⟨J,hJ⟩ := w.curvature_threshold (m:=15) (by norm_num) hμ hμ1 qstar_ge_one ha
    static_horizontal static_vertical
  refine ⟨J,fun j0 hj0 s hs => ?_⟩
  have hb := hJ j0 hj0 s hs
  refine ⟨hb.1,fun t => ?_⟩
  dsimp only
  have hqp (u : ℝ) : 0<scalar s qstar j0 u := by linarith [(hb.1 u).1]
  rw [horizontalSlope_deriv (scalar_smooth s qstar j0) hqp]
  by_cases ht : t ≤ time j0
  · obtain ⟨hv,hdv⟩ := logSlope_initial_local s j0 ht
    have hq := scalar_initial (qstar:=qstar) s ht
    have hc := Berger.roundRicci_nonnegative (m:=15)
      (by norm_num) (sq_nonneg (Scale.profile μ t))
      (by nlinarith [Scale.profile_pos μ t,Scale.profile_le_one hμ.le t])
      (by linarith [Scale.slope_lower hμ.le hμ1 t]) (Scale.slope_nonpos hμ.le t)
      (Scale.radial_concavity hμ.le hμ1 t)
    simpa only [horizontalScale,horizontalSlope,hv,hdv,hq,Real.one_rpow,mul_one,
      zero_div,sub_zero,show (15:ℝ)+1=16 by norm_num] using hc
  · obtain ⟨j,hj,hlo,hhi⟩ := GlobalGrowth.grid_bracket time_atTop j0 (le_of_not_ge ht)
    have hc := hb.2 j hj t ⟨hlo,hhi⟩
    simpa only [horizontalScale,horizontalSlope,show (15:ℝ)+1=16 by norm_num] using
      And.intro hc.1 (And.intro hc.2.1.le hc.2.2.le)
end HarmonicCounterexample.Construction

end

noncomputable section


namespace HarmonicCounterexample.Construction
open Filter LinearODE
open scoped Topology ContDiff

def mu : ℝ := exists_scale.choose
lemma mu_pos : 0 < mu := exists_scale.choose_spec.1
lemma mu_le : mu≤1/4 := exists_scale.choose_spec.2.1
lemma profile_limit : Tendsto (Scale.profile mu) atTop (𝓝 a) := exists_scale.choose_spec.2.2.1
lemma scale_match : Real.exp (-mu*Scale.total)=a := exists_scale.choose_spec.2.2.2
lemma profile_lower (t:ℝ) : a≤Scale.profile mu t := by
  rw [← scale_match];exact Scale.profile_lower mu_pos.le t

def alpha (t:ℝ) : ℝ := (Scale.profile mu t^2)⁻¹
def drift (t:ℝ) : ℝ := 14+15*Scale.slope mu t

lemma alpha_smooth : ContDiff ℝ ∞ alpha :=
  ((Scale.profile_smooth mu).pow 2).inv (fun t=>pow_ne_zero _ (Scale.profile_pos mu t).ne')
lemma alpha_pos (t:ℝ) : 0<alpha t := inv_pos.mpr (sq_pos_of_pos (Scale.profile_pos mu t))
lemma alpha_bound (t:ℝ) : |alpha t|≤2 := by
  rw [abs_of_pos (alpha_pos t)]
  have hp := profile_lower t
  have h := a_lower
  unfold alpha
  apply (inv_le_comm₀ (sq_pos_of_pos (Scale.profile_pos mu t)) (by norm_num)).mpr
  norm_num
  nlinarith
lemma drift_smooth : ContDiff ℝ ∞ drift :=
  contDiff_const.add (contDiff_const.mul (contDiff_const.mul Scale.weight_smooth))
lemma drift_bounds (t:ℝ) : 10≤drift t ∧ |drift t|≤14 := by
  have h1 := Scale.slope_lower mu_pos.le mu_le t
  have h2 := Scale.slope_nonpos mu_pos.le t
  dsimp [drift]
  constructor
  · linarith
  · rw [abs_of_nonneg (by linarith)];linarith
lemma alpha_center (t:ℝ) (ht:t≤0) : alpha t=1 := by
  simp only [alpha,Scale.profile_initial (ht.trans (by norm_num : (0:ℝ)≤2)),one_pow,inv_one]
lemma drift_center (t:ℝ) (ht:t≤0) : drift t=14 := by
  simp only [drift,Scale.slope,Scale.weight_zero (ht.trans (by norm_num : (0:ℝ)≤5/2)),mul_zero,add_zero]
lemma alpha_limit : Tendsto alpha atTop (𝓝 beta) :=
  (profile_limit.pow 2).inv₀ (pow_ne_zero _ a_pos.ne')
lemma drift_limit : Tendsto drift atTop (𝓝 14) := by
  unfold drift
  convert (tendsto_const_nhds (x := (14:ℝ))).add ((Scale.slope_limit mu).const_mul 15) using 1
  norm_num

def geometry (L:ℕ) : HistoryGeometry (system L) where
  D₀ l := Dround l.val
  D₀nonpos l := D_nonpos l.val _
  BD₀ l := D_lower l.val _
  D₀symm l := D_symmetric l.val _
  Dsymm l := D_symmetric l.val
  qstar := qstar
  qstar_ge := qstar_ge_one
  l l := degree l.val
  lpos l := degree_pos l.val
  B₀ := 14
  B_eq _ := rfl
  α := alpha
  drift := drift
  Mp := 14
  Mpnonneg := by norm_num
  αsmooth := alpha_smooth
  driftContinuous := drift_smooth.continuous
  αbound := alpha_bound
  αnonneg t := (alpha_pos t).le
  driftBound t := (drift_bounds t).2
  αcenter := alpha_center
  driftCenter := drift_center
  αlimit _ := alpha_limit
  driftLimit := drift_limit
  driftLower := Filter.Eventually.of_forall (fun t=>(drift_bounds t).1)

end HarmonicCounterexample.Construction

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff

namespace HarmonicCounterexample.Berger
open Matrix
variable {n : ℕ}

def tensorContract (M T : Mat n) : ℝ := ∑ i, ∑ j, M i j * T i j

lemma contract_add (M T U : Mat n) :
    tensorContract M (T+U) = tensorContract M T + tensorContract M U := by
  simp [tensorContract, mul_add, Finset.sum_add_distrib]

lemma contract_smul (M T : Mat n) (a : ℝ) :
    tensorContract M (a • T) = a * tensorContract M T := by
  simp only [tensorContract, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma contract_rank (M : Mat n) (u v : Space n) :
    tensorContract M (vecMulVec u v) = u ⬝ᵥ (M *ᵥ v) := by
  simp only [tensorContract, Matrix.vecMulVec_apply, dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma contract_identity (M : Mat n) : tensorContract M 1 = M.trace := by
  simp [tensorContract, Matrix.one_apply, Matrix.trace]

lemma symmetric_pairing (M : Mat n) (hM : M.IsSymm) (u v : Space n) :
    u ⬝ᵥ (M *ᵥ v) = v ⬝ᵥ (M *ᵥ u) := by
  rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, hM, dotProduct_comm]

lemma connection_lower_matrix (J : ComplexStructure (Fin n)) (x : Space n)
    (a b c d e f : ℝ) (k : Fin n) :
    (fun i j => connectionCoeff J x a b c d e f k i j) =
      a • (vecMulVec x (Pi.single k 1) + vecMulVec (Pi.single k 1) x) +
      (b*x k) • (1:Mat n) + (c*x k) • vecMulVec x x +
      (d*(J.matrix *ᵥ x) k) • (vecMulVec x (J.matrix *ᵥ x) + vecMulVec (J.matrix *ᵥ x) x) +
      (e*x k) • vecMulVec (J.matrix *ᵥ x) (J.matrix *ᵥ x) +
      f • (vecMulVec (J.matrix k) (J.matrix *ᵥ x) + vecMulVec (J.matrix *ᵥ x) (J.matrix k)) := by
  ext i j
  simp only [connectionCoeff, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.vecMulVec_apply, Matrix.one_apply, Pi.single_apply]
  simp only [eq_comm]
  ring

lemma contract_connection (J : ComplexStructure (Fin n)) (x : Space n)
    (M : Mat n) (hM : M.IsSymm) (D : ℝ)
    (hx : M *ᵥ x = x) (hw : M *ᵥ (J.matrix *ᵥ x) = D • (J.matrix *ᵥ x))
    (a b c d e f : ℝ) (k : Fin n) :
    tensorContract M (fun i j => connectionCoeff J x a b c d e f k i j) =
      (2*a+b*M.trace+c*(x ⬝ᵥ x)+e*D*(x ⬝ᵥ x)-2*f*D)*x k := by
  rw [connection_lower_matrix]
  simp only [contract_add, contract_smul, contract_rank, contract_identity]
  rw [symmetric_pairing M hM x (Pi.single k 1), hx,
    symmetric_pairing M hM (J.matrix *ᵥ x) (J.matrix k), hw]
  have horth : (J.matrix *ᵥ x) ⬝ᵥ x = 0 := by rw [dotProduct_comm, J.orthogonal_radial]
  simp only [single_dotProduct, one_mul, dotProduct_smul, smul_eq_mul,
    J.orthogonal_radial, horth, J.preserves_dot, mul_zero, add_zero]
  have hj : J.matrix k ⬝ᵥ (J.matrix *ᵥ x) = -x k := by
    exact congrFun (J.square_mulVec x) k
  rw [hj]
  ring

lemma polarTensor_symmetric (J : ComplexStructure (Fin n)) (x : Space n) (A D : ℝ) :
    (polarTensor J x A D).IsSymm := by
  unfold Matrix.IsSymm polarTensor
  simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one,
    Matrix.transpose_vecMulVec]

lemma polarTensor_trace (J : ComplexStructure (Fin n)) {x : Space n}
    (hS : x ⬝ᵥ x ≠ 0) (A D : ℝ) :
    (polarTensor J x A D).trace = 1+((n:ℝ)-2)*A+D := by
  simp only [polarTensor, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one,
    Matrix.trace_vecMulVec, J.preserves_dot, smul_eq_mul, Fintype.card_fin]
  field_simp
  ring

lemma polarTensor_radial (J : ComplexStructure (Fin n)) {x : Space n}
    (hS : x ⬝ᵥ x ≠ 0) (A D : ℝ) : polarTensor J x A D *ᵥ x = x := by
  rw [polarTensor_mulVec]
  have horth : (J.matrix *ᵥ x) ⬝ᵥ x = 0 := by rw [dotProduct_comm, J.orthogonal_radial]
  rw [horth]
  simp only [mul_zero, zero_smul, add_zero, div_mul_cancel₀ _ hS]
  module

lemma polarTensor_hopf (J : ComplexStructure (Fin n)) {x : Space n}
    (hS : x ⬝ᵥ x ≠ 0) (A D : ℝ) :
    polarTensor J x A D *ᵥ (J.matrix *ᵥ x) = D • (J.matrix *ᵥ x) := by
  rw [polarTensor_mulVec, J.orthogonal_radial, J.preserves_dot]
  simp only [mul_zero, zero_smul, add_zero, div_mul_cancel₀ _ hS]
  module

/-- The full contracted connection, derived algebraically from the actual six
Christoffel coefficients; no polar Laplacian formula is assumed. -/
lemma contract_normalizedConnection (J : ComplexStructure (Fin n)) {x : Space n}
    (hS : x ⬝ᵥ x ≠ 0) {A q : ℝ} (hA : A ≠ 0) (hq : q ≠ 0)
    (u v : ℝ) (k : Fin n) :
    tensorContract (polarTensor J x A⁻¹ (A*q)⁻¹)
      (fun i j => normalizedConnectionCoeff J x A q u v k i j) =
      (((n:ℝ)-2)/A+1/(A*q)-((n:ℝ)-1)*(1+u)-v)/(x ⬝ᵥ x)*x k := by
  unfold normalizedConnectionCoeff
  rw [contract_connection J x _ (polarTensor_symmetric J x _ _) _
    (polarTensor_radial J hS _ _) (polarTensor_hopf J hS _ _), polarTensor_trace J hS]
  unfold normalAlpha normalBeta normalGamma normalEpsilon normalZeta
  congr 1
  field_simp
  ring

end HarmonicCounterexample.Berger

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff

namespace HarmonicCounterexample.Berger
open Matrix
variable {n : ℕ}

lemma contract_comm (M T : Mat n) : tensorContract M T = tensorContract T M := by
  simp only [tensorContract, mul_comm]

lemma contract_polarTensor (J : ComplexStructure (Fin n)) (x : Space n)
    (A D : ℝ) (T : Mat n) :
    tensorContract (polarTensor J x A D) T = A*T.trace+
      (1-A)/(x ⬝ᵥ x)*(x ⬝ᵥ (T *ᵥ x))+
      (D-A)/(x ⬝ᵥ x)*((J.matrix *ᵥ x) ⬝ᵥ (T *ᵥ (J.matrix *ᵥ x))) := by
  rw [contract_comm]
  simp only [polarTensor, contract_add, contract_smul, contract_rank, contract_identity]

/-- Cartesian gradient and Hessian, with the same coordinate order as the
frozen definition of the Laplace--Beltrami operator. -/
def gradient (f : Space n → ℝ) (x : Space n) : Space n := fun i => coordDeriv i f x
def hessian (f : Space n → ℝ) (x : Space n) : Mat n := fun i j => coordDeriv i (coordDeriv j f) x
def euler (f : Space n → ℝ) (x : Space n) : ℝ := x ⬝ᵥ gradient f x
def hopfDerivative (J : ComplexStructure (Fin n)) (f : Space n → ℝ) (x : Space n) : ℝ :=
  (J.matrix *ᵥ x) ⬝ᵥ gradient f x

def euclideanLaplacian (f : Space n → ℝ) (x : Space n) : ℝ := (hessian f x).trace

lemma laplace_contract (g : SmoothMetric n) (f : Space n → ℝ) (x : Space n) :
    laplaceBeltrami g f x = tensorContract (g.coeff x)⁻¹ (hessian f x) -
      ∑ k, tensorContract (g.coeff x)⁻¹ (fun i j => christoffel g x k i j) * coordDeriv k f x := by
  simp only [laplaceBeltrami, tensorContract, hessian, mul_sub, Finset.sum_sub_distrib,
    Finset.mul_sum, Finset.sum_mul]
  congr 1
  calc
    _ = ∑ i, ∑ k, ∑ j, (g.coeff x)⁻¹ i j * (christoffel g x k i j * coordDeriv k f x) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ k, ∑ i, ∑ j, (g.coeff x)⁻¹ i j * (christoffel g x k i j * coordDeriv k f x) := by
      rw [Finset.sum_comm]
    _ = _ := by simp only [mul_assoc]

lemma euler_expansion {f : Space n → ℝ} {x : Space n}
    (hf : ∀ j, DifferentiableAt ℝ (coordDeriv j f) x) (i : Fin n) :
    coordDeriv i (euler f) x = coordDeriv i f x +
      ∑ j, x j * coordDeriv i (coordDeriv j f) x := by
  unfold euler gradient dotProduct
  rw [coordDeriv_sum]
  · simp (disch := fun_prop) only [coordDeriv_mul, coordDeriv_coordinate]
    simp [Finset.sum_add_distrib, Matrix.one_apply, add_comm]
  · intro j _
    exact (differentiableAt_apply j x).mul (hf j)

lemma euler_twice {f : Space n → ℝ} {x : Space n}
    (hf : ∀ j, DifferentiableAt ℝ (coordDeriv j f) x) :
    euler (euler f) x = euler f x + x ⬝ᵥ ((hessian f x) *ᵥ x) := by
  simp only [euler, gradient, euler_expansion hf, dotProduct, Matrix.mulVec,
    hessian, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma hopf_expansion (J : ComplexStructure (Fin n)) {f : Space n → ℝ} {x : Space n}
    (hf : ∀ j, DifferentiableAt ℝ (coordDeriv j f) x) (i : Fin n) :
    coordDeriv i (hopfDerivative J f) x =
      ∑ j, (J.matrix j i * coordDeriv j f x +
        (J.matrix *ᵥ x) j * coordDeriv i (coordDeriv j f) x) := by
  unfold hopfDerivative gradient dotProduct
  rw [coordDeriv_sum]
  · apply Finset.sum_congr rfl
    intro j _
    rw [coordDeriv_mul (by unfold Matrix.mulVec dotProduct; fun_prop) (hf j), coordDeriv_linear]
    ring
  · intro j _
    exact (by fun_prop : DifferentiableAt ℝ (fun y => ∑ i, J.matrix j i*y i) x).mul (hf j)

lemma hopf_twice (J : ComplexStructure (Fin n)) {f : Space n → ℝ} {x : Space n}
    (hf : ∀ j, DifferentiableAt ℝ (coordDeriv j f) x) :
    hopfDerivative J (hopfDerivative J f) x =
      (J.matrix *ᵥ x) ⬝ᵥ ((hessian f x) *ᵥ (J.matrix *ᵥ x)) - euler f x := by
  let w := J.matrix *ᵥ x
  change (∑ i, w i * coordDeriv i (hopfDerivative J f) x) =
    w ⬝ᵥ ((hessian f x) *ᵥ w) - euler f x
  simp_rw [hopf_expansion J hf]
  change (∑ i, w i * ∑ j, (J.matrix j i * coordDeriv j f x +
    w j * coordDeriv i (coordDeriv j f) x)) = _
  simp only [Finset.sum_add_distrib, mul_add]
  have hfirst : (∑ i, w i * ∑ j, J.matrix j i*coordDeriv j f x) = -euler f x := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have hs (j : Fin n) : ∑ i, J.matrix j i*w i = -x j :=
      congrFun (J.square_mulVec x) j
    simp_rw [show ∀ i j, w i*(J.matrix j i*coordDeriv j f x) =
      J.matrix j i*w i*coordDeriv j f x by intros; ring]
    simp only [← Finset.sum_mul, hs]
    simp [euler, gradient, dotProduct, Finset.sum_neg_distrib]
  rw [hfirst]
  have hsecond : (∑ i, w i * ∑ j, w j*coordDeriv i (coordDeriv j f) x) =
      w ⬝ᵥ ((hessian f x) *ᵥ w) := by
    change (∑ i, w i * ∑ j, w j*coordDeriv i (coordDeriv j f) x) =
      ∑ i, w i * ∑ j, coordDeriv i (coordDeriv j f) x*w j
    simp only [mul_comm]
  rw [hsecond]
  ring

/-- The complete polar Laplacian identity, derived from the actual Cartesian
Hessian and Christoffels. This isolates the analytic bridge independently of
any spectral or harmonic-polynomial assumptions. -/
theorem laplace_polar (g : SmoothMetric n) (J : ComplexStructure (Fin n))
    (f : Space n → ℝ) {x : Space n} (hS : x ⬝ᵥ x ≠ 0)
    {A q : ℝ} (hA : A ≠ 0) (hq : q ≠ 0) (u v : ℝ)
    (hg : (g.coeff x)⁻¹ = polarTensor J x A⁻¹ (A*q)⁻¹)
    (hΓ : ∀ k i j, christoffel g x k i j = normalizedConnectionCoeff J x A q u v k i j)
    (hf : ∀ j, DifferentiableAt ℝ (coordDeriv j f) x) :
    (x ⬝ᵥ x)*laplaceBeltrami g f x =
      euler (euler f) x + ((n:ℝ)-2+((n:ℝ)-1)*u+v)*euler f x +
      A⁻¹*((x ⬝ᵥ x)*euclideanLaplacian f x-euler (euler f) x-((n:ℝ)-2)*euler f x)+
      ((A*q)⁻¹-A⁻¹)*hopfDerivative J (hopfDerivative J f) x := by
  rw [laplace_contract, hg]
  simp_rw [hΓ, contract_normalizedConnection J hS hA hq u v]
  rw [contract_polarTensor, euler_twice hf, hopf_twice J hf]
  have he : ∑ k, (((n:ℝ)-2)/A+1/(A*q)-((n:ℝ)-1)*(1+u)-v)/(x ⬝ᵥ x)*x k*
      coordDeriv k f x =
      (((n:ℝ)-2)/A+1/(A*q)-((n:ℝ)-1)*(1+u)-v)/(x ⬝ᵥ x)*euler f x := by
    simp only [euler, gradient, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intros
    ring
  rw [he]
  unfold euclideanLaplacian
  field_simp
  ring

end HarmonicCounterexample.Berger

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff

namespace HarmonicCounterexample.Berger
open Matrix
variable {n : ℕ}

lemma coordDeriv_smooth {f : Space n → ℝ} (hf : ContDiff ℝ ∞ f) (i : Fin n) :
    ContDiff ℝ ∞ (coordDeriv i f) := by
  exact (hf.fderiv_right (by simp)).clm_apply contDiff_const

lemma euler_congr {f h : Space n → ℝ} {x : Space n} (he : f =ᶠ[𝓝 x] h) :
    euler f x = euler h x := by
  simp only [euler, gradient, dotProduct, coordDeriv_congr he]

lemma hopf_congr (J : ComplexStructure (Fin n)) {f h : Space n → ℝ} {x : Space n}
    (he : f =ᶠ[𝓝 x] h) : hopfDerivative J f x = hopfDerivative J h x := by
  simp only [hopfDerivative, gradient, dotProduct, coordDeriv_congr he]

lemma euler_mul {f h : Space n → ℝ} {x : Space n}
    (hf : DifferentiableAt ℝ f x) (hh : DifferentiableAt ℝ h x) :
    euler (fun y => f y*h y) x = f x*euler h x+h x*euler f x := by
  simp only [euler, gradient, dotProduct, coordDeriv_mul hf hh, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring

lemma hopf_mul (J : ComplexStructure (Fin n)) {f h : Space n → ℝ} {x : Space n}
    (hf : DifferentiableAt ℝ f x) (hh : DifferentiableAt ℝ h x) :
    hopfDerivative J (fun y => f y*h y) x =
      f x*hopfDerivative J h x+h x*hopfDerivative J f x := by
  simp only [hopfDerivative, gradient, dotProduct, coordDeriv_mul hf hh, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring

lemma coordDeriv_product_second {f h : Space n → ℝ} {x : Space n}
    (hf : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y)
    (hh : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ h y)
    (hfi : ∀ i, DifferentiableAt ℝ (coordDeriv i f) x)
    (hhi : ∀ i, DifferentiableAt ℝ (coordDeriv i h) x) (i j : Fin n) :
    coordDeriv i (coordDeriv j (fun y => f y*h y)) x =
      f x*coordDeriv i (coordDeriv j h) x+h x*coordDeriv i (coordDeriv j f) x+
      coordDeriv i f x*coordDeriv j h x+coordDeriv j f x*coordDeriv i h x := by
  have he : coordDeriv j (fun y => f y*h y) =ᶠ[𝓝 x]
      (fun y => f y*coordDeriv j h y+h y*coordDeriv j f y) := by
    filter_upwards [hf,hh] with y hfy hhy using coordDeriv_mul hfy hhy j
  rw [coordDeriv_congr he,coordDeriv_add (f := fun y => f y*coordDeriv j h y)
    (h := fun y => h y*coordDeriv j f y) ((hf.self_of_nhds).mul (hhi j))
    ((hh.self_of_nhds).mul (hfi j)),coordDeriv_mul hf.self_of_nhds (hhi j),
    coordDeriv_mul hh.self_of_nhds (hfi j)]
  ring

lemma euclideanLaplacian_mul {f h : Space n → ℝ} {x : Space n}
    (hf : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y)
    (hh : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ h y)
    (hfi : ∀ i, DifferentiableAt ℝ (coordDeriv i f) x)
    (hhi : ∀ i, DifferentiableAt ℝ (coordDeriv i h) x) :
    euclideanLaplacian (fun y => f y*h y) x =
      f x*euclideanLaplacian h x+h x*euclideanLaplacian f x+
      2*(gradient f x ⬝ᵥ gradient h x) := by
  simp only [euclideanLaplacian, hessian, Matrix.trace, Matrix.diag, gradient,
    dotProduct, coordDeriv_product_second hf hh hfi hhi, Finset.sum_add_distrib,
    Finset.mul_sum]
  ring_nf
  rw [Finset.sum_mul]

lemma euler_add {f h : Space n → ℝ} {x : Space n}
    (hf : DifferentiableAt ℝ f x) (hh : DifferentiableAt ℝ h x) :
    euler (fun y => f y+h y) x = euler f x+euler h x := by
  simp [euler, gradient, dotProduct, coordDeriv_add hf hh, mul_add, Finset.sum_add_distrib]

lemma euler_smooth {f : Space n → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (euler f) := by
  unfold euler gradient dotProduct
  exact ContDiff.sum fun i _ => (contDiff_apply ℝ ℝ i).mul (coordDeriv_smooth hf i)

lemma hopf_smooth (J : ComplexStructure (Fin n)) {f : Space n → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (hopfDerivative J f) := by
  unfold hopfDerivative gradient dotProduct Matrix.mulVec dotProduct
  apply ContDiff.sum
  intro i _
  exact (ContDiff.sum fun j _ => contDiff_const.mul (contDiff_apply ℝ ℝ j)).mul (coordDeriv_smooth hf i)

end HarmonicCounterexample.Berger

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff

namespace HarmonicCounterexample.Cartesian
open Matrix Berger
variable {n : ℕ}

lemma logProfile_differentiableAt {f f1 : ℝ → ℝ}
    (hf : ∀ t, HasDerivAt f (f1 t) t) {x : Space n} (hx : x ≠ 0) :
    DifferentiableAt ℝ (fun y => f (logRadius y)) x :=
  (hf _).differentiableAt.comp x ((logRadius_smoothAt hx).differentiableAt (by simp))

lemma logProfile_coord_differentiableAt {f f1 f2 : ℝ → ℝ}
    (hf : ∀ t, HasDerivAt f (f1 t) t) (hf1 : ∀ t, HasDerivAt f1 (f2 t) t)
    {x : Space n} (hx : x ≠ 0) (j : Fin n) :
    DifferentiableAt ℝ (coordDeriv j (fun y => f (logRadius y))) x := by
  have he : coordDeriv j (fun y => f (logRadius y)) =ᶠ[𝓝 x]
      (fun y => f1 (logRadius y)/(y ⬝ᵥ y)*y j) := by
    filter_upwards [eventually_ne_nhds hx] with y hy using coordDeriv_logProfile hy (hf _) j
  have hd : DifferentiableAt ℝ (fun y => f1 (logRadius y)/(y ⬝ᵥ y)*y j) x := by
    simpa only [div_eq_mul_inv] using
      (((logProfile_differentiableAt hf1 hx).fun_mul
        ((differentiableAt_radialSquare x).fun_inv (squareRadius_pos hx).ne')).fun_mul
        (differentiableAt_apply j x))
  exact hd.congr_of_eventuallyEq he

lemma logProfile_second {f f1 f2 : ℝ → ℝ}
    (hf : ∀ t, HasDerivAt f (f1 t) t) (hf1 : ∀ t, HasDerivAt f1 (f2 t) t)
    {x : Space n} (hx : x ≠ 0) (i j : Fin n) :
    coordDeriv i (coordDeriv j (fun y => f (logRadius y))) x =
      (f2 (logRadius x)-2*f1 (logRadius x))*x i*x j/(x ⬝ᵥ x)^2+
      f1 (logRadius x)/(x ⬝ᵥ x)*(1 : Mat n) j i := by
  have he : coordDeriv j (fun y => f (logRadius y)) =ᶠ[𝓝 x]
      (fun y => f1 (logRadius y)/(y ⬝ᵥ y)*y j) := by
    filter_upwards [eventually_ne_nhds hx] with y hy using coordDeriv_logProfile hy (hf _) j
  have hS : x ⬝ᵥ x ≠ 0 := (squareRadius_pos hx).ne'
  rw [coordDeriv_congr he,
    coordDeriv_mul (f := fun y => f1 (logRadius y)/(y ⬝ᵥ y))
      ((logProfile_differentiableAt hf1 hx).fun_mul ((differentiableAt_radialSquare x).fun_inv hS))
      (differentiableAt_apply j x),
    coordDeriv_div (logProfile_differentiableAt hf1 hx) (differentiableAt_radialSquare x) hS,
    coordDeriv_logProfile hx (hf1 _),coordDeriv_radialSquare,coordDeriv_coordinate]
  field_simp
  ring

lemma euler_logProfile {f : ℝ → ℝ} {d : ℝ} {x : Space n}
    (hx : x ≠ 0) (hf : HasDerivAt f d (logRadius x)) :
    euler (fun y => f (logRadius y)) x = d := by
  change (∑ i, x i*coordDeriv i (fun y => f (logRadius y)) x) = d
  simp only [coordDeriv_logProfile hx hf]
  simp_rw [show ∀ i : Fin n, x i*(d/(x ⬝ᵥ x)*x i) = d/(x ⬝ᵥ x)*(x i*x i) by intros; ring]
  rw [← Finset.mul_sum]
  change d/(x ⬝ᵥ x)*(x ⬝ᵥ x) = d
  exact div_mul_cancel₀ _ (squareRadius_pos hx).ne'

lemma hopf_logProfile (J : ComplexStructure (Fin n)) {f : ℝ → ℝ} {d : ℝ}
    {x : Space n} (hx : x ≠ 0) (hf : HasDerivAt f d (logRadius x)) :
    hopfDerivative J (fun y => f (logRadius y)) x = 0 := by
  change (∑ i, (J.matrix *ᵥ x) i*coordDeriv i (fun y => f (logRadius y)) x) = 0
  simp only [coordDeriv_logProfile hx hf]
  simp_rw [show ∀ i : Fin n, (J.matrix *ᵥ x) i*(d/(x ⬝ᵥ x)*x i) =
    d/(x ⬝ᵥ x)*(x i*(J.matrix *ᵥ x) i) by intros; ring]
  rw [← Finset.mul_sum]
  change d/(x ⬝ᵥ x)*(x ⬝ᵥ (J.matrix *ᵥ x)) = 0
  rw [J.orthogonal_radial,mul_zero]

lemma laplacian_logProfile {f f1 f2 : ℝ → ℝ}
    (hf : ∀ t, HasDerivAt f (f1 t) t) (hf1 : ∀ t, HasDerivAt f1 (f2 t) t)
    {x : Space n} (hx : x ≠ 0) :
    (x ⬝ᵥ x)*euclideanLaplacian (fun y => f (logRadius y)) x =
      f2 (logRadius x)+((n:ℝ)-2)*f1 (logRadius x) := by
  simp only [euclideanLaplacian,hessian,Matrix.trace,Matrix.diag,logProfile_second hf hf1 hx,
    Matrix.one_apply_eq, mul_one, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hS : x ⬝ᵥ x ≠ 0 := (squareRadius_pos hx).ne'
  have hs : (∑ i : Fin n, (f2 (logRadius x)-2*f1 (logRadius x))*x i*x i/(x ⬝ᵥ x)^2) =
      (f2 (logRadius x)-2*f1 (logRadius x))/(x ⬝ᵥ x) := by
    simp_rw [show ∀ i : Fin n, (f2 (logRadius x)-2*f1 (logRadius x))*x i*x i/(x ⬝ᵥ x)^2 =
      (f2 (logRadius x)-2*f1 (logRadius x))/(x ⬝ᵥ x)^2*(x i*x i) by intros; ring]
    rw [← Finset.mul_sum]
    change _/(x ⬝ᵥ x)^2*(x ⬝ᵥ x) = _
    field_simp [hS]
  rw [hs]
  field_simp [hS]
  ring

end HarmonicCounterexample.Cartesian

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff

namespace HarmonicCounterexample.Cartesian
open Matrix Berger
variable {n : ℕ}

lemma euler_logProfile_mul {f f1 : ℝ → ℝ} {P : Space n → ℝ} {l : ℝ}
    (hf : ∀ t, HasDerivAt f (f1 t) t) (hP : ContDiff ℝ ∞ P)
    (hE : ∀ x, euler P x = l*P x) {x : Space n} (hx : x ≠ 0) :
    euler (fun y => f (logRadius y)*P y) x = (f1 (logRadius x)+l*f (logRadius x))*P x := by
  rw [euler_mul (logProfile_differentiableAt hf hx) (hP.differentiable (by simp) x),
    euler_logProfile hx (hf _),hE]
  ring

lemma euler_twice_logProfile_mul {f f1 f2 : ℝ → ℝ} {P : Space n → ℝ} {l : ℝ}
    (hf : ∀ t, HasDerivAt f (f1 t) t) (hf1 : ∀ t, HasDerivAt f1 (f2 t) t)
    (hP : ContDiff ℝ ∞ P) (hE : ∀ x, euler P x = l*P x)
    {x : Space n} (hx : x ≠ 0) :
    euler (euler (fun y => f (logRadius y)*P y)) x =
      (f2 (logRadius x)+2*l*f1 (logRadius x)+l^2*f (logRadius x))*P x := by
  have he : euler (fun y => f (logRadius y)*P y) =ᶠ[𝓝 x]
      (fun y => (f1 (logRadius y)+l*f (logRadius y))*P y) := by
    filter_upwards [eventually_ne_nhds hx] with y hy using euler_logProfile_mul hf hP hE hy
  rw [euler_congr he]
  have hd (t : ℝ) : HasDerivAt (fun t => f1 t+l*f t) (f2 t+l*f1 t) t :=
    (hf1 t).fun_add ((hf t).const_mul l)
  rw [euler_logProfile_mul hd hP hE hx]
  ring

lemma hopf_logProfile_mul (J : ComplexStructure (Fin n)) {f f1 : ℝ → ℝ}
    {P : Space n → ℝ} (hf : ∀ t, HasDerivAt f (f1 t) t) (hP : ContDiff ℝ ∞ P)
    {x : Space n} (hx : x ≠ 0) :
    hopfDerivative J (fun y => f (logRadius y)*P y) x = f (logRadius x)*hopfDerivative J P x := by
  rw [hopf_mul J (logProfile_differentiableAt hf hx) (hP.differentiable (by simp) x),
    hopf_logProfile J hx (hf _),mul_zero,add_zero]

lemma hopf_twice_logProfile_mul (J : ComplexStructure (Fin n)) {f f1 : ℝ → ℝ}
    {P : Space n → ℝ} (hf : ∀ t, HasDerivAt f (f1 t) t) (hP : ContDiff ℝ ∞ P)
    {x : Space n} (hx : x ≠ 0) :
    hopfDerivative J (hopfDerivative J (fun y => f (logRadius y)*P y)) x =
      f (logRadius x)*hopfDerivative J (hopfDerivative J P) x := by
  have he : hopfDerivative J (fun y => f (logRadius y)*P y) =ᶠ[𝓝 x]
      (fun y => f (logRadius y)*hopfDerivative J P y) := by
    filter_upwards [eventually_ne_nhds hx] with y hy using hopf_logProfile_mul J hf hP hy
  rw [hopf_congr J he,hopf_logProfile_mul J hf (hopf_smooth J hP) hx]

lemma gradient_logProfile_dot {f f1 : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (f1 t) t)
    (P : Space n → ℝ) {x : Space n} (hx : x ≠ 0) :
    Berger.gradient (fun y => f (logRadius y)) x ⬝ᵥ Berger.gradient P x =
      f1 (logRadius x)/(x ⬝ᵥ x)*euler P x := by
  change (∑ i,coordDeriv i (fun y => f (logRadius y)) x*coordDeriv i P x) = _
  simp only [coordDeriv_logProfile hx (hf _)]
  simp only [mul_assoc,← Finset.mul_sum]
  rfl

lemma euclideanLaplacian_logProfile_mul {f f1 f2 : ℝ → ℝ} {P : Space n → ℝ} {l : ℝ}
    (hf : ∀ t, HasDerivAt f (f1 t) t) (hf1 : ∀ t, HasDerivAt f1 (f2 t) t)
    (hP : ContDiff ℝ ∞ P) (hE : ∀ x, euler P x = l*P x)
    (hH : ∀ x, euclideanLaplacian P x = 0) {x : Space n} (hx : x ≠ 0) :
    (x ⬝ᵥ x)*euclideanLaplacian (fun y => f (logRadius y)*P y) x =
      (f2 (logRadius x)+((n:ℝ)-2+2*l)*f1 (logRadius x))*P x := by
  have hfn : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ (fun y => f (logRadius y)) y := by
    filter_upwards [eventually_ne_nhds hx] with y hy using logProfile_differentiableAt hf hy
  rw [euclideanLaplacian_mul hfn (Filter.Eventually.of_forall (hP.differentiable (by simp)))
    (logProfile_coord_differentiableAt hf hf1 hx)
    (fun i => (coordDeriv_smooth hP i).differentiable (by simp) x),hH,mul_zero,zero_add,
    gradient_logProfile_dot hf P hx,hE]
  have hd := laplacian_logProfile hf hf1 hx
  have hS : x ⬝ᵥ x ≠ 0 := (squareRadius_pos hx).ne'
  field_simp
  rw [hd]
  ring

lemma coordDeriv_product_differentiableAt {f h : Space n → ℝ} {x : Space n}
    (hf : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y)
    (hh : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ h y)
    (hfi : ∀ i, DifferentiableAt ℝ (coordDeriv i f) x)
    (hhi : ∀ i, DifferentiableAt ℝ (coordDeriv i h) x) (j : Fin n) :
    DifferentiableAt ℝ (coordDeriv j (fun y => f y*h y)) x := by
  have he : coordDeriv j (fun y => f y*h y) =ᶠ[𝓝 x]
      (fun y => f y*coordDeriv j h y+h y*coordDeriv j f y) := by
    filter_upwards [hf,hh] with y hfy hhy using coordDeriv_mul hfy hhy j
  exact ((hf.self_of_nhds.fun_mul (hhi j)).fun_add
    (hh.self_of_nhds.fun_mul (hfi j))).congr_of_eventuallyEq he

/-- The actual Cartesian Laplace--Beltrami operator on a radial coefficient
 times a homogeneous harmonic polynomial. Every derivative in this statement
 is the genuine Fréchet/coordinate derivative, not a spectral placeholder. -/
theorem laplace_homogeneous_profile (g : SmoothMetric n) (J : ComplexStructure (Fin n))
    {f f1 f2 : ℝ → ℝ} {P : Space n → ℝ} {l : ℝ}
    (hf : ∀ t, HasDerivAt f (f1 t) t) (hf1 : ∀ t, HasDerivAt f1 (f2 t) t)
    (hP : ContDiff ℝ ∞ P) (hE : ∀ x, euler P x = l*P x)
    (hH : ∀ x, euclideanLaplacian P x = 0) {x : Space n} (hx : x ≠ 0)
    {A q : ℝ} (hA : A ≠ 0) (hq : q ≠ 0) (u v : ℝ)
    (hg : (g.coeff x)⁻¹ = polarTensor J x A⁻¹ (A*q)⁻¹)
    (hΓ : ∀ k i j, christoffel g x k i j = normalizedConnectionCoeff J x A q u v k i j) :
    (x ⬝ᵥ x)*laplaceBeltrami g (fun y => f (logRadius y)*P y) x =
      (f2 (logRadius x)+(2*l+(n:ℝ)-2+((n:ℝ)-1)*u+v)*f1 (logRadius x)+
        (l^2+((n:ℝ)-2+((n:ℝ)-1)*u+v)*l-A⁻¹*l*(l+(n:ℝ)-2))*f (logRadius x))*P x+
        ((A*q)⁻¹-A⁻¹)*f (logRadius x)*hopfDerivative J (hopfDerivative J P) x := by
  have hfn : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ (fun y => f (logRadius y)) y := by
    filter_upwards [eventually_ne_nhds hx] with y hy using logProfile_differentiableAt hf hy
  rw [laplace_polar g J _ (squareRadius_pos hx).ne' hA hq u v hg hΓ
    (coordDeriv_product_differentiableAt hfn
      (Filter.Eventually.of_forall (hP.differentiable (by simp)))
      (logProfile_coord_differentiableAt hf hf1 hx)
      (fun i => (coordDeriv_smooth hP i).differentiable (by simp) x)),
    euler_twice_logProfile_mul hf hf1 hP hE hx,euler_logProfile_mul hf hP hE hx,
    hopf_twice_logProfile_mul J hf hP hx,
    euclideanLaplacian_logProfile_mul hf hf1 hP hE hH hx]
  ring

end HarmonicCounterexample.Cartesian

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff

namespace HarmonicCounterexample.Cartesian
open Matrix Berger
variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- Polynomial-normalized coefficient.  This is constant in the Euclidean core. -/
def regularCoefficient (l : ℝ) (Y : ℝ → ι → ℝ) (i : ι) (t : ℝ) : ℝ :=
  Real.exp (-l*t)*Y t i

def synthesized (l : ℝ) (P : ι → Space n → ℝ) (Y : ℝ → ι → ℝ) (x : Space n) : ℝ :=
  ∑ i, regularCoefficient l Y i (logRadius x)*P i x

omit [Fintype ι] in
lemma regularCoefficient_deriv {l t : ℝ} {Y Y1 : ℝ → ι → ℝ}
    (hY : ∀ i, HasDerivAt (fun s => Y s i) (Y1 t i) t) (i : ι) :
    HasDerivAt (regularCoefficient l Y i)
      (Real.exp (-l*t)*(Y1 t i-l*Y t i)) t := by
  have he : HasDerivAt (fun s => Real.exp (-l*s)) (-l*Real.exp (-l*t)) t := by
    convert (((hasDerivAt_id t).const_mul (-l)).exp) using 1 <;> first | rfl | simp [mul_comm]
  convert he.fun_mul (hY i) using 1 <;> first | rfl | ring

omit [Fintype ι] in
lemma regularCoefficient_second {l t : ℝ} {Y Y1 Y2 : ℝ → ι → ℝ}
    (hY : ∀ i, HasDerivAt (fun s => Y s i) (Y1 t i) t)
    (hY1 : ∀ i, HasDerivAt (fun s => Y1 s i) (Y2 t i) t) (i : ι) :
    HasDerivAt (fun s => Real.exp (-l*s)*(Y1 s i-l*Y s i))
      (Real.exp (-l*t)*(Y2 t i-2*l*Y1 t i+l^2*Y t i)) t := by
  have h := regularCoefficient_deriv (l := l)
    (Y := fun s i => Y1 s i-l*Y s i)
    (Y1 := fun s i => Y2 s i-l*Y1 s i)
    (fun i => (hY1 i).fun_sub ((hY i).const_mul l)) i
  convert h using 1 <;> first | rfl | ring

omit [Fintype ι] in
lemma regularCoefficient_core {l : ℝ} {Y : ℝ → ι → ℝ} {c : ι → ℝ}
    (hc : ∀ t ≤ 0, Y t = Real.exp (l*t) • c) {t : ℝ} (ht : t ≤ 0) (i : ι) :
    regularCoefficient l Y i t = c i := by
  simp only [regularCoefficient,hc t ht,Pi.smul_apply,smul_eq_mul,← mul_assoc,← Real.exp_add]
  simp

lemma synthesized_smooth {l : ℝ} {P : ι → Space n → ℝ} {Y : ℝ → ι → ℝ}
    (hP : ∀ i, ContDiff ℝ ∞ (P i)) (hY : ContDiff ℝ ∞ Y) {c : ι → ℝ}
    (hc : ∀ t ≤ 0, Y t = Real.exp (l*t) • c) :
    ContDiff ℝ ∞ (synthesized l P Y) := by
  have hf (i : ι) : ContDiff ℝ ∞ (regularCoefficient l Y i) :=
    (contDiff_const.mul contDiff_id).exp.mul ((contDiff_apply ℝ ℝ i).comp hY)
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    have he : synthesized l P Y =ᶠ[𝓝 (0 : Space n)] (fun y => ∑ i, c i*P i y) := by
      have hr : ∀ᶠ y : Space n in 𝓝 0, squareRadius y < 1 :=
        squareRadius_smooth.continuous.continuousAt.eventually (eventually_lt_nhds (by simp))
      filter_upwards [hr] with y hy
      have ht : logRadius y ≤ 0 := by
        unfold logRadius
        exact mul_nonpos_of_nonneg_of_nonpos (by norm_num)
          (Real.log_nonpos (squareRadius_nonneg y) hy.le)
      exact Finset.sum_congr rfl fun i _ => by rw [regularCoefficient_core hc ht]
    exact ((ContDiff.sum fun i _ => contDiff_const.mul (hP i)).contDiffAt).congr_of_eventuallyEq he
  · exact ContDiffAt.sum fun i _ => ((hf i).contDiffAt.comp x (logRadius_smoothAt hx)).mul
      (hP i).contDiffAt

lemma laplace_sum (g : SmoothMetric n) {P : ι → Space n → ℝ} {x : Space n}
    (hP : ∀ i, ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ (P i) y)
    (hPi : ∀ i j, DifferentiableAt ℝ (coordDeriv j (P i)) x) :
    laplaceBeltrami g (fun y => ∑ a, P a y) x = ∑ a, laplaceBeltrami g (P a) x := by
  have he (j : Fin n) : coordDeriv j (fun y => ∑ a, P a y) =ᶠ[𝓝 x]
      (fun y => ∑ a, coordDeriv j (P a) y) := by
    have h := (Filter.eventually_all.2 hP)
    filter_upwards [h] with y hy
    exact coordDeriv_sum Finset.univ (fun a _ => hy a) j
  have hsecond (i j : Fin n) : coordDeriv i (coordDeriv j (fun y => ∑ a, P a y)) x =
      ∑ a, coordDeriv i (coordDeriv j (P a)) x := by
    rw [coordDeriv_congr (he j),coordDeriv_sum Finset.univ (fun a _ => hPi a j)]
  have hfirst (i : Fin n) : coordDeriv i (fun y => ∑ a, P a y) x =
      ∑ a, coordDeriv i (P a) x := (he i).self_of_nhds
  have hconn (i j : Fin n) : (∑ k, christoffel g x k i j*(∑ a,coordDeriv k (P a) x)) =
      ∑ a, ∑ k, christoffel g x k i j*coordDeriv k (P a) x := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
  simp only [laplaceBeltrami,hsecond,hfirst]
  simp only [hconn,← Finset.sum_sub_distrib]
  simp only [Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]

omit [Fintype ι] in
lemma laplace_regular_term (g : SmoothMetric n) (J : ComplexStructure (Fin n))
    {Y Y1 Y2 : ℝ → ι → ℝ} {P : Space n → ℝ} {l : ℝ}
    (hY : ∀ t i, HasDerivAt (fun s => Y s i) (Y1 t i) t)
    (hY1 : ∀ t i, HasDerivAt (fun s => Y1 s i) (Y2 t i) t)
    (hP : ContDiff ℝ ∞ P) (hE : ∀ x, euler P x = l*P x)
    (hH : ∀ x, euclideanLaplacian P x = 0) {x : Space n} (hx : x ≠ 0)
    {A q : ℝ} (hA : A ≠ 0) (hq : q ≠ 0) (u v : ℝ)
    (hg : (g.coeff x)⁻¹ = polarTensor J x A⁻¹ (A*q)⁻¹)
    (hΓ : ∀ k i j, christoffel g x k i j = normalizedConnectionCoeff J x A q u v k i j)
    (i : ι) :
    (x ⬝ᵥ x)*laplaceBeltrami g (fun y => regularCoefficient l Y i (logRadius y)*P y) x =
      Real.exp (-l*logRadius x)*
        ((Y2 (logRadius x) i+((n:ℝ)-2+((n:ℝ)-1)*u+v)*Y1 (logRadius x) i-
          A⁻¹*l*(l+(n:ℝ)-2)*Y (logRadius x) i)*P x+
          ((A*q)⁻¹-A⁻¹)*Y (logRadius x) i*hopfDerivative J (hopfDerivative J P) x) := by
  rw [laplace_homogeneous_profile g J
    (fun t => regularCoefficient_deriv (hY t) i)
    (fun t => regularCoefficient_second (hY t) (hY1 t) i) hP hE hH hx hA hq u v hg hΓ]
  simp only [regularCoefficient]
  ring

end HarmonicCounterexample.Cartesian

end

end OAI
