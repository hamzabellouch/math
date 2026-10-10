import OAI.Geometry.PolarProducts.LowerBound

namespace OAI

universe u78 u79

section NonsqueezingInline
section

open Set Filter Function MeasureTheory
open scoped Topology ContDiff

namespace SmoothDegree
noncomputable section

abbrev Space (d : ℕ) := Fin d → ℝ

def basis (d : ℕ) : Fin d → Space d := fun i => Pi.single i 1

def vol (d : ℕ) : (Space d) [⋀^Fin d]→L[ℝ] ℝ :=
  { Matrix.detRowAlternating with cont := continuous_id.matrix_det }

@[simp] theorem vol_apply (d : ℕ) (v : Fin d → Space d) : vol d v = Matrix.det v := rfl

@[simp] theorem vol_basis (d : ℕ) : vol d (basis d) = 1 := by
  have he : basis d = (1 : Matrix (Fin d) (Fin d) ℝ) := by
    ext i j
    simp [basis, Matrix.one_apply, Pi.single_apply, eq_comm]
  change Matrix.det (basis d) = 1
  rw [he, Matrix.det_one]

 theorem vol_update_basis {d : ℕ} (i : Fin d) (v : Space d) :
    vol d (Function.update (basis d) i v) = v i := by
  change Matrix.det (Matrix.updateRow (basis d) i v) = v i
  have hv : v = ∑ j, v j • (basis d) j := by
    ext k
    simp [basis, Pi.single_apply]
  calc
    _ = Matrix.det (Matrix.updateRow (basis d) i (∑ j, v j • (basis d) j)) :=
      congrArg (fun w => Matrix.det (Matrix.updateRow (basis d) i w)) hv
    _ = v i • Matrix.det (basis d) := Matrix.det_updateRow_sum (basis d) i v
    _ = v i := by rw [show Matrix.det (basis d) = 1 from vol_basis d]; simp

 theorem contract_basis {n : ℕ} (i : Fin (n+1)) (v : Space (n+1)) :
    (vol (n+1)).curryLeft v (i.removeNth (basis (n+1))) = (-1 : ℝ)^i.val * v i := by
  rw [ContinuousAlternatingMap.curryLeft_apply_apply,
    ← ContinuousAlternatingMap.neg_one_pow_smul_map_insertNth,
    Fin.insertNth_removeNth, vol_update_basis]
  simp only [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]

 theorem extDeriv_contract_basis {n : ℕ} {V : Space (n+1) → Space (n+1)}
    {x : Space (n+1)} {V' : Space (n+1) →L[ℝ] Space (n+1)} (hV : HasFDerivAt V V' x) :
    extDeriv (fun y => (vol (n+1)).curryLeft (V y)) x (basis (n+1)) =
      ∑ i, V' (basis (n+1) i) i := by
  have hc : DifferentiableAt ℝ (fun y => (vol (n+1)).curryLeft (V y)) x :=
    (vol (n+1)).curryLeft.differentiableAt.comp x hV.differentiableAt
  rw [extDeriv_apply hc]
  apply Finset.sum_congr rfl
  intro i hi
  have he : (fun y => (vol (n+1)).curryLeft (V y) (i.removeNth (basis (n+1)))) =
      fun y => (-1 : ℝ)^i.val * (V y) i := funext fun y => contract_basis i (V y)
  have hd : HasFDerivAt (fun y => (-1 : ℝ)^i.val * (V y) i)
      (((-1 : ℝ)^i.val) • ((ContinuousLinearMap.proj i).comp V')) x :=
    (((ContinuousLinearMap.proj i : Space (n+1) →L[ℝ] ℝ).hasFDerivAt).comp x hV).const_mul _
  rw [he, hd.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
  rw [← mul_assoc, ← pow_add, show i.val+i.val = 2*i.val by omega,
    pow_mul, neg_one_sq, one_pow, one_mul]

 theorem extDeriv_contract_eq_zero {n : ℕ} {V : Space (n+1) → Space (n+1)}
    {x : Space (n+1)} (hV : DifferentiableAt ℝ V x)
    (hdiv : ∑ i, fderiv ℝ V x (basis (n+1) i) i = 0) :
    extDeriv (fun y => (vol (n+1)).curryLeft (V y)) x = 0 := by
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  apply ((extDeriv (fun y => (vol (n+1)).curryLeft (V y)) x).toAlternatingMap.map_basis_eq_zero_iff
    (Pi.basisFun ℝ (Fin (n+1)))).mp
  have he : (Pi.basisFun ℝ (Fin (n+1)) : Fin (n+1) → Space (n+1)) = basis (n+1) := by
    ext i j; simp [basis, Pi.basisFun_apply]
  change extDeriv (fun y => (vol (n+1)).curryLeft (V y)) x _ = 0
  rw [he, extDeriv_contract_basis hV.hasFDerivAt, hdiv]

 def sqsum {d : ℕ} (x : Space d) : ℝ := ∑ i, x i ^ 2

 theorem sqsum_pos {d : ℕ} {x : Space d} (hx : x ≠ 0) : 0 < sqsum x := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by contrapose! hx; ext i; exact hx i
  exact Finset.sum_pos' (fun i _ => sq_nonneg (x i)) ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩

 def dot {d : ℕ} (x : Space d) : Space d →L[ℝ] ℝ :=
   ∑ i, x i • ContinuousLinearMap.proj i

 @[simp] theorem dot_apply {d : ℕ} (x v : Space d) : dot x v = ∑ i, x i * v i := by
  simp [dot]

 theorem hasFDerivAt_sqsum {d : ℕ} (x : Space d) :
    HasFDerivAt sqsum ((2 : ℝ) • dot x) x := by
  have h := HasFDerivAt.sum (u := Finset.univ)
    (fun i _ => ((ContinuousLinearMap.proj i : Space d →L[ℝ] ℝ).hasFDerivAt (x := x)).pow 2)
  convert! h using 1
  · ext y
    simp [sqsum]
  · ext v
    simp [dot, Finset.mul_sum, mul_assoc]

 def radial {d : ℕ} (x : Space d) : Space d :=
   (sqsum x ^ (-(d : ℝ)/2)) • x

 theorem hasFDerivAt_radial {d : ℕ} {x : Space d} (hx : x ≠ 0) :
    HasFDerivAt radial
      ((((-(d : ℝ)/2) * sqsum x ^ (-(d : ℝ)/2 - 1)) • ((2 : ℝ) • dot x)).smulRight x +
      (sqsum x ^ (-(d : ℝ)/2)) • ContinuousLinearMap.id ℝ (Space d)) x := by
  convert! ((hasFDerivAt_sqsum x).rpow_const (p := -(d : ℝ)/2)
      (Or.inl (sqsum_pos hx).ne')).smul (hasFDerivAt_id x) using 1
  exact add_comm _ _

 theorem radial_divergence {d : ℕ} {x : Space d} (hx : x ≠ 0) :
    ∑ i, fderiv ℝ (@radial d) x (basis d i) i = 0 := by
  rw [(hasFDerivAt_radial hx).fderiv]
  have hb (i : Fin d) : dot x (basis d i) = x i := by
    simp [dot_apply, basis, Pi.single_apply, eq_comm]
  simp only [add_apply, Pi.add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, Pi.smul_apply,
    smul_eq_mul, hb]
  simp only [basis, Pi.single_eq_same, mul_one, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have he : (∑ i : Fin d, (-(d : ℝ)/2 * sqsum x ^ (-(d : ℝ)/2-1) * (2*x i)) * x i) =
      -(d : ℝ) * (sqsum x ^ (-(d : ℝ)/2-1) * sqsum x) := by
    simp only [sqsum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he]
  have hp : sqsum x ^ (-(d : ℝ)/2-1) * sqsum x = sqsum x ^ (-(d : ℝ)/2) := by
    calc
      _ = sqsum x ^ (-(d : ℝ)/2-1) * sqsum x ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = sqsum x ^ (-(d : ℝ)/2-1+1) := (Real.rpow_add (sqsum_pos hx) _ _).symm
      _ = _ := by congr 1; ring
  rw [hp]
  ring

 def radialForm (n : ℕ) (x : Space (n+1)) : (Space (n+1)) [⋀^Fin n]→L[ℝ] ℝ :=
   (vol (n+1)).curryLeft (radial x)

 theorem differentiableAt_radialForm {n : ℕ} {x : Space (n+1)} (hx : x ≠ 0) :
    DifferentiableAt ℝ (radialForm n) x :=
   (vol (n+1)).curryLeft.differentiableAt.comp x (hasFDerivAt_radial hx).differentiableAt

 theorem closed_radialForm {n : ℕ} {x : Space (n+1)} (hx : x ≠ 0) :
    extDeriv (radialForm n) x = 0 :=
   extDeriv_contract_eq_zero (hasFDerivAt_radial hx).differentiableAt (radial_divergence hx)

 def pullForm {n : ℕ} (f : Space (n+1) → Space (n+1)) (x : Space (n+1)) :
    (Space (n+1)) [⋀^Fin n]→L[ℝ] ℝ :=
   (radialForm n (f x)).compContinuousLinearMap (fderiv ℝ f x)

 theorem differentiableAt_pullForm {n : ℕ} {f : Space (n+1) → Space (n+1)}
    (hf : ContDiff ℝ ∞ f) {x : Space (n+1)} (hx : f x ≠ 0) :
    DifferentiableAt ℝ (pullForm f) x := by
  apply DifferentiableAt.continuousAlternatingMapCompContinuousLinearMap
  · exact (differentiableAt_radialForm hx).comp x (hf.differentiable (by simp) x)
  · exact (hf.contDiffAt.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)

 theorem closed_pullForm {n : ℕ} {f : Space (n+1) → Space (n+1)}
    (hf : ContDiff ℝ ∞ f) {x : Space (n+1)} (hx : f x ≠ 0) :
    extDeriv (pullForm f) x = 0 := by
  change extDeriv (fun y => (radialForm n (f y)).compContinuousLinearMap (fderiv ℝ f y)) x = 0
  rw [extDeriv_pullback (differentiableAt_radialForm hx) hf.contDiffAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top),
    closed_radialForm hx]
  ext v
  rfl

 def formVector {n : ℕ} (η : Space (n+1) → (Space (n+1)) [⋀^Fin n]→L[ℝ] ℝ)
    (x : Space (n+1)) : Space (n+1) :=
   fun i => (-1 : ℝ)^i.val * η x (i.removeNth (basis (n+1)))

 theorem differentiableAt_formVector {n : ℕ}
    {η : Space (n+1) → (Space (n+1)) [⋀^Fin n]→L[ℝ] ℝ} {x : Space (n+1)}
    (hη : DifferentiableAt ℝ η x) : DifferentiableAt ℝ (formVector η) x := by
  apply differentiableAt_pi.mpr
  intro i
  exact ((ContinuousAlternatingMap.apply ℝ _ _ (i.removeNth (basis (n+1)))).differentiableAt.comp x hη).const_mul _

 theorem divergence_formVector {n : ℕ}
    {η : Space (n+1) → (Space (n+1)) [⋀^Fin n]→L[ℝ] ℝ} {x : Space (n+1)}
    (hη : DifferentiableAt ℝ η x) :
    ∑ i, fderiv ℝ (formVector η) x (basis (n+1) i) i = extDeriv η x (basis (n+1)) := by
  rw [extDeriv_apply hη]
  apply Finset.sum_congr rfl
  intro i hi
  have hd := (differentiableAt_formVector hη).hasFDerivAt
  have hei : fderiv ℝ (fun y => formVector η y i) x =
      (ContinuousLinearMap.proj i).comp (fderiv ℝ (formVector η) x) :=
    ((ContinuousLinearMap.proj i : Space (n+1) →L[ℝ] ℝ).hasFDerivAt.comp x hd).fderiv
  have hw : DifferentiableAt ℝ (fun y => η y (i.removeNth (basis (n+1)))) x :=
    (hη.hasFDerivAt.continuousAlternatingMap_apply_const _).differentiableAt
  have he : fderiv ℝ (fun y => formVector η y i) x =
      (-1 : ℝ)^i.val • fderiv ℝ (fun y => η y (i.removeNth (basis (n+1)))) x :=
    (hw.hasFDerivAt.const_mul _).fderiv
  have := congrArg (fun l : Space (n+1) →L[ℝ] ℝ => l (basis (n+1) i)) (hei.symm.trans he)
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, smul_apply,
    smul_eq_mul, zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one] using this

 theorem formVector_radialForm {n : ℕ} (x : Space (n+1)) :
    formVector (radialForm n) x = radial x := by
  ext i
  change (-1 : ℝ)^i.val * (vol (n+1)).curryLeft (radial x) (i.removeNth (basis (n+1))) = _
  rw [contract_basis, ← mul_assoc, ← pow_add,
    show i.val+i.val = 2*i.val by omega, pow_mul, neg_one_sq, one_pow, one_mul]

 theorem pullForm_eventually_id {n : ℕ} {f : Space (n+1) → Space (n+1)} {x : Space (n+1)}
    (h : f =ᶠ[𝓝 x] id) : pullForm f x = radialForm n x := by
  unfold pullForm
  rw [h.eq_of_nhds, h.fderiv_eq, fderiv_id]
  ext v
  rfl

 theorem positive_integral_cube {n : ℕ} (g : Space n → ℝ) (hg : Continuous g)
    (hp : ∀ x, 0 < g x) {R : ℝ} (hR : 0 < R) :
    0 < ∫ x in Icc (fun _ : Fin n => -R) (fun _ => R), g x := by
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall (fun x => (hp x).le)) hg.integrableOn_Icc).mpr
  have hs : Function.support g = univ := by
    ext x
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (hp x).ne'
  rw [hs, univ_inter, Real.volume_Icc_pi]
  apply pos_iff_ne_zero.mpr
  exact Finset.prod_ne_zero_iff.mpr fun _ _ => ENNReal.ofReal_ne_zero_iff.mpr (by linarith)

 theorem continuous_face {n : ℕ} {G : Space (n+1) → Space (n+1)} (hG : Continuous G)
    (i : Fin (n+1)) (a : ℝ) : Continuous (fun y : Space n => G (i.insertNth a y) i) := by
  exact (continuous_apply i).comp (hG.comp (continuous_const.finInsertNth i continuous_id))

 theorem radial_front_pos {n : ℕ} (i : Fin (n+1)) (y : Space n) {S : ℝ} (hS : 0 < S) :
    0 < radial (i.insertNth S y : Space (n+1)) i := by
  simp only [radial, Pi.smul_apply, smul_eq_mul, Fin.insertNth_apply_same]
  refine mul_pos (Real.rpow_pos_of_pos (sqsum_pos ?_) _) hS
  intro he
  have he' := congrFun he i
  exact hS.ne' (by simpa only [Fin.insertNth_apply_same, Pi.zero_apply] using he')

 theorem radial_back_neg {n : ℕ} (i : Fin (n+1)) (y : Space n) {S : ℝ} (hS : 0 < S) :
    radial (i.insertNth (-S) y : Space (n+1)) i < 0 := by
  simp only [radial, Pi.smul_apply, smul_eq_mul, Fin.insertNth_apply_same]
  refine mul_neg_of_pos_of_neg (Real.rpow_pos_of_pos (sqsum_pos ?_) _) (neg_neg_of_pos hS)
  intro he
  have he' := congrFun he i
  simp only [Fin.insertNth_apply_same, Pi.zero_apply, neg_eq_zero] at he'
  exact hS.ne' he'

 theorem face_norm_bound {n : ℕ} (i : Fin (n+1)) (y : Space n) (a : ℝ) :
    |a| ≤ ‖(i.insertNth a y : Space (n+1))‖ := by
  simpa only [Fin.insertNth_apply_same, Real.norm_eq_abs] using
    (norm_le_pi_norm (i.insertNth a y : Space (n+1)) i)

 theorem positive_flux {n : ℕ} {G : Space (n+1) → Space (n+1)} (hG : Continuous G)
    {R S : ℝ} (hS : 0 < S) (hRS : R < S)
    (hGrad : ∀ x, R < ‖x‖ → G x = radial x) (i : Fin (n+1)) :
    0 < (∫ y in Icc (fun _ : Fin n => -S) (fun _ => S), G (i.insertNth S y) i) -
      ∫ y in Icc (fun _ : Fin n => -S) (fun _ => S), G (i.insertNth (-S) y) i := by
  have hfront (y : Space n) : 0 < G (i.insertNth S y) i := by
    rw [hGrad _ (lt_of_lt_of_le hRS (by simpa only [abs_of_pos hS] using face_norm_bound i y S))]
    exact radial_front_pos i y hS
  have hback (y : Space n) : G (i.insertNth (-S) y) i < 0 := by
    rw [hGrad _ (lt_of_lt_of_le hRS (by simpa only [abs_neg, abs_of_pos hS] using face_norm_bound i y (-S)))]
    exact radial_back_neg i y hS
  have hp := positive_integral_cube _ (continuous_face hG i S) hfront hS
  have hn := positive_integral_cube (fun y => -G (i.insertNth (-S) y) i)
    (continuous_face hG i (-S)).neg (fun y => neg_pos.mpr (hback y)) hS
  rw [integral_neg] at hn
  linarith

 theorem divergence_obstruction {n : ℕ} {G : Space (n+1) → Space (n+1)}
    (hG : Differentiable ℝ G) (hdiv : ∀ x, ∑ i, fderiv ℝ G x (basis (n+1) i) i = 0)
    {R : ℝ} (hR : 0 < R) (hGrad : ∀ x, R < ‖x‖ → G x = radial x) : False := by
  let S := R+1
  have hS : 0 < S := by dsimp [S]; linarith
  have hstokes := integral_divergence_of_hasFDerivAt_off_countable
    (fun _ : Fin (n+1) => -S) (fun _ => S) (fun _ => by linarith)
    G (fderiv ℝ G) ∅ countable_empty hG.continuous.continuousOn
    (fun x _ => (hG x).hasFDerivAt)
    (show IntegrableOn (fun x => ∑ i, fderiv ℝ G x (basis (n+1) i) i)
      (Icc (fun _ : Fin (n+1) => -S) (fun _ => S)) volume from by
      simpa only [hdiv] using (integrableOn_zero : IntegrableOn (fun _ : Space (n+1) => (0 : ℝ))
        (Icc (fun _ => -S) (fun _ => S)) volume))
  change (∫ x in Icc (fun _ : Fin (n+1) => -S) (fun _ => S),
      ∑ i, fderiv ℝ G x (basis (n+1) i) i) = _ at hstokes
  simp only [hdiv, integral_zero] at hstokes
  have hp := Finset.sum_pos (s := Finset.univ)
    (fun i _ => positive_flux hG.continuous hS (show R < S by dsimp [S]; linarith) hGrad i)
    Finset.univ_nonempty
  exact (ne_of_gt hp) hstokes.symm

 theorem exists_zero_of_identity_outside {n : ℕ} {f : Space (n+1) → Space (n+1)}
    (hf : ContDiff ℝ ∞ f) {R : ℝ} (hR : 0 < R)
    (hId : ∀ x, R ≤ ‖x‖ → f x = x) : ∃ x, f x = 0 := by
  by_contra hnone
  push Not at hnone
  let G := formVector (pullForm f)
  have hGdiff : Differentiable ℝ G := fun x =>
    differentiableAt_formVector (differentiableAt_pullForm hf (hnone x))
  have hdiv (x : Space (n+1)) : ∑ i, fderiv ℝ G x (basis (n+1) i) i = 0 := by
    rw [divergence_formVector (differentiableAt_pullForm hf (hnone x)),
      closed_pullForm hf (hnone x)]
    rfl
  have hevent {x : Space (n+1)} (hx : R < ‖x‖) : f =ᶠ[𝓝 x] id := by
    have hopen : IsOpen {y : Space (n+1) | R < ‖y‖} := isOpen_lt continuous_const continuous_norm
    filter_upwards [hopen.mem_nhds hx] with y hy
    exact hId y hy.le
  have hGrad {x : Space (n+1)} (hx : R < ‖x‖) : G x = radial x := by
    change formVector (pullForm f) x = radial x
    have he := pullForm_eventually_id (hevent hx)
    have hrewrite : formVector (pullForm f) x = formVector (radialForm n) x := by
      ext i
      simp only [formVector, he]
    rw [hrewrite, formVector_radialForm]
  exact divergence_obstruction hGdiff hdiv hR (fun x hx => hGrad hx)

 theorem exists_zero_space {d : ℕ} {f : Space d → Space d}
    (hf : ContDiff ℝ ∞ f) {R : ℝ} (hR : 0 < R)
    (hId : ∀ x, R ≤ ‖x‖ → f x = x) : ∃ x, f x = 0 := by
  cases d with
  | zero => exact ⟨0, Subsingleton.elim _ _⟩
  | succ n => exact exists_zero_of_identity_outside hf hR hId

 theorem exists_zero {E : Type u78} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → E} (hf : ContDiff ℝ ∞ f)
    {R : ℝ} (hR : 0 < R) (hId : ∀ x, R ≤ ‖x‖ → f x = x) : ∃ x, f x = 0 := by
  let b := (Module.finBasis ℝ E).equivFunL
  let C := ‖b.toContinuousLinearMap‖
  have hC : 0 ≤ C := norm_nonneg _
  let S := C*R+1
  have hS : 0 < S := by dsimp [S]; positivity
  let g : Space (Module.finrank ℝ E) → Space (Module.finrank ℝ E) := fun y => b (f (b.symm y))
  have hg : ContDiff ℝ ∞ g := b.contDiff.comp (hf.comp b.symm.contDiff)
  have hgId (y : Space (Module.finrank ℝ E)) (hy : S ≤ ‖y‖) : g y = y := by
    have hbnd : ‖y‖ ≤ C*‖b.symm y‖ := by
      simpa only [ContinuousLinearEquiv.coe_coe, b.apply_symm_apply] using
        (b.toContinuousLinearMap.le_opNorm (b.symm y))
    have hn : R ≤ ‖b.symm y‖ := by dsimp [S] at hy; nlinarith
    dsimp [g]
    rw [hId _ hn, b.apply_symm_apply]
  obtain ⟨y, hy⟩ := exists_zero_space hg hS hgId
  refine ⟨b.symm y, b.injective ?_⟩
  simpa only [map_zero] using hy

 theorem exists_zero_of_compactSupport {E : Type u79} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → E} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport (fun x => f x-x)) : ∃ x, f x = 0 := by
  obtain ⟨R, hR, h⟩ := hc.exists_pos_le_norm
  exact exists_zero hf hR (fun x hx => sub_eq_zero.mp (h x hx))

end
end SmoothDegree

end
end NonsqueezingInline

end OAI
