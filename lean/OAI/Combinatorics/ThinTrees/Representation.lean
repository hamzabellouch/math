import OAI.Combinatorics.ThinTrees.TwoSystems

namespace OAI

universe uι uE uT uI uE2 uE3 uV uE4 uV2 uW

section

open Matrix Finset
open scoped BigOperators MatrixOrder Matrix.Norms.Elementwise
namespace StrongThinTree
noncomputable section

section Determinant
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma hasDerivAt_det_one_add_smul (M : Matrix ι ι ℝ) :
    HasDerivAt (fun t : ℝ => (1 + t • M).det) M.trace 0 := by
  let p : Polynomial ℝ :=
    (Matrix.det (1 + (Polynomial.X : Polynomial ℝ) • M.map Polynomial.C)).divX.divX
  have hp := p.hasDerivAt (0 : ℝ)
  have hid := hasDerivAt_id (0 : ℝ)
  have h := ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).add
    (hid.const_mul M.trace)).add (hp.mul (hid.pow 2))
  have heq : (fun t : ℝ => (1 + t • M).det) =
      (fun t : ℝ => 1 + M.trace * t + p.eval t * t ^ 2) := by
    funext t
    exact Matrix.det_one_add_smul t M
  rw [heq]
  simpa using! h

lemma hasDerivAt_det_add_smul (A B : Matrix ι ι ℝ) (hA : IsUnit A) :
    HasDerivAt (fun t : ℝ => (A + t • B).det)
      (A.det * (A⁻¹ * B).trace) 0 := by
  have hmul : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A
    ((Matrix.isUnit_iff_isUnit_det A).mp hA)
  have heq (t : ℝ) : A + t • B = A * (1 + t • (A⁻¹ * B)) := by
    simp [mul_add, ← mul_assoc, hmul]
  have heq' : (fun t : ℝ => (A + t • B).det) =
      (fun t : ℝ => A.det * (1 + t • (A⁻¹ * B)).det) := by
    funext t
    rw [heq, Matrix.det_mul]
  rw [heq']
  exact (hasDerivAt_det_one_add_smul (A⁻¹ * B)).const_mul A.det

lemma differentiable_det : Differentiable ℝ (Matrix.det : Matrix ι ι ℝ → ℝ) := by
  classical
  change Differentiable ℝ (fun M : Matrix ι ι ℝ => M.det)
  simp_rw [Matrix.det_apply]
  fun_prop

lemma fderiv_det_apply (A B : Matrix ι ι ℝ) (hA : IsUnit A) :
    fderiv ℝ Matrix.det A B = A.det * (A⁻¹ * B).trace := by
  have hc : HasDerivAt (fun t : ℝ => A + t • B) B 0 := by
    simpa using! (hasDerivAt_const (0 : ℝ) A).add
      ((hasDerivAt_id (0 : ℝ)).smul_const B)
  have hd : HasFDerivAt Matrix.det (fderiv ℝ Matrix.det A) (A + (0 : ℝ) • B) := by
    simpa using! (differentiable_det A).hasFDerivAt
  have h := hd.comp_hasDerivAt (0 : ℝ) hc
  exact h.unique (hasDerivAt_det_add_smul A B hA)

lemma one_le_det_one_add {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    1 ≤ (1 + A).det := by
  let U := hA.isHermitian.eigenvectorUnitary
  let D : Matrix ι ι ℝ := Matrix.diagonal hA.isHermitian.eigenvalues
  have hspec : A = (U : Matrix ι ι ℝ) * D * star (U : Matrix ι ι ℝ) := by
    simpa [D, U, Unitary.conjStarAlgAut_apply] using hA.isHermitian.spectral_theorem
  have hconj : 1 + A = (U : Matrix ι ι ℝ) * (1 + D) * star (U : Matrix ι ι ℝ) := by
    rw [hspec]
    simp [mul_add, add_mul]
  rw [hconj, Matrix.det_mul_comm, ← mul_assoc, Unitary.coe_star_mul_self, one_mul]
  have hdiag : 1 + D = Matrix.diagonal (fun i => 1 + hA.isHermitian.eigenvalues i) := by
    simp only [D, ← Matrix.diagonal_one, Matrix.diagonal_add]
  rw [hdiag, Matrix.det_diagonal]
  exact Finset.one_le_prod₀ (fun i _ => by linarith [hA.eigenvalues_nonneg i])

lemma posDef_sqrt_factors {A : Matrix ι ι ℝ} (hA : A.PosDef) :
    ∃ S : Matrix ι ι ℝ, S.IsHermitian ∧ IsUnit S ∧ S * S = A := by
  refine ⟨CFC.sqrt A, (CFC.sqrt_nonneg A).posSemidef.isHermitian, ?_,
    CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg⟩
  apply (isUnit_pow_iff (by decide : 2 ≠ 0)).mp
  rw [CFC.sq_sqrt A hA.posSemidef.nonneg]
  exact hA.isUnit

lemma det_le_det_add_of_posSemidef {A B : Matrix ι ι ℝ}
    (hA : A.PosDef) (hB : B.PosSemidef) : A.det ≤ (A + B).det := by
  obtain ⟨S, hSH, hSU, hS⟩ := posDef_sqrt_factors hA
  have hSi : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S
    ((Matrix.isUnit_iff_isUnit_det S).mp hSU)
  have hiS : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S
    ((Matrix.isUnit_iff_isUnit_det S).mp hSU)
  let Q := S⁻¹ * B * S⁻¹
  have hQ : Q.PosSemidef := by
    simpa only [hSH.inv.eq] using hB.mul_mul_conjTranspose_same S⁻¹
  have hdecomp : A + B = S * (1 + Q) * S := by
    dsimp [Q]
    simp only [mul_add, add_mul, mul_one, ← mul_assoc, hS]
    simp only [mul_assoc, hSi, hiS, one_mul, mul_one]
  have hdetS : S.det * S.det = A.det := by rw [← Matrix.det_mul, hS]
  have hdet : (A + B).det = A.det * (1 + Q).det := by
    rw [hdecomp, Matrix.det_mul, Matrix.det_mul]
    rw [← hdetS]
    ring
  rw [hdet]
  exact le_mul_of_one_le_right hA.det_pos.le (one_le_det_one_add hQ)

end Determinant
section Regularization
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
open Filter

lemma exists_fderiv_norm_lt_of_bddBelow (f : E → ℝ) (hf : Differentiable ℝ f)
    (L : ℝ) (hb : ∀ x, L ≤ f x) {ε : ℝ} (hε : 0 < ε) :
    ∃ x, ‖fderiv ℝ f x‖ < ε := by
  let K : ℝ := f 0 - L
  have hK : 0 ≤ K := sub_nonneg.mpr (hb 0)
  let γ : ℝ := ε ^ 2 / (16 * (K + 1))
  have hγ : 0 < γ := div_pos (sq_pos_of_pos hε) (by positivity)
  let g : E → ℝ := fun x => f x + γ * ‖x‖ ^ 2
  have hg : Continuous g := hf.continuous.add
    (continuous_const.mul (continuous_norm.pow 2))
  have hcoerc : Tendsto (fun x : E => L + γ * ‖x‖ ^ 2) (cocompact E) atTop := by
    have hn : Tendsto (fun x : E => ‖x‖ ^ 2) (cocompact E) atTop := by
      simpa only [pow_two] using
        tendsto_norm_cocompact_atTop.atTop_mul_atTop₀
          (tendsto_norm_cocompact_atTop (E := E))
    exact tendsto_const_nhds.add_atTop (hn.const_mul_atTop hγ)
  have hcoercg : Tendsto g (cocompact E) atTop :=
    tendsto_atTop_mono (fun x => by dsimp [g]; linarith [hb x]) hcoerc
  obtain ⟨x, hx⟩ := hg.exists_forall_le hcoercg
  have hx0 := hx 0
  have hvalue : γ * ‖x‖ ^ 2 ≤ K := by
    dsimp [g] at hx0
    simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] at hx0
    dsimp [K]
    linarith [hb x]
  have hmin : IsLocalMin g x := by
    exact (show IsMinOn g Set.univ x from fun y _ => hx y).isLocalMin
      (by simp)
  have hder := hmin.hasFDerivAt_eq_zero
    ((hf x).hasFDerivAt.add
      ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul γ))
  have hnorm : ‖fderiv ℝ f x‖ = 2 * γ * ‖x‖ := by
    have hd : fderiv ℝ f x = -(γ • ((2 : ℝ) • innerSL ℝ x)) := by
      apply eq_neg_of_add_eq_zero_left
      simpa only [two_smul] using hder
    rw [hd, norm_neg, norm_smul, norm_smul, innerSL_apply_norm]
    simp only [Real.norm_eq_abs, abs_of_pos hγ, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    ring
  refine ⟨x, ?_⟩
  rw [hnorm]
  have hγeq : γ * (16 * (K + 1)) = ε ^ 2 := by
    dsimp [γ]
    exact div_mul_cancel₀ _ (ne_of_gt (by positivity))
  have hbnd := mul_le_mul_of_nonneg_left hvalue (le_of_lt hγ)
  have hγK : 4 * γ * K < ε ^ 2 := by
    nlinarith
  have hxnonneg : 0 ≤ 2 * γ * ‖x‖ := by positivity
  nlinarith [sq_nonneg (2 * γ * ‖x‖)]

end Regularization
section Covariance
variable {T : Type uT} {I : Type uI} [Fintype T] [DecidableEq T] [Nonempty T]
  [Fintype I] [DecidableEq I]

def basisCov (b : Matrix I I ℝ) (a : I → ℝ) : Matrix I I ℝ :=
  b * diagonal (fun j => Real.exp (a j)) * bᵀ

def packingCov (b : T → Matrix I I ℝ) (a : EuclideanSpace ℝ (T × I)) :
    Matrix I I ℝ := ∑ t, basisCov (b t) (fun j => a (t, j))

lemma basisCov_eq_sum (b : Matrix I I ℝ) (a : I → ℝ) :
    basisCov b a = ∑ j, Real.exp (a j) • vecMulVec (fun i => b i j) (fun i => b i j) := by
  apply Matrix.ext
  intro k l
  change (∑ j, (b * diagonal (fun j => Real.exp (a j))) k j * b l j) = _
  simp only [Matrix.mul_diagonal, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.vecMulVec_apply]
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [DecidableEq T] [Nonempty T] in
lemma packingCov_eq_sum (b : T → Matrix I I ℝ) (a : EuclideanSpace ℝ (T × I)) :
    packingCov b a = ∑ e : T × I, Real.exp (a e) •
      vecMulVec (fun i => b e.1 i e.2) (fun i => b e.1 i e.2) := by
  simp only [packingCov, basisCov_eq_sum, Fintype.sum_prod_type]

omit [DecidableEq T] [Nonempty T] in
lemma differentiable_packingCov (b : T → Matrix I I ℝ) :
    Differentiable ℝ (packingCov b) := by
  have heq : packingCov b = fun a => ∑ e : T × I, Real.exp (a e) •
      vecMulVec (fun i => b e.1 i e.2) (fun i => b e.1 i e.2) :=
    funext (packingCov_eq_sum b)
  rw [heq]
  exact Differentiable.fun_sum fun e _ =>
    ((EuclideanSpace.proj (𝕜 := ℝ) e).differentiable.exp).smul_const _

omit [Nonempty T] in
lemma fderiv_packingCov_single (b : T → Matrix I I ℝ)
    (a : EuclideanSpace ℝ (T × I)) (e : T × I) :
    fderiv ℝ (packingCov b) a (EuclideanSpace.single e 1) =
      Real.exp (a e) • vecMulVec (fun i => b e.1 i e.2) (fun i => b e.1 i e.2) := by
  have heq : packingCov b = fun a => ∑ e : T × I, Real.exp (a e) •
      vecMulVec (fun i => b e.1 i e.2) (fun i => b e.1 i e.2) :=
    funext (packingCov_eq_sum b)
  have hd : HasFDerivAt (packingCov b)
      (∑ e : T × I, (Real.exp (a e) • EuclideanSpace.proj (𝕜 := ℝ) e).smulRight
        (vecMulVec (fun i => b e.1 i e.2) (fun i => b e.1 i e.2))) a := by
    rw [heq]
    exact HasFDerivAt.fun_sum fun e _ =>
      ((EuclideanSpace.proj (𝕜 := ℝ) e).hasFDerivAt.exp).smul_const _
  rw [hd.fderiv]
  simp

lemma basisCov_posDef (b : Matrix I I ℝ) (hb : IsUnit b) (a : I → ℝ) :
    (basisCov b a).PosDef := by
  have hd : (diagonal (fun j => Real.exp (a j))).PosDef :=
    Matrix.PosDef.diagonal (fun j => Real.exp_pos _)
  simpa [basisCov] using hd.mul_mul_conjTranspose_same
    (Matrix.vecMul_injective_of_isUnit hb)

omit [DecidableEq T] in
lemma packingCov_posDef (b : T → Matrix I I ℝ) (hb : ∀ t, IsUnit (b t))
    (a : EuclideanSpace ℝ (T × I)) : (packingCov b a).PosDef := by
  exact Matrix.posDef_sum Finset.univ_nonempty
    (fun t _ => basisCov_posDef (b t) (hb t) _)

lemma det_basisCov (b : Matrix I I ℝ) (a : I → ℝ) :
    (basisCov b a).det = b.det ^ 2 * Real.exp (∑ j, a j) := by
  simp only [basisCov, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
  rw [Real.exp_sum]
  ring

omit [Nonempty T] in
lemma det_basisCov_le_packingCov (b : T → Matrix I I ℝ)
    (hb : ∀ t, IsUnit (b t)) (a : EuclideanSpace ℝ (T × I)) (t : T) :
    (basisCov (b t) (fun j => a (t, j))).det ≤ (packingCov b a).det := by
  have hsum : packingCov b a = basisCov (b t) (fun j => a (t, j)) +
      ∑ u ∈ Finset.univ.erase t, basisCov (b u) (fun j => a (u, j)) := by
    exact (Finset.add_sum_erase _ _ (Finset.mem_univ t)).symm
  rw [hsum]
  apply det_le_det_add_of_posSemidef (basisCov_posDef _ (hb t) _)
  exact Matrix.posSemidef_sum _ (fun u _ => (basisCov_posDef _ (hb u) _).posSemidef)

def packingObjective (b : T → Matrix I I ℝ) (a : EuclideanSpace ℝ (T × I)) : ℝ :=
  Real.log (packingCov b a).det - (∑ e, a e) / Fintype.card T

lemma packingObjective_bddBelow (b : T → Matrix I I ℝ) (hb : ∀ t, IsUnit (b t)) :
    ∀ a, (∑ t, Real.log ((b t).det ^ 2)) / Fintype.card T ≤ packingObjective b a := by
  intro a
  have ht (t : T) : Real.log ((b t).det ^ 2) + ∑ j, a (t, j) ≤
      Real.log (packingCov b a).det := by
    have hd := (basisCov_posDef (b t) (hb t) (fun j => a (t, j))).det_pos
    have hbd := det_basisCov_le_packingCov b hb a t
    have he := Real.log_le_log hd hbd
    rw [det_basisCov, Real.log_mul (by
      have := (Matrix.isUnit_iff_isUnit_det _).mp (hb t)
      exact pow_ne_zero 2 this.ne_zero) (ne_of_gt (Real.exp_pos _)), Real.log_exp] at he
    exact he
  have hs := Finset.sum_le_sum (fun t (_ : t ∈ Finset.univ) => ht t)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  have hq : (0 : ℝ) < Fintype.card T := Nat.cast_pos.mpr Fintype.card_pos
  dsimp [packingObjective]
  rw [le_sub_iff_add_le, ← add_div, div_le_iff₀ hq]
  rw [mul_comm] at hs
  simpa only [Fintype.sum_prod_type] using hs

omit [DecidableEq T] in
lemma differentiable_packingObjective (b : T → Matrix I I ℝ) (hb : ∀ t, IsUnit (b t)) :
    Differentiable ℝ (packingObjective b) := by
  intro a
  apply DifferentiableAt.sub
  · exact ((differentiable_det _).comp a (differentiable_packingCov b a)).log
      (ne_of_gt (packingCov_posDef b hb a).det_pos)
  · have hs : DifferentiableAt ℝ (fun a : EuclideanSpace ℝ (T × I) => ∑ e, a e) a :=
      DifferentiableAt.fun_sum (fun e _ => (EuclideanSpace.proj (𝕜 := ℝ) e).differentiableAt)
    simpa only [div_eq_mul_inv] using hs.mul_const ((Fintype.card T : ℝ)⁻¹)

lemma fderiv_packingObjective_single (b : T → Matrix I I ℝ) (hb : ∀ t, IsUnit (b t))
    (a : EuclideanSpace ℝ (T × I)) (e : T × I) :
    fderiv ℝ (packingObjective b) a (EuclideanSpace.single e 1) =
      Real.exp (a e) * ((fun i => b e.1 i e.2) ⬝ᵥ
        ((packingCov b a)⁻¹ *ᵥ (fun i => b e.1 i e.2))) - 1 / Fintype.card T := by
  have hn := (differentiable_packingCov b a).hasFDerivAt
  have hd := (differentiable_det (packingCov b a)).hasFDerivAt.comp a hn
  have hpos := (packingCov_posDef b hb a).det_pos
  have hl := hd.log (ne_of_gt hpos)
  have hs : HasFDerivAt (fun a : EuclideanSpace ℝ (T × I) => ∑ e, a e)
      (∑ e, EuclideanSpace.proj (𝕜 := ℝ) e) a :=
    HasFDerivAt.fun_sum (fun e _ => (EuclideanSpace.proj (𝕜 := ℝ) e).hasFDerivAt)
  have hsq : HasFDerivAt (fun a : EuclideanSpace ℝ (T × I) => (∑ e, a e) / Fintype.card T)
      ((Fintype.card T : ℝ)⁻¹ • ∑ e, EuclideanSpace.proj (𝕜 := ℝ) e) a := by
    simpa only [div_eq_mul_inv, mul_comm] using hs.const_mul ((Fintype.card T : ℝ)⁻¹)
  have ho := hl.sub hsq
  have ho' : HasFDerivAt (packingObjective b) _ a := ho
  rw [ho'.fderiv]
  change (packingCov b a).det⁻¹ *
      (fderiv ℝ Matrix.det (packingCov b a))
        ((fderiv ℝ (packingCov b) a) (EuclideanSpace.single e 1)) -
      (Fintype.card T : ℝ)⁻¹ * (∑ j, EuclideanSpace.proj (𝕜 := ℝ) j) (EuclideanSpace.single e 1) = _
  rw [fderiv_packingCov_single]
  rw [fderiv_det_apply _ _ (packingCov_posDef b hb a).isUnit]
  simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Matrix.mul_vecMulVec,
    Matrix.trace_vecMulVec, dotProduct_comm]
  simp
  field_simp

lemma exists_small_leverages (b : T → Matrix I I ℝ) (hb : ∀ t, IsUnit (b t))
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ a : EuclideanSpace ℝ (T × I), ∀ e : T × I,
      Real.exp (a e) * ((fun i => b e.1 i e.2) ⬝ᵥ
        ((packingCov b a)⁻¹ *ᵥ (fun i => b e.1 i e.2))) ≤
      (1 + ρ) / Fintype.card T := by
  have hq : (0 : ℝ) < Fintype.card T := Nat.cast_pos.mpr Fintype.card_pos
  obtain ⟨a, ha⟩ := exists_fderiv_norm_lt_of_bddBelow (packingObjective b)
    (differentiable_packingObjective b hb)
    ((∑ t, Real.log ((b t).det ^ 2)) / Fintype.card T)
    (packingObjective_bddBelow b hb) (div_pos hρ hq)
  refine ⟨a, fun e => ?_⟩
  have hv := (fderiv ℝ (packingObjective b) a).le_opNorm (EuclideanSpace.single e 1)
  simp only [PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs] at hv
  have hu := (le_abs_self (fderiv ℝ (packingObjective b) a (EuclideanSpace.single e 1))).trans hv
  have hu' := lt_of_le_of_lt hu ha
  rw [fderiv_packingObjective_single b hb a e] at hu'
  rw [add_div]
  linarith

theorem isotropic_representation (b : T → Matrix I I ℝ) (hb : ∀ t, IsUnit (b t))
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ (M : Matrix I I ℝ) (s : T × I → ℝ), IsUnit M ∧ (∀ e, 0 < s e) ∧
      let z := fun e : T × I => s e • (M *ᵥ fun i => b e.1 i e.2)
      (∑ e, vecMulVec (z e) (z e)) = 1 ∧
      (∀ e, z e ⬝ᵥ z e ≤ (1 + ρ) / Fintype.card T) := by
  obtain ⟨a, ha⟩ := exists_small_leverages b hb hρ
  obtain ⟨S, hSH, hSU, hS⟩ := posDef_sqrt_factors (packingCov_posDef b hb a)
  let M := S⁻¹
  let s : T × I → ℝ := fun e => Real.exp (a e / 2)
  have hMU : IsUnit M := Matrix.isUnit_nonsing_inv_iff.mpr hSU
  have hMT : Mᵀ = M := by simpa [M] using hSH.inv.eq
  have hMS : M * S = 1 := Matrix.nonsing_inv_mul S
    ((Matrix.isUnit_iff_isUnit_det S).mp hSU)
  have hSM : S * M = 1 := Matrix.mul_nonsing_inv S
    ((Matrix.isUnit_iff_isUnit_det S).mp hSU)
  have hMNM : M * packingCov b a * M = 1 := by
    rw [← hS, ← mul_assoc, hMS, one_mul, hSM]
  have hMM : M * M = (packingCov b a)⁻¹ := by
    apply Eq.symm
    apply Matrix.inv_eq_left_inv
    rw [← hS, mul_assoc, ← mul_assoc M S S, hMS, one_mul, hMS]
  have hs (e : T × I) : s e * s e = Real.exp (a e) := by
    dsimp [s]
    rw [← Real.exp_add]
    congr 1
    ring
  have houter (e : T × I) :
      vecMulVec (s e • (M *ᵥ fun i => b e.1 i e.2))
        (s e • (M *ᵥ fun i => b e.1 i e.2)) =
      M * (Real.exp (a e) • vecMulVec (fun i => b e.1 i e.2) (fun i => b e.1 i e.2)) * M := by
    simp only [Matrix.smul_vecMulVec, Matrix.vecMulVec_smul, smul_smul, hs,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
    rw [← Matrix.vecMul_transpose M, hMT]
  have hnorm (e : T × I) :
      (s e • (M *ᵥ fun i => b e.1 i e.2)) ⬝ᵥ (s e • (M *ᵥ fun i => b e.1 i e.2)) =
      Real.exp (a e) * ((fun i => b e.1 i e.2) ⬝ᵥ
        ((packingCov b a)⁻¹ *ᵥ fun i => b e.1 i e.2)) := by
    simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul, ← mul_assoc, hs]
    congr 1
    rw [← hMM, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose M, hMT]
    exact dotProduct_comm _ _
  refine ⟨M, s, hMU, fun e => Real.exp_pos _, ?_, ?_⟩
  · simp_rw [houter]
    rw [← Finset.sum_mul, ← Finset.mul_sum, ← packingCov_eq_sum, hMNM]
  · intro e
    rw [hnorm]
    exact ha e

end Covariance

end
end StrongThinTree

namespace StrongThinTree.Packing
noncomputable section
open Matrix Finset
open scoped BigOperators MatrixOrder Matrix.Norms.Elementwise

variable {E : Type uE2} [Fintype E] [DecidableEq E] {q d : ℕ}

omit [Fintype E] in

 theorem represented_packing (v : E → (Fin d → ℝ)) (F : Fin q → Finset E)
    (hq : 0 < q) (hF : ∀ t, LinearIndepOn ℝ v (F t : Set E))
    (hcard : ∀ t, (F t).card = d) (hd : Pairwise (fun i j => Disjoint (F i) (F j)))
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ (M : Matrix (Fin d) (Fin d) ℝ) (s : E → ℝ),
      IsUnit M ∧ (∀ e, 0 < s e) ∧
      let z := fun e => s e • (M *ᵥ v e)
      (∑ e ∈ Finset.univ.biUnion F, vecMulVec (z e) (z e)) = 1 ∧
      (∀ e ∈ Finset.univ.biUnion F, z e ⬝ᵥ z e ≤ (1 + ρ) / q) := by
  classical
  let : Nonempty (Fin q) := Fin.pos_iff_nonempty.mp hq
  let B := Finset.univ.biUnion F
  let en (t : Fin q) : Fin d ≃ ↥(F t) :=
    Fintype.equivOfCardEq (by simp [hcard])
  let b (t : Fin q) : Matrix (Fin d) (Fin d) ℝ := fun i j => v (en t j) i
  have hb : ∀ t, IsUnit (b t) := by
    intro t
    apply Matrix.mulVec_injective_iff_isUnit.mp
    apply Matrix.mulVec_injective_iff.mpr
    exact (hF t).linearIndependent.comp (en t) (en t).injective
  let f : Fin q × Fin d → ↥B := fun tj => ⟨en tj.1 tj.2,
    Finset.mem_biUnion.mpr ⟨tj.1, Finset.mem_univ _, (en tj.1 tj.2).2⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨t, j⟩ ⟨t', j'⟩ heq
      have hev : (en t j : E) = (en t' j' : E) := congrArg Subtype.val heq
      have ht : t = t' := by
        by_contra h
        exact Finset.disjoint_left.mp (hd h) (en t j).2 (hev ▸ (en t' j').2)
      subst t'
      have hj : j = j' := (en t).injective (Subtype.ext hev)
      subst j'; rfl
    · intro e
      obtain ⟨t, ht, he⟩ := Finset.mem_biUnion.mp e.2
      refine ⟨(t, (en t).symm ⟨e, he⟩), ?_⟩
      apply Subtype.ext
      simp [f]
  let eb := Equiv.ofBijective f hf
  obtain ⟨M, s₀, hM, hs₀, hz, hnorm⟩ := isotropic_representation b hb hρ
  let s : E → ℝ := fun e => if he : e ∈ B then s₀ (eb.symm ⟨e, he⟩) else 1
  have hs : ∀ e, 0 < s e := by
    intro e
    dsimp [s]
    split_ifs
    · exact hs₀ _
    · exact zero_lt_one
  have hs_eq (tj : Fin q × Fin d) : s (eb tj) = s₀ tj := by
    simp [s, (eb tj).2]
  refine ⟨M, s, hM, hs, ?_, ?_⟩
  · rw [← Finset.sum_coe_sort]
    rw [← eb.sum_comp]
    convert hz using 1
    apply Finset.sum_congr rfl
    intro tj htj
    change vecMulVec (s (eb tj) • (M *ᵥ v (eb tj)))
      (s (eb tj) • (M *ᵥ v (eb tj))) = _
    rw [hs_eq]
    rfl
  · intro e he
    have hh := hnorm (eb.symm ⟨e, he⟩)
    have hv : v e = fun i => b (eb.symm ⟨e, he⟩).1 i (eb.symm ⟨e, he⟩).2 := by
      have hh : (en (eb.symm ⟨e, he⟩).1 (eb.symm ⟨e, he⟩).2 : E) = e :=
        congrArg Subtype.val (eb.apply_symm_apply ⟨e, he⟩)
      simp [b, hh]
    have heB : e ∈ B := he
    have hsE : s e = s₀ (eb.symm ⟨e, he⟩) := by simp only [s, dite_eq_left heB]
    change (s e • (M *ᵥ v e)) ⬝ᵥ (s e • (M *ᵥ v e)) ≤ _
    rw [hsE, hv]
    simpa only [Fintype.card_fin] using hh

end
end StrongThinTree.Packing

namespace StrongThinTree.MultiGraph
noncomputable section
open Matrix Finset
open scoped BigOperators
variable {n m : ℕ} (G : MultiGraph n m)

def zeroSumSpace (n : ℕ) : Submodule ℝ (Fin n → ℝ) :=
  LinearMap.ker (∑ u : Fin n, LinearMap.proj u)

lemma mem_zeroSumSpace (x : Fin n → ℝ) : x ∈ zeroSumSpace n ↔ ∑ u, x u = 0 := by
  simp [zeroSumSpace, LinearMap.mem_ker, LinearMap.sum_apply]

lemma incidence_zeroSum (e : Fin m) : G.incidence e ∈ zeroSumSpace n := by
  rw [mem_zeroSumSpace]
  simp [incidence, point, Pi.sub_apply, Finset.sum_sub_distrib, Pi.single_apply,
    Finset.sum_ite_eq']

lemma edgeSpan_le_zeroSum (T : Finset (Fin m)) : G.edgeSpan T ≤ zeroSumSpace n :=
  (Packing.span_le_iff G.incidence).mpr (fun e _he => G.incidence_zeroSum e)

lemma connected_span_zeroSum {T : Finset (Fin m)} (hn : 0 < n) (hT : G.Connected T) :
    G.edgeSpan T = zeroSumSpace n := by
  apply le_antisymm (G.edgeSpan_le_zeroSum T)
  intro x hx
  have hx0 := (mem_zeroSumSpace x).mp hx
  let u₀ : Fin n := ⟨0, hn⟩
  have hs : ∑ u, x u • (point u - point u₀) ∈ G.edgeSpan T := by
    apply Submodule.sum_mem
    intro u hu
    exact Submodule.smul_mem _ _ ((G.connected_iff_same T).mp hT u u₀)
  have heq : ∑ u, x u • (point u - point u₀) = x := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hx0, zero_smul, sub_zero]
    ext u
    simp [point, Pi.single_apply, Finset.sum_apply, mul_ite]
  rwa [heq] at hs

lemma zeroSum_finrank {T : Finset (Fin m)} (hn : 0 < n) (hT : G.Connected T) :
    Module.finrank ℝ (zeroSumSpace n) = n - 1 := by
  rw [← G.connected_span_zeroSum hn hT]
  exact G.connected_rank hn hT

theorem graph_isotropic_representation {q : ℕ} (hq : 0 < q) (hn : 2 ≤ n)
    (F : Fin q → Finset (Fin m)) (hF : ∀ t, G.SpanningTree (F t))
    (hd : Pairwise (fun i j => Disjoint (F i) (F j))) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ (L : zeroSumSpace n ≃ₗ[ℝ] (Fin (n - 1) → ℝ)) (s : Fin m → ℝ),
      (∀ e, 0 < s e) ∧
      let z := fun e => s e • L ⟨G.incidence e, G.incidence_zeroSum e⟩
      (∑ e ∈ Finset.univ.biUnion F, vecMulVec (z e) (z e)) = 1 ∧
      (∀ e ∈ Finset.univ.biUnion F, z e ⬝ᵥ z e ≤ (1 + ρ) / q) := by
  classical
  have hn' : 0 < n := by omega
  let L₀ : zeroSumSpace n ≃ₗ[ℝ] (Fin (n - 1) → ℝ) :=
    LinearEquiv.ofFinrankEq _ _ (by
      rw [G.zeroSum_finrank hn' (hF ⟨0, hq⟩).1]
      simp)
  let v := fun e => L₀ ⟨G.incidence e, G.incidence_zeroSum e⟩
  have hvi (t : Fin q) : LinearIndepOn ℝ v (F t : Set (Fin m)) := by
    have hi := ((G.spanningTree_iff_independent (F t)).mp (hF t)).2.linearIndependent
    have hi' : LinearIndependent ℝ
        (fun e : ↥(F t) => (⟨G.incidence e, G.incidence_zeroSum e⟩ : zeroSumSpace n)) :=
      hi.of_comp (zeroSumSpace n).subtype
    exact hi'.map' L₀.toLinearMap L₀.ker
  obtain ⟨M, s, hM, hs, hi, hb⟩ := Packing.represented_packing v F hq hvi
    (fun t => G.spanningTree_card hn' (hF t)) hd hρ
  let L := L₀.trans (Matrix.toLinearEquiv' M hM.invertible)
  exact ⟨L, s, hs, hi, hb⟩

end
end StrongThinTree.MultiGraph

namespace StrongThinTree.Packing
noncomputable section
open scoped BigOperators
open Finset
variable {E : Type uE3} {V : Type uV} [Fintype E] [DecidableEq E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

omit [Fintype E] in

lemma projected_trace_bound (v : E → V) (A U : Finset E) {c h : ℝ}
    (_hU : U ⊆ A) (hn : ∀ e ∈ A, ‖v e‖ ^ 2 ≤ h)
    (hlow : ∀ x : V, c * ‖x‖ ^ 2 ≤ ∑ e ∈ A, (inner ℝ x (v e)) ^ 2) :
    c * (Module.finrank ℝ V - Module.finrank ℝ (span v U) : ℕ) ≤
      h * (A \ U).card := by
  classical
  let W := span v U
  let b := stdOrthonormalBasis ℝ Wᗮ
  let w := fun i : Fin (Module.finrank ℝ Wᗮ) => (b i : V)
  have hw : Orthonormal ℝ w := by
    rw [orthonormal_iff_ite]
    intro i j
    exact (orthonormal_iff_ite.mp b.orthonormal) i j
  have hzero (i : Fin (Module.finrank ℝ Wᗮ)) (e : E) (he : e ∈ U) :
      inner ℝ (w i) (v e) = 0 :=
    Submodule.inner_left_of_mem_orthogonal (mem_span_self v he) (b i).2
  have hlow' (i : Fin (Module.finrank ℝ Wᗮ)) :
      c ≤ ∑ e ∈ A \ U, (inner ℝ (w i) (v e)) ^ 2 := by
    have hi := hlow (w i)
    rw [hw.norm_eq_one, one_pow, mul_one] at hi
    have heq : ∑ e ∈ A \ U, (inner ℝ (w i) (v e)) ^ 2 =
        ∑ e ∈ A, (inner ℝ (w i) (v e)) ^ 2 := by
      apply Finset.sum_subset Finset.sdiff_subset
      intro e he hne
      have heU : e ∈ U := by simpa [he] using hne
      simp [hzero i e heU]
    rwa [heq]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i hi => hlow' i)
  have hsb : (∑ i : Fin (Module.finrank ℝ Wᗮ), ∑ e ∈ A \ U,
      (inner ℝ (w i) (v e)) ^ 2) ≤ ∑ e ∈ A \ U, h := by
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro e he
    have hb := hw.sum_inner_products_le (s := Finset.univ) (v e)
    simp only [Real.norm_eq_abs, sq_abs] at hb
    exact hb.trans (hn e (Finset.mem_sdiff.mp he).1)
  have ht := hs.trans hsb
  have hdim := W.finrank_add_finrank_orthogonal
  have heq : Module.finrank ℝ Wᗮ = Module.finrank ℝ V - Module.finrank ℝ W := by omega
  simpa [heq, mul_comm, W] using ht

omit [Fintype E] in
lemma lower_frame_span (v : E → V) (A : Finset E) {c h : ℝ} (hc : 0 < c)
    (hn : ∀ e ∈ A, ‖v e‖ ^ 2 ≤ h)
    (hlow : ∀ x : V, c * ‖x‖ ^ 2 ≤ ∑ e ∈ A, (inner ℝ x (v e)) ^ 2) :
    span v A = ⊤ := by
  have hb := projected_trace_bound v A A (Subset.refl _) hn hlow
  simp only [Finset.sdiff_self, Finset.card_empty, Nat.cast_zero, mul_zero] at hb
  have hzero : (Module.finrank ℝ V - Module.finrank ℝ (span v A) : ℕ) = 0 := by
    have hh : ((Module.finrank ℝ V - Module.finrank ℝ (span v A) : ℕ) : ℝ) ≤ 0 :=
      by nlinarith
    exact_mod_cast (le_antisymm hh (Nat.cast_nonneg _))
  apply Submodule.eq_top_of_finrank_eq
  have hle := (span v A).finrank_le
  omega

theorem projected_trace_base_packing (v : E → V) (A : Finset E)
    {r : ℕ} {c h : ℝ} (hc : 0 < c) (hh : 0 < h) (hr : (r : ℝ) * h ≤ c)
    (hn : ∀ e ∈ A, ‖v e‖ ^ 2 ≤ h)
    (hlow : ∀ x : V, c * ‖x‖ ^ 2 ≤ ∑ e ∈ A, (inner ℝ x (v e)) ^ 2) :
    ∃ F : Fin r → Finset E, Valid v F ∧
      ∀ i, F i ⊆ A ∧ span v (F i) = ⊤ := by
  have htop := lower_frame_span v A hc hn hlow
  have hp : ∀ U : Finset E, U ⊆ A →
      Fintype.card (Fin r) * Module.finrank ℝ (span v A) ≤
        (A \ U).card + Fintype.card (Fin r) * Module.finrank ℝ (span v U) := by
    intro U hU
    have ht := projected_trace_bound v A U hU hn hlow
    have hdim := (span v U).finrank_le
    have hdiff : (r : ℝ) * (Module.finrank ℝ V - Module.finrank ℝ (span v U) : ℕ) ≤
        (A \ U).card := by
      have h₁ := mul_le_mul_of_nonneg_right hr
        (Nat.cast_nonneg (Module.finrank ℝ V - Module.finrank ℝ (span v U)))
      have h₂ : h * ((r : ℝ) * (Module.finrank ℝ V - Module.finrank ℝ (span v U) : ℕ)) ≤
          h * (A \ U).card := by nlinarith [h₁.trans ht]
      exact (mul_le_mul_iff_right₀ hh).mp h₂
    have hdiffN : r * (Module.finrank ℝ V - Module.finrank ℝ (span v U)) ≤
        (A \ U).card := by exact_mod_cast hdiff
    rw [htop, finrank_top, Fintype.card_fin]
    have heq : Module.finrank ℝ V =
        (Module.finrank ℝ V - Module.finrank ℝ (span v U)) + Module.finrank ℝ (span v U) := by omega
    rw [heq, Nat.mul_add]
    exact Nat.add_le_add_right hdiffN _
  obtain ⟨F, hF, hs⟩ := vector_base_packing_on v A hp
  exact ⟨F, hF, fun i => ⟨(hs i).1, (hs i).2.trans htop⟩⟩

end
end StrongThinTree.Packing

namespace StrongThinTree.Packing
noncomputable section
variable {E : Type uE4} {V : Type uV2} {W : Type uW} [Fintype E] [DecidableEq E]
  [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]

omit [Fintype E] [DecidableEq E] [FiniteDimensional ℝ V] in
lemma span_smul (v : E → V) (s : E → ℝ) (hs : ∀ e, s e ≠ 0) (U : Finset E) :
    span (fun e => s e • v e) U = span v U := by
  apply le_antisymm
  · apply (span_le_iff _).mpr
    intro e he
    exact Submodule.smul_mem _ _ (mem_span_self v he)
  · apply (span_le_iff _).mpr
    intro e he
    have h := Submodule.smul_mem (span (fun e => s e • v e) U) (s e)⁻¹
      (mem_span_self (fun e => s e • v e) he)
    simpa only [smul_smul, inv_mul_cancel₀ (hs e), one_smul] using h

omit [Fintype E] [DecidableEq E] [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
lemma span_map (v : E → V) (L : V →ₗ[ℝ] W) (U : Finset E) :
    span (fun e => L (v e)) U = (span v U).map L := by
  rw [span, Submodule.map_span, ← Set.image_image]

omit [Fintype E] [DecidableEq E] [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
lemma rank_injective_map (v : E → V) (L : V →ₗ[ℝ] W)
    (hL : Function.Injective L) (U : Finset E) :
    Module.finrank ℝ (span (fun e => L (v e)) U) = Module.finrank ℝ (span v U) := by
  rw [span_map]
  exact (Submodule.equivMapOfInjective L hL (span v U)).finrank_eq.symm

end
end StrongThinTree.Packing

namespace StrongThinTree.MultiGraph
noncomputable section
open Matrix StrongThinTree.Packing
variable {n m : ℕ} (G : StrongThinTree.MultiGraph n m)

lemma represented_rank (L : zeroSumSpace n ≃ₗ[ℝ] (Fin (n-1) → ℝ))
    (s : Fin m → ℝ) (hs : ∀ e, s e ≠ 0) (U : Finset (Fin m)) :
    Module.finrank ℝ (Packing.span
      (fun e => s e • L ⟨G.incidence e, G.incidence_zeroSum e⟩) U) =
      Module.finrank ℝ (G.edgeSpan U) := by
  rw [Packing.span_smul _ s hs]
  change Module.finrank ℝ (Packing.span
    (fun e => L.toLinearMap (⟨G.incidence e, G.incidence_zeroSum e⟩ : zeroSumSpace n)) U) = _
  rw [Packing.rank_injective_map _ L.toLinearMap L.injective]
  symm
  exact Packing.rank_injective_map
    (fun e => (⟨G.incidence e, G.incidence_zeroSum e⟩ : zeroSumSpace n))
    (zeroSumSpace n).subtype Subtype.val_injective U

theorem represented_frame_treePackable (hn : 2 ≤ n)
    (L : zeroSumSpace n ≃ₗ[ℝ] (Fin (n-1) → ℝ))
    (s : Fin m → ℝ) (hs : ∀ e, 0 < s e) (A : Finset (Fin m))
    {r : ℕ} {c h : ℝ} (hc : 0 < c) (hh : 0 < h) (hr : (r : ℝ) * h ≤ c)
    (hnorm : ∀ e ∈ A, let z := s e • L ⟨G.incidence e, G.incidence_zeroSum e⟩
      z ⬝ᵥ z ≤ h)
    (hlow : ∀ x : Fin (n-1) → ℝ, c * (x ⬝ᵥ x) ≤
      ∑ e ∈ A, (x ⬝ᵥ (s e • L ⟨G.incidence e, G.incidence_zeroSum e⟩)) ^ 2) :
    G.TreePackable A r := by
  classical
  let z := fun e => s e • L ⟨G.incidence e, G.incidence_zeroSum e⟩
  let J := (WithLp.linearEquiv 2 ℝ (Fin (n-1) → ℝ)).symm
  let v := fun e => J (z e)
  have hnorm' : ∀ e ∈ A, ‖v e‖ ^ 2 ≤ h := by
    intro e he
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa [v, J, z, dotProduct, pow_two] using hnorm e he
  have hlow' : ∀ x : EuclideanSpace ℝ (Fin (n-1)),
      c * ‖x‖ ^ 2 ≤ ∑ e ∈ A, (inner ℝ x (v e)) ^ 2 := by
    intro x
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa [EuclideanSpace.inner_eq_star_dotProduct,
      v, J, z, dotProduct, pow_two, mul_comm] using hlow x.ofLp
  have hrank (U : Finset (Fin m)) :
      Module.finrank ℝ (Packing.span v U) = Module.finrank ℝ (G.edgeSpan U) := by
    change Module.finrank ℝ (Packing.span (fun e => J.toLinearMap (z e)) U) = _
    rw [Packing.rank_injective_map z J.toLinearMap J.injective]
    exact G.represented_rank L s (fun e => ne_of_gt (hs e)) U
  have htop := Packing.lower_frame_span v A hc hnorm' hlow'
  have hfull : Module.finrank ℝ (G.edgeSpan A) = n-1 := by
    rw [← hrank, htop, finrank_top]
    simp
  obtain ⟨F, hF, hFA⟩ := Packing.projected_trace_base_packing v A hc hh hr hnorm' hlow'
  refine ⟨F, ?_, hF.2⟩
  intro i
  refine ⟨(hFA i).1, (G.spanningTree_iff_independent (F i)).mpr ⟨?_, ?_⟩⟩
  · have hdim : Module.finrank ℝ (G.edgeSpan (F i)) = n-1 := by
      rw [← hrank, (hFA i).2, finrank_top]
      simp
    apply G.connected_of_componentCount_eq_one
    have hcomp := G.incidence_rank (F i)
    have hpos := G.componentCount_pos (by omega) (F i)
    omega
  · apply linearIndependent_iff_card_eq_finrank_span.mpr
    have heq : Set.range (fun e : (F i : Set (Fin m)) => G.incidence e) =
        G.incidence '' (F i : Set (Fin m)) := by ext x; simp
    change Fintype.card ↥(F i : Set (Fin m)) = Module.finrank ℝ (Submodule.span ℝ _)
    rw [heq]
    simpa [← hrank] using (Packing.indep_rank v (hF.1 i)).symm

end
end StrongThinTree.MultiGraph

namespace StrongThinTree.MultiGraph
noncomputable section
open Matrix
variable {n m : ℕ} (G : StrongThinTree.MultiGraph n m)

theorem projected_trace_treePackable (hn : 2 ≤ n) {q : ℕ} (hq : 0 < q)
    {ρ c : ℝ} (hρ : 0 < ρ) (hc : 0 < c)
    (L : zeroSumSpace n ≃ₗ[ℝ] (Fin (n-1) → ℝ)) (s : Fin m → ℝ)
    (hs : ∀ e, 0 < s e) (A B : Finset (Fin m)) (hAB : A ⊆ B)
    (hnorm : ∀ e ∈ B, let z := s e • L ⟨G.incidence e, G.incidence_zeroSum e⟩
      z ⬝ᵥ z ≤ (1 + ρ) / q)
    (hlow : (∑ e ∈ A,
       vecMulVec (s e • L ⟨G.incidence e, G.incidence_zeroSum e⟩)
         (s e • L ⟨G.incidence e, G.incidence_zeroSum e⟩) -
       c • (1 : Matrix (Fin (n-1)) (Fin (n-1)) ℝ)).PosSemidef) :
    G.TreePackable A ⌊c * q / (1 + ρ)⌋₊ := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hp : 0 < 1 + ρ := by linarith
  apply G.represented_frame_treePackable hn L s hs A hc (div_pos hp hq')
  · have hf := Nat.floor_le (le_of_lt (div_pos (mul_pos hc hq') hp))
    apply (le_div_iff₀ (div_pos hp hq')).symm.mpr
    convert hf using 1 ; field_simp
  · intro e he
    exact hnorm e (hAB he)
  · intro x
    have ht := hlow.dotProduct_mulVec_nonneg x
    simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
      Matrix.one_mulVec, dotProduct_smul, Matrix.sum_mulVec, dotProduct_sum] at ht
    suffices heq : (∑ e ∈ A,
        x ⬝ᵥ (vecMulVec (s e • L ⟨G.incidence e, G.incidence_zeroSum e⟩)
          (s e • L ⟨G.incidence e, G.incidence_zeroSum e⟩) *ᵥ x)) =
        ∑ e ∈ A, (x ⬝ᵥ (s e • L ⟨G.incidence e, G.incidence_zeroSum e⟩)) ^ 2 by
      rw [heq] at ht
      simp only [smul_eq_mul] at ht
      linarith
    apply Finset.sum_congr rfl
    intro e he
    rw [Matrix.vecMulVec_mulVec]
    simp [dotProduct, Finset.mul_sum, pow_two, mul_comm, mul_left_comm]

end
end StrongThinTree.MultiGraph

end

end OAI
