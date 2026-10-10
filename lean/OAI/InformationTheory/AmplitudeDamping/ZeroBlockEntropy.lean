import OAI.InformationTheory.AmplitudeDamping.ScalarDeficit

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25 u_26 u_27 u_28 u_29 u_30 u_31 u_32

noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped Matrix.Norms.Elementwise ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder
open scoped BigOperators Topology
open Filter Set
open scoped BigOperators ComplexOrder MatrixOrder Topology
open scoped BigOperators ComplexOrder

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

theorem trace_re_eq_sum_eigenvalues {ω : Type u_1} [Fintype ω] [DecidableEq ω]
    {T : Matrix ω ω ℂ} (hT : T.PosSemidef) :
    T.trace.re = ∑ i, hT.isHermitian.eigenvalues i := by
  rw [hT.isHermitian.trace_eq_sum_eigenvalues]; simp

theorem logDetShift_inv_eq_sum {ω : Type u_2} [Fintype ω] [DecidableEq ω]
    {T : Matrix ω ω ℂ} (hT : T.PosSemidef) {t : ℝ} (ht : 0 < t) :
    logDetShift t⁻¹ T = ∑ i, Real.log (1+hT.isHermitian.eigenvalues i/t) := by
  rw [logDetShift_eq_sum hT (inv_nonneg.mpr ht.le)]
  simp only [div_eq_mul_inv, mul_comm]

theorem entropy_three_sub_le_deficits {ι : Type u_3} {κ : Type u_4} {μ : Type u_5} {ν : Type u_6} {τ : Type u_7}
    [Fintype ι] [Fintype κ] [Fintype μ] [Fintype ν] [Fintype τ]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq μ] [DecidableEq ν]
    {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ} {C : Matrix μ μ ℂ} {D : Matrix ν ν ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hC : C.PosSemidef) (hD : D.PosSemidef)
    (x y z : τ → ℝ) (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) (hz : ∀ i, 0 ≤ z i)
    (htrace : A.trace.re+B.trace.re+C.trace.re-D.trace.re = 0)
    (hlog : ∀ r : ℝ, 0 < r → logDetShift r A+logDetShift r B+logDetShift r C-logDetShift r D ≤
      ∑ i, deficitLog (x i) (y i) (z i) r⁻¹) :
    entropy A+entropy B+entropy C-entropy D ≤ ∑ i, scalarDeficit (x i) (y i) (z i) := by
  classical
  have hh := entropy_sum_le_of_log_sum_le
    (Sum.elim (Sum.elim (fun _ : ι ↦ (1 : ℝ))
      (Sum.elim (fun _ : κ ↦ (1 : ℝ)) (Sum.elim (fun _ : μ ↦ (1 : ℝ)) (fun _ : ν ↦ (-1 : ℝ)))))
      (fun i : τ × Fin 5 ↦ -deficitSigns i.2))
    (Sum.elim (Sum.elim hA.isHermitian.eigenvalues
      (Sum.elim hB.isHermitian.eigenvalues (Sum.elim hC.isHermitian.eigenvalues hD.isHermitian.eigenvalues)))
      (fun i : τ × Fin 5 ↦ deficitSpectrum (x i.1) (y i.1) (z i.1) i.2)) ?_ ?_ ?_
  · simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.sum_prod_type,
      one_mul, neg_mul, Finset.sum_neg_distrib,
      ← entropy_eq_sum hA.isHermitian, ← entropy_eq_sum hB.isHermitian,
      ← entropy_eq_sum hC.isHermitian, ← entropy_eq_sum hD.isHermitian, deficitSpectrum_entropy] at hh
    linarith
  · intro i
    rcases i with i | i
    · rcases i with i | i
      · exact hA.eigenvalues_nonneg i
      · rcases i with i | i
        · exact hB.eigenvalues_nonneg i
        · rcases i with i | i
          · exact hC.eigenvalues_nonneg i
          · exact hD.eigenvalues_nonneg i
    · exact deficitSpectrum_nonneg (hx i.1) (hy i.1) (hz i.1) i.2
  · simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.sum_prod_type,
      one_mul, neg_mul, Finset.sum_neg_distrib,
      ← trace_re_eq_sum_eigenvalues hA, ← trace_re_eq_sum_eigenvalues hB, ← trace_re_eq_sum_eigenvalues hC, ← trace_re_eq_sum_eigenvalues hD,
      deficitSpectrum_trace (hx _) (hy _) (hz _), Finset.sum_const_zero, neg_zero, add_zero]
    linarith
  · intro t ht'
    have h := hlog t⁻¹ (inv_pos.mpr ht')
    simp only [inv_inv] at h
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.sum_prod_type,
      one_mul, neg_mul, Finset.sum_neg_distrib,
      deficitSpectrum_log (hx _) (hy _) (hz _) ht', ← logDetShift_inv_eq_sum hA ht', ← logDetShift_inv_eq_sum hB ht', ← logDetShift_inv_eq_sum hC ht', ← logDetShift_inv_eq_sum hD ht']
    linarith

theorem deficitLog_inv {r : ℝ} (hr : 0 < r) (x : ℝ) {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z) :
    deficitLog x y z r⁻¹ = Real.log (1+r*x) -
      Real.log (1+r*x/((1+r*y)*(1+r*z))) := by
  have hdy : 1+r*y ≠ 0 := ne_of_gt (by positivity)
  have hdz : 1+r*z ≠ 0 := ne_of_gt (by positivity)
  have hiy : r⁻¹+y ≠ 0 := ne_of_gt (by positivity)
  have hiz : r⁻¹+z ≠ 0 := ne_of_gt (by positivity)
  have he : r⁻¹*x/((r⁻¹+y)*(r⁻¹+z)) = r*x/((1+r*y)*(1+r*z)) := by
    field_simp
  simp only [deficitLog, div_inv_eq_mul, mul_comm x r, he]

variable {ι : Type u_8} {μ : Type u_9} {ν : Type u_10} [Fintype ι] [Fintype μ] [Fintype ν]
  [DecidableEq ι] [DecidableEq μ] [DecidableEq ν]

omit [Fintype ι] [DecidableEq ι] in
theorem posSemidef_diag_re {P : Matrix ι ι ℂ} (hP : P.PosSemidef) (i : ι) :
    ((P i i).re : ℂ) = P i i := by
  have hi := (Complex.nonneg_iff.mp (hP.diag_nonneg (i := i))).2
  apply Complex.ext <;> simp [hi]

theorem gram_diagonal_real (s : ι → ℝ) :
    gram (Matrix.diagonal (fun i ↦ (s i : ℂ))) = Matrix.diagonal (fun i ↦ (((s i)^2 : ℝ) : ℂ)) := by
  simp only [gram, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  simp [pow_two]

omit [DecidableEq μ] in
theorem zeroBlock_diagonal_log_bound (s : ι → ℝ) (B : Matrix ι μ ℂ) (C : Matrix ν ι ℂ)
    {r : ℝ} (hr : 0 < r) :
    let A := Matrix.diagonal (fun i ↦ (s i : ℂ))
    logDetShift r (gram A)+logDetShift r (gram B)+logDetShift r (gram C)-
      logDetShift r (gram (zeroBlock A B C)) ≤
    ∑ i, deficitLog ((s i)^2) ((gram B i i).re) ((Cᴴ*C) i i).re r⁻¹ := by
  dsimp only
  have hB : (gram B).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose B
  have hC := Matrix.posSemidef_conjTranspose_mul_self C
  have hy (i : ι) : 0 ≤ (gram B i i).re := (Complex.nonneg_iff.mp (hB.diag_nonneg (i := i))).1
  have hz (i : ι) : 0 ≤ ((Cᴴ*C) i i).re := (Complex.nonneg_iff.mp (hC.diag_nonneg (i := i))).1
  have hD : (1+r • gram B).PosDef := Matrix.PosDef.one.add_posSemidef (hB.smul hr.le)
  have hE : (1+r • (Cᴴ*C)).PosDef := Matrix.PosDef.one.add_posSemidef (hC.smul hr.le)
  have hdiag {P : Matrix ι ι ℂ} (hP : P.PosSemidef) :
      Matrix.diagonal (fun i ↦ (1+r • P) i i) =
      Matrix.diagonal (fun i ↦ ((1+r*(P i i).re : ℝ) : ℂ)) := by
    congr 1
    ext i
    simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.smul_apply, Complex.ofReal_add,
      Complex.ofReal_one, Complex.ofReal_mul, posSemidef_diag_re hP, Complex.real_smul]
  have hZ : Real.sqrt r • Matrix.diagonal (fun i ↦ (s i : ℂ)) =
      Matrix.diagonal (fun i ↦ ((Real.sqrt r*s i : ℝ) : ℂ)) := by
    rw [← Matrix.diagonal_smul]
    congr 1
    ext i
    simp [Complex.real_smul]
  have hp := blockLogDet_diagonal_le (fun i ↦ ((Real.sqrt r*s i : ℝ) : ℂ)) hD hE
  rw [hdiag hB, hdiag hC, blockLogDet_diagonal_real] at hp
  · rw [logDetShift_zeroBlock hr.le, hZ, gram_diagonal_real,
      logDetShift_diagonal_real _ _ hr.le (fun i ↦ sq_nonneg (s i))]
    have he (i : ι) : (Real.sqrt r*s i)^2 = r*(s i)^2 := by
      rw [mul_pow, Real.sq_sqrt hr.le]
    simp only [he] at hp
    simp only [deficitLog_inv hr _ (hy _) (hz _), Finset.sum_sub_distrib]
    linarith
  · intro i; exact add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hr.le (hy i))
  · intro i; exact add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hr.le (hz i))

omit [DecidableEq μ] in
theorem zeroBlock_diagonal_entropy_bound (s : ι → ℝ) (B : Matrix ι μ ℂ) (C : Matrix ν ι ℂ) :
    let A := Matrix.diagonal (fun i ↦ (s i : ℂ))
    entropy (gram A)+entropy (gram B)+entropy (gram C)-entropy (gram (zeroBlock A B C)) ≤
      scalarDeficit (mass A) (mass B) (mass C) := by
  dsimp only
  let A := Matrix.diagonal (fun i ↦ (s i : ℂ))
  have hx (i : ι) : 0 ≤ (s i)^2 := sq_nonneg _
  have hy (i : ι) : 0 ≤ (gram B i i).re :=
    (Complex.nonneg_iff.mp ((Matrix.posSemidef_self_mul_conjTranspose B).diag_nonneg (i := i))).1
  have hz (i : ι) : 0 ≤ ((Cᴴ*C) i i).re :=
    (Complex.nonneg_iff.mp ((Matrix.posSemidef_conjTranspose_mul_self C).diag_nonneg (i := i))).1
  have hh := entropy_three_sub_le_deficits (Matrix.posSemidef_self_mul_conjTranspose A)
    (Matrix.posSemidef_self_mul_conjTranspose B) (Matrix.posSemidef_self_mul_conjTranspose C)
    (Matrix.posSemidef_self_mul_conjTranspose (zeroBlock A B C))
    (fun i ↦ (s i)^2) (fun i ↦ (gram B i i).re) (fun i ↦ ((Cᴴ*C) i i).re) hx hy hz
    (by change mass A+mass B+mass C-mass (zeroBlock A B C) = 0; rw [mass_zeroBlock]; ring)
    (fun r hr ↦ zeroBlock_diagonal_log_bound s B C hr)
  have hs := scalarDeficit_sum_le Finset.univ (fun i ↦ (s i)^2)
    (fun i ↦ (gram B i i).re) (fun i ↦ ((Cᴴ*C) i i).re)
    (fun i _ ↦ hx i) (fun i _ ↦ hy i) (fun i _ ↦ hz i)
  have hxsum : ∑ i, (s i)^2 = mass A := by
    simp [mass, A, gram_diagonal_real, Matrix.trace_diagonal, pow_two, Complex.mul_re]
  have hysum : ∑ i, (gram B i i).re = mass B := by simp [mass, Matrix.trace, Matrix.diag]
  have hzsum : ∑ i, ((Cᴴ*C) i i).re = mass C := by
    rw [mass, gram, Matrix.trace_mul_comm]
    simp [Matrix.trace, Matrix.diag]
  rw [hxsum, hysum, hzsum] at hs
  exact hh.trans hs

end GAD
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_11} {κ : Type u_12} {μ : Type u_13} {ν : Type u_14} [Fintype ι] [Fintype κ] [Fintype μ] [Fintype ν]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq μ] [DecidableEq ν]

omit [Fintype μ] [DecidableEq ν] [DecidableEq ι] [DecidableEq μ] in
theorem gram_biisometry (R : Matrix μ ι ℂ) (A : Matrix ι κ ℂ) (T : Matrix κ ν ℂ)
    (hT : T*Tᴴ = 1) : gram (R*A*T) = R*gram A*Rᴴ := by
  simp only [gram, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc T Tᴴ, hT, Matrix.one_mul]

omit [DecidableEq μ] [DecidableEq ν] in
theorem mass_biisometry (R : Matrix μ ι ℂ) (A : Matrix ι κ ℂ) (T : Matrix κ ν ℂ)
    (hR : Rᴴ*R = 1) (hT : T*Tᴴ = 1) : mass (R*A*T) = mass A := by
  unfold mass
  rw [gram_biisometry R A T hT, Matrix.trace_mul_cycle]
  simp only [hR, Matrix.one_mul]

omit [DecidableEq ν] in
theorem entropy_gram_biisometry (R : Matrix μ ι ℂ) (A : Matrix ι κ ℂ) (T : Matrix κ ν ℂ)
    (hR : Rᴴ*R = 1) (hT : T*Tᴴ = 1) : entropy (gram (R*A*T)) = entropy (gram A) := by
  rw [gram_biisometry R A T hT]
  have he : R*gram A*Rᴴ = gram (R*A) := by
    simp only [gram, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [he]
  change entropy ((R*A)*(R*A)ᴴ) = _
  rw [entropy_mul_conjTranspose]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Rᴴ R,
    hR, Matrix.one_mul]
  exact (entropy_mul_conjTranspose A).symm

omit [DecidableEq ι] [DecidableEq κ] [DecidableEq μ] [DecidableEq ν] in
theorem zeroBlock_bimultiply {ι' : Type u_15} {κ' : Type u_16} {μ' : Type u_17} {ν' : Type u_18}
    [Fintype ι'] [Fintype κ'] [Fintype μ'] [Fintype ν']
    (R : Matrix ι' ι ℂ) (Q : Matrix ν' ν ℂ) (S : Matrix κ κ' ℂ) (T : Matrix μ μ' ℂ)
    (A : Matrix ι κ ℂ) (B : Matrix ι μ ℂ) (C : Matrix ν κ ℂ) :
    zeroBlock (R*A*S) (R*B*T) (Q*C*S) =
      Matrix.fromBlocks R 0 0 Q * zeroBlock A B C * Matrix.fromBlocks S 0 0 T := by
  simp [zeroBlock, Matrix.fromBlocks_multiply]

omit [Fintype ι] [Fintype κ] [DecidableEq μ] [DecidableEq ν] in
theorem isometry_fromBlocks (R : Matrix μ ι ℂ) (Q : Matrix ν κ ℂ)
    (hR : Rᴴ*R = 1) (hQ : Qᴴ*Q = 1) :
    (Matrix.fromBlocks R 0 0 Q)ᴴ * Matrix.fromBlocks R 0 0 Q = 1 := by
  simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hR, hQ]

omit [Fintype μ] [Fintype ν] [DecidableEq κ] [DecidableEq ι] in
theorem coisometry_fromBlocks (R : Matrix μ ι ℂ) (Q : Matrix ν κ ℂ)
    (hR : R*Rᴴ = 1) (hQ : Q*Qᴴ = 1) :
    Matrix.fromBlocks R 0 0 Q * (Matrix.fromBlocks R 0 0 Q)ᴴ = 1 := by
  simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hR, hQ]

end GAD
open scoped BigOperators ComplexOrder
open Matrix
namespace GAD
variable {ι : Type u_19} [Fintype ι] [DecidableEq ι]

/-- Singular-value decomposition in the same finite coordinate type, including
singular matrices. The zero singular directions are completed orthonormally. -/
theorem exists_unitary_singular_decomposition (A : Matrix ι ι ℂ) :
    ∃ (U V : Matrix.unitaryGroup ι ℂ) (s : ι → ℝ),
      (∀ i, 0 ≤ s i) ∧ A = (U : Matrix ι ι ℂ) * Matrix.diagonal (fun i ↦ (s i : ℂ)) * star V := by
  let hP := Matrix.posSemidef_conjTranspose_mul_self A
  let V := hP.isHermitian.eigenvectorUnitary
  let l := hP.isHermitian.eigenvalues
  let B := A * (V : Matrix ι ι ℂ)
  have hGram : Bᴴ * B = Matrix.diagonal (fun i ↦ (l i : ℂ)) := by
    simpa only [B, Matrix.conjTranspose_mul, ← Matrix.mul_assoc,
      Matrix.star_eq_conjTranspose, V, l, Unitary.conjStarAlgAut_star_apply,
      Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using hP.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  let w (i : ι) : EuclideanSpace ℂ ι := WithLp.toLp 2 (fun k ↦ B k i)
  have hw (i j : ι) : inner ℂ (w i) (w j) = (Matrix.diagonal (fun i ↦ (l i : ℂ))) i j := by
    rw [← hGram]
    simp [w, EuclideanSpace.inner_eq_star_dotProduct, Matrix.mul_apply,
      Matrix.conjTranspose_apply, dotProduct, mul_comm]
  let s (i : ι) := Real.sqrt (l i)
  have hs (i : ι) : 0 ≤ s i := Real.sqrt_nonneg _
  have hsq (i : ι) : s i * s i = l i := Real.mul_self_sqrt (hP.eigenvalues_nonneg i)
  let v (i : ι) : EuclideanSpace ℂ ι := ((s i : ℂ)⁻¹) • w i
  have hv : Orthonormal ℂ (Set.domRestrict {i | s i ≠ 0} v) := by
    rw [orthonormal_iff_ite]
    intro i j
    simp only [Set.domRestrict_apply, v, inner_smul_left, inner_smul_right, hw,
      map_inv₀, Complex.conj_ofReal]
    by_cases hij : i = j
    · subst j
      simp only [ite_true, Matrix.diagonal_apply_eq]
      have hne : (s i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr i.property
      have hsq' : (s i : ℂ) * (s i : ℂ) = (l i : ℂ) := by exact_mod_cast hsq i
      rw [← hsq']
      field_simp
    · have hij' : (i : ι) ≠ (j : ι) := fun h ↦ hij (Subtype.ext h)
      simp [Matrix.diagonal_apply_ne _ hij', hij]
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
    (by simp : Module.finrank ℂ (EuclideanSpace ℂ ι) = Fintype.card ι)
  let U : Matrix.unitaryGroup ι ℂ :=
    ⟨(EuclideanSpace.basisFun ι ℂ).toBasis.toMatrix b.toBasis,
      (EuclideanSpace.basisFun ι ℂ).toMatrix_orthonormalBasis_mem_unitary b⟩
  have hU (i j : ι) : U i j = b j i := rfl
  have hcol (i : ι) : w i = (s i : ℂ) • b i := by
    by_cases hi : s i = 0
    · have hwi : inner ℂ (w i) (w i) = 0 := by
        rw [hw, Matrix.diagonal_apply_eq, ← hsq]
        simp [hi]
      rw [inner_self_eq_zero] at hwi
      simp [hi, hwi]
    · rw [hb i hi]
      simp only [v, smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hi), one_smul]
  have hB : B = (U : Matrix ι ι ℂ) * Matrix.diagonal (fun i ↦ (s i : ℂ)) := by
    ext k i
    have h := congrArg (fun x : EuclideanSpace ℂ ι ↦ x k) (hcol i)
    simpa [w, Matrix.mul_diagonal, hU, mul_comm] using h
  refine ⟨U, V, s, hs, ?_⟩
  rw [← hB]
  simp only [B, Matrix.mul_assoc, Unitary.coe_mul_star_self, Matrix.mul_one]
end GAD
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

section
variable {ι : Type u_20} {μ : Type u_21} {ν : Type u_22} [Fintype ι] [Fintype μ] [Fintype ν]
  [DecidableEq ι] [DecidableEq μ] [DecidableEq ν]

theorem zeroBlock_square_entropy_bound (A : Matrix ι ι ℂ) (B : Matrix ι μ ℂ) (C : Matrix ν ι ℂ) :
    entropy (gram A)+entropy (gram B)+entropy (gram C)-entropy (gram (zeroBlock A B C)) ≤
      scalarDeficit (mass A) (mass B) (mass C) := by
  obtain ⟨U,V,s,_,hA⟩ := exists_unitary_singular_decomposition A
  let R : Matrix ι ι ℂ := (star U : Matrix ι ι ℂ)
  let T : Matrix ι ι ℂ := V
  have hR : Rᴴ*R = 1 := by simp [R, ← Matrix.star_eq_conjTranspose]
  have hT : T*Tᴴ = 1 := by simp [T, ← Matrix.star_eq_conjTranspose]
  have hUR : R*(U : Matrix ι ι ℂ) = 1 := by simp [R]
  have hVT : (star V : Matrix ι ι ℂ)*T = 1 := by simp [T]
  have hdiag : R*A*T = Matrix.diagonal (fun i ↦ (s i : ℂ)) := by
    rw [hA]
    simp only [Unitary.coe_star, Matrix.mul_assoc, ← Matrix.mul_assoc R (U : Matrix ι ι ℂ), hUR, Matrix.one_mul,
      hVT, Matrix.mul_one]
  have hb := zeroBlock_diagonal_entropy_bound s (R*B) (C*T)
  dsimp only at hb
  rw [← hdiag] at hb
  have hm := entropy_gram_biisometry (Matrix.fromBlocks R 0 0 (1 : Matrix ν ν ℂ))
    (zeroBlock A B C) (Matrix.fromBlocks T 0 0 (1 : Matrix μ μ ℂ))
    (isometry_fromBlocks R 1 hR (by simp)) (coisometry_fromBlocks T 1 hT (by simp))
  rw [← zeroBlock_bimultiply] at hm
  simp only [Matrix.mul_one, Matrix.one_mul] at hm
  have hB := entropy_gram_biisometry R B (1 : Matrix μ μ ℂ) hR (by simp)
  have hC := entropy_gram_biisometry (1 : Matrix ν ν ℂ) C T (by simp) hT
  have hmB := mass_biisometry R B (1 : Matrix μ μ ℂ) hR (by simp)
  have hmC := mass_biisometry (1 : Matrix ν ν ℂ) C T (by simp) hT
  simp only [Matrix.mul_one, Matrix.one_mul] at hB hC hmB hmC
  simpa only [entropy_gram_biisometry R A T hR hT, hB, hC, hm,
    mass_biisometry R A T hR hT, hmB, hmC] using hb

end

section
variable {ι : Type u_23} {κ : Type u_24} {μ : Type u_25} {ν : Type u_26} [Fintype ι] [Fintype κ] [Fintype μ] [Fintype ν]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq μ] [DecidableEq ν]

theorem zeroBlock_entropy_bound (A : Matrix ι κ ℂ) (B : Matrix ι μ ℂ) (C : Matrix ν κ ℂ) :
    entropy (gram A)+entropy (gram B)+entropy (gram C)-entropy (gram (zeroBlock A B C)) ≤
      scalarDeficit (mass A) (mass B) (mass C) := by
  let R : Matrix (ι ⊕ κ) ι ℂ := Matrix.fromRows 1 0
  let T : Matrix κ (ι ⊕ κ) ℂ := Matrix.fromCols 0 1
  have hR : Rᴴ*R = 1 := by simp [R, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromRows]
  have hT : T*Tᴴ = 1 := by simp [T, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromCols_mul_fromRows]
  have hb := zeroBlock_square_entropy_bound (R*A*T) (R*B) (C*T)
  have hm := entropy_gram_biisometry (Matrix.fromBlocks R 0 0 (1 : Matrix ν ν ℂ))
    (zeroBlock A B C) (Matrix.fromBlocks T 0 0 (1 : Matrix μ μ ℂ))
    (isometry_fromBlocks R 1 hR (by simp)) (coisometry_fromBlocks T 1 hT (by simp))
  rw [← zeroBlock_bimultiply] at hm
  simp only [Matrix.mul_one, Matrix.one_mul] at hm
  have hB := entropy_gram_biisometry R B (1 : Matrix μ μ ℂ) hR (by simp)
  have hC := entropy_gram_biisometry (1 : Matrix ν ν ℂ) C T (by simp) hT
  have hmB := mass_biisometry R B (1 : Matrix μ μ ℂ) hR (by simp)
  have hmC := mass_biisometry (1 : Matrix ν ν ℂ) C T (by simp) hT
  simp only [Matrix.mul_one, Matrix.one_mul] at hB hC hmB hmC
  simpa only [entropy_gram_biisometry R A T hR hT, hB, hC, hm,
    mass_biisometry R A T hR hT, hmB, hmC] using hb

end

section
variable {ι : Type u_27} {κ : Type u_28} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem entropy_smul (a : ℝ) {P : Matrix ι ι ℂ} (hP : P.IsHermitian) :
    entropy (a • P) = a * entropy P + Real.negMulLog a * P.trace.re := by
  rw [entropy, ← cfc_comp_smul a Real.negMulLog P, trace_cfc_eq hP]
  simp only [smul_eq_mul, Complex.re_sum, Complex.ofReal_re,
    Real.negMulLog_mul, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    ← entropy_eq_sum hP]
  rw [hP.trace_eq_sum_eigenvalues]
  simp
  ring

omit [DecidableEq κ] in
theorem entropy_sqrt_smul {a : ℝ} (ha : 0 ≤ a) (X : Matrix ι κ ℂ) (hX : mass X = 1) :
    entropy (gram (Real.sqrt a • X)) = a * entropy (gram X) + Real.negMulLog a := by
  have hh : (gram X).IsHermitian := (Matrix.posSemidef_self_mul_conjTranspose X).isHermitian
  rw [gram_sqrt_smul ha, entropy_smul a hh]
  change a * entropy (gram X) + Real.negMulLog a * mass X = _
  rw [hX, mul_one]

omit [DecidableEq ι] [DecidableEq κ] in
theorem mass_sqrt_smul {a : ℝ} (ha : 0 ≤ a) (X : Matrix ι κ ℂ) :
    mass (Real.sqrt a • X) = a * mass X := by
  simp [mass, gram_sqrt_smul ha]

end

theorem scalarDeficit_normalized {a b c : ℝ} (h : a+b+c=1) :
    scalarDeficit a b c = Real.negMulLog a + Real.negMulLog b + Real.negMulLog c - g (b*c) := by
  have hl : blockLambdaMinus a b c = 1-blockLambdaPlus a b c := by
    unfold blockLambdaMinus blockLambdaPlus
    rw [h]; ring
  simp only [scalarDeficit, hl, g, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,
    blockLambdaPlus, h, one_pow, mul_assoc]
  ring

variable {ι : Type u_29} {κ : Type u_30} {μ : Type u_31} {ν : Type u_32} [Fintype ι] [Fintype κ] [Fintype μ] [Fintype ν]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq μ] [DecidableEq ν]

theorem zeroBlock_normalized (X : Matrix ι κ ℂ) (Y : Matrix ι μ ℂ) (Z : Matrix ν κ ℂ)
    (hX : mass X = 1) (hY : mass Y = 1) (hZ : mass Z = 1)
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a+b+c=1) :
    a*entropy (gram X)+b*entropy (gram Y)+c*entropy (gram Z)+g (b*c) ≤
      entropy (gram (zeroBlock (Real.sqrt a • X) (Real.sqrt b • Y) (Real.sqrt c • Z))) := by
  have hh := zeroBlock_entropy_bound (Real.sqrt a • X) (Real.sqrt b • Y) (Real.sqrt c • Z)
  rw [entropy_sqrt_smul ha X hX, entropy_sqrt_smul hb Y hY, entropy_sqrt_smul hc Z hZ,
    mass_sqrt_smul ha, mass_sqrt_smul hb, mass_sqrt_smul hc, hX, hY, hZ, mul_one,
    mul_one, mul_one, scalarDeficit_normalized h] at hh
  linarith

end GAD

end

end OAI
