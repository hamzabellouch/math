import Mathlib

namespace OAI

/-! Boundary Forms. -/

noncomputable section

open scoped InnerProductSpace Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

open MeasureTheory

namespace CrouzeixHilbert.Boundary

abbrev HS (k : ℕ) := EuclideanSpace ℂ (Fin k × Fin k)

def toHS {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) : HS k :=
  WithLp.toLp 2 fun ij => A ij.1 ij.2

def ofHS {k : ℕ} (v : HS k) : Matrix (Fin k) (Fin k) ℂ :=
  fun i j => v (i,j)

@[simp] theorem ofHS_toHS {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) :
    ofHS (toHS A) = A := rfl

@[simp] theorem toHS_ofHS {k : ℕ} (v : HS k) : toHS (ofHS v) = v := by
  ext ij
  rfl

theorem norm_toHS_sq {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) :
    ‖toHS A‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]
  rfl

theorem trace_conjTranspose_mul_re {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) :
    (Aᴴ * A).trace.re = ‖toHS A‖ ^ 2 := by
  rw [norm_toHS_sq]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply]

theorem trace_mul_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace.re := by
  obtain ⟨C, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  have h := (hA.mul_mul_conjTranspose_same C).trace_nonneg
  rw [Matrix.trace_mul_cycle] at h
  simpa only [Matrix.star_eq_conjTranspose, Matrix.trace_mul_comm A] using
    (Complex.nonneg_iff.mp h).1

theorem trace_fromBlocks {n m : Type*} [Fintype n] [Fintype m]
    (A : Matrix n n ℂ) (B : Matrix n m ℂ) (C : Matrix m n ℂ) (D : Matrix m m ℂ) :
    (Matrix.fromBlocks A B C D).trace = A.trace + D.trace := by
  simp [Matrix.trace, Matrix.diag, Fintype.sum_sum_type]

theorem block_posSemidef_norm_sq {k : ℕ}
    (p q r : Matrix (Fin k) (Fin k) ℂ)
    (h : (Matrix.fromBlocks p rᴴ r q).PosSemidef) :
    2 * ‖toHS r‖ ^ 2 ≤ ‖toHS p‖ ^ 2 + ‖toHS q‖ ^ 2 := by
  let J : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) ℂ :=
    Matrix.fromBlocks 1 0 0 (-1)
  have hp : pᴴ = p := (Matrix.isHermitian_fromBlocks_iff.mp h.isHermitian).1.eq
  have hq : qᴴ = q := (Matrix.isHermitian_fromBlocks_iff.mp h.isHermitian).2.2.2.eq
  have hh := trace_mul_nonneg h (h.conjTranspose_mul_mul_same J)
  have hJ : Jᴴ = J := by simp [J, Matrix.fromBlocks_conjTranspose]
  rw [hJ] at hh
  simp only [J, Matrix.fromBlocks_multiply, mul_one, one_mul, mul_zero, zero_mul,
    Matrix.mul_neg, Matrix.neg_mul, zero_add, add_zero, trace_fromBlocks,
    Matrix.trace_add, Matrix.trace_neg, Complex.add_re, Complex.neg_re] at hh
  have hr : (r * rᴴ).trace.re = ‖toHS r‖ ^ 2 := by
    rw [Matrix.trace_mul_comm, trace_conjTranspose_mul_re]
  have hpp := trace_conjTranspose_mul_re p
  have hqq := trace_conjTranspose_mul_re q
  rw [hp] at hpp
  rw [hq] at hqq
  rw [hpp, hqq] at hh
  rw [trace_conjTranspose_mul_re, hr] at hh
  linarith

theorem lp_norm_sq_eq_integral {α E : Type*} [MeasurableSpace α]
    {μ : Measure α} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : Lp E 2 μ) : ‖f‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq f, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

theorem lp_block_posSemidef_norm_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {k : ℕ} (p q r : Lp (HS k) 2 μ)
    (h : ∀ᵐ t ∂μ, (Matrix.fromBlocks (ofHS (p t))
      (ofHS (r t))ᴴ (ofHS (r t)) (ofHS (q t))).PosSemidef) :
    2 * ‖r‖ ^ 2 ≤ ‖p‖ ^ 2 + ‖q‖ ^ 2 := by
  have hi := integral_mono_ae (((Lp.memLp r).norm.integrable_sq).const_mul 2)
    (((Lp.memLp p).norm.integrable_sq).add ((Lp.memLp q).norm.integrable_sq))
    (h.mono fun t ht => by simpa only [toHS_ofHS, Pi.add_apply] using
      block_posSemidef_norm_sq (ofHS (p t)) (ofHS (q t)) (ofHS (r t)) ht)
  simpa only [Pi.add_apply, integral_const_mul, integral_add (Lp.memLp p).norm.integrable_sq
    (Lp.memLp q).norm.integrable_sq, ← lp_norm_sq_eq_integral] using hi

section Splitting

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

structure ThreeWaySplitting (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] where
  proj : Fin 3 → E →L[ℝ] E
  self_adjoint : ∀ i, ContinuousLinearMap.adjoint (proj i) = proj i
  comp : ∀ i j, (proj i).comp (proj j) = if i = j then proj i else 0
  total : proj 0 + proj 1 + proj 2 = ContinuousLinearMap.id ℝ E

namespace ThreeWaySplitting

variable (s : ThreeWaySplitting E)

@[simp] theorem proj_proj (i j : Fin 3) (x : E) :
    s.proj i (s.proj j x) = if i = j then s.proj i x else 0 := by
  have h := congrArg (fun f : E →L[ℝ] E => f x) (s.comp i j)
  by_cases hij : i = j
  · subst j
    simpa using h
  · simpa [hij] using h

theorem proj_orthogonal {i j : Fin 3} (hij : i ≠ j) (x y : E) :
    ⟪s.proj i x, s.proj j y⟫_ℝ = 0 := by
  rw [← s.self_adjoint i, ContinuousLinearMap.adjoint_inner_left,
    s.proj_proj, ite_eq_right hij, inner_zero_right]

@[simp] theorem total_apply (x : E) : s.proj 0 x + s.proj 1 x + s.proj 2 x = x := by
  simpa only [add_apply, ContinuousLinearMap.id_apply] using
    congrArg (fun f : E →L[ℝ] E => f x) s.total

theorem norm_sq_decomposition (x : E) :
    ‖x‖ ^ 2 = ‖s.proj 0 x‖ ^ 2 + ‖s.proj 1 x‖ ^ 2 + ‖s.proj 2 x‖ ^ 2 := by
  calc
    ‖x‖ ^ 2 = ‖s.proj 0 x + s.proj 1 x + s.proj 2 x‖ ^ 2 := by rw [s.total_apply]
    _ = _ := by
      simp only [norm_add_sq_real, inner_add_left,
        s.proj_orthogonal (by decide : (0 : Fin 3) ≠ 1),
        s.proj_orthogonal (by decide : (0 : Fin 3) ≠ 2),
        s.proj_orthogonal (by decide : (1 : Fin 3) ≠ 2),
        add_zero, mul_zero]

theorem norm_proj_le (i : Fin 3) : ‖s.proj i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  rw [one_mul]
  have h := s.norm_sq_decomposition u
  have h0 := sq_nonneg ‖s.proj 0 u‖
  have h1 := sq_nonneg ‖s.proj 1 u‖
  have h2 := sq_nonneg ‖s.proj 2 u‖
  have hs : ‖s.proj i u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    fin_cases i
    · change ‖s.proj 0 u‖ ^ 2 ≤ ‖u‖ ^ 2
      linarith only [h, h1, h2]
    · change ‖s.proj 1 u‖ ^ 2 ≤ ‖u‖ ^ 2
      linarith only [h, h0, h2]
    · change ‖s.proj 2 u‖ ^ 2 ≤ ‖u‖ ^ 2
      linarith only [h, h0, h1]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

def cauchyAdjoint (T : E →L[ℝ] E) : E →L[ℝ] E :=
  s.proj 0 + s.proj 1 + T.comp (s.proj 2)

@[simp] theorem cauchyAdjoint_apply (T : E →L[ℝ] E) (x : E) :
    s.cauchyAdjoint T x = s.proj 0 x + s.proj 1 x + T (s.proj 2 x) := rfl

variable {s} {T : E →L[ℝ] E}

theorem range_support (hT : (s.proj 1).comp T = T) (i : Fin 3) (x : E) :
    s.proj i (T x) = if i = 1 then T x else 0 := by
  have ht : s.proj 1 (T x) = T x := congrArg (fun f : E →L[ℝ] E => f x) hT
  calc
    s.proj i (T x) = s.proj i (s.proj 1 (T x)) := by rw [ht]
    _ = _ := by
      rw [s.proj_proj]
      split_ifs with hi
      · subst i
        exact ht
      · rfl

@[simp] theorem proj0_cauchyAdjoint (hT : (s.proj 1).comp T = T) (x : E) :
    s.proj 0 (s.cauchyAdjoint T x) = s.proj 0 x := by
  simp [range_support hT]

@[simp] theorem proj1_cauchyAdjoint (hT : (s.proj 1).comp T = T) (x : E) :
    s.proj 1 (s.cauchyAdjoint T x) = s.proj 1 x + T (s.proj 2 x) := by
  simp [range_support hT]

@[simp] theorem proj2_cauchyAdjoint (hT : (s.proj 1).comp T = T) (x : E) :
    s.proj 2 (s.cauchyAdjoint T x) = 0 := by
  simp [range_support hT]

theorem norm_cauchyAdjoint_sq (hT : (s.proj 1).comp T = T) (x : E) :
    ‖s.cauchyAdjoint T x‖ ^ 2 =
      ‖s.proj 0 x‖ ^ 2 + ‖s.proj 1 x + T (s.proj 2 x)‖ ^ 2 := by
  rw [s.norm_sq_decomposition (s.cauchyAdjoint T x)]
  simp only [proj0_cauchyAdjoint hT, proj1_cauchyAdjoint hT,
    proj2_cauchyAdjoint hT, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero]

omit [CompleteSpace E] in
theorem norm_apply_le_of_norm_le_one {L : E →L[ℝ] E} (hL : ‖L‖ ≤ 1) (x : E) :
    ‖L x‖ ≤ ‖x‖ := by
  calc
    ‖L x‖ ≤ ‖L‖ * ‖x‖ := L.le_opNorm x
    _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hL (norm_nonneg x)
    _ = ‖x‖ := one_mul _

theorem weighted_norm_sq (hT : (s.proj 1).comp T = T) (hTnorm : ‖T‖ ≤ 1) (x : E) :
    ‖s.cauchyAdjoint T x‖ ^ 2 + ‖s.proj 0 (s.cauchyAdjoint T x)‖ ^ 2 ≤
      2 * ‖x‖ ^ 2 := by
  have hn := norm_apply_le_of_norm_le_one hTnorm (s.proj 2 x)
  have hnsq : ‖T (s.proj 2 x)‖ ^ 2 ≤ ‖s.proj 2 x‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hsum := norm_add_le (s.proj 1 x) (T (s.proj 2 x))
  have hsumsq := pow_le_pow_left₀ (norm_nonneg _) hsum 2
  rw [norm_cauchyAdjoint_sq hT, proj0_cauchyAdjoint hT, s.norm_sq_decomposition x]
  nlinarith [sq_nonneg (‖s.proj 1 x‖ - ‖T (s.proj 2 x)‖)]

structure CompatibleInvolution (s : ThreeWaySplitting E) where
  op : E ≃ₗᵢ[ℝ] E
  involutive : Function.Involutive op
  proj_zero : ∀ x, op (s.proj 0 x) = s.proj 0 (op x)
  proj_pos : ∀ x, op (s.proj 1 x) = s.proj 2 (op x)

namespace CompatibleInvolution

variable (j : CompatibleInvolution s)

@[simp] theorem op_op (x : E) : j.op (j.op x) = x := j.involutive x

theorem proj_neg (x : E) : j.op (s.proj 2 x) = s.proj 1 (j.op x) := by
  have h := congrArg j.op (j.proj_pos (j.op x))
  simpa only [j.op_op] using h.symm

theorem norm_add_op_sq (u : E) (hneg : s.proj 2 u = 0)
    (h0 : j.op (s.proj 0 u) = s.proj 0 u) :
    ‖u + j.op u‖ ^ 2 = 2 * (‖u‖ ^ 2 + ‖s.proj 0 u‖ ^ 2) := by
  have hu : u = s.proj 0 u + s.proj 1 u := by
    simpa only [hneg, add_zero] using (s.total_apply u).symm
  have hju : j.op u = s.proj 0 u + s.proj 2 (j.op u) := by
    calc
      j.op u = j.op (s.proj 0 u + s.proj 1 u) := congrArg j.op hu
      _ = _ := by rw [map_add, h0, j.proj_pos]
  have hi : ⟪u, j.op u⟫_ℝ = ‖s.proj 0 u‖ ^ 2 := by
    calc
      ⟪u, j.op u⟫_ℝ = ⟪s.proj 0 u + s.proj 1 u,
          s.proj 0 u + s.proj 2 (j.op u)⟫_ℝ := congrArg₂ (inner ℝ) hu hju
      _ = _ := by
        simp only [inner_add_left, inner_add_right,
          s.proj_orthogonal (by decide : (0 : Fin 3) ≠ 2),
          s.proj_orthogonal (by decide : (1 : Fin 3) ≠ 0),
          s.proj_orthogonal (by decide : (1 : Fin 3) ≠ 2),
          real_inner_self_eq_norm_sq, add_zero]
  rw [norm_add_sq_real, hi, j.op.norm_map]
  ring

theorem cauchyAdjoint_add_op_sq (hT : (s.proj 1).comp T = T) (u : E)
    (hu : j.op u = u) :
    ‖s.cauchyAdjoint T u + j.op (s.cauchyAdjoint T u)‖ ^ 2 =
      2 * (‖s.cauchyAdjoint T u‖ ^ 2 + ‖s.proj 0 (s.cauchyAdjoint T u)‖ ^ 2) := by
  apply j.norm_add_op_sq _ (proj2_cauchyAdjoint hT u)
  rw [proj0_cauchyAdjoint hT, j.proj_zero, hu]

theorem adjoint_reflected_orthogonal (hT : (s.proj 1).comp T = T)
    (r : E) (hr : s.proj 0 r = 0) :
    ⟪s.cauchyAdjoint T r, j.op (s.cauchyAdjoint T (j.op r))⟫_ℝ = 0 := by
  let g := s.cauchyAdjoint T r
  let h := s.cauchyAdjoint T (j.op r)
  have hg : g = s.proj 1 g := by
    have ht := s.total_apply g
    simpa only [g, proj0_cauchyAdjoint hT, proj2_cauchyAdjoint hT, hr,
      zero_add, add_zero] using ht.symm
  have hm : s.proj 0 (j.op r) = 0 := by rw [← j.proj_zero, hr, map_zero]
  have hh : h = s.proj 1 h := by
    have ht := s.total_apply h
    simpa only [h, proj0_cauchyAdjoint hT, proj2_cauchyAdjoint hT, hm,
      zero_add, add_zero] using ht.symm
  calc
    ⟪g, j.op h⟫_ℝ = ⟪s.proj 1 g, s.proj 2 (j.op h)⟫_ℝ := by
      have hjh : j.op h = s.proj 2 (j.op h) := by
        calc
          j.op h = j.op (s.proj 1 h) := congrArg j.op hh
          _ = _ := j.proj_pos h
      exact congrArg₂ (inner ℝ) hg hjh
    _ = 0 := s.proj_orthogonal (by decide) _ _

theorem norm_cross_ge (hT : (s.proj 1).comp T = T)
    (r : E) (hr : s.proj 0 r = 0) (κ : ℝ) :
    κ ^ 2 * ‖s.cauchyAdjoint T r‖ ^ 2 ≤
      ‖κ • s.cauchyAdjoint T r + κ⁻¹ • j.op (s.cauchyAdjoint T (j.op r))‖ ^ 2 := by
  rw [norm_add_sq_real, inner_smul_left, inner_smul_right,
    j.adjoint_reflected_orthogonal hT r hr, mul_zero, mul_zero, mul_zero, add_zero]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  exact le_add_of_nonneg_right (by positivity)

end CompatibleInvolution

theorem ordered_projection (L : E →L[ℝ] E)
    (hL : (ContinuousLinearMap.adjoint (s.cauchyAdjoint T)).comp
        (L.comp (ContinuousLinearMap.adjoint (s.cauchyAdjoint T))) =
      L.comp (ContinuousLinearMap.adjoint (s.cauchyAdjoint T))) (r : E) :
    s.cauchyAdjoint T (ContinuousLinearMap.adjoint L r) =
      s.cauchyAdjoint T (ContinuousLinearMap.adjoint L (s.cauchyAdjoint T r)) := by
  have h := congrArg ContinuousLinearMap.adjoint hL
  simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint] at h
  exact (congrArg (fun M : E →L[ℝ] E => M r) h).symm

theorem norm_adjoint_apply_le_of_norm_le_one {L : E →L[ℝ] E}
    (hL : ‖L‖ ≤ 1) (x : E) : ‖ContinuousLinearMap.adjoint L x‖ ≤ ‖x‖ :=
  norm_apply_le_of_norm_le_one ((ContinuousLinearMap.adjoint.norm_map L).trans_le hL) x

theorem diagonal_estimate (j : CompatibleInvolution s)
    (hT : (s.proj 1).comp T = T) (hTnorm : ‖T‖ ≤ 1)
    (L : E →L[ℝ] E) (hLnorm : ‖L‖ ≤ 1)
    (hL : (ContinuousLinearMap.adjoint (s.cauchyAdjoint T)).comp
        (L.comp (ContinuousLinearMap.adjoint (s.cauchyAdjoint T))) =
      L.comp (ContinuousLinearMap.adjoint (s.cauchyAdjoint T)))
    (p r : E) (hp : p = ContinuousLinearMap.adjoint L r) (hpstar : j.op p = p) :
    ‖s.cauchyAdjoint T p + j.op (s.cauchyAdjoint T (j.op p))‖ ^ 2 ≤
      4 * ‖s.cauchyAdjoint T r‖ ^ 2 := by
  have hd : s.cauchyAdjoint T p =
      s.cauchyAdjoint T (ContinuousLinearMap.adjoint L (s.cauchyAdjoint T r)) := by
    rw [hp, ordered_projection L hL r]
  have hn := norm_adjoint_apply_le_of_norm_le_one hLnorm (s.cauchyAdjoint T r)
  have hnsq := pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hw := weighted_norm_sq hT hTnorm
    (ContinuousLinearMap.adjoint L (s.cauchyAdjoint T r))
  rw [hpstar, j.cauchyAdjoint_add_op_sq hT p hpstar, hd]
  linarith

theorem ordered_comparison_of_block_norm (j : CompatibleInvolution s)
    (hT : (s.proj 1).comp T = T) (hTnorm : ‖T‖ ≤ 1)
    (L R : E →L[ℝ] E) (hLnorm : ‖L‖ ≤ 1) (hRnorm : ‖R‖ ≤ 1)
    (hL : (ContinuousLinearMap.adjoint (s.cauchyAdjoint T)).comp
        (L.comp (ContinuousLinearMap.adjoint (s.cauchyAdjoint T))) =
      L.comp (ContinuousLinearMap.adjoint (s.cauchyAdjoint T)))
    (hR : (ContinuousLinearMap.adjoint (s.cauchyAdjoint T)).comp
        (R.comp (ContinuousLinearMap.adjoint (s.cauchyAdjoint T))) =
      R.comp (ContinuousLinearMap.adjoint (s.cauchyAdjoint T)))
    (p q r : E) (hp : p = ContinuousLinearMap.adjoint L r)
    (hq : q = ContinuousLinearMap.adjoint R r)
    (hpstar : j.op p = p) (hqstar : j.op q = q)
    (hrmean : s.proj 0 r = 0) (hpmean : s.proj 0 p ≠ 0)
    (κ : ℝ) (hκ : 0 < κ)
    (hblock : 2 * ‖κ • s.cauchyAdjoint T r +
          κ⁻¹ • j.op (s.cauchyAdjoint T (j.op r))‖ ^ 2 ≤
      ‖s.cauchyAdjoint T p + j.op (s.cauchyAdjoint T (j.op p))‖ ^ 2 +
      ‖s.cauchyAdjoint T q + j.op (s.cauchyAdjoint T (j.op q))‖ ^ 2) : κ ≤ 2 := by
  have hg : s.cauchyAdjoint T r ≠ 0 := by
    intro hg
    have hd : s.cauchyAdjoint T p = 0 := by
      rw [hp, ordered_projection L hL r, hg, map_zero, map_zero]
    apply hpmean
    rw [← proj0_cauchyAdjoint hT p, hd, map_zero]
  have hgp : 0 < ‖s.cauchyAdjoint T r‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hg)
  have hpbound := diagonal_estimate j hT hTnorm L hLnorm hL p r hp hpstar
  have hqbound := diagonal_estimate j hT hTnorm R hRnorm hR q r hq hqstar
  have hcross := j.norm_cross_ge hT r hrmean κ
  have hm : κ ^ 2 * ‖s.cauchyAdjoint T r‖ ^ 2 ≤
      4 * ‖s.cauchyAdjoint T r‖ ^ 2 := by linarith
  have hsq : κ ^ 2 ≤ 4 := (mul_le_mul_iff_of_pos_right hgp).mp hm
  nlinarith

end ThreeWaySplitting

end Splitting

section FieldAction

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def fieldAction (L : α → E →L[ℝ] E) (hL : AEStronglyMeasurable L μ)
    (hLn : ∀ᵐ t ∂μ, ‖L t‖ ≤ 1) : Lp E 2 μ →L[ℝ] Lp E 2 μ := by
  let mem : ∀ u : Lp E 2 μ, MemLp (fun t => L t (u t)) 2 μ := fun u =>
    (Lp.memLp u).mono
      ((show Continuous (fun z : (E →L[ℝ] E) × E => z.1 z.2) by fun_prop).comp_aestronglyMeasurable (hL.prodMk (Lp.aestronglyMeasurable u)))
      (hLn.mono fun t ht => by
        calc
          ‖L t (u t)‖ ≤ ‖L t‖ * ‖u t‖ := (L t).le_opNorm _
          _ ≤ 1 * ‖u t‖ := mul_le_mul_of_nonneg_right ht (norm_nonneg _)
          _ = ‖u t‖ := one_mul _)
  let M : Lp E 2 μ →ₗ[ℝ] Lp E 2 μ := {
    toFun u := (mem u).toLp _
    map_add' u v := by
      apply Lp.ext
      filter_upwards [(mem (u + v)).coeFn_toLp, (mem u).coeFn_toLp,
        (mem v).coeFn_toLp, Lp.coeFn_add u v,
        Lp.coeFn_add ((mem u).toLp _) ((mem v).toLp _)] with t huv hu hv ha hb
      simp only [huv, hb, hu, hv, ha, map_add, Pi.add_apply]
    map_smul' c u := by
      apply Lp.ext
      filter_upwards [(mem (c • u)).coeFn_toLp, (mem u).coeFn_toLp,
        Lp.coeFn_smul c u, Lp.coeFn_smul c ((mem u).toLp _)] with t hcu hu ha hb
      simp only [hcu, hb, hu, ha, map_smul, Pi.smul_apply, RingHom.id_apply] }
  apply M.mkContinuous 1
  intro u
  rw [one_mul]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [(mem u).coeFn_toLp, hLn] with t ht hn
  change ‖((mem u).toLp _) t‖ ≤ ‖u t‖
  rw [ht]
  exact ThreeWaySplitting.norm_apply_le_of_norm_le_one hn _

omit [CompleteSpace E] in
theorem fieldAction_apply_ae (L : α → E →L[ℝ] E) (hL : AEStronglyMeasurable L μ)
    (hLn : ∀ᵐ t ∂μ, ‖L t‖ ≤ 1) (u : Lp E 2 μ) :
    fieldAction L hL hLn u =ᵐ[μ] fun t => L t (u t) := by
  unfold fieldAction
  dsimp only [LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]
  exact MemLp.coeFn_toLp _

omit [CompleteSpace E] in
theorem norm_fieldAction_le (L : α → E →L[ℝ] E) (hL : AEStronglyMeasurable L μ)
    (hLn : ∀ᵐ t ∂μ, ‖L t‖ ≤ 1) : ‖fieldAction L hL hLn‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro u
  rw [one_mul]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [fieldAction_apply_ae L hL hLn u, hLn] with t ht hn
  rw [ht]
  exact ThreeWaySplitting.norm_apply_le_of_norm_le_one hn _

theorem adjoint_fieldAction (L M : α → E →L[ℝ] E)
    (hL : AEStronglyMeasurable L μ) (hM : AEStronglyMeasurable M μ)
    (hLn : ∀ᵐ t ∂μ, ‖L t‖ ≤ 1) (hMn : ∀ᵐ t ∂μ, ‖M t‖ ≤ 1)
    (ha : ∀ᵐ t ∂μ, ContinuousLinearMap.adjoint (L t) = M t) :
    ContinuousLinearMap.adjoint (fieldAction L hL hLn) = fieldAction M hM hMn := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro u v
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [fieldAction_apply_ae M hM hMn u, fieldAction_apply_ae L hL hLn v, ha]
    with t hu hv ht
  rw [hu, hv, ← ht, ContinuousLinearMap.adjoint_inner_left]

end FieldAction

section MatrixMultipliers

def hsEquiv (k : ℕ) : Matrix (Fin k) (Fin k) ℂ ≃ₗ[ℝ] HS k where
  toFun := toHS
  invFun := ofHS
  left_inv := ofHS_toHS
  right_inv := toHS_ofHS
  map_add' A B := by ext ij; rfl
  map_smul' c A := by ext ij; rfl

@[simp] theorem hsEquiv_apply {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) :
    hsEquiv k A = toHS A := rfl

@[simp] theorem hsEquiv_symm_apply {k : ℕ} (u : HS k) :
    (hsEquiv k).symm u = ofHS u := rfl

theorem inner_toHS {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℂ) :
    ⟪toHS A, toHS B⟫_ℂ = (Aᴴ * B).trace := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, toHS,
    Fintype.sum_prod_type, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, starRingEnd_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem real_inner_toHS {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℂ) :
    ⟪toHS A, toHS B⟫_ℝ = (Aᴴ * B).trace.re := by
  rw [← inner_toHS]
  simp only [PiLp.inner_apply, toHS, real_inner_eq_re_inner ℂ,
    RCLike.re_to_complex, Complex.re_sum]

theorem norm_toHS_conjTranspose {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) :
    ‖toHS Aᴴ‖ = ‖toHS A‖ := by
  have h : ‖toHS Aᴴ‖ ^ 2 = ‖toHS A‖ ^ 2 := by
    simp only [norm_toHS_sq, Matrix.conjTranspose_apply, norm_star]
    exact Finset.sum_comm
  nlinarith [norm_nonneg (toHS Aᴴ), norm_nonneg (toHS A)]

theorem norm_toHS_mul_le {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℂ) :
    ‖toHS (A * B)‖ ≤ ‖A‖ * ‖toHS B‖ := by
  let col : Matrix (Fin k) (Fin k) ℂ → Fin k → EuclideanSpace ℂ (Fin k) :=
    fun M j => WithLp.toLp 2 (fun i => M i j)
  have hcol (M : Matrix (Fin k) (Fin k) ℂ) :
      ‖toHS M‖ ^ 2 = ∑ j, ‖col M j‖ ^ 2 := by
    rw [norm_toHS_sq]
    simp only [PiLp.norm_sq_eq_of_L2, col]
    change (∑ i, ∑ j, ‖M i j‖ ^ 2) = ∑ j, ∑ i, ‖M i j‖ ^ 2
    exact Finset.sum_comm
  have hn (j : Fin k) : ‖col (A * B) j‖ ≤ ‖A‖ * ‖col B j‖ := by
    exact Matrix.l2_opNorm_mulVec A (col B j)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [hcol, mul_pow, hcol, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (hn j) 2

theorem norm_toHS_mul_le_right {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℂ) :
    ‖toHS (A * B)‖ ≤ ‖toHS A‖ * ‖B‖ := by
  calc
    ‖toHS (A * B)‖ = ‖toHS (Bᴴ * Aᴴ)‖ := by
      rw [← Matrix.conjTranspose_mul, norm_toHS_conjTranspose]
    _ ≤ ‖Bᴴ‖ * ‖toHS Aᴴ‖ := norm_toHS_mul_le _ _
    _ = ‖toHS A‖ * ‖B‖ := by
      rw [Matrix.l2_opNorm_conjTranspose, norm_toHS_conjTranspose, mul_comm]

def hsLeft {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) : HS k →L[ℝ] HS k :=
  ((hsEquiv k).toLinearMap.comp
    ((LinearMap.mulLeft ℝ A).comp (hsEquiv k).symm.toLinearMap)).toContinuousLinearMap

def hsRight {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) : HS k →L[ℝ] HS k :=
  ((hsEquiv k).toLinearMap.comp
    ((LinearMap.mulRight ℝ A).comp (hsEquiv k).symm.toLinearMap)).toContinuousLinearMap

@[simp] theorem hsLeft_apply {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) (u : HS k) :
    hsLeft A u = toHS (A * ofHS u) := rfl

@[simp] theorem hsRight_apply {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) (u : HS k) :
    hsRight A u = toHS (ofHS u * A) := rfl

theorem norm_hsLeft_le {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) :
    ‖hsLeft A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro u
  simpa only [hsLeft_apply, toHS_ofHS] using norm_toHS_mul_le A (ofHS u)

theorem norm_hsRight_le {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) :
    ‖hsRight A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro u
  simpa only [hsRight_apply, toHS_ofHS, mul_comm] using norm_toHS_mul_le_right (ofHS u) A

@[simp] theorem adjoint_hsLeft {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) :
    ContinuousLinearMap.adjoint (hsLeft A) = hsLeft Aᴴ := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro u v
  obtain ⟨U, rfl⟩ := (hsEquiv k).surjective u
  obtain ⟨V, rfl⟩ := (hsEquiv k).surjective v
  simp only [hsEquiv_apply, hsLeft_apply, ofHS_toHS, 
    real_inner_toHS, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

@[simp] theorem adjoint_hsRight {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) :
    ContinuousLinearMap.adjoint (hsRight A) = hsRight Aᴴ := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro u v
  obtain ⟨U, rfl⟩ := (hsEquiv k).surjective u
  obtain ⟨V, rfl⟩ := (hsEquiv k).surjective v
  simp only [hsEquiv_apply, hsRight_apply, ofHS_toHS, 
    real_inner_toHS, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm (V * A)]

def hsLeftCoefficient (k : ℕ) :
    Matrix (Fin k) (Fin k) ℂ →L[ℝ] (HS k →L[ℝ] HS k) :=
  ({ toFun := hsLeft
     map_add' := fun A B => by
       apply ContinuousLinearMap.ext
       intro u
       change toHS ((A + B) * ofHS u) = toHS (A * ofHS u) + toHS (B * ofHS u)
       rw [add_mul]
       simpa only [hsEquiv_apply] using (hsEquiv k).map_add _ _
     map_smul' := fun c A => by
       apply ContinuousLinearMap.ext
       intro u
       change toHS ((c • A) * ofHS u) = c • toHS (A * ofHS u)
       rw [Matrix.smul_mul]
       simpa only [hsEquiv_apply] using (hsEquiv k).map_smul c _ } :
    Matrix (Fin k) (Fin k) ℂ →ₗ[ℝ] (HS k →L[ℝ] HS k)).toContinuousLinearMap

def hsRightCoefficient (k : ℕ) :
    Matrix (Fin k) (Fin k) ℂ →L[ℝ] (HS k →L[ℝ] HS k) :=
  ({ toFun := hsRight
     map_add' := fun A B => by
       apply ContinuousLinearMap.ext
       intro u
       change toHS (ofHS u * (A + B)) = toHS (ofHS u * A) + toHS (ofHS u * B)
       rw [mul_add]
       simpa only [hsEquiv_apply] using (hsEquiv k).map_add _ _
     map_smul' := fun c A => by
       apply ContinuousLinearMap.ext
       intro u
       change toHS (ofHS u * (c • A)) = c • toHS (ofHS u * A)
       rw [Matrix.mul_smul]
       simpa only [hsEquiv_apply] using (hsEquiv k).map_smul c _ } :
    Matrix (Fin k) (Fin k) ℂ →ₗ[ℝ] (HS k →L[ℝ] HS k)).toContinuousLinearMap

def hsStar (k : ℕ) : HS k ≃ₗᵢ[ℝ] HS k where
  toFun u := toHS (ofHS u)ᴴ
  invFun u := toHS (ofHS u)ᴴ
  left_inv u := by simp
  right_inv u := by simp
  map_add' u v := by
    change toHS ((ofHS u + ofHS v)ᴴ) = _
    rw [Matrix.conjTranspose_add]
    simpa only [hsEquiv_apply] using (hsEquiv k).map_add _ _
  map_smul' c u := by
    change toHS ((c • ofHS u)ᴴ) = c • toHS (ofHS u)ᴴ
    rw [Matrix.conjTranspose_smul, star_trivial]
    simpa only [hsEquiv_apply] using (hsEquiv k).map_smul c _
  norm_map' u := by
    change ‖toHS (ofHS u)ᴴ‖ = ‖u‖
    rw [norm_toHS_conjTranspose, toHS_ofHS]

@[simp] theorem hsStar_apply {k : ℕ} (u : HS k) : hsStar k u = toHS (ofHS u)ᴴ := rfl

@[simp] theorem hsStar_hsStar {k : ℕ} (u : HS k) : hsStar k (hsStar k u) = u := by simp

end MatrixMultipliers

section L2Multipliers

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {k : ℕ}

def lpStar : Lp (HS k) 2 μ ≃ₗᵢ[ℝ] Lp (HS k) 2 μ := by
  let M := (hsStar k).toContinuousLinearMap.compLpL 2 μ
  have hinv : Function.Involutive M := by
    intro u
    apply Lp.ext
    filter_upwards [(hsStar k).toContinuousLinearMap.coeFn_compLpL u,
      (hsStar k).toContinuousLinearMap.coeFn_compLpL (M u)] with t hu hMu
    exact hMu.trans (by change hsStar k (M u t) = u t; rw [hu]; exact hsStar_hsStar _)
  refine {
    toLinearEquiv := {
      toLinearMap := M.toLinearMap
      invFun := M
      left_inv := hinv
      right_inv := hinv }
    norm_map' := fun u => ?_ }
  have hn : ∀ᵐ t ∂μ, ‖M u t‖ = ‖u t‖ :=
    ((hsStar k).toContinuousLinearMap.coeFn_compLpL u).mono fun t ht => by
      rw [ht]
      exact (hsStar k).norm_map _
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (hn.mono fun _ ht => ht.le))
    (Lp.norm_le_norm_of_ae_le (hn.mono fun _ ht => ht.ge))

theorem lpStar_apply_ae (u : Lp (HS k) 2 μ) :
    lpStar u =ᵐ[μ] fun t => toHS (ofHS (u t))ᴴ :=
  (hsStar k).toContinuousLinearMap.coeFn_compLpL u

@[simp] theorem lpStar_lpStar (u : Lp (HS k) 2 μ) : lpStar (lpStar u) = u := by
  apply Lp.ext
  filter_upwards [lpStar_apply_ae u, lpStar_apply_ae (lpStar u)] with t hu hsu
  simp only [hsu, hu, ofHS_toHS, Matrix.conjTranspose_conjTranspose, toHS_ofHS]

def lpLeft (F : α → Matrix (Fin k) (Fin k) ℂ) (hm : AEStronglyMeasurable F μ)
    (hn : ∀ᵐ t ∂μ, ‖F t‖ ≤ 1) : Lp (HS k) 2 μ →L[ℝ] Lp (HS k) 2 μ :=
  fieldAction (fun t => hsLeft (F t))
    ((hsLeftCoefficient k).continuous.comp_aestronglyMeasurable hm)
    (hn.mono fun _ ht => (norm_hsLeft_le _).trans ht)

def lpRight (F : α → Matrix (Fin k) (Fin k) ℂ) (hm : AEStronglyMeasurable F μ)
    (hn : ∀ᵐ t ∂μ, ‖F t‖ ≤ 1) : Lp (HS k) 2 μ →L[ℝ] Lp (HS k) 2 μ :=
  fieldAction (fun t => hsRight (F t))
    ((hsRightCoefficient k).continuous.comp_aestronglyMeasurable hm)
    (hn.mono fun _ ht => (norm_hsRight_le _).trans ht)

theorem lpLeft_apply_ae (F : α → Matrix (Fin k) (Fin k) ℂ)
    (hm : AEStronglyMeasurable F μ) (hn : ∀ᵐ t ∂μ, ‖F t‖ ≤ 1)
    (u : Lp (HS k) 2 μ) :
    lpLeft F hm hn u =ᵐ[μ] fun t => toHS (F t * ofHS (u t)) :=
  fieldAction_apply_ae _ _ _ _

theorem lpRight_apply_ae (F : α → Matrix (Fin k) (Fin k) ℂ)
    (hm : AEStronglyMeasurable F μ) (hn : ∀ᵐ t ∂μ, ‖F t‖ ≤ 1)
    (u : Lp (HS k) 2 μ) :
    lpRight F hm hn u =ᵐ[μ] fun t => toHS (ofHS (u t) * F t) :=
  fieldAction_apply_ae _ _ _ _

theorem norm_lpLeft_le (F : α → Matrix (Fin k) (Fin k) ℂ)
    (hm : AEStronglyMeasurable F μ) (hn : ∀ᵐ t ∂μ, ‖F t‖ ≤ 1) :
    ‖lpLeft F hm hn‖ ≤ 1 := norm_fieldAction_le _ _ _

theorem norm_lpRight_le (F : α → Matrix (Fin k) (Fin k) ℂ)
    (hm : AEStronglyMeasurable F μ) (hn : ∀ᵐ t ∂μ, ‖F t‖ ≤ 1) :
    ‖lpRight F hm hn‖ ≤ 1 := norm_fieldAction_le _ _ _

theorem aestronglyMeasurable_conjTranspose (F : α → Matrix (Fin k) (Fin k) ℂ)
    (hm : AEStronglyMeasurable F μ) : AEStronglyMeasurable (fun t => (F t)ᴴ) μ :=
  (show Continuous (fun A : Matrix (Fin k) (Fin k) ℂ => Aᴴ) by fun_prop).comp_aestronglyMeasurable hm

theorem lpLeft_adjoint_apply_ae (F : α → Matrix (Fin k) (Fin k) ℂ)
    (hm : AEStronglyMeasurable F μ) (hn : ∀ᵐ t ∂μ, ‖F t‖ ≤ 1)
    (u : Lp (HS k) 2 μ) :
    ContinuousLinearMap.adjoint (lpLeft F hm hn) u =ᵐ[μ]
      fun t => toHS ((F t)ᴴ * ofHS (u t)) := by
  have hm' := aestronglyMeasurable_conjTranspose F hm
  have hn' : ∀ᵐ t ∂μ, ‖(F t)ᴴ‖ ≤ 1 := hn.mono fun t ht => by
    rwa [Matrix.l2_opNorm_conjTranspose]
  have h : ContinuousLinearMap.adjoint (lpLeft F hm hn) = lpLeft (fun t => (F t)ᴴ) hm' hn' :=
    adjoint_fieldAction _ _ _ _ _ _ (Filter.Eventually.of_forall fun t => adjoint_hsLeft _)
  rw [h]
  exact lpLeft_apply_ae _ _ _ _

theorem lpRight_adjoint_apply_ae (F : α → Matrix (Fin k) (Fin k) ℂ)
    (hm : AEStronglyMeasurable F μ) (hn : ∀ᵐ t ∂μ, ‖F t‖ ≤ 1)
    (u : Lp (HS k) 2 μ) :
    ContinuousLinearMap.adjoint (lpRight F hm hn) u =ᵐ[μ]
      fun t => toHS (ofHS (u t) * (F t)ᴴ) := by
  have hm' := aestronglyMeasurable_conjTranspose F hm
  have hn' : ∀ᵐ t ∂μ, ‖(F t)ᴴ‖ ≤ 1 := hn.mono fun t ht => by
    rwa [Matrix.l2_opNorm_conjTranspose]
  have h : ContinuousLinearMap.adjoint (lpRight F hm hn) = lpRight (fun t => (F t)ᴴ) hm' hn' :=
    adjoint_fieldAction _ _ _ _ _ _ (Filter.Eventually.of_forall fun t => adjoint_hsRight _)
  rw [h]
  exact lpRight_apply_ae _ _ _ _

theorem lpStar_eq_self_iff (u : Lp (HS k) 2 μ) :
    lpStar u = u ↔ ∀ᵐ t ∂μ, (ofHS (u t)).IsHermitian := by
  constructor
  · intro h
    filter_upwards [lpStar_apply_ae u] with t ht
    rw [h] at ht
    have he := congrArg ofHS ht
    exact (he.trans (ofHS_toHS _)).symm
  · intro h
    apply Lp.ext
    filter_upwards [lpStar_apply_ae u, h] with t ht he
    rw [ht, he.eq, toHS_ofHS]

theorem lp_ordered_comparison
    (s : ThreeWaySplitting (Lp (HS k) 2 μ))
    (hstar0 : ∀ u, lpStar (s.proj 0 u) = s.proj 0 (lpStar u))
    (hstar1 : ∀ u, lpStar (s.proj 1 u) = s.proj 2 (lpStar u))
    (T : Lp (HS k) 2 μ →L[ℝ] Lp (HS k) 2 μ)
    (hT : (s.proj 1).comp T = T) (hTnorm : ‖T‖ ≤ 1)
    (F : α → Matrix (Fin k) (Fin k) ℂ)
    (hm : AEStronglyMeasurable F μ) (hn : ∀ᵐ t ∂μ, ‖F t‖ ≤ 1)
    (hleft : (ContinuousLinearMap.adjoint (s.cauchyAdjoint T)).comp
        ((lpLeft F hm hn).comp (ContinuousLinearMap.adjoint (s.cauchyAdjoint T))) =
      (lpLeft F hm hn).comp (ContinuousLinearMap.adjoint (s.cauchyAdjoint T)))
    (hright : (ContinuousLinearMap.adjoint (s.cauchyAdjoint T)).comp
        ((lpRight F hm hn).comp (ContinuousLinearMap.adjoint (s.cauchyAdjoint T))) =
      (lpRight F hm hn).comp (ContinuousLinearMap.adjoint (s.cauchyAdjoint T)))
    (p q r : Lp (HS k) 2 μ)
    (hpstar : ∀ᵐ t ∂μ, (ofHS (p t)).IsHermitian)
    (hqstar : ∀ᵐ t ∂μ, (ofHS (q t)).IsHermitian)
    (hp : ∀ᵐ t ∂μ, ofHS (p t) = (F t)ᴴ * ofHS (r t))
    (hq : ∀ᵐ t ∂μ, ofHS (q t) = ofHS (r t) * (F t)ᴴ)
    (hrmean : s.proj 0 r = 0) (hpmean : s.proj 0 p ≠ 0)
    (κ : ℝ) (hκ : 0 < κ)
    (hblock : let D := s.cauchyAdjoint T
      let pₑ := D p + lpStar (D (lpStar p))
      let qₑ := D q + lpStar (D (lpStar q))
      let rₑ := κ • D r + κ⁻¹ • lpStar (D (lpStar r))
      ∀ᵐ t ∂μ, (Matrix.fromBlocks (ofHS (pₑ t))
        (ofHS (rₑ t))ᴴ (ofHS (rₑ t)) (ofHS (qₑ t))).PosSemidef) : κ ≤ 2 := by
  let j : s.CompatibleInvolution := {
    op := lpStar
    involutive := lpStar_lpStar
    proj_zero := hstar0
    proj_pos := hstar1 }
  have hp' : p = ContinuousLinearMap.adjoint (lpLeft F hm hn) r := by
    apply Lp.ext
    filter_upwards [hp, lpLeft_adjoint_apply_ae F hm hn r] with t ht ha
    rw [ha, ← ht, toHS_ofHS]
  have hq' : q = ContinuousLinearMap.adjoint (lpRight F hm hn) r := by
    apply Lp.ext
    filter_upwards [hq, lpRight_adjoint_apply_ae F hm hn r] with t ht ha
    rw [ha, ← ht, toHS_ofHS]
  exact ThreeWaySplitting.ordered_comparison_of_block_norm j hT hTnorm
    (lpLeft F hm hn) (lpRight F hm hn) (norm_lpLeft_le F hm hn)
    (norm_lpRight_le F hm hn) hleft hright p q r hp' hq'
    ((lpStar_eq_self_iff p).mpr hpstar) ((lpStar_eq_self_iff q).mpr hqstar)
    hrmean hpmean κ hκ (lp_block_posSemidef_norm_sq _ _ _ hblock)

end L2Multipliers

end CrouzeixHilbert.Boundary

end

end OAI
