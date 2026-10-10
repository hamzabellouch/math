import OAI.Analysis.LpDimension.Entropy

namespace OAI

noncomputable section
open MeasureTheory Filter Matrix NormedSpace
open scoped BigOperators Topology Matrix Matrix.Norms.Operator
universe u uV

namespace SubpolynomialLp

open scoped Matrix.Norms.Operator
open Matrix NormedSpace
section PositiveExponential
variable {V : Type uV} [Fintype V] [DecidableEq V]
lemma matrix_pow_nonneg (A : Matrix V V ℝ) (hA : ∀ i j, 0 ≤ A i j) :
    ∀ k : ℕ, ∀ i j, 0 ≤ (A ^ k) i j := by
  intro k
  induction k with
  | zero => intro i j; simp only [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ k hk =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg (fun l _ => mul_nonneg (hk i l) (hA l j))

omit [Fintype V] [DecidableEq V] in
lemma matrix_tsum_apply (f : ℕ → Matrix V V ℝ) (hf : Summable f) (i j : V) :
    (∑' k, f k) i j = ∑' k, f k i j :=
  ((Pi.hasSum.mp (Pi.hasSum.mp hf.hasSum i)) j).tsum_eq.symm


lemma matrix_exp_pos (A : Matrix V V ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (i j : V) (hij : 0 < A i j) : 0 < exp A i j := by
  have hs := expSeries_summable' (𝕂 := ℝ) A
  have hsi := (Pi.summable.mp hs) i
  have hsij := (Pi.summable.mp hsi) j
  have he : exp A = ∑' k : ℕ, ((k.factorial : ℝ)⁻¹) • A ^ k :=
    congrFun (exp_eq_tsum ℝ) A
  rw [he]
  rw [matrix_tsum_apply _ hs i j]
  apply hsij.tsum_pos
    (fun k => mul_nonneg (by positivity) (matrix_pow_nonneg A hA k i j)) 1
  simpa using hij

lemma matrix_exp_scalar (t : ℝ) :
    exp (t • (1 : Matrix V V ℝ)) = Real.exp t • (1 : Matrix V V ℝ) := by
  convert (algebraMap_exp_comm (𝔸 := Matrix V V ℝ) t).symm using 1
  all_goals simp only [Algebra.algebraMap_eq_smul_one, Real.exp_eq_exp_ℝ]
  all_goals rfl

lemma matrix_exp_add_scalar (A : Matrix V V ℝ) (r : ℝ) :
    exp (A + r • 1) = Real.exp r • exp A := by
  rw [Matrix.exp_add_of_commute A (r • 1) ((Commute.one_right A).smul_right r),
    matrix_exp_scalar, Matrix.mul_smul, Matrix.mul_one]

lemma matrix_exp_pos_of_offdiag (A : Matrix V V ℝ)
    (hA : ∀ i j, i ≠ j → 0 < A i j) (i j : V) : 0 < exp A i j := by
  let r : ℝ := 1 + ∑ i, |A i i|
  have hd (i : V) : 0 < A i i + r := by
    have hb := Finset.single_le_sum (f := fun k => |A k k|)
      (fun k _ => abs_nonneg (A k k)) (Finset.mem_univ i)
    have := neg_abs_le (A i i)
    dsimp [r]
    linarith
  have hp (i j : V) : 0 < (A + r • 1) i j := by
    by_cases hij : i = j
    · subst j
      simpa using hd i
    · simpa [Matrix.one_apply, hij] using hA i j hij
  have hp' := matrix_exp_pos (A + r • 1) (fun i j => (hp i j).le) i j (hp i j)
  rw [matrix_exp_add_scalar] at hp'
  exact (mul_pos_iff_of_pos_left (Real.exp_pos r)).mp hp'

end PositiveExponential

section MatrixSpectral
variable {V : Type uV} [Fintype V] [DecidableEq V]

lemma matrix_exp_conj_unitary (U : Matrix.unitaryGroup V ℝ) (A : Matrix V V ℝ) :
    exp ((U : Matrix V V ℝ) * A * star (U : Matrix V V ℝ)) =
      (U : Matrix V V ℝ) * exp A * star (U : Matrix V V ℝ) := by
  let φ := Unitary.conjStarAlgAut ℝ (Matrix V V ℝ) U
  have hc : Continuous φ := φ.toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
  exact (NormedSpace.map_exp φ.toAlgEquiv.toAlgHom hc A).symm

lemma matrix_exp_spectral (S : Matrix V V ℝ) (hS : S.IsHermitian) (t : ℝ) :
    exp (t • S) = (hS.eigenvectorUnitary : Matrix V V ℝ) *
      Matrix.diagonal (fun k => Real.exp (t * hS.eigenvalues k)) *
        star (hS.eigenvectorUnitary : Matrix V V ℝ) := by
  conv_lhs => rw [hS.spectral_theorem, Unitary.conjStarAlgAut_apply]
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, matrix_exp_conj_unitary,
    ← Matrix.diagonal_smul, Matrix.exp_diagonal]
  congr 2
  ext i
  simp [Pi.exp_def, Real.exp_eq_exp_ℝ]


def spectralKernelProjection (S : Matrix V V ℝ) (hS : S.IsHermitian) : Matrix V V ℝ :=
  Unitary.conjStarAlgAut ℝ (Matrix V V ℝ) hS.eigenvectorUnitary
    (Matrix.diagonal (fun k => if hS.eigenvalues k = 0 then 1 else 0))

lemma matrix_exp_neg_tendsto (S : Matrix V V ℝ) (hS : S.PosSemidef) :
    Tendsto (fun t : ℝ => exp (-t • S)) atTop (𝓝 (spectralKernelProjection S hS.1)) := by
  have he (k : V) : Tendsto (fun t : ℝ => Real.exp (-t * hS.1.eigenvalues k))
      atTop (𝓝 (if hS.1.eigenvalues k = 0 then 1 else 0)) := by
    by_cases hk : hS.1.eigenvalues k = 0
    · simp only [hk, mul_zero, Real.exp_zero, ite_true]
      exact tendsto_const_nhds
    · simp only [hk, ite_false]
      have hp := lt_of_le_of_ne (hS.eigenvalues_nonneg k) (Ne.symm hk)
      simpa only [id_eq, neg_mul, Function.comp_def] using Real.tendsto_exp_atBot.comp
        (tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_mul_const hp))
  have hd : Tendsto (fun t : ℝ => Matrix.diagonal (fun k => Real.exp (-t * hS.1.eigenvalues k)))
      atTop (𝓝 (Matrix.diagonal (fun k => if hS.1.eigenvalues k = 0 then 1 else 0))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    by_cases hij : i = j
    · subst j
      simpa only [Matrix.diagonal_apply_eq] using he i
    · simp only [Matrix.diagonal_apply_ne _ hij]
      exact tendsto_const_nhds
  simpa only [matrix_exp_spectral S hS.1, spectralKernelProjection, Unitary.conjStarAlgAut_apply]
    using (hd.const_mul (hS.1.eigenvectorUnitary : Matrix V V ℝ)).mul_const
      (star (hS.1.eigenvectorUnitary : Matrix V V ℝ))

lemma mul_spectralKernelProjection (S : Matrix V V ℝ) (hS : S.IsHermitian) :
    S * spectralKernelProjection S hS = 0 := by
  unfold spectralKernelProjection
  conv_lhs => lhs; rw [hS.spectral_theorem]
  rw [← map_mul, Matrix.diagonal_mul_diagonal]
  have hz : (fun k => (RCLike.ofReal ∘ hS.eigenvalues) k *
      (if hS.eigenvalues k = 0 then 1 else 0)) = (0 : V → ℝ) := by
    funext k
    by_cases hk : hS.eigenvalues k = 0 <;> simp [hk]
  rw [hz]
  simp

end MatrixSpectral

section WeightedHeat
variable {V : Type uV} [Fintype V] [DecidableEq V]

def weightedGenerator (L : Matrix V V ℝ) (d : V → ℝ) :=
  diagonal (fun i => d i * d i) * L

def symmetricGenerator (L : Matrix V V ℝ) (d : V → ℝ) :=
  diagonal d * L * diagonal d

def weightedHeatKernel (L : Matrix V V ℝ) (d : V → ℝ) (t : ℝ) : Matrix V V ℝ :=
  diagonal d * exp (-t • symmetricGenerator L d) * diagonal d

lemma weightedHeatKernel_generator (L : Matrix V V ℝ) (d : V → ℝ) (t : ℝ) :
    weightedHeatKernel L d t =
      exp (-t • weightedGenerator L d) * diagonal (fun i => d i * d i) := by
  have hs : SemiconjBy (diagonal d) (symmetricGenerator L d) (weightedGenerator L d) := by
    dsimp [SemiconjBy, symmetricGenerator, weightedGenerator]
    rw [← diagonal_mul_diagonal]
    simp only [Matrix.mul_assoc]
  have he := (hs.smul_right (-t)).exp_right
  change diagonal d * exp (-t • symmetricGenerator L d) =
    exp (-t • weightedGenerator L d) * diagonal d at he
  unfold weightedHeatKernel
  rw [he, Matrix.mul_assoc, diagonal_mul_diagonal]

lemma weightedHeatKernel_zero (L : Matrix V V ℝ) (d : V → ℝ) :
    weightedHeatKernel L d 0 = diagonal (fun i => d i * d i) := by
  simp [weightedHeatKernel, diagonal_mul_diagonal]

lemma weightedHeatKernel_hasDerivAt (L : Matrix V V ℝ) (d : V → ℝ) (t : ℝ) :
    HasDerivAt (weightedHeatKernel L d)
      (-weightedGenerator L d * weightedHeatKernel L d t) t := by
  have hh := (hasDerivAt_exp_smul_const' (-weightedGenerator L d) t).mul_const
    (diagonal (fun i => d i * d i))
  convert hh using 1
  all_goals first
    | rfl
    | (simp only [weightedHeatKernel_generator, smul_neg, neg_smul, Matrix.mul_assoc]; rfl)
    | (funext s; simp only [weightedHeatKernel_generator, smul_neg, neg_smul]; rfl)

lemma weightedHeatKernel_continuous (L : Matrix V V ℝ) (d : V → ℝ) :
    Continuous (weightedHeatKernel L d) :=
  continuous_iff_continuousAt.mpr (fun t => (weightedHeatKernel_hasDerivAt L d t).continuousAt)

lemma symmetricGenerator_symmetric (L : Matrix V V ℝ) (hL : L.IsSymm) (d : V → ℝ) :
    (symmetricGenerator L d).IsSymm := by
  unfold symmetricGenerator Matrix.IsSymm
  simp only [Matrix.transpose_mul, Matrix.diagonal_transpose, hL.eq, Matrix.mul_assoc]

lemma weightedHeatKernel_symmetric (L : Matrix V V ℝ) (hL : L.IsSymm) (d : V → ℝ) (t : ℝ) :
    (weightedHeatKernel L d t).IsSymm := by
  unfold weightedHeatKernel Matrix.IsSymm
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.diagonal_transpose,
    ← Matrix.exp_transpose, Matrix.transpose_smul, (symmetricGenerator_symmetric L hL d).eq]
  simp only [Matrix.mul_assoc]

lemma weightedHeatKernel_semigroup (L : Matrix V V ℝ) (d μ : V → ℝ)
    (hdμ : ∀ i, d i * μ i * d i = 1) (s t : ℝ) :
    weightedHeatKernel L d (s+t) =
      weightedHeatKernel L d s * diagonal μ * weightedHeatKernel L d t := by
  have he : diagonal d * diagonal μ * diagonal d = (1 : Matrix V V ℝ) := by
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
    ext i j
    simp only [diagonal_apply, Matrix.one_apply]
    split_ifs <;> simp_all
  have hexp : exp (-(s+t) • symmetricGenerator L d) =
      exp (-s • symmetricGenerator L d) * exp (-t • symmetricGenerator L d) := by
    rw [neg_add, add_smul]
    exact Matrix.exp_add_of_commute _ _ (((Commute.refl (symmetricGenerator L d)).smul_left (-s)).smul_right (-t))
  unfold weightedHeatKernel
  rw [hexp]
  calc
    _ = diagonal d * exp (-s • symmetricGenerator L d) *
        (diagonal d * diagonal μ * diagonal d) * exp (-t • symmetricGenerator L d) * diagonal d := by
      rw [he]
      simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

lemma symmetricGenerator_posSemidef (L : Matrix V V ℝ) (hL : L.PosSemidef) (d : V → ℝ) :
    (symmetricGenerator L d).PosSemidef := by
  simpa only [symmetricGenerator, Matrix.diagonal_conjTranspose, star_trivial] using
    hL.conjTranspose_mul_mul_same (diagonal d)

lemma weightedHeatKernel_entry_hasDerivAt (L : Matrix V V ℝ) (d : V → ℝ)
    (t : ℝ) (i v : V) :
    HasDerivAt (fun s => weightedHeatKernel L d s i v)
      (-(d i * d i) * (L *ᵥ fun j => weightedHeatKernel L d t j v) i) t := by
  have hh := hasDerivAt_pi.mp (hasDerivAt_pi.mp (weightedHeatKernel_hasDerivAt L d t) i) v
  convert hh using 1
  first
    | rfl
    | (simp only [weightedGenerator, neg_mul, Matrix.mul_assoc]
       rw [Matrix.neg_apply, Matrix.diagonal_mul]
       rfl)


lemma weightedHeatKernel_pos (L : Matrix V V ℝ) (d : V → ℝ)
    (hd : ∀ i, 0 < d i) (hL : ∀ i j, i ≠ j → L i j < 0)
    (t : ℝ) (ht : 0 < t) (i j : V) : 0 < weightedHeatKernel L d t i j := by
  rw [weightedHeatKernel_generator, Matrix.mul_diagonal]
  apply mul_pos _ (mul_pos (hd j) (hd j))
  apply matrix_exp_pos_of_offdiag
  intro a b hab
  change 0 < -t * (weightedGenerator L d a b)
  rw [weightedGenerator, Matrix.diagonal_mul]
  exact mul_pos_of_neg_of_neg (neg_lt_zero.mpr ht)
    (mul_neg_of_pos_of_neg (mul_pos (hd a) (hd a)) (hL a b hab))

lemma weightedHeatKernel_tendsto (L : Matrix V V ℝ) (hL : L.PosSemidef) (d : V → ℝ) :
    Tendsto (weightedHeatKernel L d) atTop
      (𝓝 (diagonal d * spectralKernelProjection (symmetricGenerator L d)
        (symmetricGenerator_posSemidef L hL d).1 * diagonal d)) := by
  exact ((matrix_exp_neg_tendsto _ (symmetricGenerator_posSemidef L hL d)).const_mul
    (diagonal d)).mul_const (diagonal d)

lemma weightedHeatKernel_limit_ker (L : Matrix V V ℝ) (hL : L.IsHermitian) (d : V → ℝ)
    (hd : ∀ i, d i ≠ 0) :
    L * (diagonal d * spectralKernelProjection (symmetricGenerator L d)
      (Matrix.isHermitian_iff_isSymm.mpr (symmetricGenerator_symmetric L
        (Matrix.isHermitian_iff_isSymm.mp hL) d)) * diagonal d) = 0 := by
  let hS : (symmetricGenerator L d).IsHermitian :=
    Matrix.isHermitian_iff_isSymm.mpr (symmetricGenerator_symmetric L
      (Matrix.isHermitian_iff_isSymm.mp hL) d)
  let Z := spectralKernelProjection (symmetricGenerator L d) hS
  change L * (diagonal d * Z * diagonal d) = 0
  have hz : diagonal d * (L * (diagonal d * Z * diagonal d)) = 0 := by
    calc
      _ = symmetricGenerator L d * Z * diagonal d := by
        simp only [symmetricGenerator, Matrix.mul_assoc]
      _ = 0 := by rw [mul_spectralKernelProjection, Matrix.zero_mul]
  ext i j
  have hh := congrFun₂ hz i j
  rw [Matrix.diagonal_mul] at hh
  exact (mul_eq_zero.mp hh).resolve_left (hd i)

end WeightedHeat

end SubpolynomialLp

end

end OAI
