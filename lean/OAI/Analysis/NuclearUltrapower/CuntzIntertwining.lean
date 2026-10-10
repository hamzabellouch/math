import OAI.Analysis.NuclearUltrapower.CuntzWords

namespace OAI

section

noncomputable section
open Filter
open scoped TensorProduct InnerProductSpace Topology
namespace NuclearUltrapower.CuntzAveraging
open CuntzModel CuntzWords CuntzUniversal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (R : Algebra →⋆ₙₐ[ℂ] (H →L[ℂ] H))

def rowSum (N : ℕ) : H →L[ℂ] Target H := ∑ k ∈ Finset.range N, row R k

@[simp] theorem rowSum_apply (N : ℕ) (x : H) :
    rowSum R N x = ∑ k ∈ Finset.range N, row R k x := by simp only [rowSum,sum_apply]

theorem inner_rows (n m : ℕ) (x y : H) :
    ⟪row R n x,row R m y⟫_ℂ = if n = m then ⟪x,R 1 y⟫_ℂ else 0 := by
  split_ifs with h
  · subst m; exact inner_row R n x y
  · exact inner_row_ne R h x y

theorem inner_rowSum (N : ℕ) (x y : H) :
    ⟪rowSum R N x, rowSum R N y⟫_ℂ = (N : ℂ) * ⟪x,R 1 y⟫_ℂ := by
  simp only [rowSum_apply,sum_inner,inner_sum,inner_rows,Finset.sum_ite_eq',
    Finset.sum_ite_mem,Finset.sum_const,Finset.inter_self,Finset.card_range,nsmul_eq_mul]

theorem rowSum_norm_sq (N : ℕ) (x : H) :
    ‖rowSum R N x‖^2 = (N : ℝ) * ‖R 1 x‖^2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ),inner_rowSum,← support_inner]
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  simp

/-- Square-length averages avoid square-root denominators while retaining the
exact isometry on the support of an arbitrary nonunital representation. -/
def weight (n : ℕ) : ℂ := (((n : ℝ)+1)⁻¹ : ℝ)

@[simp] theorem weight_norm (n : ℕ) : ‖weight n‖ = ((n : ℝ)+1)⁻¹ := by
  rw [weight,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]

def averaged (n : ℕ) : H →L[ℂ] Target H := weight n • rowSum R ((n+1)^2)

@[simp] theorem averaged_norm (n : ℕ) (x : H) : ‖averaged R n x‖ = ‖R 1 x‖ := by
  have hn : (n : ℝ)+1 ≠ 0 := by positivity
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change ‖weight n • rowSum R ((n+1)^2) x‖^2 = _
  simp only [norm_smul,weight_norm,mul_pow,rowSum_norm_sq,
    Nat.cast_pow,Nat.cast_add,Nat.cast_one]
  field_simp

theorem averaged_norm_le (n : ℕ) : ‖averaged R n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul,averaged_norm]
  exact support_norm_le R x

omit [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] in
theorem range_telescope {E : Type*} [AddCommGroup E] (f : ℕ → E) (N : ℕ) :
    ∑ k ∈ Finset.range N, (f k - f (k+1)) = f 0 - f N := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ,ih]; abel

omit [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] in
theorem range_telescope_rev {E : Type*} [AddCommGroup E] (f : ℕ → E) (N : ℕ) :
    ∑ k ∈ Finset.range N, (f (k+1) - f k) = f N - f 0 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ,ih]; abel

/-- Only two boundary rows survive for a generator. -/
theorem rowSum_generator (N : ℕ) (i : Fin 2) :
    (rowSum R N).comp (R (generator i)) - (left i).comp (rowSum R N) =
      ((row R 0)-(row R N)).comp (R (generator i)) := by
  ext x
  simp only [sub_apply,ContinuousLinearMap.comp_apply,rowSum_apply,map_sum]
  have he (k : ℕ) : left i (row R k x) = row R (k+1) (R (generator i) x) :=
    congrArg (fun T : H →L[ℂ] Target H => T x) (row_next_generator R k i).symm
  simp_rw [he]
  rw [← Finset.sum_sub_distrib,range_telescope]

/-- The adjoint generator has the same two-boundary estimate. -/
theorem rowSum_adjoint (N : ℕ) (i : Fin 2) :
    (rowSum R N).comp (star (R (generator i))) - (star (left i)).comp (rowSum R N) =
      (star (left i)).comp ((row R N)-(row R 0)) := by
  ext x
  simp only [ContinuousLinearMap.comp_apply,sub_apply,rowSum_apply,map_sum,map_sub]
  have he (k : ℕ) : row R k (star (R (generator i)) x) =
      star (left (H := H) i) (row R (k+1) x) :=
    congrArg (fun T : H →L[ℂ] Target H => T x) (left_star_row_next R k i).symm
  simp_rw [he]
  rw [← Finset.sum_sub_distrib]
  exact range_telescope_rev (fun k => star (left (H := H) i) (row R k x)) N

end NuclearUltrapower.CuntzAveraging
end
end

section

noncomputable section
open Filter
open scoped Topology
namespace NuclearUltrapower

/-- A uniformly bounded sequence of linear maps converges to zero everywhere
once it does so on a dense range. This elementary argument requires no
separability or pointwise boundedness theorem. -/
theorem dense_bounded_tendsto_zero {A E P : Type*}
    [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (D : ℕ → A →ₗ[ℂ] E) (C : ℝ) (hC : 0 < C)
    (hbound : ∀ n a, ‖D n a‖ ≤ C * ‖a‖)
    (g : P → A) (hg : DenseRange g)
    (hlim : ∀ p, Tendsto (fun n => D n (g p)) atTop (𝓝 0)) (a : A) :
    Tendsto (fun n => D n a) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨p,hp⟩ := hg.exists_dist_lt a (show 0 < ε/(2*C) by positivity)
  have hev := Metric.tendsto_nhds.mp (hlim p) (ε/2) (by positivity)
  filter_upwards [hev] with n hn
  rw [dist_zero_right] at hn ⊢
  rw [dist_eq_norm] at hp
  have hb : C * ‖a - g p‖ < ε/2 := by
    have hh := (lt_div_iff₀ (show 0 < 2*C by positivity)).mp hp
    nlinarith
  calc
    ‖D n a‖ = ‖D n (a-g p) + D n (g p)‖ := by rw [← map_add,sub_add_cancel]
    _ ≤ ‖D n (a-g p)‖ + ‖D n (g p)‖ := norm_add_le _ _
    _ ≤ C*‖a-g p‖ + ‖D n (g p)‖ := add_le_add (hbound n _) le_rfl
    _ < ε := by linarith

section Defects
variable {A H K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (R : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (T : A →⋆ₙₐ[ℂ] (K →L[ℂ] K))

def intertwiningDefect (W : H →L[ℂ] K) : A →ₗ[ℂ] (H →L[ℂ] K) where
  toFun a := W.comp (R a) - (T a).comp W
  map_add' a b := by
    simp only [map_add,ContinuousLinearMap.comp_add,ContinuousLinearMap.add_comp]
    abel
  map_smul' c a := by
    simp only [map_smul,ContinuousLinearMap.comp_smul,ContinuousLinearMap.smul_comp,smul_sub,RingHom.id_apply]

@[simp] theorem intertwiningDefect_apply (W : H →L[ℂ] K) (a : A) :
    intertwiningDefect R T W a = W.comp (R a) - (T a).comp W := rfl

theorem intertwiningDefect_bound (W : H →L[ℂ] K) (hW : ‖W‖ ≤ 1) (a : A) :
    ‖intertwiningDefect R T W a‖ ≤ 2 * ‖a‖ := by
  have hR := NonUnitalStarAlgHom.norm_apply_le R a
  have hT := NonUnitalStarAlgHom.norm_apply_le T a
  calc
    _ ≤ ‖W.comp (R a)‖ + ‖(T a).comp W‖ := norm_sub_le _ _
    _ ≤ ‖W‖*‖R a‖ + ‖T a‖*‖W‖ :=
      add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.opNorm_comp_le _ _)
    _ ≤ 2*‖a‖ := by
      have h₁ := mul_le_mul hW hR (norm_nonneg _) zero_le_one
      have h₂ := mul_le_mul hT hW (norm_nonneg _) (norm_nonneg _)
      nlinarith

theorem intertwiningDefect_mul (W : H →L[ℂ] K) (a b : A) :
    intertwiningDefect R T W (a*b) =
      (intertwiningDefect R T W a).comp (R b) + (T a).comp (intertwiningDefect R T W b) := by
  ext x
  simp only [intertwiningDefect_apply,ContinuousLinearMap.comp_apply,map_mul,
    mul_apply_eq_comp,sub_apply,add_apply,map_sub]
  abel

/-- Approximate intertwining propagates through products without any finite
coordinate relation being silently imposed. -/
theorem intertwiningDefect_tendsto_mul (W : ℕ → H →L[ℂ] K) {a b : A}
    (ha : Tendsto (fun n => intertwiningDefect R T (W n) a) atTop (𝓝 0))
    (hb : Tendsto (fun n => intertwiningDefect R T (W n) b) atTop (𝓝 0)) :
    Tendsto (fun n => intertwiningDefect R T (W n) (a*b)) atTop (𝓝 0) := by
  have hc₁ : Continuous (fun U : H →L[ℂ] K => U.comp (R b)) := by fun_prop
  have hc₂ : Continuous (fun U : H →L[ℂ] K => (T a).comp U) := by fun_prop
  have hh := (hc₁.continuousAt.tendsto.comp ha).add (hc₂.continuousAt.tendsto.comp hb)
  simpa only [Function.comp_def,ContinuousLinearMap.zero_comp,ContinuousLinearMap.comp_zero,
    add_zero,← intertwiningDefect_mul] using hh
end Defects
end NuclearUltrapower
end
end

section

noncomputable section
open Filter
open scoped TensorProduct InnerProductSpace Topology
namespace NuclearUltrapower.CuntzAveraging
open CuntzModel CuntzWords CuntzUniversal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (R : Algebra →⋆ₙₐ[ℂ] (H →L[ℂ] H))

local instance : IsBoundedSMul ℂ (CuntzModel.Space ⊗[ℂ] H) := NormedSpace.toIsBoundedSMul
local instance : NormedSpace ℂ (Target H) := inferInstance

def concrete : Algebra →⋆ₐ[ℂ] (Space →L[ℂ] Space) :=
  modelMap shift CuntzModel.relations

def amplified : Algebra →⋆ₐ[ℂ] (Target H →L[ℂ] Target H) :=
  tensorLeftHom.comp concrete

@[simp] theorem amplified_generator (i : Fin 2) : amplified (H := H) (generator i) = left i := by
  change tensorLeftHom (concrete (generator i)) = _
  rw [concrete,modelMap_generator]
  rfl

abbrev defect (n : ℕ) : Algebra →ₗ[ℂ] (H →L[ℂ] Target H) :=
  intertwiningDefect R amplified.toNonUnitalStarAlgHom (averaged R n)

@[simp] theorem averaged_support (n : ℕ) : (averaged R n).comp (R 1) = averaged R n := by
  ext x
  change weight n • (rowSum R ((n+1)^2) (R 1 x)) =
    weight n • (rowSum R ((n+1)^2) x)
  congr 1
  simp only [rowSum_apply]
  apply Finset.sum_congr rfl
  intro k _
  exact congrArg (fun T : H →L[ℂ] Target H => T x) (row_support R k)

@[simp] theorem defect_one (n : ℕ) : defect R n 1 = 0 := by
  change (averaged R n).comp (R 1) - (amplified 1).comp (averaged R n) = 0
  rw [averaged_support,map_one]
  change averaged R n - (ContinuousLinearMap.id ℂ _).comp (averaged R n) = 0
  rw [ContinuousLinearMap.id_comp,sub_self]

theorem generator_norm_le (i : Fin 2) : ‖generator i‖ ≤ 1 := by
  simpa [CuntzPolynomial.evalLetter] using
    CuntzPolynomial.evalLetter_norm_le generator CuntzUniversal.relations (i,false)

theorem rowSum_generator_bound (N : ℕ) (i : Fin 2) :
    ‖(rowSum R N).comp (R (generator i)) - (left i).comp (rowSum R N)‖ ≤ 2 := by
  rw [rowSum_generator]
  have hrow : ‖row R 0 - row R N‖ ≤ 2 :=
    (norm_sub_le (row R 0) (row R N)).trans (by linarith [row_norm_le R 0,row_norm_le R N])
  have hRi : ‖R (generator i)‖ ≤ 1 :=
    (NonUnitalStarAlgHom.norm_apply_le R _).trans (generator_norm_le i)
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by nlinarith [norm_nonneg (row R 0-row R N),norm_nonneg (R (generator i))])

theorem rowSum_adjoint_bound (N : ℕ) (i : Fin 2) :
    ‖(rowSum R N).comp (star (R (generator i))) - (star (left i)).comp (rowSum R N)‖ ≤ 2 := by
  rw [rowSum_adjoint]
  have hrow : ‖row R N - row R 0‖ ≤ 2 :=
    (norm_sub_le (row R N) (row R 0)).trans (by linarith [row_norm_le R N,row_norm_le R 0])
  have hleft : ‖star (left (H := H) i)‖ ≤ 1 := by
    exact (norm_star (left (H := H) i)).le.trans (left_norm_le i)
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by nlinarith [norm_nonneg (row R N-row R 0),norm_nonneg (star (left (H := H) i))])

theorem defect_generator_bound (n : ℕ) (i : Fin 2) :
    ‖defect R n (generator i)‖ ≤ ((n : ℝ)+1)⁻¹ * 2 := by
  have he : defect R n (generator i) = weight n •
      ((rowSum R ((n+1)^2)).comp (R (generator i)) - (left i).comp (rowSum R ((n+1)^2))) := by
    ext x
    change weight n • (rowSum R ((n+1)^2) (R (generator i) x)) -
      amplified (generator i) (weight n • rowSum R ((n+1)^2) x) =
      weight n • (rowSum R ((n+1)^2) (R (generator i) x) - left (H := H) i (rowSum R ((n+1)^2) x))
    rw [amplified_generator,map_smul,smul_sub]
  rw [he,norm_smul,weight_norm]
  exact mul_le_mul_of_nonneg_left (rowSum_generator_bound R _ i) (by positivity)

theorem defect_adjoint_bound (n : ℕ) (i : Fin 2) :
    ‖defect R n (star (generator i))‖ ≤ ((n : ℝ)+1)⁻¹ * 2 := by
  have he : defect R n (star (generator i)) = weight n •
      ((rowSum R ((n+1)^2)).comp (star (R (generator i))) -
        (star (left i)).comp (rowSum R ((n+1)^2))) := by
    ext x
    change weight n • (rowSum R ((n+1)^2) (R (star (generator i)) x)) -
      amplified (star (generator i)) (weight n • rowSum R ((n+1)^2) x) =
      weight n • (rowSum R ((n+1)^2) (star (R (generator i)) x) - star (left (H := H) i) (rowSum R ((n+1)^2) x))
    rw [map_star,map_star,amplified_generator,map_smul,smul_sub]
  rw [he,norm_smul,weight_norm]
  exact mul_le_mul_of_nonneg_left (rowSum_adjoint_bound R _ i) (by positivity)

theorem inverse_weight_tendsto : Tendsto (fun n : ℕ => ((n : ℝ)+1)⁻¹ * 2) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ)+1) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  simpa only [zero_mul,Function.comp_def] using (tendsto_inv_atTop_zero.comp ht).mul_const 2

theorem defect_generator_tendsto (i : Fin 2) :
    Tendsto (fun n => defect R n (generator i)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero (fun n => norm_nonneg _) (fun n => defect_generator_bound R n i)
    inverse_weight_tendsto

theorem defect_adjoint_tendsto (i : Fin 2) :
    Tendsto (fun n => defect R n (star (generator i))) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero (fun n => norm_nonneg _) (fun n => defect_adjoint_bound R n i)
    inverse_weight_tendsto

/-- Second-coordinate intertwining is exact, even for a degenerate range. -/
theorem averaged_commuting (n : ℕ) (T : H →L[ℂ] H)
    (hT : ∀ a, Commute (R a) T) :
    (averaged R n).comp T = (right T).comp (averaged R n) := by
  ext x
  change weight n • rowSum R ((n+1)^2) (T x) =
    right T (weight n • rowSum R ((n+1)^2) x)
  rw [map_smul]
  congr 1
  simp only [rowSum_apply,map_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact congrArg (fun U : H →L[ℂ] Target H => U x) (row_commuting R k T hT)

end NuclearUltrapower.CuntzAveraging
end
end

end OAI
