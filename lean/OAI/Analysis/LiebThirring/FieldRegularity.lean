import OAI.Analysis.LiebThirring.RankOne

namespace OAI

universe u25 u26 u27 u28 u29 u30 u31

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
open Matrix
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
noncomputable section
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace SharpLiebThirring.MatrixProof
open Matrix
open scoped Matrix.Norms.L2Operator
variable {n : Type u25} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
lemma hsSquared_nonneg (A : Matrix n n ℂ) : 0 ≤ hsSquared A := by
  exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ Complex.normSq_nonneg _

def flattenCLM : Matrix n n ℂ →L[ℝ] EuclideanSpace ℂ (n × n) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A ↦ WithLp.toLp 2 (fun ij ↦ A ij.1 ij.2)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

def unflattenCLM : EuclideanSpace ℂ (n × n) →L[ℝ] Matrix n n ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v i j ↦ v (i, j)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

omit [DecidableEq n] in
@[simp] lemma unflatten_flatten (A : Matrix n n ℂ) : unflattenCLM (flattenCLM A) = A := rfl

omit [DecidableEq n] in
lemma flatten_norm_sq (A : Matrix n n ℂ) : ‖flattenCLM A‖ ^ 2 = hsSquared A := by
  rw [EuclideanSpace.norm_sq_eq, hsSquared, Fintype.sum_prod_type]
  change (∑ i, ∑ j, ‖A i j‖ ^ 2) = _
  simp only [Complex.sq_norm]


lemma cfc_lipschitz_norm {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    {f : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ x ∈ spectrum ℝ A, ∀ y ∈ spectrum ℝ B, |f x - f y| ≤ L * |x - y|) :
    ‖cfc f A - cfc f B‖ ≤
      (‖(unflattenCLM : EuclideanSpace ℂ (n × n) →L[ℝ] Matrix n n ℂ)‖ *
        ‖(flattenCLM : Matrix n n ℂ →L[ℝ] EuclideanSpace ℂ (n × n))‖) * L * ‖A - B‖ := by
  have hs := hsSquared_cfc_sub hA hB f L hL
    (fun i j ↦ hf _ (hA.eigenvalues_mem_spectrum_real i) _ (hB.eigenvalues_mem_spectrum_real j))
  rw [← hA.cfc_eq, ← hB.cfc_eq, ← flatten_norm_sq, ← flatten_norm_sq] at hs
  have h1 : ‖flattenCLM (cfc f A - cfc f B)‖ ≤ L * ‖flattenCLM (A - B)‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hL (norm_nonneg _))).1
    simpa only [mul_pow] using hs
  calc
    _ = ‖unflattenCLM (flattenCLM (cfc f A - cfc f B))‖ := rfl
    _ ≤ ‖unflattenCLM (n := n)‖ * ‖flattenCLM (cfc f A - cfc f B)‖ := (unflattenCLM (n := n)).le_opNorm _
    _ ≤ ‖unflattenCLM (n := n)‖ * (L * (‖flattenCLM (n := n)‖ * ‖A - B‖)) := by
      exact mul_le_mul_of_nonneg_left (h1.trans
        (mul_le_mul_of_nonneg_left ((flattenCLM (n := n)).le_opNorm _) hL)) (norm_nonneg _)
    _ = _ := by ring

end SharpLiebThirring.MatrixProof
namespace SharpLiebThirring.MatrixProof
open Matrix
open scoped Matrix.Norms.L2Operator
variable {n : Type u26} [Fintype n] [DecidableEq n]

lemma mixed_left_cfc_apply {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (V : unitary (Matrix n n ℂ)) (f : ℝ → ℝ) (i j : n) :
    (star (hA.eigenvectorUnitary : Matrix n n ℂ) * cfc f A * (V : Matrix n n ℂ)) i j =
      (f (hA.eigenvalues i) : ℂ) *
        (star (hA.eigenvectorUnitary : Matrix n n ℂ) * (V : Matrix n n ℂ)) i j := by
  rw [hA.cfc_eq]
  change (star (hA.eigenvectorUnitary : Matrix n n ℂ) *
    ((hA.eigenvectorUnitary : Matrix n n ℂ) * diagonal (fun i ↦ (f (hA.eigenvalues i) : ℂ)) *
      star (hA.eigenvectorUnitary : Matrix n n ℂ)) * (V : Matrix n n ℂ)) i j = _
  simp only [← mul_assoc, Unitary.coe_star_mul_self, one_mul]
  rw [mul_assoc, diagonal_mul]

lemma mixed_right_cfc_apply {B : Matrix n n ℂ} (hB : B.IsHermitian)
    (U : unitary (Matrix n n ℂ)) (g : ℝ → ℝ) (i j : n) :
    (star (U : Matrix n n ℂ) * cfc g B * (hB.eigenvectorUnitary : Matrix n n ℂ)) i j =
      (g (hB.eigenvalues j) : ℂ) *
        (star (U : Matrix n n ℂ) * (hB.eigenvectorUnitary : Matrix n n ℂ)) i j := by
  rw [hB.cfc_eq]
  change (star (U : Matrix n n ℂ) *
    ((hB.eigenvectorUnitary : Matrix n n ℂ) * diagonal (fun j ↦ (g (hB.eigenvalues j) : ℂ)) *
      star (hB.eigenvectorUnitary : Matrix n n ℂ)) * (hB.eigenvectorUnitary : Matrix n n ℂ)) i j = _
  simp only [mul_assoc, Unitary.coe_star_mul_self, mul_one]
  rw [← mul_assoc, mul_diagonal, mul_comm]

lemma real_star_mul_real (x y : ℝ) (z : ℂ) :
    (star ((x : ℂ) * z) * ((y : ℂ) * z)).re = x * y * Complex.normSq z := by
  simp [Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

lemma trace_cfc_product {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (f g : ℝ → ℝ) :
    (trace (cfc f A * cfc g B)).re =
      ∑ i, ∑ j, f (hA.eigenvalues i) * g (hB.eigenvalues j) *
        Complex.normSq ((star (hA.eigenvectorUnitary : Matrix n n ℂ) *
          (hB.eigenvectorUnitary : Matrix n n ℂ)) i j) := by
  have hF : (cfc f A).IsHermitian := (cfc_predicate f A).isHermitian
  rw [← hF.star_eq, ← trace_star_mul_change hA.eigenvectorUnitary hB.eigenvectorUnitary,
    trace_star_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [mixed_left_cfc_apply, mixed_right_cfc_apply, real_star_mul_real]

lemma trace_taylor_identity {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (F f : ℝ → ℝ) :
    (trace (cfc F B)).re - (trace (cfc F A)).re - (trace (cfc f A * (B - A))).re =
      ∑ i, ∑ j, (F (hB.eigenvalues j) - F (hA.eigenvalues i) -
        f (hA.eigenvalues i) * (hB.eigenvalues j - hA.eigenvalues i)) *
        Complex.normSq ((star (hA.eigenvectorUnitary : Matrix n n ℂ) *
          (hB.eigenvectorUnitary : Matrix n n ℂ)) i j) := by
  have h₁ := trace_cfc_product hA hB (fun _ ↦ 1) F
  have h₂ := trace_cfc_product hA hB F (fun _ ↦ 1)
  have h₃ := trace_cfc_product hA hB f id
  have h₄ := trace_cfc_product hA hB (fun x ↦ f x * x) (fun _ ↦ 1)
  have hcA : cfc (fun _ : ℝ ↦ 1) A = 1 := by
    erw [cfc_const (1 : ℝ) A hA]; simp
  have hcB : cfc (fun _ : ℝ ↦ 1) B = 1 := by
    erw [cfc_const (1 : ℝ) B hB]; simp
  rw [hcA, one_mul] at h₁
  rw [hcB, mul_one] at h₂ h₄
  erw [cfc_id ℝ B hB] at h₃
  have hm : cfc (fun x ↦ f x * x) A = cfc f A * A := by
    erw [cfc_mul f id A (A.finite_real_spectrum.continuousOn f)
      (by fun_prop), cfc_id ℝ A hA]
  rw [hm] at h₄
  rw [mul_sub, trace_sub, Complex.sub_re, h₁, h₂, h₃, h₄]
  simp only [id_eq, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma trace_taylor_bound {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    {F f : ℝ → ℝ} {L : ℝ}
    (hF : ∀ x ∈ spectrum ℝ A, ∀ y ∈ spectrum ℝ B,
      |F y - F x - f x * (y - x)| ≤ L * (y - x) ^ 2) :
    |(trace (cfc F B)).re - (trace (cfc F A)).re - (trace (cfc f A * (B - A))).re| ≤
      L * hsSquared (B - A) := by
  let U := hA.eigenvectorUnitary
  let V := hB.eigenvectorUnitary
  have hm (i j : n) :
      (star (U : Matrix n n ℂ) * (B - A) * (V : Matrix n n ℂ)) i j =
        ((hB.eigenvalues j - hA.eigenvalues i : ℝ) : ℂ) *
          (star (U : Matrix n n ℂ) * (V : Matrix n n ℂ)) i j := by
    have ha : A = conjStarAlgAut ℂ (Matrix n n ℂ) U
        (diagonal (fun i ↦ (hA.eigenvalues i : ℂ))) := hA.spectral_theorem
    have hb : B = conjStarAlgAut ℂ (Matrix n n ℂ) V
        (diagonal (fun i ↦ (hB.eigenvalues i : ℂ))) := hB.spectral_theorem
    have hh := mixed_diagonal_sub_apply U V hA.eigenvalues hB.eigenvalues i j
    rw [← ha, ← hb] at hh
    rw [← neg_sub A B, Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply, hh]
    simp only [Complex.ofReal_sub]
    ring
  rw [trace_taylor_identity hA hB, ← hsSquared_change U V (B - A)]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  simp only [hsSquared, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro j _
  rw [hm, Complex.normSq_mul, Complex.normSq_ofReal, abs_mul,
    abs_of_nonneg (Complex.normSq_nonneg _)]
  have hh := hF _ (hA.eigenvalues_mem_spectrum_real i) _ (hB.eigenvalues_mem_spectrum_real j)
  have hp := mul_le_mul_of_nonneg_right hh
    (Complex.normSq_nonneg ((star (U : Matrix n n ℂ) * (V : Matrix n n ℂ)) i j))
  nlinarith [hp]

end SharpLiebThirring.MatrixProof

open scoped NNReal
namespace SharpLiebThirring.ScalarProof
open Set
lemma primitive_lipschitz {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) :
    LipschitzWith ⟨δ ^ (σ - 3 / 2), Real.rpow_nonneg hδ.le _⟩
      (regularizedPrimitive σ δ) := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x ↦ (primitive_hasDerivAt σ hδ x).differentiableAt)
  intro x
  rw [(primitive_hasDerivAt σ hδ x).deriv]
  change ‖(max x 0 + δ) ^ (σ - 3 / 2)‖ ≤ δ ^ (σ - 3 / 2)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  exact Real.rpow_le_rpow_of_nonpos hδ (by have := le_max_right x 0; linarith) (by linarith)

lemma scalar_trace_taylor {F f : ℝ → ℝ} {C : ℝ≥0}
    (hF : ∀ x, HasDerivAt F (f x) x) (hf : LipschitzWith C f) (x y : ℝ) :
    |F y - F x - f x * (y - x)| ≤ (C : ℝ) * (y - x) ^ 2 := by
  have hd (t : ℝ) (_ : t ∈ uIcc x y) :
      HasDerivWithinAt (fun t ↦ F t - F x - f x * (t - x))
        (f t - f x) (uIcc x y) t := by
    convert! ((hF t).sub_const (F x) |>.sub
      (((hasDerivAt_id t).sub_const x).const_mul (f x))).hasDerivWithinAt using 1
    simp
  have hb (t : ℝ) (ht : t ∈ uIcc x y) : ‖f t - f x‖ ≤ (C : ℝ) * ‖y - x‖ := by
    exact (hf.norm_sub_le t x).trans (mul_le_mul_of_nonneg_left
      (abs_sub_left_of_mem_uIcc ht) C.coe_nonneg)
  have hh := (convex_uIcc x y).norm_image_sub_le_of_norm_hasDerivWithin_le
    hd hb (left_mem_uIcc) (right_mem_uIcc)
  simpa only [sub_self, mul_zero, sub_zero, Real.norm_eq_abs, mul_assoc, ← sq, sq_abs] using hh

/-- The second scalar primitive used for the matrix trace potential. -/
def secondPrimitive (σ δ y : ℝ) : ℝ := ∫ t in 0..y, regularizedPrimitive σ δ t

lemma secondPrimitive_hasDerivAt (σ : ℝ) {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    HasDerivAt (secondPrimitive σ δ) (regularizedPrimitive σ δ y) y := by
  exact intervalIntegral.integral_hasDerivAt_right
    ((primitive_differentiable σ hδ).continuous.intervalIntegrable 0 y)
    (primitive_differentiable σ hδ).continuous.stronglyMeasurable.stronglyMeasurableAtFilter
    (primitive_differentiable σ hδ).continuous.continuousAt

end SharpLiebThirring.ScalarProof

namespace SharpLiebThirring.MatrixProof
open Matrix ScalarProof Asymptotics Filter
open scoped Matrix.Norms.L2Operator Topology
variable {n : Type u27} [Fintype n] [DecidableEq n]

def hermitianInclusion : selfAdjoint (Matrix n n ℂ) →L[ℝ] Matrix n n ℂ :=
  { toFun := Subtype.val
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl
    cont := continuous_subtype_val }

lemma trace_primitive_hasFDerivAt {F f : ℝ → ℝ} {C : ℝ≥0}
    (hF : ∀ x, HasDerivAt F (f x) x) (hf : LipschitzWith C f)
    (A : selfAdjoint (Matrix n n ℂ)) :
    HasFDerivAt (fun B : selfAdjoint (Matrix n n ℂ) ↦ (trace (cfc F (B : Matrix n n ℂ))).re)
      ((tracePairCLM (cfc f (A : Matrix n n ℂ))).comp hermitianInclusion) A := by
  rw [hasFDerivAt_iff_isLittleO]
  apply IsBigO.trans_isLittleO (g := fun B : selfAdjoint (Matrix n n ℂ) ↦ ‖B - A‖ ^ 2)
    ?_ (isLittleO_pow_sub_sub A (by norm_num : 1 < (2 : ℕ)))
  apply IsBigO.of_bound ((C : ℝ) * ‖flattenCLM (n := n)‖ ^ 2)
  filter_upwards [] with B
  have hh := trace_taylor_bound A.property.isHermitian B.property.isHermitian
    (F := F) (f := f) (L := (C : ℝ))
    (fun x _ y _ ↦ scalar_trace_taylor hF hf x y)
  change |(trace (cfc F (B : Matrix n n ℂ))).re - (trace (cfc F (A : Matrix n n ℂ))).re -
    (trace (cfc f (A : Matrix n n ℂ) * ((B : Matrix n n ℂ) - (A : Matrix n n ℂ)))).re| ≤ _
  have hb := (flattenCLM (n := n)).le_opNorm ((B : Matrix n n ℂ) - (A : Matrix n n ℂ))
  have hb2 := sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) |>.2 hb
  rw [flatten_norm_sq, mul_pow] at hb2
  refine hh.trans ((mul_le_mul_of_nonneg_left hb2 C.coe_nonneg).trans_eq ?_)
  change (C : ℝ) * (‖flattenCLM (n := n)‖ ^ 2 * ‖B - A‖ ^ 2) = _
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  ring

lemma trace_secondPrimitive_hasFDerivAt {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (A : selfAdjoint (Matrix n n ℂ)) :
    HasFDerivAt (fun B : selfAdjoint (Matrix n n ℂ) ↦
      (trace (cfc (secondPrimitive σ δ) (B : Matrix n n ℂ))).re)
      ((tracePairCLM (cfc (regularizedPrimitive σ δ) (A : Matrix n n ℂ))).comp hermitianInclusion) A :=
  trace_primitive_hasFDerivAt (secondPrimitive_hasDerivAt σ hδ) (primitive_lipschitz hσ hδ) A

end SharpLiebThirring.MatrixProof

namespace SharpLiebThirring.ScalarProof
open Set
lemma primitive_remainder_lipschitz {σ δ a x r y z : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (ha : 0 < a) (hr : 0 ≤ r) (hxr : a ≤ x - r) (hy : |y| ≤ r) (hz : |z| ≤ r) :
    ‖(regularizedPrimitive σ δ (x + y) - regularizedPrimitive σ δ x -
        (x + δ) ^ (σ - 3 / 2) * y) -
      (regularizedPrimitive σ δ (x + z) - regularizedPrimitive σ δ x -
        (x + δ) ^ (σ - 3 / 2) * z)‖ ≤
      ((3 / 2 - σ) * (a + δ) ^ (σ - 5 / 2) * r) * ‖y - z‖ := by
  have hd (t : ℝ) (ht : t ∈ Icc (-r) r) :
      HasDerivWithinAt (fun t : ℝ ↦ regularizedPrimitive σ δ (x + t) -
        regularizedPrimitive σ δ x - (x + δ) ^ (σ - 3 / 2) * t)
        ((x + t + δ) ^ (σ - 3 / 2) - (x + δ) ^ (σ - 3 / 2)) (Icc (-r) r) t := by
    have hxt : 0 ≤ x + t := by have := ht.1; linarith
    convert! (((primitive_hasDerivAt σ hδ (x + t)).comp t ((hasDerivAt_id t).const_add x)).sub_const
        (regularizedPrimitive σ δ x) |>.sub
        ((hasDerivAt_id t).const_mul ((x + δ) ^ (σ - 3 / 2)))).hasDerivWithinAt using 1
    simp [max_eq_left hxt]
  have hb (t : ℝ) (ht : t ∈ Icc (-r) r) :
      ‖(x + t + δ) ^ (σ - 3 / 2) - (x + δ) ^ (σ - 3 / 2)‖ ≤
        (3 / 2 - σ) * (a + δ) ^ (σ - 5 / 2) * r := by
    have hh := derivative_lipschitz_on_positive hσ hδ ha
      (show a ≤ x + t by have := ht.1; linarith) (show a ≤ x by linarith)
    simp only [add_sub_cancel_left] at hh
    refine hh.trans (mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by linarith)
      (Real.rpow_nonneg (by linarith) _)))
    exact abs_le.2 ht
  exact (convex_Icc (-r) r).norm_image_sub_le_of_norm_hasDerivWithin_le hd hb
    (abs_le.1 hz) (abs_le.1 hy)
end SharpLiebThirring.ScalarProof

namespace SharpLiebThirring.MatrixProof
open Matrix ScalarProof
open scoped Matrix.Norms.L2Operator
variable {n : Type u28} [Fintype n] [DecidableEq n]

def matrixNormBridge (n : Type u29) [Fintype n] [DecidableEq n] : ℝ :=
  ‖(unflattenCLM : EuclideanSpace ℂ (n × n) →L[ℝ] Matrix n n ℂ)‖ *
    ‖(flattenCLM : Matrix n n ℂ →L[ℝ] EuclideanSpace ℂ (n × n))‖

lemma matrixNormBridge_nonneg : 0 ≤ matrixNormBridge n := mul_nonneg (norm_nonneg _) (norm_nonneg _)

lemma cfc_remainder_eq (σ : ℝ) {δ : ℝ} (hδ : 0 < δ) (x : ℝ)
    {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    cfc (fun y : ℝ ↦ regularizedPrimitive σ δ (x + y) -
      regularizedPrimitive σ δ x - (x + δ) ^ (σ - 3 / 2) * y) A =
      cfc (regularizedPrimitive σ δ) (x • 1 + A) -
        regularizedPrimitive σ δ x • 1 - (x + δ) ^ (σ - 3 / 2) • A := by
  have hc := (primitive_differentiable σ hδ).continuous
  erw [cfc_sub (fun y : ℝ ↦ regularizedPrimitive σ δ (x + y) -
      regularizedPrimitive σ δ x) (fun y : ℝ ↦ (x + δ) ^ (σ - 3 / 2) * y) A
      (by fun_prop) (by fun_prop),
    cfc_sub (fun y : ℝ ↦ regularizedPrimitive σ δ (x + y))
      (fun _ : ℝ ↦ regularizedPrimitive σ δ x) A (by fun_prop) (by fun_prop),
    cfc_const (regularizedPrimitive σ δ x) A hA,
    cfc_const_mul_id ((x + δ) ^ (σ - 3 / 2)) A hA,
    Algebra.algebraMap_eq_smul_one, ← cfc_scalar_add _ hc x hA]

lemma cfc_remainder_lipschitz {σ δ a x r : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (ha : 0 < a) (hr : 0 ≤ r) (hxr : a ≤ x - r)
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hnA : ‖A‖ ≤ r) (hnB : ‖B‖ ≤ r) :
    ‖(cfc (regularizedPrimitive σ δ) (x • 1 + A) -
      regularizedPrimitive σ δ x • 1 - (x + δ) ^ (σ - 3 / 2) • A) -
      (cfc (regularizedPrimitive σ δ) (x • 1 + B) -
      regularizedPrimitive σ δ x • 1 - (x + δ) ^ (σ - 3 / 2) • B)‖ ≤
      matrixNormBridge n * ((3 / 2 - σ) * (a + δ) ^ (σ - 5 / 2) * r) * ‖A - B‖ := by
  rw [← cfc_remainder_eq σ hδ x hA, ← cfc_remainder_eq σ hδ x hB]
  apply cfc_lipschitz_norm hA hB (mul_nonneg (mul_nonneg (by linarith)
    (Real.rpow_nonneg (by linarith) _)) hr)
  intro y hy z hz
  exact primitive_remainder_lipschitz hσ hδ ha hr hxr
    ((spectrum_abs_le_matrix_norm hy).trans hnA) ((spectrum_abs_le_matrix_norm hz).trans hnB)

omit [Fintype n] in
lemma quadraticMatrix_sub (C B D : Matrix n n ℂ) (s : ℝ) :
    quadraticMatrix C B s - quadraticMatrix C D s = (-2 * s) • (B - D) := by
  unfold quadraticMatrix
  module

lemma cfc_quadratic_lipschitz {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    {C B D : Matrix n n ℂ} (hC : C.IsHermitian) (hB : B.IsHermitian)
    (hD : D.IsHermitian) (s : ℝ) :
    ‖cfc (regularizedPrimitive σ δ) (quadraticMatrix C B s) -
      cfc (regularizedPrimitive σ δ) (quadraticMatrix C D s)‖ ≤
      matrixNormBridge n * δ ^ (σ - 3 / 2) * (2 * |s|) * ‖B - D‖ := by
  have hh := cfc_lipschitz_norm (quadraticMatrix_hermitian hC hB s)
    (quadraticMatrix_hermitian hC hD s) (Real.rpow_nonneg hδ.le (σ - 3 / 2))
    (fun x _ y _ ↦ (primitive_lipschitz hσ hδ).norm_sub_le x y)
  rw [quadraticMatrix_sub, norm_smul] at hh
  simpa [Real.norm_eq_abs, abs_mul, mul_assoc, matrixNormBridge] using hh

lemma pairedFieldIntegrand_lipschitz_global {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    {C B D : Matrix n n ℂ} (hC : C.IsHermitian) (hB : B.IsHermitian)
    (hD : D.IsHermitian) (s : ℝ) :
    ‖pairedFieldIntegrand σ δ C B s - pairedFieldIntegrand σ δ C D s‖ ≤
      (4 * matrixNormBridge n * δ ^ (σ - 3 / 2) * |s|) * ‖B - D‖ := by
  have he : pairedFieldIntegrand σ δ C B s - pairedFieldIntegrand σ δ C D s =
      (cfc (regularizedPrimitive σ δ) (quadraticMatrix C B s) -
        cfc (regularizedPrimitive σ δ) (quadraticMatrix C D s)) +
      (cfc (regularizedPrimitive σ δ) (quadraticMatrix C B (-s)) -
        cfc (regularizedPrimitive σ δ) (quadraticMatrix C D (-s))) := by
    unfold pairedFieldIntegrand
    abel
  rw [he]
  have h1 := cfc_quadratic_lipschitz hσ hδ hC hB hD s
  have h2 := cfc_quadratic_lipschitz hσ hδ hC hB hD (-s)
  rw [abs_neg] at h2
  linarith [norm_add_le
    (cfc (regularizedPrimitive σ δ) (quadraticMatrix C B s) -
      cfc (regularizedPrimitive σ δ) (quadraticMatrix C D s))
    (cfc (regularizedPrimitive σ δ) (quadraticMatrix C B (-s)) -
      cfc (regularizedPrimitive σ δ) (quadraticMatrix C D (-s)))]

end SharpLiebThirring.MatrixProof

namespace SharpLiebThirring.MatrixProof
open Matrix ScalarProof
open scoped Matrix.Norms.L2Operator
variable {n : Type u30} [Fintype n] [DecidableEq n]

def quadraticRemainder (σ δ : ℝ) (C B : Matrix n n ℂ) (s : ℝ) : Matrix n n ℂ :=
  cfc (regularizedPrimitive σ δ) (quadraticMatrix C B s) -
    regularizedPrimitive σ δ (s ^ 2) • 1 -
    (s ^ 2 + δ) ^ (σ - 3 / 2) • (C - (2 * s) • B)

lemma quadraticRemainder_lipschitz_tail {σ δ M : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    {C B D : Matrix n n ℂ} (hC : C.IsHermitian) (hB : B.IsHermitian) (hD : D.IsHermitian)
    (hBM : ‖B‖ ≤ M) (hDM : ‖D‖ ≤ M) {s : ℝ}
    (hs : max 1 (2 * (‖C‖ + 2 * M)) ≤ |s|) :
    ‖quadraticRemainder σ δ C B s - quadraticRemainder σ δ C D s‖ ≤
      (2 * matrixNormBridge n * (3 / 2 - σ) * (‖C‖ + 2 * M) *
        (1 / 4 : ℝ) ^ (σ - 5 / 2) * (1 + s ^ 2) ^ (σ - 3 / 2)) * ‖B - D‖ := by
  have hs1 : 1 ≤ |s| := (le_max_left _ _).trans hs
  have hsA : 2 * (‖C‖ + 2 * M) ≤ |s| := (le_max_right _ _).trans hs
  have hM : 0 ≤ M := (norm_nonneg _).trans hBM
  let A := ‖C‖ + 2 * M
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hs2 : 0 < s ^ 2 := by nlinarith [sq_abs s]
  have hxr : s ^ 2 / 2 ≤ s ^ 2 - A * |s| := by
    dsimp [A]; nlinarith [sq_abs s]
  have hnB : ‖C - (2 * s) • B‖ ≤ A * |s| :=
    (perturbed_norm_le hs1).trans (mul_le_mul_of_nonneg_right (by dsimp [A]; linarith) (abs_nonneg _))
  have hnD : ‖C - (2 * s) • D‖ ≤ A * |s| :=
    (perturbed_norm_le hs1).trans (mul_le_mul_of_nonneg_right (by dsimp [A]; linarith) (abs_nonneg _))
  have hh := cfc_remainder_lipschitz hσ hδ (by linarith : 0 < s ^ 2 / 2)
    (mul_nonneg hA (abs_nonneg s)) hxr
    (hC.sub (hB.smul (isSelfAdjoint_iff.2 rfl : IsSelfAdjoint (2 * s))))
    (hC.sub (hD.smul (isSelfAdjoint_iff.2 rfl : IsSelfAdjoint (2 * s)))) hnB hnD
  have he : (C - (2 * s) • B) - (C - (2 * s) • D) = (-2 * s) • (B - D) := by module
  rw [he, norm_smul] at hh
  simp only [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hh
  have hw := quadratic_taylor_weight (A := 1) hσ hδ hs1
  simp only [one_mul, one_pow, mul_one, sq_abs] at hw
  have hp : 0 ≤ 2 * matrixNormBridge n * (3 / 2 - σ) * A * ‖B - D‖ := by
    have := matrixNormBridge_nonneg (n := n)
    have : 0 ≤ 3 / 2 - σ := by linarith
    positivity
  calc
    _ ≤ matrixNormBridge n * ((3 / 2 - σ) * (s ^ 2 / 2 + δ) ^ (σ - 5 / 2) * (A * |s|)) *
        (2 * |s| * ‖B - D‖) := hh
    _ = (2 * matrixNormBridge n * (3 / 2 - σ) * A * ‖B - D‖) *
        ((s ^ 2 / 2 + δ) ^ (σ - 5 / 2) * s ^ 2) := by rw [← sq_abs s]; ring
    _ ≤ (2 * matrixNormBridge n * (3 / 2 - σ) * A * ‖B - D‖) *
        ((1 / 4 : ℝ) ^ (σ - 5 / 2) * (1 + s ^ 2) ^ (σ - 3 / 2)) :=
      mul_le_mul_of_nonneg_left hw hp
    _ = _ := by dsimp [A]; ring

lemma pairedFieldIntegrand_remainder_difference (σ δ : ℝ) (C B D : Matrix n n ℂ) (s : ℝ) :
    pairedFieldIntegrand σ δ C B s - pairedFieldIntegrand σ δ C D s =
      (quadraticRemainder σ δ C B s - quadraticRemainder σ δ C D s) +
      (quadraticRemainder σ δ C B (-s) - quadraticRemainder σ δ C D (-s)) := by
  unfold pairedFieldIntegrand quadraticRemainder
  simp only [neg_sq]
  module

lemma pairedFieldIntegrand_lipschitz_tail {σ δ M : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    {C B D : Matrix n n ℂ} (hC : C.IsHermitian) (hB : B.IsHermitian) (hD : D.IsHermitian)
    (hBM : ‖B‖ ≤ M) (hDM : ‖D‖ ≤ M) {s : ℝ}
    (hs : max 1 (2 * (‖C‖ + 2 * M)) ≤ |s|) :
    ‖pairedFieldIntegrand σ δ C B s - pairedFieldIntegrand σ δ C D s‖ ≤
      (4 * matrixNormBridge n * (3 / 2 - σ) * (‖C‖ + 2 * M) *
        (1 / 4 : ℝ) ^ (σ - 5 / 2) * (1 + s ^ 2) ^ (σ - 3 / 2)) * ‖B - D‖ := by
  have h1 := quadraticRemainder_lipschitz_tail hσ hδ hC hB hD hBM hDM hs
  have h2 := quadraticRemainder_lipschitz_tail hσ hδ hC hB hD hBM hDM
    (s := -s) (by rwa [abs_neg])
  rw [neg_sq] at h2
  rw [pairedFieldIntegrand_remainder_difference]
  linarith [norm_add_le (quadraticRemainder σ δ C B s - quadraticRemainder σ δ C D s)
    (quadraticRemainder σ δ C B (-s) - quadraticRemainder σ δ C D (-s))]

end SharpLiebThirring.MatrixProof

namespace SharpLiebThirring.MatrixProof
open Matrix ScalarProof MeasureTheory
open scoped Matrix.Norms.L2Operator NNReal
variable {n : Type u31} [Fintype n] [DecidableEq n]

def fieldLipEnvelope (σ δ M : ℝ) (C : Matrix n n ℂ) (s : ℝ) : ℝ :=
  (Set.Icc (-max 1 (2 * (‖C‖ + 2 * M))) (max 1 (2 * (‖C‖ + 2 * M)))).indicator
    (fun s : ℝ ↦ 4 * matrixNormBridge n * δ ^ (σ - 3 / 2) * |s|) s +
  4 * matrixNormBridge n * (3 / 2 - σ) * (‖C‖ + 2 * M) *
    (1 / 4 : ℝ) ^ (σ - 5 / 2) * (1 + s ^ 2) ^ (σ - 3 / 2)

lemma fieldLipEnvelope_nonneg {σ δ M : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (hM : 0 ≤ M) (C : Matrix n n ℂ) (s : ℝ) : 0 ≤ fieldLipEnvelope σ δ M C s := by
  have h1 : 0 ≤ matrixNormBridge n := matrixNormBridge_nonneg
  have h2 : 0 ≤ 3 / 2 - σ := by linarith
  unfold fieldLipEnvelope
  apply add_nonneg
  · exact Set.indicator_nonneg (fun _ _ ↦ by positivity) _
  · positivity

lemma integrable_fieldLipEnvelope {σ δ : ℝ} (hσ : σ < 1) (M : ℝ)
    (C : Matrix n n ℂ) : Integrable (fieldLipEnvelope σ δ M C) := by
  apply Integrable.add
  · apply IntegrableOn.integrable_indicator _ measurableSet_Icc
    exact (by fun_prop : Continuous (fun s : ℝ ↦
      4 * matrixNormBridge n * δ ^ (σ - 3 / 2) * |s|)).integrableOn_Icc
  · exact (normalization_integrable hσ).const_mul _

lemma pairedFieldIntegrand_lipschitz_envelope {σ δ M : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    {C B D : Matrix n n ℂ} (hC : C.IsHermitian) (hB : B.IsHermitian) (hD : D.IsHermitian)
    (hBM : ‖B‖ ≤ M) (hDM : ‖D‖ ≤ M) (s : ℝ) :
    ‖pairedFieldIntegrand σ δ C B s - pairedFieldIntegrand σ δ C D s‖ ≤
      fieldLipEnvelope σ δ M C s * ‖B - D‖ := by
  have hM : 0 ≤ M := (norm_nonneg _).trans hBM
  have h1 : 0 ≤ matrixNormBridge n := matrixNormBridge_nonneg
  have h2 : 0 ≤ 3 / 2 - σ := by linarith
  let R := max 1 (2 * (‖C‖ + 2 * M))
  by_cases hs : |s| ≤ R
  · have hs' : s ∈ Set.Icc (-R) R := abs_le.mp hs
    have hh := pairedFieldIntegrand_lipschitz_global hσ hδ hC hB hD s
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    unfold fieldLipEnvelope
    rw [Set.indicator_of_mem hs']
    exact le_add_of_nonneg_right (by positivity)
  · have hh := pairedFieldIntegrand_lipschitz_tail hσ hδ hC hB hD hBM hDM
      (le_of_not_ge hs)
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact le_add_of_nonneg_left (Set.indicator_nonneg (fun _ _ ↦ by positivity) _)

lemma pairedFieldIntegrand_norm_on_ball {σ δ M : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (hM : 0 ≤ M) {C B : Matrix n n ℂ} (hC : C.IsHermitian) (hB : B.IsHermitian)
    (hBM : ‖B‖ ≤ M) (s : ℝ) :
    ‖pairedFieldIntegrand σ δ C B s‖ ≤
      ‖pairedFieldIntegrand σ δ C 0 s‖ + fieldLipEnvelope σ δ M C s * M := by
  have hh := pairedFieldIntegrand_lipschitz_envelope hσ hδ hC hB Matrix.isHermitian_zero
    hBM (by simpa using hM) s
  simp only [sub_zero] at hh
  have hs := hh.trans (mul_le_mul_of_nonneg_left hBM (fieldLipEnvelope_nonneg hσ hδ hM C s))
  have ht := norm_le_norm_add_norm_sub' (pairedFieldIntegrand σ δ C B s)
    (pairedFieldIntegrand σ δ C 0 s)
  linarith

lemma hermitianField_lipschitz_bound {σ δ M : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    {C B D : Matrix n n ℂ} (hC : C.IsHermitian) (hB : B.IsHermitian) (hD : D.IsHermitian)
    (hBM : ‖B‖ ≤ M) (hDM : ‖D‖ ≤ M) :
    ‖hermitianField σ δ C B - hermitianField σ δ C D‖ ≤
      (|fieldNormalization σ / 2| * ∫ s : ℝ, fieldLipEnvelope σ δ M C s) * ‖B - D‖ := by
  have hiB := integrable_pairedFieldIntegrand hσ hδ hC hB
  have hiD := integrable_pairedFieldIntegrand hσ hδ hC hD
  unfold hermitianField
  rw [← smul_sub, ← integral_sub hiB hiD, norm_smul, Real.norm_eq_abs]
  have hh := norm_integral_le_of_norm_le (integrable_fieldLipEnvelope hσ M C |>.mul_const ‖B - D‖)
    (Filter.Eventually.of_forall (pairedFieldIntegrand_lipschitz_envelope hσ hδ hC hB hD hBM hDM))
  rw [integral_mul_const] at hh
  exact (mul_le_mul_of_nonneg_left hh (abs_nonneg _)).trans_eq (mul_assoc _ _ _).symm

lemma hermitianField_locallyLipschitz {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    {C : Matrix n n ℂ} (hC : C.IsHermitian) :
    LocallyLipschitz (fun B : selfAdjoint (Matrix n n ℂ) ↦ hermitianField σ δ C B) := by
  intro B
  let M : ℝ := ‖B‖ + 1
  let L : ℝ := |fieldNormalization σ / 2| * ∫ s : ℝ, fieldLipEnvelope σ δ M C s
  have hL : 0 ≤ L := mul_nonneg (abs_nonneg _) (integral_nonneg (fun s ↦
    fieldLipEnvelope_nonneg hσ hδ (by dsimp [M]; positivity) C s))
  refine ⟨⟨L, hL⟩, Metric.ball B 1, Metric.ball_mem_nhds B (by norm_num), ?_⟩
  change @LipschitzOnWith _ _ (PseudoMetricSpace.toPseudoEMetricSpace)
    (PseudoMetricSpace.toPseudoEMetricSpace) _ _ _
  apply lipschitzOnWith_iff_norm_sub_le.mpr
  intro A hA D hD
  have hAM : ‖(A : Matrix n n ℂ)‖ ≤ M := by
    change ‖A‖ ≤ ‖B‖ + 1
    exact norm_le_norm_add_const_of_dist_le (Metric.mem_ball.mp hA).le
  have hDM : ‖(D : Matrix n n ℂ)‖ ≤ M := by
    change ‖D‖ ≤ ‖B‖ + 1
    exact norm_le_norm_add_const_of_dist_le (Metric.mem_ball.mp hD).le
  exact hermitianField_lipschitz_bound hσ hδ hC A.prop D.prop hAM hDM

end SharpLiebThirring.MatrixProof

end
end
end

end OAI
