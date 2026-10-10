import OAI.Analysis.OInfinity.TensorApproximation
import OAI.Analysis.OInfinity.VacuumCorner

namespace OAI

/-! # Tensor-norm nuclearity of O∞

Finite unused-generator corners control the Fock matrix in every C*-completion
of the algebraic tensor product.  The two Gram summands of the return map give
a uniform factor-two norm comparison, and the C*-identity removes that factor.
This proves the tensor-norm nuclearity input used by the absorption criterion.
-/

noncomputable section
open scoped CStarAlgebra TensorProduct
open Filter Topology

namespace WeakPureInfiniteness

private lemma algebraNorm_le_sub_add {R : Type*} [Ring R] [Algebra ℂ R]
    (p : AlgebraNorm ℂ R) (x y : R) : p x ≤ p (x - y) + p y := by
  simpa only [sub_add_cancel] using map_add_le_add p (x - y) y

private lemma algebraNorm_le_rev_sub_add {R : Type*} [Ring R] [Algebra ℂ R]
    (p : AlgebraNorm ℂ R) (x y : R) : p x ≤ p (y - x) + p y := by
  simpa only [map_sub_rev p] using algebraNorm_le_sub_add p x y

private lemma algebraNorm_le_of_approximation {R : Type*} [Ring R] [Algebra ℂ R]
    (p : AlgebraNorm ℂ R) (x : R) (y : ℕ → R) (C : ℝ)
    (ht : Tendsto (fun n => p (y n - x)) atTop (𝓝 0))
    (hb : ∀ᶠ n : ℕ in atTop, p (y n) ≤ C) : p x ≤ C := by
  have hupper : ∀ᶠ n : ℕ in atTop, p x ≤ p (y n - x) + C := by
    filter_upwards [hb] with n hn
    exact (algebraNorm_le_rev_sub_add p x (y n)).trans (add_le_add_right hn _)
  simpa only [zero_add] using ge_of_tendsto (ht.add_const C) hupper

private lemma map_smul_mul {A E : Type*} [NonUnitalCStarAlgebra A]
    [NonUnitalCStarAlgebra E] (R : A →⋆ₙₐ[ℂ] E) (c : ℂ) (a : A) (z : E) :
    R (c • a) * z = c • (R a * z) := by
  calc
    R (c • a) * z = (c • R a) * z := congrArg (fun x : E => x * z) (map_smul R c a)
    _ = _ := smul_mul_assoc c (R a) z

private lemma map_scaled_sum_mul {A E : Type*} [NonUnitalCStarAlgebra A]
    [NonUnitalCStarAlgebra E] (R : A →⋆ₙₐ[ℂ] E) (c : ℂ) (a b : A) (z : E) :
    R (c • (a + b)) * z = c • (R a * z + R b * z) := by
  rw [map_smul_mul]
  exact congrArg (fun x : E => c • x)
    ((congrArg (fun x : E => x * z) (map_add R a b)).trans (add_mul (R a) (R b) z))

private lemma map_star_sandwich {A E : Type*} [NonUnitalCStarAlgebra A]
    [NonUnitalCStarAlgebra E] (R : A →⋆ₙₐ[ℂ] E) (x a y : A) :
    star (R x) * R a * R y = R (star x * a * y) := by
  rw [map_mul, map_mul, map_star]

private lemma map_scalar_unit_mul {A B E : Type*} [CStarAlgebra A] [CStarAlgebra B]
    [NonUnitalCStarAlgebra E] (R : A →⋆ₙₐ[ℂ] E) (S : B →⋆ₙₐ[ℂ] E)
    (hsupport : ∀ b, R 1 * S b = S b) (c : ℂ) (b : B) :
    R (c • (1 : A)) * S b = S (c • b) := by
  calc
    _ = c • (R 1 * S b) := map_smul_mul R c 1 (S b)
    _ = c • S b := congrArg (fun x : E => c • x) (hsupport b)
    _ = S (c • b) := (map_smul S c b).symm

variable {B E : Type*} [CStarAlgebra B] [NonUnitalCStarAlgebra E]

local instance oInfinityTensorNormLocal1 : PartialOrder B := CStarAlgebra.spectralOrder _
local instance oInfinityTensorNormLocal2 : StarOrderedRing B := CStarAlgebra.spectralOrderedRing _
local instance oInfinityTensorNormLocal3 : PartialOrder OInfinity := CStarAlgebra.spectralOrder _
local instance oInfinityTensorNormLocal4 : StarOrderedRing OInfinity := CStarAlgebra.spectralOrderedRing _

def fockTensorCoefficient (N m : ℕ) (a : OInfinity) :
    B →ₗ[ℂ] CStarMatrix (FiniteFockIndex N m) (FiniteFockIndex N m) B where
  toFun b := CStarMatrix.ofMatrix (fun i j => oInfinityFockCompression N m a i j • b)
  map_add' b c := by
    ext i j
    change oInfinityFockCompression N m a i j • (b + c) =
      oInfinityFockCompression N m a i j • b + oInfinityFockCompression N m a i j • c
    exact smul_add _ _ _
  map_smul' c b := by
    ext i j
    exact smul_comm _ _ _

def fockTensorBilinear (N m : ℕ) :
    OInfinity →ₗ[ℂ] B →ₗ[ℂ] CStarMatrix (FiniteFockIndex N m) (FiniteFockIndex N m) B where
  toFun := fockTensorCoefficient N m
  map_add' a b := by
    ext c i j
    change oInfinityFockCompression N m (a + b) i j • c = _
    rw [map_add, CStarMatrix.add_apply, add_smul]
    rfl
  map_smul' c a := by
    ext b i j
    change oInfinityFockCompression N m (c • a) i j • b = _
    rw [map_smul, CStarMatrix.smul_apply]
    exact mul_smul _ _ _

def fockTensorMatrix (N m : ℕ) :
    OInfinity ⊗[ℂ] B →ₗ[ℂ] CStarMatrix (FiniteFockIndex N m) (FiniteFockIndex N m) B :=
  TensorProduct.lift (fockTensorBilinear N m)

@[simp] lemma fockTensorMatrix_tmul (N m : ℕ) (a : OInfinity) (b : B)
    (i j : FiniteFockIndex N m) :
    fockTensorMatrix N m (a ⊗ₜ[ℂ] b) i j = oInfinityFockCompression N m a i j • b := rfl

def tensorCommutingBilinear {A : Type*} [NonUnitalCStarAlgebra A]
    (R : A →⋆ₙₐ[ℂ] E) (S : B →⋆ₙₐ[ℂ] E) : A →ₗ[ℂ] B →ₗ[ℂ] E where
  toFun a :=
    { toFun b := R a * S b
      map_add' b c := by rw [map_add, mul_add]
      map_smul' c b := by rw [map_smul, mul_smul_comm]; rfl }
  map_add' a b := by
    ext c
    change R (a + b) * S c = R a * S c + R b * S c
    exact (congrArg (fun x : E => x * S c) (map_add R a b)).trans (add_mul _ _ _)
  map_smul' c a := by
    ext b
    change R (c • a) * S b = c • (R a * S b)
    exact map_smul_mul R c a (S b)

def tensorCommutingEval {A : Type*} [NonUnitalCStarAlgebra A]
    (R : A →⋆ₙₐ[ℂ] E) (S : B →⋆ₙₐ[ℂ] E) : A ⊗[ℂ] B →ₗ[ℂ] E := TensorProduct.lift (tensorCommutingBilinear R S)

@[simp] lemma tensorCommutingEval_tmul {A : Type*} [NonUnitalCStarAlgebra A]
    (R : A →⋆ₙₐ[ℂ] E) (S : B →⋆ₙₐ[ℂ] E) (a : A) (b : B) : tensorCommutingEval R S (a ⊗ₜ[ℂ] b) = R a * S b := rfl

lemma commuting_vacuum_compression (R : OInfinity →⋆ₙₐ[ℂ] E) (S : B →⋆ₙₐ[ℂ] E)
    (hcomm : ∀ a b, Commute (R a) (S b)) (hsupport : ∀ b, R 1 * S b = S b)
    {N m : ℕ} (c : List (ℕ × Bool) →₀ ℂ)
    (hc : ∀ w ∈ c.support, ∀ p ∈ w, p.1 < N) (b : B)
    (i j : FiniteFockIndex N m) :
    star (R (finiteVacuumCorner N m i)) *
      tensorCommutingEval R S (cuntzPolynomial oInfinityIsometry c ⊗ₜ[ℂ] b) *
        R (finiteVacuumCorner N m j) =
    S (fockTensorMatrix N m (cuntzPolynomial oInfinityIsometry c ⊗ₜ[ℂ] b) i j) := by
  rw [tensorCommutingEval_tmul, fockTensorMatrix_tmul]
  calc
    _ = (star (R (finiteVacuumCorner N m i)) * R (cuntzPolynomial oInfinityIsometry c)) *
        (S b * R (finiteVacuumCorner N m j)) := by noncomm_ring
    _ = (star (R (finiteVacuumCorner N m i)) * R (cuntzPolynomial oInfinityIsometry c) *
        R (finiteVacuumCorner N m j)) * S b := by
      rw [(hcomm _ b).symm.eq]
      simp only [mul_assoc]
    _ = R (star (finiteVacuumCorner N m i) * cuntzPolynomial oInfinityIsometry c *
        finiteVacuumCorner N m j) * S b :=
      congrArg (fun z : E => z * S b) (map_star_sandwich R _ _ _)
    _ = R (oInfinityFockCompression N m (cuntzPolynomial oInfinityIsometry c) i j • 1) * S b :=
      congrArg (fun z : OInfinity => R z * S b) (finiteVacuumCorner_polynomial c hc i j)
    _ = _ := map_scalar_unit_mul R S hsupport _ b

def polynomialTensorSum (l : List ((List (ℕ × Bool) →₀ ℂ) × B)) : OInfinity ⊗[ℂ] B :=
  (l.map fun t => cuntzPolynomial oInfinityIsometry t.1 ⊗ₜ[ℂ] t.2).sum

lemma exists_tensorApproximation_polynomialSum (n : ℕ) (x : OInfinity ⊗[ℂ] B) :
    ∃ l : List ((List (ℕ × Bool) →₀ ℂ) × B),
      oInfinityTensorApproximation n x = polynomialTensorSum l := by
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    obtain ⟨c, hc⟩ := exists_oInfinityApproximation_polynomial n a
    refine ⟨[(c, b)], ?_⟩
    simp only [oInfinityTensorApproximation_tmul, polynomialTensorSum, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero, hc]
  | add x y hx hy =>
    obtain ⟨l, hl⟩ := hx
    obtain ⟨k, hk⟩ := hy
    refine ⟨l ++ k, ?_⟩
    simp only [map_add, hl, hk, polynomialTensorSum, List.map_append, List.sum_append]

omit [CStarAlgebra B] in
lemma exists_polynomialTensor_alphabet_bound (l : List ((List (ℕ × Bool) →₀ ℂ) × B)) :
    ∃ N : ℕ, ∀ t ∈ l, ∀ w ∈ t.1.support, ∀ p ∈ w, p.1 < N := by
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons t l ih =>
    obtain ⟨N, hN⟩ := exists_polynomial_alphabet_bound t.1
    obtain ⟨M, hM⟩ := ih
    refine ⟨max N M, ?_⟩
    intro u hu w hw p hp
    rcases List.mem_cons.mp hu with rfl | hu
    · exact (hN w hw p hp).trans_le (le_max_left _ _)
    · exact (hM u hu w hw p hp).trans_le (le_max_right _ _)

lemma commuting_vacuum_compression_list (R : OInfinity →⋆ₙₐ[ℂ] E) (S : B →⋆ₙₐ[ℂ] E)
    (hcomm : ∀ a b, Commute (R a) (S b)) (hsupport : ∀ b, R 1 * S b = S b)
    {N m : ℕ} (l : List ((List (ℕ × Bool) →₀ ℂ) × B))
    (hl : ∀ t ∈ l, ∀ w ∈ t.1.support, ∀ p ∈ w, p.1 < N)
    (i j : FiniteFockIndex N m) :
    star (R (finiteVacuumCorner N m i)) * tensorCommutingEval R S (polynomialTensorSum l) *
        R (finiteVacuumCorner N m j) = S (fockTensorMatrix N m (polynomialTensorSum l) i j) := by
  induction l with
  | nil => simp [polynomialTensorSum]
  | cons t l ih =>
    have ht := commuting_vacuum_compression R S hcomm hsupport t.1
      (hl t (List.mem_cons_self ..)) t.2 i j
    have htail := ih (fun u hu => hl u (List.mem_cons_of_mem _ hu))
    simpa only [polynomialTensorSum, List.map_cons, List.sum_cons, map_add, mul_add,
      add_mul, CStarMatrix.add_apply] using congrArg₂ (· + ·) ht htail

lemma fockTensorMatrix_polynomial_norm_le (R : OInfinity →⋆ₙₐ[ℂ] E) (S : B →⋆ₙₐ[ℂ] E)
    (hcomm : ∀ a b, Commute (R a) (S b)) (hsupport : ∀ b, R 1 * S b = S b)
    (hS : Function.Injective S) {N m : ℕ} (l : List ((List (ℕ × Bool) →₀ ℂ) × B))
    (hl : ∀ t ∈ l, ∀ w ∈ t.1.support, ∀ p ∈ w, p.1 < N) :
    ‖fockTensorMatrix N m (polynomialTensorSum l)‖ ≤
      ‖tensorCommutingEval R S (polynomialTensorSum l)‖ := by
  let r (i : FiniteFockIndex N m) := R (finiteVacuumCorner N m i)
  have hr (i j : FiniteFockIndex N m) : star (r i) * r j = if i = j then R 1 else 0 := by
    dsimp [r]
    rw [← map_star, ← map_mul, finiteVacuumCorner_relations]
    split_ifs <;> simp only [map_zero]
  have heStar : star (R 1) = R 1 := by rw [← map_star, star_one]
  have hre (i : FiniteFockIndex N m) : r i * R 1 = r i := by
    dsimp [r]
    rw [← map_mul, mul_one]
  exact supportedCuntz_compression_norm_le r (R 1) S hr hsupport heStar hre hS _ _
    (commuting_vacuum_compression_list R S hcomm hsupport l hl)

lemma mappedFockCuntz_relations (R : OInfinity →⋆ₙₐ[ℂ] E) (N m : ℕ)
    (i j : FiniteFockIndex N m) :
    star (R (finiteFockCuntzFamily N m i)) * R (finiteFockCuntzFamily N m j) =
      if i = j then R 1 else 0 := by
  rw [← map_star, ← map_mul, finiteFockCuntzFamily_relations]
  split_ifs <;> simp only [map_zero]

def representedFockGram (R : OInfinity →⋆ₙₐ[ℂ] E) (S : B →⋆ₙₐ[ℂ] E)
    (hsupport : ∀ b, R 1 * S b = S b) (N m : ℕ)
    (c : FiniteFockIndex N m → OInfinity) :
    CStarMatrix (FiniteFockIndex N m) (FiniteFockIndex N m) B →L[ℂ] E :=
  (ContinuousLinearMap.mulLeftRight ℂ E
    (star (∑ i, R (finiteFockCuntzFamily N m i) * R (c i)))
    (∑ i, R (finiteFockCuntzFamily N m i) * R (c i))).comp
      (starHomContinuousLinear (supportedCuntzMatrixHom
        (fun i => R (finiteFockCuntzFamily N m i)) (R 1) S
        (mappedFockCuntz_relations R N m) hsupport))

lemma representedFockGram_apply (R : OInfinity →⋆ₙₐ[ℂ] E) (S : B →⋆ₙₐ[ℂ] E)
    (hsupport : ∀ b, R 1 * S b = S b) (N m : ℕ)
    (c : FiniteFockIndex N m → OInfinity)
    (M : CStarMatrix (FiniteFockIndex N m) (FiniteFockIndex N m) B) :
    representedFockGram R S hsupport N m c M =
      ∑ i, ∑ j, star (R (c i)) * S (M i j) * R (c j) := by
  have heStar : star (R 1) = R 1 := by rw [← map_star, star_one]
  have hv (i : FiniteFockIndex N m) : R 1 * R (c i) = R (c i) := by
    rw [← map_mul, one_mul]
  exact supportedCuntz_gram_apply _ _ _ _ (mappedFockCuntz_relations R N m)
    hsupport heStar hv M

lemma representedFockGram_norm_le (R : OInfinity →⋆ₙₐ[ℂ] E) (S : B →⋆ₙₐ[ℂ] E)
    (hsupport : ∀ b, R 1 * S b = S b) (N m : ℕ)
    (c : FiniteFockIndex N m → OInfinity)
    (M : CStarMatrix (FiniteFockIndex N m) (FiniteFockIndex N m) B) :
    ‖representedFockGram R S hsupport N m c M‖ ≤
      ‖∑ i, star (c i) * c i‖ * ‖M‖ := by
  have hv (i : FiniteFockIndex N m) : R 1 * R (c i) = R (c i) := by
    rw [← map_mul, one_mul]
  have h := supportedCuntz_gram_norm_le (fun i => R (finiteFockCuntzFamily N m i))
    (fun i => R (c i)) (R 1) S (mappedFockCuntz_relations R N m) hsupport hv M
  have he : (∑ i, star (R (c i)) * R (c i)) = R (∑ i, star (c i) * c i) := by
    simp only [map_sum, map_mul, map_star]
  have hR : ‖∑ i, star (R (c i)) * R (c i)‖ ≤ ‖∑ i, star (c i) * c i‖ := by
    rw [he]
    exact NonUnitalStarAlgHom.norm_apply_le R _
  exact h.trans (mul_le_mul_of_nonneg_right hR (norm_nonneg _))

lemma representedFockGram_tmul (R : OInfinity →⋆ₙₐ[ℂ] E) (S : B →⋆ₙₐ[ℂ] E)
    (hcomm : ∀ a b, Commute (R a) (S b)) (hsupport : ∀ b, R 1 * S b = S b)
    (N m : ℕ) (c : FiniteFockIndex N m → OInfinity) (a : OInfinity) (b : B) :
    representedFockGram R S hsupport N m c (fockTensorMatrix N m (a ⊗ₜ[ℂ] b)) =
      R (cuntzGramMap (finiteFockCuntzFamily N m) (finiteFockCuntzFamily_relations N m)
        c (oInfinityFockCompression N m a)) * S b := by
  rw [representedFockGram_apply, cuntzGramMap_apply]
  simp only [fockTensorMatrix_tmul, map_sum, map_smul, Finset.sum_mul, smul_mul_assoc]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_smul_comm, smul_mul_assoc, map_mul, map_star]
  congr 1
  calc
    _ = star (R (c i)) * (S b * R (c j)) := mul_assoc _ _ _
    _ = _ := by rw [(hcomm (c j) b).symm.eq]; simp only [mul_assoc]

def representedFockReturn (R : OInfinity →⋆ₙₐ[ℂ] E) (S : B →⋆ₙₐ[ℂ] E)
    (hsupport : ∀ b, R 1 * S b = S b) (N m : ℕ) :
    CStarMatrix (FiniteFockIndex N m) (FiniteFockIndex N m) B →L[ℂ] E :=
  (((((m : ℝ) + 1)⁻¹ : ℝ) : ℂ)) •
    (representedFockGram R S hsupport N m finiteFockUnweightedCoefficient +
      representedFockGram R S hsupport N m finiteFockWeightedCoefficient)

lemma representedFockReturn_norm_le (R : OInfinity →⋆ₙₐ[ℂ] E) (S : B →⋆ₙₐ[ℂ] E)
    (hsupport : ∀ b, R 1 * S b = S b) (N m : ℕ)
    (M : CStarMatrix (FiniteFockIndex N m) (FiniteFockIndex N m) B) :
    ‖representedFockReturn R S hsupport N m M‖ ≤ 2 * ‖M‖ := by
  have hK : 0 < (m : ℝ) + 1 := by positivity
  have hu := (representedFockGram_norm_le R S hsupport N m finiteFockUnweightedCoefficient M).trans
    (mul_le_mul_of_nonneg_right (finiteFockCoefficient_norm_le N m).1 (norm_nonneg M))
  have hw := (representedFockGram_norm_le R S hsupport N m finiteFockWeightedCoefficient M).trans
    (mul_le_mul_of_nonneg_right (finiteFockCoefficient_norm_le N m).2 (norm_nonneg M))
  change ‖(((((m : ℝ) + 1)⁻¹ : ℝ) : ℂ)) •
    (representedFockGram R S hsupport N m finiteFockUnweightedCoefficient M +
      representedFockGram R S hsupport N m finiteFockWeightedCoefficient M)‖ ≤ _
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hK.le)]
  calc
    _ ≤ ((m : ℝ) + 1)⁻¹ * (((m : ℝ) + 1) * ‖M‖ + ((m : ℝ) + 1) * ‖M‖) :=
      mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add hu hw)) (inv_nonneg.mpr hK.le)
    _ = _ := by field_simp [hK.ne']; ring

lemma representedFockReturn_tmul (R : OInfinity →⋆ₙₐ[ℂ] E) (S : B →⋆ₙₐ[ℂ] E)
    (hcomm : ∀ a b, Commute (R a) (S b)) (hsupport : ∀ b, R 1 * S b = S b)
    (N m : ℕ) (a : OInfinity) (b : B) :
    representedFockReturn R S hsupport N m (fockTensorMatrix N m (a ⊗ₜ[ℂ] b)) =
      R (oInfinityFockApproximation N m a) * S b := by
  change (((((m : ℝ) + 1)⁻¹ : ℝ) : ℂ)) •
    (representedFockGram R S hsupport N m finiteFockUnweightedCoefficient
        (fockTensorMatrix N m (a ⊗ₜ[ℂ] b)) +
      representedFockGram R S hsupport N m finiteFockWeightedCoefficient
        (fockTensorMatrix N m (a ⊗ₜ[ℂ] b))) = _
  rw [representedFockGram_tmul R S hcomm, representedFockGram_tmul R S hcomm]
  change _ = R ((((((m : ℝ) + 1)⁻¹ : ℝ) : ℂ)) •
    (cuntzGramMap (finiteFockCuntzFamily N m) (finiteFockCuntzFamily_relations N m)
      finiteFockUnweightedCoefficient (oInfinityFockCompression N m a) +
     cuntzGramMap (finiteFockCuntzFamily N m) (finiteFockCuntzFamily_relations N m)
      finiteFockWeightedCoefficient (oInfinityFockCompression N m a))) * S b
  exact (map_scaled_sum_mul R _ _ _ (S b)).symm

lemma representedFockReturn_approximation (R : OInfinity →⋆ₙₐ[ℂ] E) (S : B →⋆ₙₐ[ℂ] E)
    (hcomm : ∀ a b, Commute (R a) (S b)) (hsupport : ∀ b, R 1 * S b = S b)
    (n : ℕ) (x : OInfinity ⊗[ℂ] B) :
    representedFockReturn R S hsupport n (n + 1) (fockTensorMatrix n (n + 1) x) =
      tensorCommutingEval R S (oInfinityTensorApproximation n x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    simpa only [oInfinityTensorApproximation_tmul, tensorCommutingEval_tmul,
      oInfinityApproximationSequence] using
      representedFockReturn_tmul R S hcomm hsupport n (n + 1) a b
  | add x y hx hy => simp only [map_add, hx, hy]

lemma tensor_norm_bound_of_approximation
    (p q : Pureness.CStarAlgebraNorm (OInfinity ⊗[ℂ] B)) (x : OInfinity ⊗[ℂ] B)
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n, q.toAlgebraNorm (oInfinityTensorApproximation n x) ≤
      C * p.toAlgebraNorm (oInfinityTensorApproximation n x)) :
    q.toAlgebraNorm x ≤ C * p.toAlgebraNorm x := by
  have hupper (n : ℕ) : q.toAlgebraNorm x ≤
      q.toAlgebraNorm (oInfinityTensorApproximation n x - x) +
        C * (p.toAlgebraNorm (oInfinityTensorApproximation n x - x) + p.toAlgebraNorm x) := by
    have hq := algebraNorm_le_rev_sub_add q.toAlgebraNorm x (oInfinityTensorApproximation n x)
    have hp := algebraNorm_le_sub_add p.toAlgebraNorm (oInfinityTensorApproximation n x) x
    exact hq.trans (add_le_add_right ((hb n).trans (mul_le_mul_of_nonneg_left hp hC)) _)
  have ht := (oInfinityTensorApproximation_error_tendsto q x).add
    (((oInfinityTensorApproximation_error_tendsto p x).add_const (p.toAlgebraNorm x)).const_mul C)
  simpa only [zero_add] using ge_of_tendsto ht (Filter.Eventually.of_forall hupper)

local instance (priority := 2000) tensorNormFastNonAssoc
    {A : Type*} [CStarAlgebra A] (p : Pureness.CStarAlgebraNorm (A ⊗[ℂ] B)) :
    NonUnitalNonAssocSemiring p.Completion :=
  (Pureness.CStarAlgebraNorm.completionCStarAlgebra p).toNonUnitalNonAssocSemiring

local instance (priority := 2000) tensorNormFastAddMonoid
    {A : Type*} [CStarAlgebra A] (p : Pureness.CStarAlgebraNorm (A ⊗[ℂ] B)) : AddMonoid p.Completion :=
  (Pureness.CStarAlgebraNorm.completionCStarAlgebra p).toAddMonoid

local instance (priority := 2000) tensorNormFastAddCommGroup
    {A : Type*} [CStarAlgebra A] (p : Pureness.CStarAlgebraNorm (A ⊗[ℂ] B)) :
    AddCommGroup p.Completion :=
  (Pureness.CStarAlgebraNorm.completionCStarAlgebra p).toAddCommGroup

local instance (priority := 2000) tensorNormFastModule
    {A : Type*} [CStarAlgebra A] (p : Pureness.CStarAlgebraNorm (A ⊗[ℂ] B)) : Module ℂ p.Completion :=
  (Pureness.CStarAlgebraNorm.completionCStarAlgebra p).toNormedSpace.toModule

local instance (priority := 2000) tensorNormFastDistribMulAction
    {A : Type*} [CStarAlgebra A] (p : Pureness.CStarAlgebraNorm (A ⊗[ℂ] B)) : DistribMulAction ℂ p.Completion :=
  (tensorNormFastModule p).toDistribMulAction

local instance (priority := 2000) tensorNormFastNorm
    {A : Type*} [CStarAlgebra A] (p : Pureness.CStarAlgebraNorm (A ⊗[ℂ] B)) : Norm p.Completion :=
  (Pureness.CStarAlgebraNorm.completionCStarAlgebra p).toNorm

def tensorNormLeft {A : Type*} [CStarAlgebra A]
    (p : Pureness.CStarAlgebraNorm (A ⊗[ℂ] B)) :
    A →⋆ₙₐ[ℂ] p.Completion where
  toFun a := p.completionMap (a ⊗ₜ[ℂ] (1 : B))
  map_zero' := by simp
  map_add' a b := by simp [TensorProduct.add_tmul]
  map_smul' z a := by
    rw [← TensorProduct.smul_tmul']
    exact p.completionMap.map_smul z _
  map_mul' a b := by rw [← map_mul]; simp
  map_star' a := by rw [← map_star]; simp

def tensorNormRight {A : Type*} [CStarAlgebra A]
    (p : Pureness.CStarAlgebraNorm (A ⊗[ℂ] B)) :
    B →⋆ₙₐ[ℂ] p.Completion where
  toFun b := p.completionMap ((1 : A) ⊗ₜ[ℂ] b)
  map_zero' := by simp
  map_add' a b := by simp [TensorProduct.tmul_add]
  map_smul' z a := by
    rw [TensorProduct.tmul_smul]
    exact p.completionMap.map_smul z _
  map_mul' a b := by rw [← map_mul]; simp
  map_star' a := by rw [← map_star]; simp

lemma tensorNorm_commute {A : Type*} [CStarAlgebra A]
    (p : Pureness.CStarAlgebraNorm (A ⊗[ℂ] B)) (a : A) (b : B) : Commute (tensorNormLeft p a) (tensorNormRight p b) := by
  exact ((Commute.one_right a).tmul (Commute.one_left b)).map p.completionMap

lemma tensorNorm_support {A : Type*} [CStarAlgebra A]
    (p : Pureness.CStarAlgebraNorm (A ⊗[ℂ] B))
    (b : B) : tensorNormLeft p 1 * tensorNormRight p b = tensorNormRight p b := by
  change p.completionMap (1 ⊗ₜ[ℂ] 1) * p.completionMap (1 ⊗ₜ[ℂ] b) = _
  rw [← map_mul]
  simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rfl

lemma tensorNormRight_injective {A : Type*} [CStarAlgebra A] [Nontrivial A]
    (p : Pureness.CStarAlgebraNorm (A ⊗[ℂ] B)) :
    Function.Injective (tensorNormRight p) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro b hb
  have hn : ‖b‖ = 0 := by
    have he := congrArg norm hb
    change ‖p.completionMap ((1 : A) ⊗ₜ[ℂ] b)‖ = ‖(0 : p.Completion)‖ at he
    rw [p.completionMap_norm, NuclearUnitization.cstar_norm_tmul, norm_one,
      one_mul, norm_zero] at he
    exact he
  exact norm_eq_zero.mp hn

lemma tensorNorm_eval {A : Type*} [CStarAlgebra A]
    (p : Pureness.CStarAlgebraNorm (A ⊗[ℂ] B)) (x : A ⊗[ℂ] B) :
    tensorCommutingEval (tensorNormLeft p) (tensorNormRight p) x = p.completionMap x := by
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    change p.completionMap (a ⊗ₜ[ℂ] 1) * p.completionMap (1 ⊗ₜ[ℂ] b) = _
    rw [← map_mul]
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  | add x y hx hy => simp only [map_add, hx, hy]

lemma tensorNorm_fock_return_bound
    (q : Pureness.CStarAlgebraNorm (OInfinity ⊗[ℂ] B)) (n : ℕ) (x : OInfinity ⊗[ℂ] B) :
    q.toAlgebraNorm (oInfinityTensorApproximation n x) ≤
      2 * ‖fockTensorMatrix n (n + 1) x‖ := by
  rw [← q.completionMap_norm, ← tensorNorm_eval, ← representedFockReturn_approximation
    _ _ (tensorNorm_commute q) (tensorNorm_support q)]
  exact representedFockReturn_norm_le _ _ _ _ _ _

lemma tensorNorm_polynomial_bound
    (p q : Pureness.CStarAlgebraNorm (OInfinity ⊗[ℂ] B))
    (l : List ((List (ℕ × Bool) →₀ ℂ) × B)) :
    q.toAlgebraNorm (polynomialTensorSum l) ≤ 2 * p.toAlgebraNorm (polynomialTensorSum l) := by
  obtain ⟨N, hN⟩ := exists_polynomialTensor_alphabet_bound l
  have hb : ∀ᶠ n : ℕ in atTop,
      q.toAlgebraNorm (oInfinityTensorApproximation n (polynomialTensorSum l)) ≤
        2 * p.toAlgebraNorm (polynomialTensorSum l) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    have hc := fockTensorMatrix_polynomial_norm_le (tensorNormLeft p) (tensorNormRight p)
      (tensorNorm_commute p) (tensorNorm_support p) (tensorNormRight_injective p)
      (m := n + 1) l (fun t ht w hw a ha => (hN t ht w hw a ha).trans_le hn)
    rw [tensorNorm_eval, p.completionMap_norm] at hc
    exact (tensorNorm_fock_return_bound q n _).trans (mul_le_mul_of_nonneg_left hc (by norm_num))
  exact algebraNorm_le_of_approximation q.toAlgebraNorm (polynomialTensorSum l)
    (fun n => oInfinityTensorApproximation n (polynomialTensorSum l))
    (2 * p.toAlgebraNorm (polynomialTensorSum l))
    (oInfinityTensorApproximation_error_tendsto q (polynomialTensorSum l)) hb

lemma tensorNorm_uniform_bound
    (p q : Pureness.CStarAlgebraNorm (OInfinity ⊗[ℂ] B)) (x : OInfinity ⊗[ℂ] B) :
    q.toAlgebraNorm x ≤ 2 * p.toAlgebraNorm x := by
  apply tensor_norm_bound_of_approximation p q x (by norm_num)
  intro n
  obtain ⟨l, hl⟩ := exists_tensorApproximation_polynomialSum n x
  rw [hl]
  exact tensorNorm_polynomial_bound p q l

/-- The Fock approximation and unused-generator corners give uniqueness of every
C*-norm on the algebraic tensor product with `OInfinity`. -/
theorem oInfinity_isNuclear : Pureness.IsNuclear OInfinity := by
  intro B _
  constructor
  intro p q
  exact Pureness.CStarAlgebraNorm.eq_of_mutual_bound p q
    ⟨2, tensorNorm_uniform_bound q p⟩ ⟨2, tensorNorm_uniform_bound p q⟩

end WeakPureInfiniteness

end

end OAI
