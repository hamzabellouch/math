import OAI.Analysis.FreeEntropy.CumulantResidual

namespace OAI

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation
section General
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

 theorem fisher_le_scaled_test {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (Z : Fin n → H →L[ℂ] H) (η : Fin n → H) (v : ℝ) (hv : 0 < v)
    (ht : ∀ i w, inner ℂ (η i) (wordEval Z w τ.vacuum) =
      (v : ℂ) * derivativeMoment τ Z i w)
    (hn : ∀ i, ‖η i‖ ^ 2 ≤ v) : freeFisher τ Z ≤ ENNReal.ofReal ((n : ℝ)/v) := by
  have ht' (i : Fin n) (w : List (Fin n)) :
      inner ℂ ((v⁻¹ : ℂ) • η i) (wordEval Z w τ.vacuum) = derivativeMoment τ Z i w := by
    rw [inner_smul_left, ht i w]
    simp [hv.ne']
  apply (freeFisher_le_testVectors τ Z (fun i => ((v⁻¹ : ℂ) • η i)) ht').trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ = ∑ i, v⁻¹ ^ 2 * ‖η i‖ ^ 2 := by
      simp only [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, mul_pow, inv_pow, sq_abs]
    _ ≤ ∑ _i : Fin n, v⁻¹ ^ 2 * v := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hn i) (sq_nonneg _))
    _ = _ := by simp [pow_two, hv.ne', div_eq_mul_inv]

omit [CompleteSpace H] in
theorem norm_sq_sqrt_pair [CompleteSpace H] {x y : H} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : inner ℂ x y = 0) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ‖(Real.sqrt a : ℂ) • x + (Real.sqrt b : ℂ) • y‖ ^ 2 = a + b := by
  rw [norm_add_sq (𝕜 := ℂ), inner_smul_left, inner_smul_right, hxy]
  simp [norm_smul, hx, hy,
    Real.norm_eq_abs, Real.sq_sqrt ha, Real.sq_sqrt hb,
    abs_of_nonneg (Real.sqrt_nonneg a), abs_of_nonneg (Real.sqrt_nonneg b)]

end General

namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]
 theorem noise_basis_test {n : ℕ} (J : Set N)
    (X : Fin n → Space B N G →L[ℂ] Space B N G)
    (hX : ∀ j, X j ∈ backgroundAlgebra J)
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀ j, σ j ∉ J)
    (u : ℝ) (i : Fin n) (w : List (Fin n)) :
    inner ℂ (basis (noiseWord [σ i]))
      (wordEval (heatTuple X (fun k => semicircularN (σ k)) u) w
        (tracialVector B N G).vacuum) =
      (Real.sqrt u : ℂ) * derivativeMoment (tracialVector B N G)
        (heatTuple X (fun k => semicircularN (σ k)) u) i w := by
  simpa only [List.map_cons, List.map_nil, List.reverse_singleton, List.length_singleton, pow_one,
    reverseDerivativeMoment, derivativeMoment] using wick_testing J X hX σ hσ hs u [i] w

 theorem semicircularN_vacuum (i : N) :
    semicircularN i (tracialVector B N G).vacuum = basis (noiseWord [i]) := by
  simp [semicircularN, tracialVector, basis, creationN_single, annihilationN_single,
    removeN, empty, noiseWord_cons, noiseWord_nil]
end FreeTensor
namespace Model
open FreeTensor
variable (p : ℕ) [NeZero p]

 theorem initialIndex_fresh (i : Fin (p+1)) : initialIndex p i ∉ Set.range (auxiliaryIndex p) := by
  rintro ⟨j,h⟩
  exact auxiliaryIndex_fresh p j ⟨i,h.symm⟩

 def doublyNoised (h s : ℝ) := heatTuple (X p h) (auxiliaryNoise p) s
 def noiseVector₀ (i : Fin (p+1)) : H p := basis (noiseWord [initialIndex p i])
 def noiseVector₁ (i : Fin (p+1)) : H p := basis (noiseWord [auxiliaryIndex p i])

 theorem doublyNoised_comm (h s : ℝ) : doublyNoised p h s =
    heatTuple (heatTuple (C p) (auxiliaryNoise p) s) (initialNoise p) h := by
  funext i
  simp only [doublyNoised, X, heatTuple]
  abel

 theorem auxiliaryBackground_mem (s : ℝ) (i : Fin (p+1)) :
    heatTuple (C p) (auxiliaryNoise p) s i ∈ backgroundAlgebra (Set.range (auxiliaryIndex p)) := by
  apply heatTuple_mem_background _ _ _ (C_mem_background p _)
  intro j
  exact semicircularN_mem_background _ ⟨j,rfl⟩

 theorem noiseVector₀_test (h s : ℝ) (i : Fin (p+1)) (w : List (Fin (p+1))) :
    inner ℂ (noiseVector₀ p i) (wordEval (doublyNoised p h s) w (τ p).vacuum) =
      (Real.sqrt h : ℂ) * derivativeMoment (τ p) (doublyNoised p h s) i w := by
  rw [doublyNoised_comm]
  exact noise_basis_test _ _ (auxiliaryBackground_mem p s)
    (initialIndex p) (initialIndex_injective p) (initialIndex_fresh p) h i w

 theorem noiseVector₁_test (h s : ℝ) (i : Fin (p+1)) (w : List (Fin (p+1))) :
    inner ℂ (noiseVector₁ p i) (wordEval (doublyNoised p h s) w (τ p).vacuum) =
      (Real.sqrt s : ℂ) * derivativeMoment (τ p) (doublyNoised p h s) i w :=
  noise_basis_test _ _ (X_mem_background p h)
    (auxiliaryIndex p) (auxiliaryIndex_injective p) (auxiliaryIndex_fresh p) s i w

omit [NeZero p] in
theorem noiseVector₀_norm [NeZero p] (i : Fin (p+1)) : ‖noiseVector₀ p i‖ = 1 := by
  simp [noiseVector₀, basis, lp.norm_single (E := fun _ => ℂ) (p := 2)]

omit [NeZero p] in
theorem noiseVector₁_norm [NeZero p] (i : Fin (p+1)) : ‖noiseVector₁ p i‖ = 1 := by
  simp [noiseVector₁, basis, lp.norm_single (E := fun _ => ℂ) (p := 2)]
 theorem noiseVector_orthogonal (i j : Fin (p+1)) : inner ℂ (noiseVector₀ p i) (noiseVector₁ p j) = 0 := by
  have hneq : [initialIndex p i] ≠ [auxiliaryIndex p j] := by
    intro he
    have he' : initialIndex p i = auxiliaryIndex p j := List.cons.inj he |>.1
    exact auxiliaryIndex_fresh p j ⟨i,he'⟩
  exact noise_basis_orthonormal.inner_eq_zero hneq

theorem doublyNoised_fisher_le (h s : ℝ) (hh : 0 ≤ h) (hs : 0 ≤ s) (hu : 0 < h+s) :
    freeFisher (τ p) (doublyNoised p h s) ≤ ENNReal.ofReal ((p+1 : ℕ)/(h+s)) := by
  let η : Fin (p+1) → H p := fun i => (Real.sqrt h : ℂ) • noiseVector₀ p i +
    (Real.sqrt s : ℂ) • noiseVector₁ p i
  apply fisher_le_scaled_test (τ p) _ η (h+s) hu
  · intro i w
    simp only [η, inner_add_left, inner_smul_left, Complex.conj_ofReal,
      noiseVector₀_test, noiseVector₁_test, ← mul_assoc, ← pow_two]
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, Real.sq_sqrt hh, Real.sq_sqrt hs]
    push_cast
    ring
  · intro i
    exact (norm_sq_sqrt_pair (noiseVector₀_norm p i) (noiseVector₁_norm p i)
      (noiseVector_orthogonal p i i) h s hh hs).le

 theorem noiseVector₀_C (i j : Fin (p+1)) : inner ℂ (noiseVector₀ p i) (C p j (τ p).vacuum) = 0 := by
  have ht := noise_basis_test ∅ (C p) (C_mem_background p ∅) (initialIndex p)
    (initialIndex_injective p) (by simp) 0 i [j]
  simpa [heatTuple, wordEval, noiseVector₀] using ht
 theorem noiseVector₁_C (i j : Fin (p+1)) : inner ℂ (noiseVector₁ p i) (C p j (τ p).vacuum) = 0 := by
  have ht := noise_basis_test ∅ (C p) (C_mem_background p ∅) (auxiliaryIndex p)
    (auxiliaryIndex_injective p) (by simp) 0 i [j]
  simpa [heatTuple, wordEval, noiseVector₁] using ht

 theorem doublyNoised_vacuum (h s : ℝ) (i : Fin (p+1)) :
    doublyNoised p h s i (τ p).vacuum = C p i (τ p).vacuum +
      ((Real.sqrt h : ℂ) • noiseVector₀ p i + (Real.sqrt s : ℂ) • noiseVector₁ p i) := by
  change (C p i (τ p).vacuum + (Real.sqrt h : ℂ) •
    semicircularN (initialIndex p i) (τ p).vacuum) +
    (Real.sqrt s : ℂ) • semicircularN (auxiliaryIndex p i) (τ p).vacuum = _
  rw [semicircularN_vacuum, semicircularN_vacuum]
  simp only [noiseVector₀, noiseVector₁, add_assoc]

 theorem doublyNoised_variance (h s : ℝ) (hh : 0 ≤ h) (hs : 0 ≤ s) (i : Fin (p+1)) :
    ‖doublyNoised p h s i (τ p).vacuum‖ ^ 2 = ‖C p i (τ p).vacuum‖ ^ 2 + h+s := by
  have hc : inner ℂ (C p i (τ p).vacuum)
      ((Real.sqrt h : ℂ) • noiseVector₀ p i + (Real.sqrt s : ℂ) • noiseVector₁ p i) = 0 := by
    rw [← inner_conj_symm, inner_add_left, inner_smul_left, inner_smul_left,
      noiseVector₀_C, noiseVector₁_C]
    simp
  rw [doublyNoised_vacuum, norm_add_sq (𝕜 := ℂ), hc,
    norm_sq_sqrt_pair (noiseVector₀_norm p i) (noiseVector₁_norm p i)
      (noiseVector_orthogonal p i i) h s hh hs]
  simp
  ring

 theorem C_vacuum_norm_sq_le (hp : 2 ≤ p) (i : Fin (p+1)) :
    ‖C p i (τ p).vacuum‖ ^ 2 ≤ 4 := by
  have h := (C p i).le_opNorm (τ p).vacuum
  rw [(τ p).norm_vacuum] at h
  have h' := C_norm_le p hp i
  nlinarith [norm_nonneg (C p i (τ p).vacuum)]

 theorem doublyNoised_fisher_lower (hp : 2 ≤ p) (h s : ℝ)
    (hh : 0 ≤ h) (hs : 0 ≤ s) (hu : 0 < h+s) :
    ENNReal.ofReal ((p+1 : ℕ)/(h+s+4)) ≤ freeFisher (τ p) (doublyNoised p h s) := by
  apply le_trans _ (freeFisher_lower_covariance (τ p) (doublyNoised p h s))
  apply ENNReal.ofReal_le_ofReal
  calc
    _ = ∑ _i : Fin (p+1), 1 / (h+s+4) := by simp [div_eq_mul_inv]
    _ ≤ _ := Finset.sum_le_sum (fun i _ => by
      apply one_div_le_one_div_of_le
      · rw [doublyNoised_variance p h s hh hs]
        nlinarith [sq_nonneg ‖C p i (τ p).vacuum‖]
      · rw [doublyNoised_variance p h s hh hs]
        linarith [C_vacuum_norm_sq_le p hp i])

end Model
end FiniteEntropySeparation

end

end OAI
