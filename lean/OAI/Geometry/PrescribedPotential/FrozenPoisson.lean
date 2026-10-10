import Mathlib
import OAI.Geometry.PrescribedPotential.AnalyticSupport

namespace OAI

/-! Frozen Poisson. -/

section

 

noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder SchwartzMap Real

namespace FrozenPoisson
open EllipticKernel
variable {n : ℕ}

 
lemma posDef_factor (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) :
    ∃ B : Matrix (Fin n) (Fin n) ℂ, IsUnit B ∧ H = star B * B := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hH.posSemidef.nonneg
  refine ⟨B, ?_, hB⟩
  rw [Matrix.isUnit_iff_isUnit_det]
  apply isUnit_iff_ne_zero.mpr
  intro hb
  have he := congrArg Matrix.det hB
  rw [Matrix.det_mul, hb, mul_zero] at he
  exact ne_of_gt hH.det_pos he

 

def symbol (H : Matrix (Fin n) (Fin n) ℂ) (ξ : EC n) : ℝ :=
  (2 * Real.pi)^2 * traceBilin H (rankOne ξ)

lemma trace_rankOne_factor (H B : Matrix (Fin n) (Fin n) ℂ)
    (hB : H⁻¹ = star B * B) (ξ : EC n) :
    traceBilin H (rankOne ξ) = (1/4 : ℝ) * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) B ξ‖^2 := by
  rw [traceBilin_apply, pull_rankOne, Matrix.mul_smul, Matrix.trace_smul]
  simp only [Complex.smul_re, smul_eq_mul]
  congr 1
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm, hB,
    ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  change (star (coordinateEquiv n ξ) ᵥ* Bᴴ ⬝ᵥ B *ᵥ coordinateEquiv n ξ).re = _
  rw [← Matrix.star_mulVec, dotProduct_comm]
  have he := EuclideanSpace.inner_eq_star_dotProduct
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) B ξ) (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) B ξ)
  rw [Matrix.ofLp_toEuclideanCLM] at he
  rw [coordinateEquiv_apply, ← he]
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast

lemma symbol_eq_norm_sq (H B : Matrix (Fin n) (Fin n) ℂ)
    (hB : H⁻¹ = star B * B) (ξ : EC n) :
    symbol H ξ = ‖Real.pi • Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) B ξ‖^2 := by
  rw [symbol, trace_rankOne_factor H B hB, norm_smul, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  ring

 
def factorMap (B : Matrix (Fin n) (Fin n) ℂ) : EC n →L[ℝ] EC n :=
  Real.pi • (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) B).restrictScalars ℝ

lemma factorMap_injective (B : Matrix (Fin n) (Fin n) ℂ) (hB : IsUnit B) :
    Function.Injective (factorMap B) := by
  intro x y h
  have he : Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) B x =
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) B y := by
    have hh := congrArg (fun w : EC n => (Real.pi⁻¹ : ℝ) • w) h
    simpa [factorMap, smul_smul, Real.pi_ne_zero] using hh
  apply WithLp.ofLp_injective
  apply Matrix.mulVec_injective_iff_isUnit.mpr hB
  exact congrArg WithLp.ofLp he

lemma symbol_eq_factorMap (H B : Matrix (Fin n) (Fin n) ℂ)
    (hB : H⁻¹ = star B * B) : symbol H = fun ξ => ‖factorMap B ξ‖^2 :=
  funext (symbol_eq_norm_sq H B hB)

lemma symbol_nonneg (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) (ξ : EC n) :
    0 ≤ symbol H ξ := by
  obtain ⟨B, _, hB⟩ := posDef_factor H⁻¹ hH.inv
  rw [symbol_eq_factorMap H B hB]
  positivity

lemma symbol_temperate (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) :
    (symbol H).HasTemperateGrowth := by
  obtain ⟨B, _, hB⟩ := posDef_factor H⁻¹ hH.inv
  rw [symbol_eq_factorMap H B hB]
  exact (Function.hasTemperateGrowth_norm_sq _).comp (factorMap B).hasTemperateGrowth

 

def inverseSymbol (H : Matrix (Fin n) (Fin n) ℂ) (ξ : EC n) : ℂ :=
  ((1 + symbol H ξ)⁻¹ : ℝ)

lemma inverseSymbol_temperate (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) :
    (inverseSymbol H).HasTemperateGrowth := by
  obtain ⟨B, _, hB⟩ := posDef_factor H⁻¹ hH.inv
  have he : inverseSymbol H = Complex.ofReal ∘
      ((fun ξ : EC n => (1 + ‖ξ‖^2)^(-1 : ℝ)) ∘ factorMap B) := by
    funext ξ
    simp only [Function.comp_apply, Real.rpow_neg_one, inverseSymbol,
      symbol_eq_factorMap H B hB]
  rw [he]
  exact Complex.hasTemperateGrowth_ofReal.comp
    ((Function.hasTemperateGrowth_one_add_norm_sq_rpow _ (-1)).comp
      (factorMap B).hasTemperateGrowth)

 

lemma inverseSymbol_weighted_bounded (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) :
    ∃ C, ∀ ξ : EC n, ‖(1 + ‖ξ‖^2 : ℝ) * inverseSymbol H ξ‖ ≤ C := by
  obtain ⟨B, hBu, hB⟩ := posDef_factor H⁻¹ hH.inv
  obtain ⟨K, _, hK⟩ := (factorMap B).toLinearMap.injective_iff_antilipschitz.mp
    (factorMap_injective B hBu)
  refine ⟨1 + (K : ℝ)^2, fun ξ => ?_⟩
  have hle := hK.le_mul_norm (map_zero (factorMap B)) ξ
  have hsq := pow_le_pow_left₀ (norm_nonneg ξ) hle 2
  change ‖ξ‖^2 ≤ ((K : ℝ) * ‖factorMap B ξ‖)^2 at hsq
  rw [mul_pow] at hsq
  simp only [inverseSymbol, symbol_eq_factorMap H B hB, ← Complex.ofReal_mul,
    Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity), mul_inv_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg (K : ℝ), sq_nonneg ‖factorMap B ξ‖]

open TemperedDistribution

 
def shifted (H : Matrix (Fin n) (Fin n) ℂ) :
    𝓢'(EC n, ℂ) →L[ℂ] 𝓢'(EC n, ℂ) :=
  fourierMultiplierCLM ℂ (fun ξ => ((1 + symbol H ξ : ℝ) : ℂ))

 
def resolvent (H : Matrix (Fin n) (Fin n) ℂ) :
    𝓢'(EC n, ℂ) →L[ℂ] 𝓢'(EC n, ℂ) :=
  fourierMultiplierCLM ℂ (inverseSymbol H)

lemma forward_temperate (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) :
    (fun ξ => ((1 + symbol H ξ : ℝ) : ℂ)).HasTemperateGrowth :=
  Complex.hasTemperateGrowth_ofReal.comp
    ((Function.HasTemperateGrowth.const 1).add (symbol_temperate H hH))

lemma shifted_resolvent (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (u : 𝓢'(EC n, ℂ)) : shifted H (resolvent H u) = u := by
  rw [shifted, resolvent,
    fourierMultiplierCLM_fourierMultiplierCLM_apply (inverseSymbol_temperate H hH)
      (forward_temperate H hH)]
  have he : inverseSymbol H * (fun ξ => ((1 + symbol H ξ : ℝ) : ℂ)) =
      fun _ => (1 : ℂ) := by
    funext ξ
    simp only [Pi.mul_apply, inverseSymbol, ← Complex.ofReal_mul]
    rw [inv_mul_cancel₀ (by linarith [symbol_nonneg H hH ξ]), Complex.ofReal_one]
  rw [he, fourierMultiplierCLM_const]
  simp

lemma resolvent_shifted (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (u : 𝓢'(EC n, ℂ)) : resolvent H (shifted H u) = u := by
  rw [shifted, resolvent,
    fourierMultiplierCLM_fourierMultiplierCLM_apply (forward_temperate H hH)
      (inverseSymbol_temperate H hH), mul_comm]
  have he : inverseSymbol H * (fun ξ => ((1 + symbol H ξ : ℝ) : ℂ)) =
      fun _ => (1 : ℂ) := by
    funext ξ
    simp only [Pi.mul_apply, inverseSymbol, ← Complex.ofReal_mul]
    rw [inv_mul_cancel₀ (by linarith [symbol_nonneg H hH ξ]), Complex.ofReal_one]
  rw [he, fourierMultiplierCLM_const]
  simp

 
theorem resolvent_memSobolev (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    {s : ℝ} {u : 𝓢'(EC n, ℂ)} (hu : MemSobolev s 2 u) :
    MemSobolev (s + 2) 2 (resolvent H u) := by
  rw [add_comm s 2, ← memSobolev_besselPotential_iff]
  have he : besselPotential (EC n) ℂ 2 (resolvent H u) =
      fourierMultiplierCLM ℂ (fun ξ => (1 + ‖ξ‖^2 : ℝ) * inverseSymbol H ξ) u := by
    rw [besselPotential, resolvent,
      fourierMultiplierCLM_fourierMultiplierCLM_apply (inverseSymbol_temperate H hH)
        (by fun_prop)]
    congr 2
    ext ξ
    simp [mul_comm]
  rw [he]
  apply hu.fourierMultiplierCLM_of_bounded _ (inverseSymbol_weighted_bounded H hH)
  have hi := inverseSymbol_temperate H hH
  fun_prop

 

theorem frozen_sobolev_resolvent (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    {s : ℝ} (f : 𝓢'(EC n, ℂ)) (hf : MemSobolev s 2 f) :
    ∃! u : 𝓢'(EC n, ℂ), shifted H u = f ∧ MemSobolev (s + 2) 2 u := by
  refine ⟨resolvent H f, ⟨shifted_resolvent H hH f, resolvent_memSobolev H hH hf⟩, ?_⟩
  intro u hu
  rw [← hu.1, resolvent_shifted H hH]

 
open LineDeriv

section BilinearExpansion
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι]

def rankTwo (v w : E) : Bilin E := (realInner v).smulRight (realInner w)

lemma bilin_expansion (b : OrthonormalBasis ι ℝ E) (B : Bilin E) :
    B = ∑ i, ∑ j, B (b i) (b j) • rankTwo (b i) (b j) := by
  ext x y
  conv_lhs => rw [← b.sum_repr' x, ← b.sum_repr' y]
  simp only [map_sum, map_smul, _root_.sum_apply,
    _root_.smul_apply, smul_eq_mul, rankTwo,
    ContinuousLinearMap.smulRight_apply, realInner_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma second_symbol_expansion (b : OrthonormalBasis ι ℝ E) (L : SecondOrder E) (ξ : E) :
    L (rankOne ξ) = ∑ i, ∑ j,
      L (rankTwo (b i) (b j)) * inner ℝ ξ (b i) * inner ℝ ξ (b j) := by
  rw [bilin_expansion b (rankOne ξ)]
  simp only [map_sum, map_smul, rankOne, ContinuousLinearMap.smulRight_apply,
    _root_.smul_apply, realInner_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring
end BilinearExpansion

section Differential
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma second_deriv_multiplier (v w : E) (u : 𝓢'(E, ℂ)) :
    ∂_{v} (∂_{w} u) = fourierMultiplierCLM ℂ
      (fun ξ => (-(2 * Real.pi)^2 : ℂ) * (inner ℝ ξ v : ℂ) * (inner ℝ ξ w : ℂ)) u := by
  rw [lineDeriv_eq_fourierMultiplierCLM, lineDeriv_eq_fourierMultiplierCLM,
    ContinuousLinearMap.map_smul,
    fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop) (by fun_prop),
    smul_smul]
  have hg : ((fun ξ => (inner ℝ ξ w : ℂ)) * (fun ξ => (inner ℝ ξ v : ℂ))).HasTemperateGrowth := by
    fun_prop
  rw [← _root_.smul_apply, ← fourierMultiplierCLM_smul hg]
  congr 2
  ext ξ
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  have hi := Complex.I_sq
  calc
    _ = ((2 * Real.pi : ℂ)^2 * Complex.I^2) *
          (inner ℝ ξ w : ℂ) * (inner ℝ ξ v : ℂ) := by ring
    _ = _ := by rw [hi]; ring

lemma multiplier_sub {g₁ g₂ : E → ℂ}
    (h₁ : g₁.HasTemperateGrowth) (h₂ : g₂.HasTemperateGrowth) (u : 𝓢'(E, ℂ)) :
    fourierMultiplierCLM ℂ (g₁ - g₂) u =
      fourierMultiplierCLM ℂ g₁ u - fourierMultiplierCLM ℂ g₂ u := by
  simp only [fourierMultiplierCLM_apply]
  rw [smulLeftCLM_sub h₁ h₂, _root_.sub_apply]
  simp only [sub_eq_add_neg, FourierTransform.fourierInv_add, FourierTransform.fourierInv_neg]

end Differential

section DifferentialExpansion
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι]

 

def differentialWithBasis (b : OrthonormalBasis ι ℝ E) (L : SecondOrder E) :
    𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ) :=
  ∑ i, ∑ j, (L (rankTwo (b i) (b j)) : ℂ) •
    (lineDerivOpCLM ℂ 𝓢'(E, ℂ) (b i) ∘L lineDerivOpCLM ℂ 𝓢'(E, ℂ) (b j))

lemma differentialWithBasis_fourier (b : OrthonormalBasis ι ℝ E)
    (L : SecondOrder E) (u : 𝓢'(E, ℂ)) :
    differentialWithBasis b L u = fourierMultiplierCLM ℂ
      (fun ξ => (-(2 * Real.pi)^2 : ℂ) * (L (rankOne ξ) : ℂ)) u := by
  let a : ι → ι → E → ℂ := fun i j ξ => (L (rankTwo (b i) (b j)) : ℂ) *
    ((-(2 * Real.pi)^2 : ℂ) * (inner ℝ ξ (b i) : ℂ) * (inner ℝ ξ (b j) : ℂ))
  have ha i j : (a i j).HasTemperateGrowth := by dsimp [a]; fun_prop
  have ht i j : (L (rankTwo (b i) (b j)) : ℂ) • ∂_{b i} (∂_{b j} u) =
      fourierMultiplierCLM ℂ (a i j) u := by
    rw [second_deriv_multiplier, ← _root_.smul_apply,
      ← fourierMultiplierCLM_smul (by fun_prop)]
    rfl
  have hm : fourierMultiplierCLM ℂ (fun ξ => ∑ i, ∑ j, a i j ξ) =
      ∑ i, ∑ j, fourierMultiplierCLM ℂ (a i j) := by
    rw [fourierMultiplierCLM_sum ℂ (by intro i _; fun_prop)]
    apply Finset.sum_congr rfl
    intro i _
    exact fourierMultiplierCLM_sum ℂ (fun j _ => ha i j)
  simp only [differentialWithBasis, _root_.sum_apply, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, lineDerivOpCLM_apply, ht]
  have hsum : (∑ i, ∑ j, fourierMultiplierCLM ℂ (a i j)) u =
      ∑ i, ∑ j, fourierMultiplierCLM ℂ (a i j) u := by
    simp only [_root_.sum_apply]
  rw [← hsum, ← hm]
  congr 2
  ext ξ
  rw [second_symbol_expansion b L ξ]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp [a]
  ring

end DifferentialExpansion

 
def frozenDifferential (H : Matrix (Fin n) (Fin n) ℂ) :
    𝓢'(EC n, ℂ) →L[ℂ] 𝓢'(EC n, ℂ) :=
  differentialWithBasis (stdOrthonormalBasis ℝ (EC n)) (traceBilin H)

lemma frozenDifferential_fourier (H : Matrix (Fin n) (Fin n) ℂ) (u : 𝓢'(EC n, ℂ)) :
    frozenDifferential H u = fourierMultiplierCLM ℂ (fun ξ => (-symbol H ξ : ℝ)) u := by
  rw [frozenDifferential, differentialWithBasis_fourier]
  congr 2
  ext ξ
  simp only [symbol, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_ofNat, neg_mul]

lemma shifted_eq_identity_sub (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (u : 𝓢'(EC n, ℂ)) : shifted H u = u - frozenDifferential H u := by
  rw [frozenDifferential_fourier]
  have hn : (fun ξ => ((-symbol H ξ : ℝ) : ℂ)).HasTemperateGrowth :=
    Complex.hasTemperateGrowth_ofReal.comp (symbol_temperate H hH).neg
  have he := multiplier_sub (Function.HasTemperateGrowth.const (1 : ℂ)) hn u
  simpa only [Pi.sub_def, Complex.ofReal_neg, sub_neg_eq_add, shifted,
    Complex.ofReal_add, Complex.ofReal_one, fourierMultiplierCLM_const,
    _root_.smul_apply, ContinuousLinearMap.id_apply, one_smul] using he

 

theorem frozen_differential_sobolev_resolvent
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    {s : ℝ} (f : 𝓢'(EC n, ℂ)) (hf : MemSobolev s 2 f) :
    ∃! u : 𝓢'(EC n, ℂ), u - frozenDifferential H u = f ∧ MemSobolev (s + 2) 2 u := by
  simpa only [← shifted_eq_identity_sub H hH] using frozen_sobolev_resolvent H hH f hf

section SmoothComparison
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι]

 
def smoothDifferentialWithBasis (b : OrthonormalBasis ι ℝ E) (L : SecondOrder E) :
    𝓢(E, ℝ) →L[ℝ] 𝓢(E, ℝ) :=
  ∑ i, ∑ j, L (rankTwo (b i) (b j)) •
    (lineDerivOpCLM ℝ 𝓢(E, ℝ) (b i) ∘L lineDerivOpCLM ℝ 𝓢(E, ℝ) (b j))

lemma smooth_second_deriv (f : 𝓢(E, ℝ)) (v w x : E) :
    (∂_{v} (∂_{w} f)) x = fderiv ℝ (fderiv ℝ f) x v w := by
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  change fderiv ℝ (fun y => fderiv ℝ f y w) x v = _
  exact PotentialKaehler.fderiv_eval_derivative f.smooth'.contDiffAt v w

lemma smoothDifferentialWithBasis_apply (b : OrthonormalBasis ι ℝ E)
    (L : SecondOrder E) (f : 𝓢(E, ℝ)) (x : E) :
    smoothDifferentialWithBasis b L f x = L (fderiv ℝ (fderiv ℝ f) x) := by
  rw [bilin_expansion b (fderiv ℝ (fderiv ℝ f) x)]
  simp only [smoothDifferentialWithBasis, _root_.sum_apply, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, lineDerivOpCLM_apply, smooth_second_deriv, map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

def complexify : 𝓢(E, ℝ) →L[ℝ] 𝓢(E, ℂ) :=
  SchwartzMap.postcompCLM Complex.ofRealCLM

lemma complexify_deriv (f : 𝓢(E, ℝ)) (v : E) :
    complexify (∂_{v} f) = ∂_{v} (complexify f) := by
  ext x
  change Complex.ofReal (fderiv ℝ f x v) =
    fderiv ℝ (Complex.ofRealCLM ∘ f) x v
  rw [(Complex.ofRealCLM.hasFDerivAt.comp x (f.hasFDerivAt x)).fderiv]
  rfl

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma weak_complexify_deriv (f : 𝓢(E, ℝ)) (v : E) :
    (complexify (∂_{v} f) : 𝓢'(E, ℂ)) = ∂_{v} (complexify f : 𝓢'(E, ℂ)) := by
  rw [complexify_deriv]
  exact (TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq _ v).symm

lemma differentialWithBasis_real (b : OrthonormalBasis ι ℝ E)
    (L : SecondOrder E) (f : 𝓢(E, ℝ)) :
    differentialWithBasis b L (complexify f : 𝓢'(E, ℂ)) =
      (complexify (smoothDifferentialWithBasis b L f) : 𝓢'(E, ℂ)) := by
  simp only [differentialWithBasis, smoothDifferentialWithBasis,
    _root_.sum_apply, _root_.smul_apply, ContinuousLinearMap.comp_apply,
    lineDerivOpCLM_apply, map_sum, map_smul]
  simp only [ContinuousLinearMap.map_smul_of_tower]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [weak_complexify_deriv, weak_complexify_deriv]
  apply ContinuousLinearMap.ext
  intro h
  exact Complex.coe_smul _ _

end SmoothComparison

 

lemma frozenDifferential_real_trace (H : Matrix (Fin n) (Fin n) ℂ) (f : 𝓢(EC n, ℝ)) :
    ∃ l : 𝓢(EC n, ℝ),
      (∀ x, l x = traceBilin H (fderiv ℝ (fderiv ℝ f) x)) ∧
      frozenDifferential H (SchwartzMap.toTemperedDistributionCLM (EC n) ℂ
        MeasureTheory.volume (complexify f)) =
      SchwartzMap.toTemperedDistributionCLM (EC n) ℂ MeasureTheory.volume (complexify l) := by
  refine ⟨smoothDifferentialWithBasis (stdOrthonormalBasis ℝ (EC n)) (traceBilin H) f, ?_, ?_⟩
  · exact fun x => smoothDifferentialWithBasis_apply _ _ _ x
  · exact differentialWithBasis_real _ _ _

end FrozenPoisson

end
end

end OAI
