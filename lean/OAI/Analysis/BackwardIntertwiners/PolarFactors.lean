import OAI.Analysis.BackwardIntertwiners.SpectralProjections

namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

open Topology MeasureTheory Set
open scoped ENNReal

open scoped Classical

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def coordinateShift (n : ℤ) : GlobalHilbert →L[ℂ] GlobalHilbert :=
  (fiberReindex (Equiv.addRight (-n))).toLinearIsometry.toContinuousLinearMap.compLpL 2 baseMeasure
lemma coordinateShift_ae (n : ℤ) (f : GlobalHilbert) :
    ∀ᵐ x ∂baseMeasure, ∀ j, coordinateShift n f x j = f x (j-n) := by
  filter_upwards [ContinuousLinearMap.coeFn_compLpL
    (fiberReindex (Equiv.addRight (-n))).toLinearIsometry.toContinuousLinearMap f] with x hx j
  change coordinateShift n f x = fiberReindex (Equiv.addRight (-n)) (f x) at hx
  rw [hx]
  rfl
lemma coordinateShift_zero : coordinateShift 0 = 1 := by
  ext1 f
  apply Lp.ext
  filter_upwards [coordinateShift_ae 0 f] with x hx
  ext j
  simpa using hx j
lemma coordinateShift_add (m n : ℤ) : coordinateShift (m+n) = coordinateShift m * coordinateShift n := by
  ext1 f
  apply Lp.ext
  filter_upwards [coordinateShift_ae (m+n) f,coordinateShift_ae m (coordinateShift n f),
    coordinateShift_ae n f] with x hmn hm hn
  ext j
  change coordinateShift (m+n) f x j = coordinateShift m (coordinateShift n f) x j
  rw [hmn,hm,hn]
  exact congrArg (fun k : ℤ => f x k) (by omega)
lemma coordinateShift_norm_le (n : ℤ) (f : GlobalHilbert) : ‖coordinateShift n f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [ContinuousLinearMap.coeFn_compLpL
    (fiberReindex (Equiv.addRight (-n))).toLinearIsometry.toContinuousLinearMap f] with x hx
  change coordinateShift n f x = fiberReindex (Equiv.addRight (-n)) (f x) at hx
  rw [hx]
  exact le_of_eq ((fiberReindex _).norm_map _)
lemma coordinateShift_norm (n : ℤ) (f : GlobalHilbert) : ‖coordinateShift n f‖ = ‖f‖ := by
  apply le_antisymm (coordinateShift_norm_le n f)
  have h : coordinateShift (-n) (coordinateShift n f) = f := by
    have hh := congrArg (fun T : GlobalHilbert →L[ℂ] GlobalHilbert => T f) (coordinateShift_add (-n) n)
    simpa only [neg_add_cancel,coordinateShift_zero,one_apply_eq_self,mul_apply_eq_comp] using hh.symm
  have hn := coordinateShift_norm_le (-n) (coordinateShift n f)
  rwa [h] at hn


def shiftIsometry (n : ℤ) : GlobalHilbert ≃ₗᵢ[ℂ] GlobalHilbert where
  toFun := coordinateShift n
  invFun := coordinateShift (-n)
  map_add' := (coordinateShift n).map_add
  map_smul' := (coordinateShift n).map_smul
  left_inv f := by
    have h := congrArg (fun T : GlobalHilbert →L[ℂ] GlobalHilbert => T f) (coordinateShift_add (-n) n)
    simpa only [neg_add_cancel,coordinateShift_zero,one_apply_eq_self,mul_apply_eq_comp] using h.symm
  right_inv f := by
    have h := congrArg (fun T : GlobalHilbert →L[ℂ] GlobalHilbert => T f) (coordinateShift_add n (-n))
    simpa only [add_neg_cancel,coordinateShift_zero,one_apply_eq_self,mul_apply_eq_comp] using h.symm
  norm_map' := coordinateShift_norm n
lemma coordinateShift_star (n : ℤ) : star (coordinateShift n) = coordinateShift (-n) := by
  change (coordinateShift n).adjoint = _
  exact (ContinuousLinearMap.eq_adjoint_iff _ _).mpr (by
    intro f g
    change inner ℂ (shiftIsometry (-n) f) g = inner ℂ f (shiftIsometry n g)
    have h := (shiftIsometry n).inner_map_map (shiftIsometry (-n) f) g
    have he : shiftIsometry n (shiftIsometry (-n) f) = f := (shiftIsometry n).apply_symm_apply f
    rw [he] at h
    exact h.symm) |>.symm

def shiftUnit : (GlobalHilbert →L[ℂ] GlobalHilbert)ˣ where
  val := coordinateShift 1
  inv := coordinateShift (-1)
  val_inv := by rw [←coordinateShift_add]; norm_num [coordinateShift_zero]
  inv_val := by rw [←coordinateShift_add]; norm_num [coordinateShift_zero]
lemma shiftUnit_zpow (n : ℤ) : ((shiftUnit^n : (GlobalHilbert →L[ℂ] GlobalHilbert)ˣ) : GlobalHilbert →L[ℂ] GlobalHilbert) = coordinateShift n := by
  induction n using Int.induction_on with
  | zero => simp [coordinateShift_zero]
  | succ n ih => rw [zpow_add_one,Units.val_mul,ih]; exact (coordinateShift_add _ _).symm
  | pred n ih => rw [zpow_sub_one,Units.val_mul,ih]; exact (coordinateShift_add _ _).symm

lemma forward_polar_factor : forwardOperator = coordinateShift 1 * polarDiagonal 0 := by
  ext1 f
  apply Lp.ext
  filter_upwards [forwardOperator_ae f,coordinateShift_ae 1 (polarDiagonal 0 f),polarDiagonal_ae 0 f] with x hs hu hd
  ext j
  change forwardOperator f x j = coordinateShift 1 (polarDiagonal 0 f) x j
  rw [hs,forwardFiber_apply,hu,hd,add_zero]
lemma polarDiagonal_conjugate (n : ℤ) :
    coordinateShift (-n) * polarDiagonal 0 * coordinateShift n = polarDiagonal n := by
  ext1 f
  apply Lp.ext
  filter_upwards [coordinateShift_ae (-n) (polarDiagonal 0 (coordinateShift n f)),
    polarDiagonal_ae 0 (coordinateShift n f),coordinateShift_ae n f,polarDiagonal_ae n f] with x hu hd hv ha
  ext j
  change coordinateShift (-n) (polarDiagonal 0 (coordinateShift n f)) x j = polarDiagonal n f x j
  rw [hu,hd,hv,ha]
  simp only [sub_neg_eq_add,add_zero,add_sub_cancel_right]

def betaRootSymbol : DiagonalSymbol :=
  ⟨fun x j => (Real.sqrt (explicitBeta x j):ℂ),
    ⟨fun j => Complex.continuous_ofReal.measurable.comp (Real.continuous_sqrt.measurable.comp (measurable_explicitBeta j)),
      1, zero_le_one, fun x j => by
        simp only [Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
        apply Real.sqrt_le_one.mpr
        exact (explicitBeta_le x j).trans (Real.exp_le_one_iff.mpr (by norm_num))⟩⟩
lemma betaRootSymbol_star : star betaRootSymbol = betaRootSymbol := by
  apply Subtype.ext
  funext x j
  exact Complex.conj_ofReal _
lemma betaRootSymbol_sq : betaRootSymbol * betaRootSymbol = betaSymbol 0 := by
  apply Subtype.ext
  funext x j
  change (Real.sqrt (explicitBeta x j):ℂ) * (Real.sqrt (explicitBeta x j):ℂ) = (explicitBeta x (j+0):ℂ)
  rw [add_zero,←Complex.ofReal_mul,Real.mul_self_sqrt (explicitBeta_pos _ _).le]
lemma polarDiagonal_nonneg : 0 ≤ polarDiagonal 0 := by
  have h := star_mul_self_nonneg (diagonalOperator betaRootSymbol)
  rwa [←diagonalOperator_star,betaRootSymbol_star,←diagonalOperator_mul,betaRootSymbol_sq] at h
local instance realOperatorTower : IsScalarTower ℝ (GlobalHilbert →L[ℂ] GlobalHilbert) (GlobalHilbert →L[ℂ] GlobalHilbert) where
  smul_assoc scalar first second := by ext vector; rfl
local instance realOperatorCommute : SMulCommClass ℝ (GlobalHilbert →L[ℂ] GlobalHilbert) (GlobalHilbert →L[ℂ] GlobalHilbert) where
  smul_comm scalar first second := by
    apply ContinuousLinearMap.ext
    intro vector
    exact (first.map_smul_of_tower scalar (second vector)).symm
local instance complexNormalCalculus : ContinuousFunctionalCalculus ℂ (GlobalHilbert →L[ℂ] GlobalHilbert) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus
local instance complexClosedCalculus : NonUnitalClosedEmbeddingContinuousFunctionalCalculus ℂ (GlobalHilbert →L[ℂ] GlobalHilbert) IsStarNormal :=
  IsStarNormal.instNonUnitalContinuousFunctionalCalculus
local instance realSelfAdjointCalculus : NonUnitalContinuousFunctionalCalculus ℝ (GlobalHilbert →L[ℂ] GlobalHilbert) IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus (A := GlobalHilbert →L[ℂ] GlobalHilbert)
lemma polar_modulus : CFC.sqrt (star forwardOperator * forwardOperator) = polarDiagonal 0 := by
  rw [forward_polar_factor,star_mul,coordinateShift_star,mul_assoc,
    ←mul_assoc (coordinateShift (-1)) (coordinateShift 1),←coordinateShift_add]
  norm_num only [Int.reduceNeg,Int.reduceAdd,coordinateShift_zero,one_mul]
  rw [(polarDiagonal_selfAdjoint 0).star_eq]
  exact CFC.sqrt_mul_self _ polarDiagonal_nonneg
lemma polarDiagonal_injective : Function.Injective (polarDiagonal 0) := by
  intro f g he
  apply Lp.ext
  filter_upwards [polarDiagonal_ae 0 f,polarDiagonal_ae 0 g] with x hf hg
  ext j
  have h := congrArg (fun v : GlobalHilbert => v x j) he
  rw [hf,hg] at h
  exact mul_left_cancel₀ (by exact_mod_cast (explicitBeta_pos x (j+0)).ne') h
lemma polarDiagonal_denseRange : DenseRange (polarDiagonal 0) := by
  have hk : (polarDiagonal 0).ker = ⊥ := LinearMap.ker_eq_bot.mpr polarDiagonal_injective
  have hadj : (polarDiagonal 0).adjoint = polarDiagonal 0 := (polarDiagonal_selfAdjoint 0).star_eq
  have hc : (polarDiagonal 0).range.topologicalClosure = ⊤ := by
    rw [←Submodule.orthogonal_orthogonal_eq_closure,ContinuousLinearMap.orthogonal_range,hadj,hk,Submodule.bot_orthogonal_eq_top]
  intro v
  change v ∈ (polarDiagonal 0).range.topologicalClosure
  rw [hc]
  trivial


end
end BackwardIntertwiners

end OAI
