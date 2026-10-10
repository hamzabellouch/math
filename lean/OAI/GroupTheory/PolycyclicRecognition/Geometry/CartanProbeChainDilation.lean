import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoxDilation

namespace OAI

/-! # Exact translation of the normalized probe generator chains -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set
open scoped Manifold

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- The exact weight dilation preserves the coordinate bound when the
reference template is translated by the pivot height. -/
theorem probe_dilation_coordinate_norm {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    (w : W) (β : M.Bases) (r : ℝ) (v : cartanRootIdeal H) :
    ‖(M.boxBasis T hunimod eW ((fun x => x + w) '' E) β r).equivFun
      (cartanIdealWeightDilation T H (r • cartanHeightSection T H (eW.symm w)) v)‖ =
      ‖(M.boxBasis T hunimod eW E β r).equivFun v‖ := by
  rw [← M.idealWeightDilation_boxBasis T hunimod eW hE hne w β r]
  change ‖(M.boxBasis T hunimod eW E β r).equivFun
    ((cartanIdealWeightDilation T H (r • cartanHeightSection T H (eW.symm w))).symm
      (cartanIdealWeightDilation T H (r • cartanHeightSection T H (eW.symm w)) v))‖ = _
  rw [LieEquiv.symm_apply_apply]

/-- The same dilation translates the generator amplitude exponent exactly. -/
theorem probe_dilation_coefficient_bound {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    (w : W) (r t B : ℝ) (i : Fin M.letterCount)
    (ht : |t| ≤ B * Real.exp (r * (M.supportIn T hunimod eW).weightSupport E i)) :
    |t * Real.exp (r * M.weight i (cartanHeightSection T H (eW.symm w)))| ≤
      B * Real.exp (r * (M.supportIn T hunimod eW).weightSupport ((fun x => x + w) '' E) i) := by
  rw [(M.supportIn T hunimod eW).weightSupport_translate hE hne w i,
    abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ (B * Real.exp (r * (M.supportIn T hunimod eW).weightSupport E i)) *
        Real.exp (r * M.weight i (cartanHeightSection T H (eW.symm w))) :=
      mul_le_mul_of_nonneg_right ht (Real.exp_pos _).le
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      simp only [supportIn, SupportDatum.transport, supportDatum_weight,
        cartanHeightWeight, LinearMap.comp_apply, LinearEquiv.coe_coe, Weight.toLinear_apply]
      ring

variable {EN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N]

omit hunimod [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] eW in
/-- Dilation carries each actual generator edge to the same letter with
its explicitly rescaled coefficient. -/
theorem probe_dilation_generator_step
    (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
    (ExpN : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExpN : IsGroupExponential ExpN)
    (hbij : Function.Bijective ExpN) (dynkin : NilpotentDynkinExpansionInput EN N)
    (h : H) (u v : cartanRootIdeal H) (i : Fin M.letterCount) (t : ℝ)
    (hedge : ExpN (eN v) = ExpN (eN u) * ExpN (eN (t • M.letter i))) :
    ExpN (eN (cartanIdealWeightDilation T H h v)) =
      ExpN (eN (cartanIdealWeightDilation T H h u)) *
        ExpN (eN ((t * Real.exp (M.weight i h)) • M.letter i)) := by
  let D := cartanIdealWeightDilation T H h
  let S := integrateNilpotentLieEquiv eN ExpN hbij dynkin hExpN M.bound_zero D
  have hS (x : cartanRootIdeal H) : S (ExpN (eN x)) = ExpN (eN (D x)) :=
    integrateNilpotentLieEquiv_apply_exp eN ExpN hbij dynkin hExpN M.bound_zero D x
  have hletter : D (t • M.letter i) = (t * Real.exp (M.weight i h)) • M.letter i := by
    rw [map_smul]
    have hi := M.idealWeightDilation_word T h (FreeMagma.of i)
    simp only [evalBracketWord_of, bracketWordExponent_of] at hi
    rw [hi, smul_smul]
  calc
    _ = S (ExpN (eN v)) := (hS v).symm
    _ = S (ExpN (eN u)) * S (ExpN (eN (t • M.letter i))) := by rw [hedge, map_mul]
    _ = _ := by rw [hS, hS, hletter]

end PolycyclicRecognition.CartanWordModel

end

end OAI
