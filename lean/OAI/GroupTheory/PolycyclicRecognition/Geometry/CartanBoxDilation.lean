import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanWeightDilation
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanGroupBoxes
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentAutomorphism

namespace OAI

/-! # Exact template shifts for actual Cartan boxes

The scalar action on generalized weight spaces is a genuine Lie automorphism.
It takes each scaled word basis to the basis for the translated template.
The finite Dynkin identity then integrates it to the needed group automorphism.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieModule LieAlgebra
open scoped BigOperators Manifold

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

omit hunimod [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] eW in
/-- Every actual bracket word is scaled by the exponential of its total
weight, even when its total weight is zero. -/
theorem idealWeightDilation_word (h : H) (w : FreeMagma (Fin M.letterCount)) :
    cartanIdealWeightDilation T H h (evalBracketWord M.letter w) =
      Real.exp (bracketWordExponent (fun i => M.weight i h) w) • evalBracketWord M.letter w := by
  induction w using FreeMagma.rec with
  | of i =>
    rw [evalBracketWord_of, bracketWordExponent_of]
    apply Subtype.ext
    exact cartanWeightScale_apply_root T H h (M.weight i) (M.letter_root i)
  | mul u v hu hv =>
    change cartanIdealWeightDilation T H h (evalBracketWord M.letter (u * v)) =
      Real.exp (bracketWordExponent (fun i => M.weight i h) (u * v)) •
        evalBracketWord M.letter (u * v)
    rw [evalBracketWord_mul, LieEquiv.map_lie, hu, hv, bracketWordExponent_mul,
      Real.exp_add, smul_lie, lie_smul, smul_smul]

/-- Translation adds the total word weight to its box exponent. -/
theorem boxCost_translate {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    (w : W) (z : M.wordList) :
    M.boxCost T hunimod eW ((fun x => x + w) '' E) z =
      M.boxCost T hunimod eW E z +
        bracketWordExponent (fun i => M.weight i (cartanHeightSection T H (eW.symm w))) z := by
  unfold boxCost
  have hs : (M.supportIn T hunimod eW).weightSupport ((fun x => x + w) '' E) =
      (M.supportIn T hunimod eW).weightSupport E +
        (fun i => M.weight i (cartanHeightSection T H (eW.symm w))) := by
    funext i
    exact (M.supportIn T hunimod eW).weightSupport_translate hE hne w i
  rw [hs, bracketWordExponent_add]

/-- All word bases keep their determinant exponent under template translation. -/
theorem columnBasisWeight_boxCost_translate {E : Set W}
    (hE : IsCompact E) (hne : E.Nonempty) (w : W) (β : M.Bases) :
    columnBasisWeight (M.boxCost T hunimod eW ((fun x => x + w) '' E)) β.val =
      columnBasisWeight (M.boxCost T hunimod eW E) β.val := by
  rw [M.columnBasisWeight_boxCost, M.columnBasisWeight_boxCost]
  exact (M.supportIn T hunimod eW).basisTemplateSupport_translate hE hne w β

/-- Thus a maximizing basis remains maximizing after translation. -/
theorem maximizing_box_basis_translate
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {E : Set W} (hE : IsCompact E) (hne : E.Nonempty) (w : W) (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val) :
    IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW ((fun x => x + w) '' E)) β.val := by
  refine ⟨hβ.1, ?_⟩
  intro z hz
  let γ := wordBasisOfDet M.letter M.wordList b₀ z hz
  change columnBasisWeight (M.boxCost T hunimod eW ((fun x => x + w) '' E)) γ.val ≤ _
  rw [M.columnBasisWeight_boxCost_translate T hunimod eW hE hne w γ,
    M.columnBasisWeight_boxCost_translate T hunimod eW hE hne w β]
  exact hβ.2 z hz

/-- The scaled basis itself shifts exactly, with no loss in its radius. -/
theorem idealWeightDilation_boxBasis {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    (w : W) (β : M.Bases) (r : ℝ) :
    (M.boxBasis T hunimod eW E β r).map
      (cartanIdealWeightDilation T H (r • cartanHeightSection T H (eW.symm w))).toLinearEquiv =
        M.boxBasis T hunimod eW ((fun x => x + w) '' E) β r := by
  apply DFunLike.ext
  intro j
  simp only [Basis.map_apply, boxBasis, exponentialRescaleBasis, Basis.unitsSMul_apply,
    Units.smul_def, Units.val_mk0, map_smul]
  have hword := M.idealWeightDilation_word T (r • cartanHeightSection T H (eW.symm w)) (β.val j)
  have hb := WordBasisSelections.eval_words M.letter M.wordList β j
  change evalBracketWord M.letter (β.val j) = _ at hb
  rw [hb] at hword
  change Real.exp (r * M.boxCost T hunimod eW E (β.val j)) •
    cartanIdealWeightDilation T H (r • cartanHeightSection T H (eW.symm w))
      (WordBasisSelections.basis M.letter M.wordList β j) =
    Real.exp (r * M.boxCost T hunimod eW ((fun x => x + w) '' E) (β.val j)) •
      WordBasisSelections.basis M.letter M.wordList β j
  rw [hword, M.boxCost_translate T hunimod eW hE hne, smul_smul]
  have he : bracketWordExponent (fun i => M.weight i
      (r • cartanHeightSection T H (eW.symm w))) (β.val j) =
      r * bracketWordExponent (fun i => M.weight i
        (cartanHeightSection T H (eW.symm w))) (β.val j) := by
    simp only [bracketWordExponent, map_smul, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, ← Real.exp_add]
  congr 2
  ring

variable {EN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N]
  (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
  (Exp : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExp : IsGroupExponential Exp)
  (hbij : Function.Bijective Exp) (dynkin : NilpotentDynkinExpansionInput EN N)

/-- Exact weight dilation in the actual nilpotent group. -/
def groupWeightDilation (w : W) (r : ℝ) : N ≃* N :=
  integrateNilpotentLieEquiv eN Exp hbij dynkin hExp M.bound_zero
    (cartanIdealWeightDilation T H (r • cartanHeightSection T H (eW.symm w)))

/-- The exponential image of a coordinate cube shifts with its basis. -/
theorem groupWeightDilation_box {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    (w : W) (β : M.Bases) (r R : ℝ) :
    M.groupWeightDilation T eW eN Exp hExp hbij dynkin w r ''
      M.groupBox T hunimod eW (Exp ∘ eN) E β r R =
        M.groupBox T hunimod eW (Exp ∘ eN) ((fun x => x + w) '' E) β r R := by
  let F := cartanIdealWeightDilation T H (r • cartanHeightSection T H (eW.symm w))
  let b := M.boxBasis T hunimod eW E β r
  have hb := M.idealWeightDilation_boxBasis T hunimod eW hE hne w β r
  change b.map F.toLinearEquiv = _ at hb
  ext g
  constructor
  · rintro ⟨_, ⟨x, rfl, hx⟩, rfl⟩
    refine ⟨F x, ?_, ?_⟩
    · exact (integrateNilpotentLieEquiv_apply_exp eN Exp hbij dynkin hExp M.bound_zero F x).symm
    · change ‖(M.boxBasis T hunimod eW ((fun x => x + w) '' E) β r).equivFun (F x)‖ ≤ R
      rw [← hb]
      change ‖b.equivFun (F.symm (F x))‖ ≤ R
      simpa only [F.symm_apply_apply] using hx
  · rintro ⟨x, rfl, hx⟩
    refine ⟨(Exp ∘ eN) (F.symm x), ⟨F.symm x, rfl, ?_⟩, ?_⟩
    · change ‖b.equivFun (F.symm x)‖ ≤ R
      change ‖(M.boxBasis T hunimod eW ((fun x => x + w) '' E) β r).equivFun x‖ ≤ R at hx
      rw [← hb] at hx
      exact hx
    · change integrateNilpotentLieEquiv eN Exp hbij dynkin hExp M.bound_zero F
        (Exp (eN (F.symm x))) = Exp (eN x)
      rw [integrateNilpotentLieEquiv_apply_exp, F.apply_symm_apply]

end PolycyclicRecognition.CartanWordModel

end

end OAI
