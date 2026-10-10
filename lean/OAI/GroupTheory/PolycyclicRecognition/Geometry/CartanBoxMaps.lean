import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanRootWidths
import OAI.GroupTheory.PolycyclicRecognition.Geometry.FiniteLieNorm

namespace OAI

/-! # Propagating root-action bounds through Cartan boxes

A Lie map which preserves the letter root spaces has a polynomial bound in
every maximizing box. The proof propagates the bounds on letters through
actual bracket words, then through their coordinate basis. This is the
algebraic step in the box-conjugation estimate.
-/

noncomputable section

namespace PolycyclicRecognition

open Module
open scoped BigOperators Manifold

variable {I L : Type*} [LieRing L] [LieAlgebra ℝ L] [Fintype I] [DecidableEq I]

/-- Independent exponential scaling of letters multiplies a word by the
exponential of the sum of its letter exponents. -/
theorem evalBracketWord_exp_smul (X : I → L) (s : I → ℝ) (r : ℝ) (w : FreeMagma I) :
    evalBracketWord (fun i => Real.exp (r * s i) • X i) w =
      Real.exp (r * bracketWordExponent s w) • evalBracketWord X w := by
  induction w using FreeMagma.rec with
  | of i => simp only [evalBracketWord_of, bracketWordExponent_of]
  | mul u v hu hv =>
    change evalBracketWord (fun i => Real.exp (r * s i) • X i) (u * v) =
      Real.exp (r * bracketWordExponent s (u * v)) • evalBracketWord X (u * v)
    rw [evalBracketWord_mul, hu, hv, smul_lie, lie_smul, smul_smul,
      ← Real.exp_add, bracketWordExponent_mul, mul_add, evalBracketWord_mul]

/-- A bound on the images of basis vectors bounds the full linear map in
the coordinate maximum norm. -/
theorem norm_basis_linearMap_le {J : Type*} [Fintype J] (b : Basis J ℝ L)
    (F : L →ₗ[ℝ] L) {K : ℝ}
    (hF : ∀ j, ‖b.equivFun (F (b j))‖ ≤ K) (v : L) :
    ‖b.equivFun (F v)‖ ≤ (Fintype.card J : ℝ) * K * ‖b.equivFun v‖ := by
  conv_lhs => rw [← b.sum_repr v]
  rw [map_sum, map_sum]
  apply (norm_sum_le _ _).trans
  calc
    (∑ j, ‖b.equivFun (F (b.repr v j • b j))‖) ≤
        ∑ _j : J, ‖b.equivFun v‖ * K := by
      apply Finset.sum_le_sum
      intro j _
      rw [map_smul, map_smul, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (norm_le_pi_norm (b.equivFun v) j) (hF j)
        (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- A coordinate bound transfers to the exponential image when the maps
intertwine the exponential. -/
theorem image_exponentialCoordinateBox_subset
    {G J : Type*} [Fintype J] (b : Basis J ℝ L) (Exp : L → G)
    (F : L →ₗ[ℝ] L) (f : G → G) (hcomm : ∀ x, f (Exp x) = Exp (F x))
    {A : ℝ} (hA : 0 ≤ A) (hF : ∀ x, ‖b.equivFun (F x)‖ ≤ A * ‖b.equivFun x‖)
    (R : ℝ) : f '' exponentialCoordinateBox Exp b R ⊆ exponentialCoordinateBox Exp b (A * R) := by
  rintro _ ⟨_, ⟨x, rfl, hx⟩, rfl⟩
  exact ⟨F x, (hcomm x).symm, (hF x).trans (mul_le_mul_of_nonneg_left hx hA)⟩

namespace CartanWordModel

variable [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (LieAlgebra.ad ℝ L x) = 0)
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- A fixed degree bound for the finite list of actual words. -/
def wordDegreeBound : ℕ := ∑ w : M.wordList, bracketWordLength (w : FreeMagma (Fin M.letterCount))

omit T hunimod eW [FiniteDimensional ℝ L] [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] in
theorem word_degrees_le (w : M.wordList) :
    bracketWordNodes (w : FreeMagma (Fin M.letterCount)) ≤ M.wordDegreeBound ∧
      bracketWordLength (w : FreeMagma (Fin M.letterCount)) ≤ M.wordDegreeBound := by
  have h : bracketWordLength (w : FreeMagma (Fin M.letterCount)) ≤ M.wordDegreeBound :=
    Finset.single_le_sum (f := fun w : M.wordList => bracketWordLength (w : FreeMagma (Fin M.letterCount)))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ w)
  exact ⟨(by rw [bracketWordLength_eq_nodes_add_one] at h; omega), h⟩

/-- Root-space preservation and a bound on the unscaled letter images imply
a uniform polynomial bound on a Lie map in every maximizing scaled box. -/
theorem exists_box_lieMap_bound
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {E : Set W}, IsCompact E → E.Nonempty →
      ∀ β : M.Bases,
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (M.boxCost T hunimod eW E) β.val →
      ∀ r : ℝ, 0 ≤ r → ∀ (F : cartanRootIdeal H →ₗ⁅ℝ⁆ cartanRootIdeal H)
        (K : ℝ), 0 ≤ K →
      (∀ i, (F (M.letter i) : L) ∈ LieAlgebra.rootSpace H (M.weight i)) →
      (∀ i, ‖(WordBasisSelections.basis M.letter M.wordList β).equivFun
        (F (M.letter i))‖ ≤ K) →
      ∀ v, ‖(M.boxBasis T hunimod eW E β r).equivFun (F v)‖ ≤
        A * (1 + K) ^ M.wordDegreeBound * ‖(M.boxBasis T hunimod eW E β r).equivFun v‖ := by
  obtain ⟨C, hC, hbracket⟩ := exists_uniform_rescaled_structureConstant_bound
    M.letter M.bound_zero b₀
  let d := finrank ℝ (cartanRootIdeal H)
  let Q := 1 + (d : ℝ) ^ 2 * C
  refine ⟨(d : ℝ) * Q ^ M.wordDegreeBound, by positivity, ?_⟩
  intro E hE hne β hβ r hr F K hK hroot hF v
  let s := (M.supportIn T hunimod eW).weightSupport E
  let b := M.boxBasis T hunimod eW E β r
  let X : Fin M.letterCount → cartanRootIdeal H := fun i => Real.exp (r * s i) • M.letter i
  have hX (i : Fin M.letterCount) : ‖b.equivFun (F (X i))‖ ≤ K := by
    rw [show F (X i) = Real.exp (r * s i) • F (M.letter i) by exact F.map_smul _ _]
    exact (M.norm_scaled_root_le T hunimod eW hE hne β i (F (M.letter i)) (hroot i) hr).trans (hF i)
  have hb (i j k : Fin d) : |b.repr ⁅b i, b j⁆ k| ≤ C :=
    hbracket s β hβ r hr i j k
  have hword (w : M.wordList) :
      ‖b.equivFun (evalBracketWord (fun i => F (X i)) w)‖ ≤
        Q ^ M.wordDegreeBound * (1 + K) ^ M.wordDegreeBound := by
    have hh := norm_basis_evalBracketWord_le b (fun i => F (X i)) hC hK hb hX w
    simp only [Fintype.card_fin] at hh
    apply hh.trans
    have hd := M.word_degrees_le w
    change ((d : ℝ) ^ 2 * C) ^ bracketWordNodes (w : FreeMagma (Fin M.letterCount)) *
      K ^ bracketWordLength (w : FreeMagma (Fin M.letterCount)) ≤ _
    apply mul_le_mul
    · exact (pow_le_pow_left₀ (by positivity) (show (d : ℝ) ^ 2 * C ≤ Q by dsimp [Q]; linarith) _).trans
        (pow_le_pow_right₀ (by dsimp [Q]; exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) hC)) hd.1)
    · exact (pow_le_pow_left₀ hK (show K ≤ 1 + K by linarith) _).trans
        (pow_le_pow_right₀ (by linarith) hd.2)
    · positivity
    · positivity
  have hbase (j : Fin d) : ‖b.equivFun (F (b j))‖ ≤
      Q ^ M.wordDegreeBound * (1 + K) ^ M.wordDegreeBound := by
    have he : evalBracketWord X (β.val j) = b j := by
      rw [evalBracketWord_exp_smul]
      have h := WordBasisSelections.eval_words M.letter M.wordList β j
      change evalBracketWord M.letter (β.val j) = _ at h
      rw [h]
      simp only [b, boxBasis, exponentialRescaleBasis, Basis.unitsSMul_apply,
        Units.smul_def, Units.val_mk0]
      rfl
    rw [← he, evalBracketWord_map]
    exact hword (β.val j)
  have h := norm_basis_linearMap_le b F.toLinearMap hbase v
  simp only [Fintype.card_fin] at h
  change ‖b.equivFun (F v)‖ ≤ (d : ℝ) *
    (Q ^ M.wordDegreeBound * (1 + K) ^ M.wordDegreeBound) * ‖b.equivFun v‖ at h
  convert h using 1
  ring

variable {EN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N]
  (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
  (Exp : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExp : IsGroupExponential Exp)
  (hbij : Function.Bijective Exp) (dynkin : NilpotentDynkinExpansionInput EN N)

/-- The Lie-map estimate gives a bound on the actual nilpotent group boxes,
using the already constructed group automorphism. -/
theorem exists_groupBox_automorphism_bound
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {E : Set W}, IsCompact E → E.Nonempty →
      ∀ β : M.Bases,
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (M.boxCost T hunimod eW E) β.val →
      ∀ r : ℝ, 0 ≤ r → ∀ (F : cartanRootIdeal H ≃ₗ⁅ℝ⁆ cartanRootIdeal H)
        (K : ℝ), 0 ≤ K →
      (∀ i, (F (M.letter i) : L) ∈ LieAlgebra.rootSpace H (M.weight i)) →
      (∀ i, ‖(WordBasisSelections.basis M.letter M.wordList β).equivFun
        (F (M.letter i))‖ ≤ K) →
      ∀ R : ℝ,
      integrateNilpotentLieEquiv eN Exp hbij dynkin hExp M.bound_zero F ''
        M.groupBox T hunimod eW (Exp ∘ eN) E β r R ⊆
        M.groupBox T hunimod eW (Exp ∘ eN) E β r
          (A * (1 + K) ^ M.wordDegreeBound * R) := by
  obtain ⟨A, hA, hbound⟩ := M.exists_box_lieMap_bound T hunimod eW b₀
  refine ⟨A, hA, ?_⟩
  intro E hE hne β hβ r hr F K hK hroot hF R
  exact image_exponentialCoordinateBox_subset (M.boxBasis T hunimod eW E β r)
    (Exp ∘ eN) F.toLinearEquiv.toLinearMap
    (integrateNilpotentLieEquiv eN Exp hbij dynkin hExp M.bound_zero F)
    (integrateNilpotentLieEquiv_apply_exp eN Exp hbij dynkin hExp M.bound_zero F)
    (mul_nonneg hA (pow_nonneg (by linarith) _))
    (hbound hE hne β hβ r hr F.toLieHom K hK hroot hF) R

end CartanWordModel
end PolycyclicRecognition

end

end OAI
