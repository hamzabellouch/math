import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanControlledAction
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RescaledBasisChange

namespace OAI

/-! # Homothetic templates and the interior gain for Cartan actions -/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra LieModule
open scoped BigOperators

namespace SupportDatum

/-- Positive homotheties scale each letter support exactly. -/
theorem weightSupport_image_smul
    {W I B : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] [Fintype I] [Fintype B]
    (D : SupportDatum W I B) {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    {t : ℝ} (ht : 0 ≤ t) (i : I) :
    D.weightSupport ((fun x => t • x) '' E) i = t * D.weightSupport E i := by
  have hc : IsCompact ((fun x : W => t • x) '' E) :=
    hE.image (continuous_const.smul continuous_id : Continuous (fun x : W => t • x))
  have hn := hne.image (fun x => t • x)
  obtain ⟨x, hx, hs⟩ := D.exists_weightSupport_point hE hne i
  obtain ⟨_, ⟨y, hy, rfl⟩, hs'⟩ := D.exists_weightSupport_point hc hn i
  apply le_antisymm
  · rw [hs', map_smul, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (D.weight_le_weightSupport hE hy i) ht
  · rw [hs, ← smul_eq_mul, ← map_smul]
    exact D.weight_le_weightSupport hc ⟨x, hx, rfl⟩ i

end SupportDatum

namespace CartanWordModel

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- Homothety scales every actual word cost, including zero-weight words. -/
theorem boxCost_image_smul {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    {t : ℝ} (ht : 0 ≤ t) (w : M.wordList) :
    M.boxCost T hunimod eW ((fun x => t • x) '' E) w =
      t * M.boxCost T hunimod eW E w := by
  simp only [boxCost, bracketWordExponent,
    (M.supportIn T hunimod eW).weightSupport_image_smul hE hne ht, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A maximizing basis is unchanged by a nonnegative homothety. -/
theorem maximizing_box_basis_smul
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {E : Set W} (hE : IsCompact E) (hne : E.Nonempty) {t : ℝ} (ht : 0 ≤ t)
    (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val) :
    IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW ((fun x => t • x) '' E)) β.val := by
  refine ⟨hβ.1, ?_⟩
  intro γ hγ
  simp only [columnBasisWeight, M.boxCost_image_smul T hunimod eW hE hne ht,
    ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (hβ.2 γ hγ) ht

/-- Coordinates in a smaller homothetic box gain a definite exponential
factor when measured in the original box. -/
theorem norm_boxBasis_interior_le
    {E : Set W} (hE : IsCompact E) (hne : E.Nonempty) {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (β : M.Bases) {r lo : ℝ} (hr : 0 ≤ r)
    (hlo : ∀ w : M.wordList, lo ≤ M.boxCost T hunimod eW E w)
    (v : cartanRootIdeal H) :
    ‖(M.boxBasis T hunimod eW E β r).equivFun v‖ ≤
      Real.exp (r * ((t - 1) * lo)) *
        ‖(M.boxBasis T hunimod eW ((fun x => t • x) '' E) β r).equivFun v‖ := by
  apply norm_change_exponentialRescaleBasis_le _ _ _ hr _ v
  intro i
  rw [M.boxCost_image_smul T hunimod eW hE hne ht]
  have h := mul_le_mul_of_nonpos_left (hlo (β.val i)) (sub_nonpos.mpr ht1)
  nlinarith

/-- The actual Cartan action has the interior exponential gain, up to the
already proved polynomial residual action. -/
theorem exists_interior_adjoint_bound
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) :
    ∃ (A : ℝ) (p : ℕ), 0 ≤ A ∧ ∀ {E : Set W}, IsCompact E → E.Nonempty →
      ∀ {t : ℝ}, 0 ≤ t → t ≤ 1 → ∀ (β : M.Bases),
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (M.boxCost T hunimod eW E) β.val →
      ∀ (γ : M.Bases) (r lo : ℝ), 0 ≤ r →
      (∀ w : M.wordList, lo ≤ M.boxCost T hunimod eW E w) →
      ∀ (h : H) (w : W), w ∈ (fun x => t • x) '' E →
      eW (heightProjection T.character (h : L)) = r • w → ∀ v : cartanRootIdeal H,
      ‖(M.boxBasis T hunimod eW E β r).equivFun
        (cartanIdealAdjointAutomorphism T H h v)‖ ≤
      Real.exp (r * ((t - 1) * lo)) *
        (A * (1 + ‖(Module.finBasis ℝ H).equivFun h‖) ^ p *
          ‖(WordBasisSelections.basis M.letter M.wordList γ).equivFun v‖) := by
  obtain ⟨A, p, hA, hbound⟩ := M.exists_controlled_adjoint_bound T hunimod eW b₀
  refine ⟨A, p, hA, ?_⟩
  intro E hE hne t ht ht1 β hβ γ r lo hr hlo h w hw hh v
  apply (M.norm_boxBasis_interior_le T hunimod eW hE hne ht ht1 β hr hlo _).trans
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  exact hbound (hE.image (continuous_const.smul continuous_id)) (hne.image _)
    β (M.maximizing_box_basis_smul T hunimod eW b₀ hE hne ht β hβ)
    γ r hr h w hw hh v

end CartanWordModel
end PolycyclicRecognition

end

end OAI
