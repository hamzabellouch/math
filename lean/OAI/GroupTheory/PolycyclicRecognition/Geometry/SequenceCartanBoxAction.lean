import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanActualConjugation
import OAI.GroupTheory.PolycyclicRecognition.Analysis.TemplateBoxEnvelopes
import OAI.GroupTheory.PolycyclicRecognition.Analysis.TemplateSupportOrder

namespace OAI

/-! # Vanishing-height Cartan conjugation preserves a scaled template box

The input box is already exponentially scaled. The small translation of its
template is absorbed into one subexponential radius in the original basis.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra Filter Set Metric
open scoped Manifold Topology Pointwise

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  {EN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N]
  (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
  (Exp : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExp : IsGroupExponential Exp)
  (hbij : Function.Bijective Exp) (dynkin : NilpotentDynkinExpansionInput EN N)

theorem exists_sequence_small_height_box_action
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {E : Set W} (hE : IsCompact E) (hne : E.Nonempty) (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    (scale RH R η : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hscale : ∀ n, 0 < scale n) (hRH0 : ∀ n, 0 ≤ RH n) (hR0 : ∀ n, 0 ≤ R n)
    (hη0 : ∀ n, 0 ≤ η n) (hRH : HasSubexponentialUpperBoundSeq scale RH)
    (hR : HasSubexponentialUpperBoundSeq scale R) (hη : Tendsto η atTop (𝓝 0)) :
    ∃ S : ℕ → ℝ, (∀ n, 0 ≤ S n) ∧ HasSubexponentialUpperBoundSeq scale S ∧
      ∀ n (h : H) (g : N), ‖(finBasis ℝ H).equivFun h‖ ≤ RH n →
        ‖eW (heightProjection T.character (h : L))‖ ≤ η n * scale n →
        g ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) (R n) →
        M.adjointGroupAutomorphism T eN Exp hExp hbij dynkin h g ∈
          M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) (S n) := by
  obtain ⟨A, p, hA, hact⟩ := M.exists_adjoint_groupBox_bound T eN Exp hExp hbij dynkin
    hunimod eW b₀
  obtain ⟨C, _, hcost⟩ := M.exists_boxCost_thickening_constant T hunimod eW
  let R' := fun n => A * (1 + RH n) ^ p * R n
  have hR'0 : ∀ n, 0 ≤ R' n := fun n =>
    mul_nonneg (mul_nonneg hA (pow_nonneg (by linarith [hRH0 n]) p)) (hR0 n)
  have hR' : HasSubexponentialUpperBoundSeq scale R' :=
    ((sequence_subexponential_upper_const hs A).mul
      (((sequence_subexponential_upper_const hs 1).add hRH hs).pow hs
        (Eventually.of_forall (fun n => by linarith [hRH0 n])) p)
      (Eventually.of_forall (fun _ => hA))).mul hR
        (Eventually.of_forall (fun n => mul_nonneg hA (pow_nonneg (by linarith [hRH0 n]) p)))
  have hCη : Tendsto (fun n => C * η n) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hη
  obtain ⟨S, hS0, hS, henclose⟩ := exists_sequence_word_box_envelope M.letter M.wordList b₀
    (M.boxCost T hunimod eW E) β hβ scale (fun n => C * η n) R' hs
    (fun n => (hscale n).le) hCη hR'0 hR'
  refine ⟨S, hS0, hS, ?_⟩
  intro n h g hlog hh hg
  let w := (scale n)⁻¹ • eW (heightProjection T.character (h : L))
  have hw : ‖w‖ ≤ η n := by
    dsimp only [w]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (hscale n), inv_mul_eq_div]
    exact (div_le_iff₀ (hscale n)).mpr hh
  have hh' : eW (heightProjection T.character (h : L)) = scale n • w := by
    simp only [w, smul_smul, mul_inv_cancel₀ (hscale n).ne', one_smul]
  have hg' := hact hE hne β hβ (scale n) (hscale n).le h w hh' (R n) g hg
  obtain ⟨v, hv, hb⟩ := hg'
  refine ⟨v, hv, henclose n (M.boxCost T hunimod eW ((fun x => x + w) '' E)) β ?_ v ?_⟩
  · intro z
    have hnear : ((fun x => x + w) '' E) ⊆ E + closedBall 0 (η n) := by
      rintro y ⟨x, hx, rfl⟩
      exact add_mem_add hx (by simpa using hw)
    have hweights := (M.supportIn T hunimod eW).weightSupport_mono
      (hE.image (continuous_id.add continuous_const)) (hne.image _) (hE.add (isCompact_closedBall _ _)) hnear
    apply le_trans _ (hcost hE hne (hη0 n) z)
    unfold boxCost bracketWordExponent
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hweights i) (Nat.cast_nonneg _))
  · apply hb.trans
    dsimp only [R']
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) p) hA) (hR0 n)

end PolycyclicRecognition.CartanWordModel

end

end OAI
