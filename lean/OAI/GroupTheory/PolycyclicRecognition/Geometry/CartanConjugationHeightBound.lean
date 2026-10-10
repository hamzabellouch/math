import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanActualConjugation
import OAI.GroupTheory.PolycyclicRecognition.Analysis.TemplateBoxEnvelopes
import OAI.GroupTheory.PolycyclicRecognition.Analysis.TemplateSupportOrder
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RescaledBasisChange
import OAI.GroupTheory.PolycyclicRecognition.Analysis.RescaledBasisScaleChange
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubexponentialOperations

namespace OAI

/-! # The exact exponential height loss in conjugated Cartan boxes -/

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

/-- Conjugation changes a scaled box by a polynomial in the Cartan
logarithm and an exponential in its height. The height coefficient is
independent of the template, its scale and its maximizing basis. -/
theorem exists_adjoint_groupBox_height_bound
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) :
    ∃ (A K : ℝ) (p : ℕ), 0 ≤ A ∧ 0 ≤ K ∧
      ∀ {E : Set W}, IsCompact E → E.Nonempty → ∀ β : M.Bases,
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (M.boxCost T hunimod eW E) β.val →
      ∀ r : ℝ, 0 < r → ∀ (h : H) (R : ℝ) (g : N),
      g ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β r R →
      M.adjointGroupAutomorphism T eN Exp hExp hbij dynkin h g ∈
        M.groupBox T hunimod eW (Exp ∘ eN) E β r
          (A * (1 + ‖(finBasis ℝ H).equivFun h‖) ^ p *
            Real.exp (K * ‖eW (heightProjection T.character (h : L))‖) * R) := by
  obtain ⟨A, p, hA, hact⟩ := M.exists_adjoint_groupBox_bound T eN Exp hExp hbij dynkin
    hunimod eW b₀
  obtain ⟨K, hK, hcost⟩ := M.exists_boxCost_thickening_constant T hunimod eW
  refine ⟨A, K, p, hA, hK, ?_⟩
  intro E hE hne β hβ r hr h R g hg
  let w := r⁻¹ • eW (heightProjection T.character (h : L))
  have hh : eW (heightProjection T.character (h : L)) = r • w := by
    simp only [w, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have hw : r * ‖w‖ = ‖eW (heightProjection T.character (h : L))‖ := by
    dsimp only [w]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
    field_simp
  have hnear : ((fun x => x + w) '' E) ⊆ E + closedBall 0 ‖w‖ := by
    rintro y ⟨x, hx, rfl⟩
    exact add_mem_add hx (by simp)
  have hweights := (M.supportIn T hunimod eW).weightSupport_mono
    (hE.image (continuous_id.add continuous_const)) (hne.image _)
    (hE.add (isCompact_closedBall _ _)) hnear
  have hcost' z : M.boxCost T hunimod eW ((fun x => x + w) '' E) z ≤
      M.boxCost T hunimod eW E z + K * ‖w‖ := by
    apply le_trans _ (hcost hE hne (norm_nonneg w) z)
    unfold boxCost bracketWordExponent
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hweights i) (Nat.cast_nonneg _))
  obtain ⟨v, hv, hb⟩ := hact hE hne β hβ r hr.le h w hh R g hg
  refine ⟨v, hv, ?_⟩
  have hc := norm_change_exponentialRescaleBasis_le
    (WordBasisSelections.basis M.letter M.wordList β)
    (fun j => M.boxCost T hunimod eW E (β.val j))
    (fun j => M.boxCost T hunimod eW ((fun x => x + w) '' E) (β.val j))
    hr.le (α := K * ‖w‖) (fun j => by linarith [hcost' (β.val j)]) v
  change ‖(M.boxBasis T hunimod eW E β r).equivFun v‖ ≤
    Real.exp (r * (K * ‖w‖)) *
      ‖(M.boxBasis T hunimod eW ((fun x => x + w) '' E) β r).equivFun v‖ at hc
  have he : r * (K * ‖w‖) = K * ‖eW (heightProjection T.character (h : L))‖ := by
    rw [← hw]; ring
  rw [he] at hc
  exact hc.trans ((mul_le_mul_of_nonneg_left hb (Real.exp_nonneg _)).trans_eq (by ring))

/-- A strict gain in box scale absorbs the conjugation height loss.
The remaining radius shows the precise exponent margin used in the
basepoint sampling comparison. -/
theorem exists_adjoint_groupBox_scale_margin
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) :
    ∃ (A K : ℝ) (p : ℕ), 0 ≤ A ∧ 0 ≤ K ∧
      ∀ {E : Set W}, IsCompact E → E.Nonempty → ∀ β : M.Bases,
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (M.boxCost T hunimod eW E) β.val →
      ∀ lo : ℝ, (∀ w : M.wordList, lo ≤ M.boxCost T hunimod eW E w) →
      ∀ s t : ℝ, 0 < s → s ≤ t → ∀ (h : H) (R : ℝ) (g : N),
      g ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β s R →
      M.adjointGroupAutomorphism T eN Exp hExp hbij dynkin h g ∈
        M.groupBox T hunimod eW (Exp ∘ eN) E β t
          (A * (1 + ‖(finBasis ℝ H).equivFun h‖) ^ p * R *
            Real.exp (K * ‖eW (heightProjection T.character (h : L))‖ - (t - s) * lo)) := by
  obtain ⟨A, K, p, hA, hK, hbound⟩ := M.exists_adjoint_groupBox_height_bound
    T hunimod eW eN Exp hExp hbij dynkin b₀
  refine ⟨A, K, p, hA, hK, ?_⟩
  intro E hE hne β hβ lo hlo s t hs hst h R g hg
  obtain ⟨v, hv, hb⟩ := hbound hE hne β hβ s hs h R g hg
  refine ⟨v, hv, ?_⟩
  have hc := norm_scale_exponentialRescaleBasis_le
    (WordBasisSelections.basis M.letter M.wordList β)
    (fun j => M.boxCost T hunimod eW E (β.val j)) t s (-(t - s) * lo)
    (fun j => calc
      (s - t) * M.boxCost T hunimod eW E (β.val j) ≤ (s - t) * lo :=
        mul_le_mul_of_nonpos_left (hlo (β.val j)) (sub_nonpos.mpr hst)
      _ = _ := by ring) v
  change ‖(M.boxBasis T hunimod eW E β t).equivFun v‖ ≤
    Real.exp (-(t - s) * lo) * ‖(M.boxBasis T hunimod eW E β s).equivFun v‖ at hc
  apply hc.trans
  apply (mul_le_mul_of_nonneg_left hb (Real.exp_nonneg _)).trans_eq
  rw [show Real.exp (K * ‖eW (heightProjection T.character (h : L))‖ - (t - s) * lo) =
      Real.exp (K * ‖eW (heightProjection T.character (h : L))‖) *
        Real.exp (-((t - s) * lo)) by rw [Real.exp_sub, Real.exp_neg, div_eq_mul_inv]]
  rw [neg_mul]
  ac_rfl

/-- A positive exponent margin absorbs every polynomial logarithmic loss
and every subexponential input radius. This turns the quantitative bound
into the exact box inclusion required by Haar-density domination. -/
theorem exists_eventual_adjoint_box_inclusion
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {E : Set W} (hE : IsCompact E) (hne : E.Nonempty) (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    (lo : ℝ) (hlo : ∀ w : M.wordList, lo ≤ M.boxCost T hunimod eW E w) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ scale source target RH R heightBound : ℕ → ℝ,
      Tendsto scale atTop atTop →
      (∀ n, 0 ≤ RH n) → (∀ n, 0 ≤ R n) →
      HasSubexponentialUpperBoundSeq scale RH → HasSubexponentialUpperBoundSeq scale R →
      ∀ ε : ℝ, 0 < ε →
      (∀ᶠ n in atTop, 0 < source n ∧ source n ≤ target n ∧
        K * heightBound n - (target n - source n) * lo ≤ -ε * scale n) →
      ∀ᶠ n in atTop, ∀ h : H,
        ‖(finBasis ℝ H).equivFun h‖ ≤ RH n →
        ‖eW (heightProjection T.character (h : L))‖ ≤ heightBound n →
        ∀ g : N, g ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β (source n) (R n) →
        M.adjointGroupAutomorphism T eN Exp hExp hbij dynkin h g ∈
          M.groupBox T hunimod eW (Exp ∘ eN) E β (target n) 1 := by
  obtain ⟨A, K, p, hA, hK, hbound⟩ := M.exists_adjoint_groupBox_scale_margin
    T hunimod eW eN Exp hExp hbij dynkin b₀
  refine ⟨K, hK, ?_⟩
  intro scale source target RH R heightBound hs hRH0 hR0 hRH hR ε hε hgap
  let U := fun n => A * (1 + RH n) ^ p * R n
  have hU : HasSubexponentialUpperBoundSeq scale U :=
    ((sequence_subexponential_upper_const hs A).mul
      (((sequence_subexponential_upper_const hs 1).add hRH hs).pow hs
        (Eventually.of_forall (fun n => by linarith [hRH0 n])) p)
      (Eventually.of_forall (fun _ => hA))).mul hR
      (Eventually.of_forall (fun n => mul_nonneg hA (pow_nonneg (by linarith [hRH0 n]) _)))
  filter_upwards [hgap, hU ε hε] with n hn hUn h hh hheight g hg
  obtain ⟨v, hv, hc⟩ := hbound hE hne β hβ lo hlo (source n) (target n)
    hn.1 hn.2.1 h (R n) g hg
  refine ⟨v, hv, hc.trans ?_⟩
  have hp : (1 + ‖(finBasis ℝ H).equivFun h‖) ^ p ≤ (1 + RH n) ^ p :=
    pow_le_pow_left₀ (by positivity) (by linarith) p
  have he : Real.exp (K * ‖eW (heightProjection T.character (h : L))‖ -
      (target n - source n) * lo) ≤ Real.exp (-ε * scale n) := by
    apply Real.exp_le_exp.mpr
    exact (sub_le_sub_right (mul_le_mul_of_nonneg_left hheight hK) _).trans hn.2.2
  calc
    _ ≤ U n * Real.exp (-ε * scale n) := by
      apply mul_le_mul _ he (Real.exp_nonneg _) ?_
      · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hA) (hR0 n)
      · exact mul_nonneg (mul_nonneg hA (pow_nonneg (by linarith [hRH0 n]) _)) (hR0 n)
    _ ≤ Real.exp (ε * scale n) * Real.exp (-ε * scale n) :=
      mul_le_mul_of_nonneg_right hUn (Real.exp_nonneg _)
    _ = 1 := by rw [← Real.exp_add]; simp

end PolycyclicRecognition.CartanWordModel

end

end OAI
