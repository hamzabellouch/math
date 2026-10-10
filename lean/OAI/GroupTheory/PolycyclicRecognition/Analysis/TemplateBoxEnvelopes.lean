import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanGroupBoxes
import OAI.GroupTheory.PolycyclicRecognition.Analysis.WordBoxComparison

namespace OAI

/-! # A single box envelope for vanishing template thickenings -/

noncomputable section
namespace PolycyclicRecognition

open Module LieModule Set Filter Metric
open scoped Topology Pointwise

namespace SupportDatum

variable {W I B : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B] [Nonempty B]
  (D : SupportDatum W I B)

omit [Nonempty B] in
/-- Thickening the height template changes each weight by at most its
operator norm times the thickening radius. -/
theorem weightSupport_thickening_le {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    {ε : ℝ} (hε : 0 ≤ ε) (i : I) :
    D.weightSupport (E + closedBall 0 ε) i ≤
      D.weightSupport E i + ‖(D.weight i).toContinuousLinearMap‖ * ε := by
  have hne' : (E + closedBall (0 : W) ε).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨x + 0, add_mem_add hx (by simpa using hε)⟩
  apply D.weightSupport_le_of_nearby (hE.add (isCompact_closedBall 0 ε)) hne' hE
  rintro x ⟨y, hy, z, hz, rfl⟩
  refine ⟨y, hy, ?_⟩
  simpa only [add_sub_cancel_left, mem_closedBall, dist_zero_right] using hz

end SupportDatum

theorem bracketWordExponent_le_add_of_le {I : Type*} [Fintype I] [DecidableEq I]
    (s t u : I → ℝ) (h : ∀ i, s i ≤ t i + u i) (w : FreeMagma I) :
    bracketWordExponent s w ≤ bracketWordExponent t w + bracketWordExponent u w := by
  rw [← bracketWordExponent_add]
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (h i) (Nat.cast_nonneg _))

namespace CartanWordModel

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (LieAlgebra.ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- The finite word list has one constant for all compact templates. -/
theorem exists_boxCost_thickening_constant :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {E : Set W}, IsCompact E → E.Nonempty →
      ∀ {ε : ℝ}, 0 ≤ ε → ∀ w : M.wordList,
        M.boxCost T hunimod eW (E + closedBall 0 ε) w ≤
          M.boxCost T hunimod eW E w + C * ε := by
  let D := M.supportIn T hunimod eW
  let c := fun w : M.wordList =>
    ∑ i, (bracketWordCount (w : FreeMagma (Fin M.letterCount)) i : ℝ) *
      ‖(D.weight i).toContinuousLinearMap‖
  let C := ∑ w, c w
  have hc (w : M.wordList) : 0 ≤ c w :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
  have hC : 0 ≤ C := Finset.sum_nonneg (fun w _ => hc w)
  have hcC (w : M.wordList) : c w ≤ C :=
    Finset.single_le_sum (fun w _ => hc w) (Finset.mem_univ w)
  refine ⟨C, hC, ?_⟩
  intro E hE hne ε hε w
  have hh := bracketWordExponent_le_add_of_le
    (D.weightSupport (E + closedBall 0 ε)) (D.weightSupport E)
    (fun i => ‖(D.weight i).toContinuousLinearMap‖ * ε)
    (D.weightSupport_thickening_le hE hne hε) w.val
  have he : bracketWordExponent (fun i => ‖(D.weight i).toContinuousLinearMap‖ * ε) w.val =
      c w * ε := by simp only [bracketWordExponent, c, Finset.sum_mul, mul_assoc]
  change bracketWordExponent (D.weightSupport (E + closedBall 0 ε)) w.val ≤
    bracketWordExponent (D.weightSupport E) w.val + C * ε
  rw [he] at hh
  exact hh.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right (hcC w) hε))

/-- Every enlarged-template box is contained in one fixed-template box
with a common subexponential radius. The enlarged maximizing basis may
change at every scale, or between endpoints at the same scale. -/
theorem exists_template_box_envelope_sequence {N : Type*}
    (Exp : cartanRootIdeal H → N)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    (scale ε R : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (hscale0 : ∀ n, 0 ≤ scale n) (hε0 : ∀ n, 0 ≤ ε n) (hε : Tendsto ε atTop (𝓝 0))
    (hR0 : ∀ n, 0 ≤ R n) (hR : HasSubexponentialUpperBoundSeq scale R) :
    ∃ V : ℕ → ℝ, (∀ n, 0 ≤ V n) ∧ HasSubexponentialUpperBoundSeq scale V ∧
      ∀ n (γ : M.Bases),
        M.groupBox T hunimod eW Exp (E + closedBall 0 (ε n)) γ (scale n) (R n) ⊆
          M.groupBox T hunimod eW Exp E β (scale n) (V n) := by
  obtain ⟨C, _, hcost⟩ := M.exists_boxCost_thickening_constant T hunimod eW
  have heps : Tendsto (fun n => C * ε n) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hε
  obtain ⟨V, hV0, hV, hv⟩ := exists_sequence_word_box_envelope M.letter M.wordList b₀
    (M.boxCost T hunimod eW E) β hβ scale (fun n => C * ε n) R hscale hscale0 heps hR0 hR
  refine ⟨V, hV0, hV, ?_⟩
  intro n γ x hx
  obtain ⟨v, he, hb⟩ := hx
  exact ⟨v, he, hv n (M.boxCost T hunimod eW (E + closedBall 0 (ε n))) γ
    (hcost hE hne (hε0 n)) v hb⟩

end CartanWordModel
end PolycyclicRecognition

end

end OAI
