import OAI.Analysis.LipschitzHilbert.Fourier.LocalAnnularVariation

namespace OAI

/-! Exhaust the line by growing roots while keeping the comparison mesh
fixed. The annular variation constant is independent of the root size. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators FourierTransform ENNReal NNReal

namespace LipschitzHilbert

def expandingGrid (N M : ℕ) : FiniteLineGrid where
  branching := 4
  branching_pos := by norm_num
  origin := -((4 : ℝ) ^ M) / 2
  width := (4 : ℝ) ^ M
  width_pos := by positivity
  depth := M + N

theorem expandingGrid_root (N M : ℕ) :
    (expandingGrid N M).root = Ico (-((4 : ℝ) ^ M) / 2) ((4 : ℝ) ^ M / 2) := by
  unfold FiniteLineGrid.root expandingGrid
  congr 1
  ring

theorem expandingGrid_mesh (N M i : ℕ) :
    (expandingGrid N M).meshWidth (M + i) = ((4 : ℝ) ^ i)⁻¹ := by
  simp only [FiniteLineGrid.meshWidth, expandingGrid, Nat.cast_ofNat, pow_add]
  field_simp

theorem expandingGrid_mono (N : ℕ) : Monotone (fun M => (expandingGrid N M).root) := by
  intro M K hMK
  change (expandingGrid N M).root ⊆ (expandingGrid N K).root
  rw [expandingGrid_root, expandingGrid_root]
  have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hMK
  exact Ico_subset_Ico (by linarith) (by linarith)

theorem expandingGrid_cover (N : ℕ) : (⋃ M, (expandingGrid N M).root) = univ := by
  ext x
  simp only [mem_iUnion, mem_univ, iff_true]
  obtain ⟨M,hM⟩ := pow_unbounded_of_one_lt (2 * |x|) (by norm_num : (1 : ℝ) < 4)
  refine ⟨M,?_⟩
  rw [expandingGrid_root]
  constructor <;> linarith [neg_abs_le x, le_abs_self x]

theorem scalar_annular_variation (hL : LepingleInput) :
    ∃ K : ℝ≥0, 0 < K ∧ ∀ (N : ℕ) (f : Fin N → SchwartzMap ℝ ℂ),
      (∀ j ξ, |ξ| < bandInner j.val → 𝓕 (f j) ξ = 0) →
      (∀ j ξ, bandOuter j.val < |ξ| → 𝓕 (f j) ξ = 0) →
      (∫⁻ x, ENNReal.ofReal (finiteCubicVariation (fun i => partialBandSum f i x) N) ^
        (2 / 3 : ℝ)) ≤
      (K : ℝ≥0∞) * ENNReal.ofReal (∑ j, ∫ x, ‖f j x‖ ^ 2) := by
  obtain ⟨K,hK,hbound⟩ := geometric_annular_variation hL
  refine ⟨K,hK,?_⟩
  intro N f hlow hhigh
  let V := fun x => ENNReal.ofReal (finiteCubicVariation (fun i => partialBandSum f i x) N) ^
    (2 / 3 : ℝ)
  change (∫⁻ x, V x) ≤ _
  rw [← setLIntegral_univ, ← expandingGrid_cover N,
    setLIntegral_iUnion_of_directed V (expandingGrid_mono N).directed_le]
  apply iSup_le
  intro M
  exact hbound N (expandingGrid N M) M f (by simp [expandingGrid])
    (expandingGrid_mesh N M) hlow hhigh

end LipschitzHilbert

end

end OAI
