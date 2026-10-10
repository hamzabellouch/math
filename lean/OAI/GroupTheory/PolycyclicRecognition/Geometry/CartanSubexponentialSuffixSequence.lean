import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSuffixGeneratorSequence
import OAI.GroupTheory.PolycyclicRecognition.Analysis.RescaledBasisScaleChange
import OAI.GroupTheory.PolycyclicRecognition.Algebra.WordExponentBounds
import OAI.GroupTheory.PolycyclicRecognition.Analysis.BoxCoordinateChanges

namespace OAI

/-! # Bounded root chains for subexponentially large suffixes -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieModule Filter
open scoped Manifold Topology

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

include T in
/-- A vanishing relative enlargement of the scale absorbs the entire
subexponential radius. The resulting word has fixed length, and its
prefixes and coefficients obey the original-scale bounds. -/
theorem exists_cartan_subexponential_suffix_sequence
    [Nonempty (Fin M.letterCount)]
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) :
    ∃ (N : ℕ) (C : ℝ), 1 ≤ C ∧
      ∀ (s t : Fin M.letterCount → ℝ), (∀ i, 0 < s i) → (∀ i, s i ≤ t i) →
      ∀ (β γ : M.Bases),
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (fun w => bracketWordExponent s w) β.val →
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (fun w => bracketWordExponent t w) γ.val →
      ∀ (scale : ℕ → ℝ), Tendsto scale atTop atTop → (∀ n, 1 ≤ scale n) →
      ∀ (ε₀ : ℕ → ℝ), (∀ n, 0 ≤ ε₀ n) → Tendsto ε₀ atTop (𝓝 0) →
      ∀ (base : ℕ → cartanRootIdeal H),
      (∀ n, ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList γ)
        (fun j => bracketWordExponent t (γ.val j)) (scale n)).equivFun (base n)‖ ≤
          Real.exp (scale n * ε₀ n)) →
      ∀ (K : Type*) (v : ℕ → K → cartanRootIdeal H),
      (∀ n q, ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun j => bracketWordExponent s (β.val j)) (scale n)).equivFun (v n q)‖ ≤
          Real.exp (scale n * ε₀ n)) →
      ∃ (ε : ℕ → ℝ) (vertex : ℕ → K → Fin (N + 1) → cartanRootIdeal H)
        (mode : ℕ → K → Fin N → Fin M.letterCount) (coeff : ℕ → K → Fin N → ℝ),
        (∀ n, 0 ≤ ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
        (∀ n q, vertex n q 0 = base n) ∧
        (∀ n q, F.ExpN (F.N.equiv (vertex n q (Fin.last N))) =
          F.ExpN (F.N.equiv (base n)) * F.ExpN (F.N.equiv (v n q))) ∧
        (∀ n q j, ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList γ)
          (fun j => bracketWordExponent t (γ.val j)) (scale n)).equivFun (vertex n q j)‖ ≤
            Real.exp (scale n * ε n)) ∧
        (∀ n q j, |coeff n q j| ≤ C * Real.exp (scale n * (s (mode n q j) + ε n))) ∧
        (∀ n q j, F.ExpN (F.N.equiv (vertex n q j.succ)) =
          F.ExpN (F.N.equiv (vertex n q j.castSucc)) *
            F.ExpN (F.N.equiv (coeff n q j • M.letter (mode n q j)))) := by
  obtain ⟨N, C, hC, hchain⟩ := M.exists_cartan_suffix_generator_sequence T F
    hExpG realize haarN dynkinN b₀ 1
  refine ⟨N, C, hC, ?_⟩
  intro s t hs hst β γ hβ hγ scale hscale hscale1 ε₀ hε₀0 hε₀ base hbase K v hv
  obtain ⟨lo, _, hlo, _, hlow⟩ := exists_positive_wordExponent_bounds s hs M.wordList
  obtain ⟨_, hi, _, hhi, hhigh⟩ := exists_positive_wordExponent_bounds t
    (fun i => (hs i).trans_le (hst i)) M.wordList
  let α : ℕ → ℝ := fun n => ε₀ n / lo
  let larger : ℕ → ℝ := fun n => scale n * (1 + α n)
  have hα0 n : 0 ≤ α n := div_nonneg (hε₀0 n) hlo.le
  have hα : Tendsto α atTop (𝓝 0) := by
    simpa only [div_zero, zero_div] using hε₀.div_const lo
  have hscale0 n : 0 ≤ scale n := (by norm_num : (0 : ℝ) ≤ 1).trans (hscale1 n)
  have hle n : scale n ≤ larger n := by
    dsimp [larger]
    nlinarith [mul_nonneg (hscale0 n) (hα0 n)]
  have hlarge : Tendsto larger atTop atTop := tendsto_atTop_mono hle hscale
  have hlarge1 n : 1 ≤ larger n := (hscale1 n).trans (hle n)
  have hshrink (n : ℕ) (b : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ
      (cartanRootIdeal H)) (cost : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ)
      (hcost : ∀ j, lo ≤ cost j) (x : cartanRootIdeal H)
      (hx : ‖(exponentialRescaleBasis b cost (scale n)).equivFun x‖ ≤
        Real.exp (scale n * ε₀ n)) :
      ‖(exponentialRescaleBasis b cost (larger n)).equivFun x‖ ≤ 1 := by
    have hg j : (scale n - larger n) * cost j ≤ -(scale n * ε₀ n) := calc
      _ = -(scale n * α n) * cost j := by dsimp [larger]; ring
      _ ≤ -(scale n * α n) * lo :=
        mul_le_mul_of_nonpos_left (hcost j) (neg_nonpos.mpr (mul_nonneg (hscale0 n) (hα0 n)))
      _ = _ := by dsimp [α]; field_simp
    calc
      _ ≤ Real.exp (-(scale n * ε₀ n)) *
          ‖(exponentialRescaleBasis b cost (scale n)).equivFun x‖ :=
        norm_scale_exponentialRescaleBasis_le b cost (larger n) (scale n) _ hg x
      _ ≤ Real.exp (-(scale n * ε₀ n)) * Real.exp (scale n * ε₀ n) :=
        mul_le_mul_of_nonneg_left hx (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  have hbase' n : ‖(exponentialRescaleBasis
      (WordBasisSelections.basis M.letter M.wordList γ)
      (fun j => bracketWordExponent t (γ.val j)) (larger n)).equivFun (base n)‖ ≤
      Real.exp (larger n * 0) := by
    simp only [mul_zero, Real.exp_zero]
    exact hshrink n _ _ (fun j => (hlow (γ.val j)).1.trans
      (bracketWordExponent_mono hst _)) _ (hbase n)
  have hv' n q : ‖(exponentialRescaleBasis
      (WordBasisSelections.basis M.letter M.wordList β)
      (fun j => bracketWordExponent s (β.val j)) (larger n)).equivFun (v n q)‖ ≤ 1 :=
    hshrink n _ _ (fun j => (hlow (β.val j)).1) _ (hv n q)
  obtain ⟨ε₂, vertex, mode, coeff, hε₂0, hε₂, hstart, hend, hvertex, hcoeff, hedge⟩ :=
    hchain s t hst β γ hβ hγ larger hlarge hlarge1 (fun _ => 0)
      (fun _ => le_rfl) tendsto_const_nhds base hbase' K v hv'
  let ε : ℕ → ℝ := fun n => α n * hi + (1 + α n) * ε₂ n
  have hε0 n : 0 ≤ ε n := add_nonneg (mul_nonneg (hα0 n) hhi)
    (mul_nonneg (by linarith [hα0 n]) (hε₂0 n))
  have hε : Tendsto ε atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero, zero_mul] using
      (hα.mul_const hi).add ((tendsto_const_nhds.add hα).mul hε₂)
  refine ⟨ε, vertex, mode, coeff, hε0, hε, hstart, hend, ?_, ?_, hedge⟩
  · intro n q j
    have hg k : (larger n - scale n) * bracketWordExponent t (γ.val k) ≤
        scale n * α n * hi := by
      have h := mul_le_mul_of_nonneg_left (hhigh (γ.val k)).2
        (mul_nonneg (hscale0 n) (hα0 n))
      dsimp [larger]
      nlinarith
    calc
      _ ≤ Real.exp (scale n * α n * hi) *
          ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList γ)
            (fun k => bracketWordExponent t (γ.val k)) (larger n)).equivFun (vertex n q j)‖ :=
        norm_scale_exponentialRescaleBasis_le _ _ (scale n) (larger n) _ hg _
      _ ≤ Real.exp (scale n * α n * hi) * Real.exp (larger n * ε₂ n) :=
        mul_le_mul_of_nonneg_left (hvertex n q j) (Real.exp_pos _).le
      _ = Real.exp (scale n * ε n) := by
        rw [← Real.exp_add]
        congr 1
        dsimp [larger, ε]
        ring
  · intro n q j
    apply (hcoeff n q j).trans
    apply mul_le_mul_of_nonneg_left _ ((by norm_num : (0 : ℝ) ≤ 1).trans hC)
    apply Real.exp_le_exp.mpr
    have hi' : s (mode n q j) ≤ hi := (hst _).trans (by
      simpa only [bracketWordExponent_of] using
        (hhigh ⟨FreeMagma.of (mode n q j), M.letter_mem_wordList _⟩).2)
    have hmul := mul_le_mul_of_nonneg_left hi' (hα0 n)
    have := mul_le_mul_of_nonneg_left hmul (hscale0 n)
    dsimp [larger, ε]
    nlinarith

end PolycyclicRecognition.CartanWordModel

end

end OAI
